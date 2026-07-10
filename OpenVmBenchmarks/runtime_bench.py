#!/usr/bin/env python3
"""Benchmark the *runtime* of the optimizer over a benchmark set.

For each case, run:
  - `apc-optimizer run <case>`      -> wall time of the whole optimizer call (the "(N ms)" line)
  - `apc-optimizer profile <case>`  -> per-pass timing, cumulative across all fixpoint iterations

and aggregate: total/mean/median optimizer time, the slowest cases, and where the time goes
per pass across the whole set. Cases run *serially* so timings don't fight for cores.

This measures runtime only; effectiveness is benchmark.py's job.

    OpenVmBenchmarks/runtime_bench.py                 # all openvm-eth cases
    OpenVmBenchmarks/runtime_bench.py --n 20          # top 20 by cost rank
    OpenVmBenchmarks/runtime_bench.py --repeat 3      # best-of-3 per case (less noise)
    OpenVmBenchmarks/runtime_bench.py --md bench.md   # also write a markdown summary
"""
from __future__ import annotations

import argparse
import os
import re
import statistics
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent      # OpenVmBenchmarks
REPO = Path(__file__).resolve().parents[1]  # OpenVmBenchmarks -> repo root
DEFAULT_BENCHMARK = "openvm-eth"

# `apc-optimizer run` total, e.g. "  (339 ms)".
RUN_MS_RE = re.compile(r"^\s*\((\d+) ms\)\s*$", re.M)
# `apc-optimizer profile` header, e.g. "profile <file>: 3 cleanup iterations, 311 ms total".
PROFILE_HEAD_RE = re.compile(r": (\d+) cleanup iterations, (\d+) ms total")
# `apc-optimizer profile` per-pass line, e.g. "  domainBatch: 258 ms".
PROFILE_PASS_RE = re.compile(r"^\s+(\w+): (\d+) ms$", re.M)


def best_of(cmd, repeat, parse):
    """Run `cmd` `repeat` times, parse each output, return the result with the smallest key.
    Taking the minimum discards scheduling noise (the optimizer is deterministic)."""
    best = None
    for _ in range(repeat):
        out = subprocess.run(cmd, capture_output=True, text=True, check=True).stdout
        parsed = parse(out)
        if parsed is None:
            raise ValueError(f"could not parse output of {' '.join(map(str, cmd))}:\n{out}")
        if best is None or parsed[0] < best[0]:
            best = parsed
    return best


def parse_run(out):
    m = RUN_MS_RE.search(out)
    return (int(m.group(1)),) if m else None


def parse_profile(out):
    m = PROFILE_HEAD_RE.search(out)
    if not m:
        return None
    passes = {name: int(ms) for name, ms in PROFILE_PASS_RE.findall(out)}
    return int(m.group(2)), int(m.group(1)), passes


def fmt_ms(ms):
    return f"{ms / 1000:.1f} s" if ms >= 10_000 else f"{ms} ms"


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("benchmark", nargs="?", default=DEFAULT_BENCHMARK,
                    help=f"benchmark name -- a subdirectory of OpenVmBenchmarks/ "
                         f"(default: {DEFAULT_BENCHMARK})")
    ap.add_argument("--n", type=int, default=None, metavar="N",
                    help="only the top N cases by cost rank (default: all)")
    ap.add_argument("--repeat", type=int, default=1,
                    help="runs per case; the fastest is kept (default: 1)")
    ap.add_argument("--no-build", action="store_true",
                    help="skip `lake build` (the binary must already exist)")
    ap.add_argument("--md", type=Path, default=None, metavar="OUT.md",
                    help="also write a markdown summary (for CI job summaries / PR comments)")
    args = ap.parse_args()

    bench_dir = HERE / args.benchmark
    if not bench_dir.is_dir():
        sys.exit(f"error: no benchmark {args.benchmark!r} under {HERE}")

    os.chdir(REPO)
    if not args.no_build:
        print("building apc-optimizer...", file=sys.stderr)
        subprocess.run(["lake", "build"], check=True)
    binary = REPO / ".lake" / "build" / "bin" / "apc-optimizer"
    if not binary.exists():
        sys.exit(f"error: {binary} missing (build first or drop --no-build)")

    cases = sorted(f for f in bench_dir.glob("apc_*_pc*.json.gz")
                   if not f.name.endswith(".powdr_opt.json.gz"))
    if not cases:
        sys.exit(f"no benchmark cases in {bench_dir}")
    if args.n is not None:
        cases = cases[: args.n]

    run_ms = {}          # case name -> optimizer call wall time (ms)
    pass_ms = {}         # pass name -> cumulative ms across all cases
    iters = {}           # case name -> cleanup iterations
    for i, case in enumerate(cases):
        (total,) = best_of([str(binary), "run", str(case)], args.repeat, parse_run)
        _, its, passes = best_of([str(binary), "profile", str(case)], args.repeat, parse_profile)
        run_ms[case.name] = total
        iters[case.name] = its
        for name, ms in passes.items():
            pass_ms[name] = pass_ms.get(name, 0) + ms
        print(f"[{i + 1}/{len(cases)}] {case.name}: {fmt_ms(total)}, {its} iterations",
              file=sys.stderr)

    times = sorted(run_ms.values())
    total = sum(times)
    slowest = sorted(run_ms.items(), key=lambda kv: -kv[1])[:10]
    pass_total = sum(pass_ms.values())
    passes = sorted(pass_ms.items(), key=lambda kv: -kv[1])

    lines = []
    lines.append(f"### Optimizer runtime — {args.benchmark}, {len(cases)} cases"
                 + (f", best of {args.repeat}" if args.repeat > 1 else ""))
    lines.append("")
    lines.append(f"| total | mean | median | max |")
    lines.append(f"|---|---|---|---|")
    lines.append(f"| {fmt_ms(total)} | {fmt_ms(total // len(times))} "
                 f"| {fmt_ms(int(statistics.median(times)))} | {fmt_ms(times[-1])} |")
    lines.append("")
    lines.append("<details><summary>Slowest cases (whole optimizer call)</summary>")
    lines.append("")
    lines.append("| case | time |")
    lines.append("|---|---|")
    for name, ms in slowest:
        lines.append(f"| {name} | {fmt_ms(ms)} |")
    lines.append("")
    lines.append("</details>")
    lines.append("")
    lines.append(f"Per-pass time, cumulative over all cases and fixpoint iterations "
                 f"({fmt_ms(pass_total)} attributed):")
    lines.append("")
    lines.append("| pass | time | share |")
    lines.append("|---|---|---|")
    for name, ms in passes:
        if ms == 0:
            continue
        share = 100 * ms / pass_total if pass_total else 0
        lines.append(f"| {name} | {fmt_ms(ms)} | {share:.1f}% |")
    zero = [name for name, ms in passes if ms == 0]
    if zero:
        lines.append(f"| {', '.join(zero)} | 0 ms | — |")
    lines.append("")
    lines.append(f"Cleanup iterations per case: "
                 f"min {min(iters.values())}, median {int(statistics.median(iters.values()))}, "
                 f"max {max(iters.values())}.")
    md = "\n".join(lines) + "\n"

    print()
    print(md)
    if args.md is not None:
        args.md.write_text(md)
        print(f"wrote {args.md}", file=sys.stderr)


if __name__ == "__main__":
    main()
