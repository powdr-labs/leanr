#!/usr/bin/env python3
"""Benchmark the *runtime* of the optimizer over a benchmark set.

For each case, run:
  - `apc-optimizer run <case>`      -> wall time of the whole optimizer call (the "(N ms)" line)
  - `apc-optimizer profile <case>`  -> per-pass timing, cumulative across all fixpoint iterations

and aggregate: total/mean/median optimizer time, the slowest cases, and where the time goes
per pass across the whole set. Cases run *serially* so timings don't fight for cores.

This measures runtime only; effectiveness is benchmark.py's job.

    Benchmarks/runtime_bench.py                 # all openvm-eth cases
    Benchmarks/runtime_bench.py --n 20          # top 20 by cost rank
    Benchmarks/runtime_bench.py --repeat 3      # best-of-3 per case (less noise)
    Benchmarks/runtime_bench.py --md bench.md   # also write a markdown summary
    Benchmarks/runtime_bench.py --json out.json # also dump raw results (for --compare)

To compare two runs (e.g. a PR head against main, both benched on the same machine — timings
from different machines don't compare), dump each with --json and then:

    Benchmarks/runtime_bench.py --compare base.json target.json --md bench.md
"""
from __future__ import annotations

import argparse
import json
import os
import re
import statistics
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]  # Benchmarks -> repo root
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


def fmt_ratio(target, base):
    """target / base, so < 1× means the target got faster. When both sides are tiny the ratio
    is scheduling noise, not signal — render it as —."""
    if max(target, base) < 50:
        return "—"
    if base == 0:
        return "∞"
    return f"{target / base:.2f}×"


def bench(args):
    """Run the benchmark, returning {benchmark, repeat, run_ms, pass_ms, iters}."""
    repo = args.repo.resolve()
    bench_dir = repo / "Benchmarks" / "OpenVM" / args.benchmark
    if not bench_dir.is_dir():
        sys.exit(f"error: no benchmark {args.benchmark!r} under {bench_dir.parent}")

    binary = args.binary.resolve() if args.binary is not None else None
    os.chdir(repo)
    if binary is None:
        if not args.no_build:
            print("building apc-optimizer...", file=sys.stderr)
            subprocess.run(["lake", "build"], check=True)
        binary = repo / ".lake" / "build" / "bin" / "apc-optimizer"
    if not binary.exists():
        sys.exit(f"error: {binary} missing (build first, or pass --binary/--no-build correctly)")

    cases = sorted(f for f in bench_dir.glob("apc_*_pc*.json.gz")
                   if not f.name.endswith((".powdr_opt.json.gz", ".apc_opt.json.gz")))
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
    return {"benchmark": args.benchmark, "repeat": args.repeat,
            "run_ms": run_ms, "pass_ms": pass_ms, "iters": iters}


def summary_stats(run_ms):
    times = sorted(run_ms.values())
    return sum(times), sum(times) // len(times), int(statistics.median(times)), times[-1]


def emit_md(data):
    """Markdown summary of one benchmark run."""
    run_ms, pass_ms, iters = data["run_ms"], data["pass_ms"], data["iters"]
    total, mean, median, worst = summary_stats(run_ms)
    pass_total = sum(pass_ms.values())
    passes = sorted(pass_ms.items(), key=lambda kv: -kv[1])

    lines = []
    lines.append(f"### Optimizer runtime — {data['benchmark']}, {len(run_ms)} cases"
                 + (f", best of {data['repeat']}" if data["repeat"] > 1 else ""))
    lines.append("")
    lines.append("| total | mean | median | max |")
    lines.append("|---|---|---|---|")
    lines.append(f"| {fmt_ms(total)} | {fmt_ms(mean)} | {fmt_ms(median)} | {fmt_ms(worst)} |")
    lines.append("")
    lines.append("<details><summary>Slowest cases (whole optimizer call)</summary>")
    lines.append("")
    lines.append("| case | time |")
    lines.append("|---|---|")
    for name, ms in sorted(run_ms.items(), key=lambda kv: -kv[1])[:10]:
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
    return "\n".join(lines) + "\n"


def emit_compare_md(base, target):
    """Markdown comparison of two runs (columns: target, baseline, target/baseline ratio)."""
    common = sorted(set(base["run_ms"]) & set(target["run_ms"]))
    dropped = (set(base["run_ms"]) | set(target["run_ms"])) - set(common)
    b_run = {k: base["run_ms"][k] for k in common}
    t_run = {k: target["run_ms"][k] for k in common}
    bt, bmean, bmed, bmax = summary_stats(b_run)
    tt, tmean, tmed, tmax = summary_stats(t_run)

    lines = []
    lines.append(f"### Optimizer runtime — {target['benchmark']}, {len(common)} cases, "
                 f"target vs baseline (same runner)"
                 + (f", best of {target['repeat']}" if target["repeat"] > 1 else ""))
    lines.append("")
    lines.append("Δ = target / baseline; below 1× means the target is faster.")
    lines.append("")
    lines.append("| | target | baseline | Δ |")
    lines.append("|---|---|---|---|")
    for label, t, b in (("total", tt, bt), ("mean", tmean, bmean),
                        ("median", tmed, bmed), ("max", tmax, bmax)):
        lines.append(f"| {label} | {fmt_ms(t)} | {fmt_ms(b)} | {fmt_ratio(t, b)} |")
    lines.append("")
    lines.append("<details><summary>Slowest cases (whole optimizer call, by target time)</summary>")
    lines.append("")
    lines.append("| case | target | baseline | Δ |")
    lines.append("|---|---|---|---|")
    for name, ms in sorted(t_run.items(), key=lambda kv: -kv[1])[:10]:
        lines.append(f"| {name} | {fmt_ms(ms)} | {fmt_ms(b_run[name])} "
                     f"| {fmt_ratio(ms, b_run[name])} |")
    lines.append("")
    lines.append("</details>")
    lines.append("")
    lines.append("Per-pass time, cumulative over all cases and fixpoint iterations:")
    lines.append("")
    lines.append("| pass | target | baseline | Δ |")
    lines.append("|---|---|---|---|")
    all_passes = {**base["pass_ms"], **target["pass_ms"]}
    for name in sorted(all_passes, key=lambda n: -target["pass_ms"].get(n, 0)):
        t, b = target["pass_ms"].get(name, 0), base["pass_ms"].get(name, 0)
        if t == 0 and b == 0:
            continue
        lines.append(f"| {name} | {fmt_ms(t)} | {fmt_ms(b)} | {fmt_ratio(t, b)} |")
    if dropped:
        lines.append("")
        lines.append(f"Cases present on only one side (not compared): "
                     f"{', '.join(sorted(dropped))}.")
    return "\n".join(lines) + "\n"


def emit_detail_compare_md(base, target):
    """The collapsed runtime-detail tables (slowest cases, then per-stage), main = baseline vs
    this branch = target, for embedding under the effectiveness table. Δ = this branch / main."""
    common = sorted(set(base["run_ms"]) & set(target["run_ms"]))
    b_run, t_run = base["run_ms"], target["run_ms"]
    lines = ["<details><summary>Slowest cases (out of top 10)</summary>", "",
             "| case | main | this branch | Δ |", "|---|---|---|---|"]
    for name in sorted(common, key=lambda n: -t_run[n])[:10]:
        lines.append(f"| {name} | {fmt_ms(b_run[name])} | {fmt_ms(t_run[name])} "
                     f"| {fmt_ratio(t_run[name], b_run[name])} |")
    lines += ["", "</details>", "<details><summary>Per-stage runtime breakdown (out of top 10)</summary>", "",
              "| pass | main | this branch | Δ |", "|---|---|---|---|"]
    all_passes = {**base["pass_ms"], **target["pass_ms"]}
    for name in sorted(all_passes, key=lambda n: -target["pass_ms"].get(n, 0)):
        t, b = target["pass_ms"].get(name, 0), base["pass_ms"].get(name, 0)
        if t == 0 and b == 0:
            continue
        lines.append(f"| {name} | {fmt_ms(b)} | {fmt_ms(t)} | {fmt_ratio(t, b)} |")
    lines += ["", "</details>"]
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("benchmark", nargs="?", default=DEFAULT_BENCHMARK,
                    help=f"benchmark name -- a subdirectory of Benchmarks/OpenVM/ "
                         f"(default: {DEFAULT_BENCHMARK})")
    ap.add_argument("--n", type=int, default=None, metavar="N",
                    help="only the top N cases by cost rank (default: all)")
    ap.add_argument("--repeat", type=int, default=1,
                    help="runs per case; the fastest is kept (default: 1)")
    ap.add_argument("--no-build", action="store_true",
                    help="skip `lake build` (the binary must already exist)")
    ap.add_argument("--binary", type=Path, default=None, metavar="EXE",
                    help="bench this apc-optimizer executable instead of building the repo's "
                         "(e.g. a prebuilt CI artifact); implies no build")
    ap.add_argument("--repo", type=Path, default=REPO, metavar="DIR",
                    help="repository to build and bench (default: the one holding this script; "
                         "lets a saved copy of the script bench another checkout, e.g. a baseline)")
    ap.add_argument("--md", type=Path, default=None, metavar="OUT.md",
                    help="also write a markdown summary (for CI job summaries / PR comments)")
    ap.add_argument("--json", type=Path, default=None, metavar="OUT.json",
                    help="also dump the raw per-case/per-pass results (input for --compare)")
    ap.add_argument("--compare", nargs=2, default=None, metavar=("BASE.json", "TARGET.json"),
                    help="don't bench; render a comparison of two --json dumps instead")
    ap.add_argument("--details", action="store_true",
                    help="with --compare, emit only the collapsed detail tables "
                         "(slowest cases + per-stage, main vs this branch)")
    args = ap.parse_args()

    if args.compare is not None:
        base, target = (json.loads(Path(p).read_text()) for p in args.compare)
        md = emit_detail_compare_md(base, target) if args.details else emit_compare_md(base, target)
    else:
        data = bench(args)
        if args.json is not None:
            args.json.write_text(json.dumps(data))
            print(f"wrote {args.json}", file=sys.stderr)
        md = emit_md(data)

    print()
    print(md)
    if args.md is not None:
        args.md.write_text(md)
        print(f"wrote {args.md}", file=sys.stderr)


if __name__ == "__main__":
    main()
