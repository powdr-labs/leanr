#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.9"
# dependencies = ["tqdm"]
# ///
"""Benchmark apc-optimizer against powdr over a named benchmark set.

Each benchmark is a subdirectory of OpenVmBenchmarks/ holding apc_<rank>_pc<pc>.json.gz
case pairs (plus manifest.json / apc_candidates.json). The default and main benchmark
used for optimization is `openvm-eth`. For each case, run `apc-optimizer compare` (the same
optimizer run as the autoopt loop) and aggregate effectiveness -- distinct variables
before / after -- for apc-optimizer vs powdr. Cases run in parallel with a progress bar. The
optimizer takes no iteration count: its cleanup loop runs to a fixpoint on an
input-derived budget.

Run it directly (uv installs tqdm automatically); the optional positional argument
selects the benchmark by name (default: openvm-eth):

    OpenVmBenchmarks/benchmark.py                 # all openvm-eth cases
    OpenVmBenchmarks/benchmark.py openvm-eth      # same, named explicitly
    OpenVmBenchmarks/benchmark.py --n 20          # top 20 by cost rank
    OpenVmBenchmarks/benchmark.py --n 10 --report report.html

With --report, writes a self-contained interactive HTML page to click through
each block and compare its assembly, original circuit, and the powdr / apc-optimizer
optimized circuits.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

try:
    from tqdm import tqdm
except ModuleNotFoundError:  # allow plain `python3 benchmark.py` without uv
    print("note: tqdm not installed; run via uv for a progress bar (or `pip install tqdm`).",
          file=sys.stderr)

    def tqdm(iterable, **_kwargs):
        return iterable

HERE = Path(__file__).resolve().parent       # OpenVmBenchmarks
REPO = Path(__file__).resolve().parents[1]    # OpenVmBenchmarks -> repo root
# Each benchmark is a subdirectory of HERE; `openvm-eth` is the main one used for optimization.
DEFAULT_BENCHMARK = "openvm-eth"
NAME_RE = re.compile(r"apc_(\d+)_pc(.+)\.json\.gz$")
# `apc-optimizer compare` stat lines, e.g. "  before: 62 vars, 55 constraints, 12 bus interactions".
# Capture all three measures per role (variables, constraints, bus interactions).
STAT_RE = {
    role: re.compile(rf"^\s*{role}\s*:\s*(\d+)\s+vars,\s*(\d+)\s+constraints,\s*(\d+)\s+bus")
    for role in ("before", "apc-optimizer", "powdr")
}
# Size measures, in priority order (variables > bus interactions > algebraic constraints).
METRICS = ("vars", "bus", "constraints")
METRIC_LABEL = {"vars": "variables", "bus": "bus interactions", "constraints": "constraints"}


def _ratio(before, after):
    """Shrink factor `before / after`, guarding the degenerate zero cases so geomean stays finite:
    nothing to shrink (before == 0) -> 1; everything removed (after == 0) -> before (i.e. / 1)."""
    if before == 0:
        return 1.0
    if after == 0:
        return float(before)
    return before / after


def parse_compare(text):
    """Parse a `apc-optimizer compare` run into {role: {vars, constraints, bus}} for the three roles."""
    got = {}
    for line in text.splitlines():
        for role, rx in STAT_RE.items():
            m = rx.match(line)
            if m:
                got[role] = {"vars": int(m.group(1)), "constraints": int(m.group(2)),
                             "bus": int(m.group(3))}
    if {"before", "apc-optimizer", "powdr"} <= got.keys():
        return got
    return None


def _metrics_from_json(o):
    """Pull the three size measures out of a `apc-optimizer report` circuit object."""
    return {"vars": o["vars"], "constraints": o["constraints"], "bus": o["bus"]}


def run_one(binary, unopt, want_report):
    """Run one case, returning (name, metrics, report_json, err). `metrics` is
    {role: {vars, constraints, bus}} for role in before/apc-optimizer/powdr, or None on failure."""
    name = unopt.name
    opt = unopt.with_name(unopt.name.replace(".json.gz", ".powdr_opt.json.gz"))
    if not opt.exists():
        return name, None, None, "no .powdr_opt"
    sub = "report" if want_report else "compare"
    try:
        out = subprocess.run([str(binary), sub, str(unopt), str(opt)],
                             capture_output=True, text=True, check=True).stdout
    except subprocess.CalledProcessError:
        return name, None, None, "apc-optimizer failed"
    if want_report:
        try:
            j = json.loads(out)
            metrics = {"before": _metrics_from_json(j["original"]),
                       "apc-optimizer": _metrics_from_json(j["apc-optimizer"]),
                       "powdr": _metrics_from_json(j["powdr"])}
        except Exception:
            return name, None, None, "report parse failed"
        return name, metrics, j, None
    parsed = parse_compare(out)
    return name, parsed, None, None if parsed else "parse failed"


def load_asm(bench_dir):
    """Map benchmark unopt filename -> assembly text, bridging manifest.json
    (filename -> decimal start_pcs) and apc_candidates.json (start_pcs ->
    instructions). Returns {} if that data isn't present."""
    try:
        cand = json.loads((bench_dir / "apc_candidates.json").read_text())
        man = json.loads((bench_dir / "manifest.json").read_text())
    except FileNotFoundError:
        return {}
    labels = cand.get("labels", {})
    asm_by_pcs = {}
    for e in cand.get("apcs", []):
        blocks = e["original_blocks"]
        lines = []
        for i, b in enumerate(blocks):
            lbl = labels.get(str(b["start_pc"]), [])
            tag = "  <" + ", ".join(lbl) + ">" if lbl else ""
            if i == 0:
                # the first block's start pc is already shown in the caption; don't repeat it
                if tag:
                    lines.append(tag.strip())
            else:
                lines += ["", f"pc {b['start_pc']}{tag}"]
            lines += b["instructions"]
        asm_by_pcs["_".join(str(b["start_pc"]) for b in blocks)] = "\n".join(lines)
    return {e["files"]["unopt"]: asm_by_pcs.get("_".join(map(str, e["start_pcs"])), "")
            for e in man.get("entries", [])}


def available_benchmarks():
    """Benchmark names available: subdirectories of HERE that hold apc_*_pc*.json.gz cases."""
    return sorted(d.name for d in HERE.iterdir()
                  if d.is_dir() and any(d.glob("apc_*_pc*.json.gz")))


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("benchmark", nargs="?", default=DEFAULT_BENCHMARK,
                    help=f"benchmark name -- a subdirectory of OpenVmBenchmarks/ "
                         f"(default: {DEFAULT_BENCHMARK})")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4,
                    help="cases to run in parallel (default: number of cores)")
    ap.add_argument("--n", type=int, default=None, metavar="N",
                    help="only the top N cases by cost rank (default: all)")
    ap.add_argument("--report", type=Path, default=None, metavar="OUT.html",
                    help="also write a self-contained interactive HTML report to this path")
    ap.add_argument("--md", type=Path, default=None, metavar="OUT.md",
                    help="also write the summary as markdown (for CI job summaries / PR comments)")
    args = ap.parse_args()

    bench_dir = HERE / args.benchmark
    if not bench_dir.is_dir():
        avail = ", ".join(available_benchmarks()) or "(none found)"
        sys.exit(f"error: no benchmark {args.benchmark!r} under {HERE} (available: {avail})")

    os.chdir(REPO)
    print("building apc-optimizer...", file=sys.stderr)
    subprocess.run(["lake", "build"], check=True)
    binary = REPO / ".lake" / "build" / "bin" / "apc-optimizer"
    if not binary.exists():
        sys.exit(f"error: {binary} missing after build")

    cases = sorted(f for f in bench_dir.glob("apc_*_pc*.json.gz")
                   if not f.name.endswith(".powdr_opt.json.gz"))
    if not cases:
        sys.exit(f"no benchmark cases in {bench_dir}")
    if args.n is not None:
        cases = cases[: args.n]

    want_report = args.report is not None
    results, reports, skipped = [], {}, []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(run_one, binary, c, want_report) for c in cases]
        for fut in tqdm(as_completed(futures), total=len(futures),
                        desc="apc-optimizer compare", unit="case"):
            name, metrics, report, err = fut.result()
            if metrics is None:
                skipped.append((name, err))
                continue
            results.append((name, metrics))  # (name, {role: {vars, constraints, bus}})
            if report is not None:
                reports[name] = report

    if not results:
        sys.exit("no results produced")

    n = len(results)

    def agg(role, mt):  # aggregate effectiveness: sum of befores / sum of afters
        sb = sum(m["before"][mt] for _, m in results)
        sa = sum(m[role][mt] for _, m in results)
        return sb / sa if sa else float("inf")

    def geo(role, mt):  # geometric mean of the per-case shrink factors
        return math.exp(sum(math.log(_ratio(m["before"][mt], m[role][mt]))
                            for _, m in results) / n)

    # Wins/losses stay on the primary metric (variables).
    summary = {
        "n": n,
        "wins": sum(1 for _, m in results if m["apc-optimizer"]["vars"] < m["powdr"]["vars"]),
        "losses": sum(1 for _, m in results if m["apc-optimizer"]["vars"] > m["powdr"]["vars"]),
    }
    for role in ("apc-optimizer", "powdr"):
        for mt in METRICS:
            summary[f"{role}_{mt}_agg"] = agg(role, mt)
            summary[f"{role}_{mt}_geo"] = geo(role, mt)

    print(f"\n=== {args.benchmark}: apc-optimizer vs powdr over {n} cases ===")
    print("effectiveness = size before / size after (larger is better); "
          "priority: variables > bus interactions > constraints")
    print(f"  {'measure':<18}{'apc-optimizer (agg / geo)':<26}{'powdr (agg / geo)':<26}diff (agg)")
    for mt in METRICS:
        la, lg = summary[f"apc-optimizer_{mt}_agg"], summary[f"apc-optimizer_{mt}_geo"]
        pa, pg = summary[f"powdr_{mt}_agg"], summary[f"powdr_{mt}_geo"]
        print(f"  {METRIC_LABEL[mt]:<18}{f'{la:.3f}x / {lg:.3f}x':<26}"
              f"{f'{pa:.3f}x / {pg:.3f}x':<26}{la - pa:+.3f}x")
    print(f"per-case (by variables): apc-optimizer wins {summary['wins']}, loses {summary['losses']}, "
          f"ties {n - summary['wins'] - summary['losses']}")
    if skipped:
        print(f"\nskipped {len(skipped)}:", file=sys.stderr)
        for name, err in skipped:
            print(f"  {name}: {err}", file=sys.stderr)

    if args.md is not None:
        lines = [f"### Effectiveness — {args.benchmark}, {n} cases, apc-optimizer vs powdr", "",
                 "Effectiveness = size before / size after (larger is better); "
                 "priority: variables > bus interactions > constraints. "
                 "agg = Σbefore ⁄ Σafter, geo = geomean of per-case factors.", "",
                 "| measure | apc-optimizer (agg / geo) | powdr (agg / geo) | diff (agg) |",
                 "|---|---|---|---|"]
        for mt in METRICS:
            la, lg = summary[f"apc-optimizer_{mt}_agg"], summary[f"apc-optimizer_{mt}_geo"]
            pa, pg = summary[f"powdr_{mt}_agg"], summary[f"powdr_{mt}_geo"]
            lines.append(f"| {METRIC_LABEL[mt]} | {la:.3f}× / {lg:.3f}× "
                         f"| {pa:.3f}× / {pg:.3f}× | {la - pa:+.3f}× |")
        lines.append("")
        lines.append(f"Per-case (by variables): apc-optimizer wins {summary['wins']}, "
                     f"loses {summary['losses']}, ties {n - summary['wins'] - summary['losses']}.")
        if skipped:
            lines.append("")
            lines.append(f"Skipped {len(skipped)}: "
                         + ", ".join(f"{name} ({err})" for name, err in skipped) + ".")
        args.md.write_text("\n".join(lines) + "\n")
        print(f"wrote {args.md}", file=sys.stderr)

    if want_report:
        asm = load_asm(bench_dir)
        html_cases = []
        for name, _metrics in sorted(results, key=lambda r: r[0]):
            m = NAME_RE.search(name)
            rank, pc = (m.group(1), m.group(2)) if m else ("?", name)
            r = reports[name]
            html_cases.append({"rank": rank, "pc": pc, "asm": asm.get(name, ""),
                               "original": r["original"], "powdr": r["powdr"], "apc-optimizer": r["apc-optimizer"]})
        args.report.write_text(build_html(html_cases, args.benchmark, summary))
        print(f"\nwrote report ({len(html_cases)} cases) to {args.report}", file=sys.stderr)


def build_html(cases, benchmark, summary):
    return (HTML_TEMPLATE
            .replace("__BENCH__", benchmark)
            .replace("__N__", str(len(cases)))
            .replace("__SUMMARY__", json.dumps(summary))
            .replace("__DATA__", json.dumps(cases).replace("</", "<\\/")))


HTML_TEMPLATE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>apc-optimizer benchmark report</title>
<style>
  :root {
    --bg:#ffffff; --bg2:#f6f8fa; --fg:#1f2328; --dim:#656d76; --line:#d0d7de;
    --accent:#0969da; --accent-bg:#ddf4ff; --powdr:#9a6700; --apc-optimizer:#1a7f37;
    --mono:12.5px/1.55 ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;
  }
  * { box-sizing:border-box; }
  body { margin:0; height:100vh; display:flex; overflow:hidden;
         font:14px/1.5 -apple-system,BlinkMacSystemFont,"Segoe UI",Helvetica,Arial,sans-serif;
         background:var(--bg); color:var(--fg); }

  #side { width:270px; flex:none; border-right:1px solid var(--line); display:flex; flex-direction:column; }
  #sidehead { flex:none; padding:14px 16px; border-bottom:1px solid var(--line); background:var(--bg2); }
  #sidehead .title { font-weight:600; font-size:15px; letter-spacing:-.01em; }
  #sidehead .meta { color:var(--dim); font-size:12px; margin:2px 0 8px; }
  #summary { font-size:12px; line-height:1.7; }
  #summary .el { color:var(--apc-optimizer); font-weight:600; } #summary .ep { color:var(--powdr); font-weight:600; }
  #summary .dim { color:var(--dim); margin-top:3px; }
  #summary .srow { display:flex; gap:6px; align-items:baseline; }
  #summary .srow .slbl { flex:1; color:var(--dim); }
  #summary .srow .el, #summary .srow .ep { width:48px; text-align:right; }
  #summary .shead { font-size:11px; }
  #cases { flex:1; overflow:auto; padding:8px; }
  .caseb { display:block; width:100%; text-align:left; background:none; border:1px solid transparent;
           border-radius:8px; color:var(--fg); padding:10px 12px; margin-bottom:4px; cursor:pointer; }
  .caseb:hover { background:var(--bg2); }
  .caseb.sel { background:var(--accent-bg); border-color:#b6e3ff; }
  .crow { display:flex; align-items:baseline; gap:8px; margin-bottom:3px; }
  .crow .rank { font-weight:600; font-size:13px; } .crow .pc { color:var(--dim); font-size:11px; }
  .ceff { font-size:12px; }
  .ceff .ep { color:var(--powdr); } .ceff .el { color:var(--apc-optimizer); } .ceff .win { font-weight:700; }

  #main { flex:1; display:flex; flex-direction:column; min-width:0; }
  #bar { flex:none; display:flex; align-items:center; justify-content:space-between; gap:12px;
         padding:10px 16px; border-bottom:1px solid var(--line); }
  .caption { font-size:13px; color:var(--dim); } .caption b { color:var(--fg); }
  .tabs { display:inline-flex; border:1px solid var(--line); border-radius:8px; overflow:hidden; }
  .tabs button { border:0; background:var(--bg); color:var(--dim); padding:6px 16px; cursor:pointer;
                 font-size:13px; border-right:1px solid var(--line); }
  .tabs button:last-child { border-right:0; }
  .tabs button:hover { background:var(--bg2); }
  .tabs button.active { background:var(--accent); color:#fff; font-weight:600; }

  #content { flex:1; display:flex; flex-direction:column; min-height:0; padding:14px; gap:14px; }
  .panel { display:flex; flex-direction:column; min-height:0; background:var(--bg);
           border:1px solid var(--line); border-radius:10px; }
  .panel.circuit { flex:1; }
  .panel.asm { flex:none; max-height:30vh; }
  .panel.collapsed { flex:none; }
  .panel.collapsed pre { display:none; }
  .phead { display:flex; align-items:baseline; gap:8px; padding:9px 14px; cursor:pointer; user-select:none;
           border-bottom:1px solid var(--line); background:var(--bg2); border-radius:10px 10px 0 0; }
  .panel.collapsed .phead { border-bottom:0; border-radius:10px; }
  .caret { color:var(--dim); font-size:10px; width:9px; flex:none; }
  .caret::before { content:"\25BE"; } .panel.collapsed .caret::before { content:"\25B8"; }
  .phead .plabel { font-weight:600; font-size:13px; }
  .p-orig .plabel { color:var(--dim); }
  .p-apc-optimizer .plabel { color:var(--apc-optimizer); } .p-powdr .plabel { color:var(--powdr); }
  .phead .pstats { color:var(--dim); font-size:12px; }
  .panel pre { flex:1; margin:0; padding:12px 14px; overflow:auto; font:var(--mono); white-space:pre; tab-size:2;
               border-radius:0 0 10px 10px; }

  .vardiff { position:relative; cursor:default; text-decoration:underline dotted var(--dim); text-underline-offset:3px; }
  .vardiff .rem { color:#cf222e; } .vardiff .add { color:var(--apc-optimizer); }
  .vardiff .pop { display:none; position:fixed; z-index:20; gap:16px; text-decoration:none;
                  background:var(--bg); border:1px solid var(--line); border-radius:8px; padding:10px;
                  box-shadow:0 6px 20px rgba(31,35,40,.15); }
  .vardiff:hover .pop { display:flex; }
  .popcol { max-height:min(50vh,360px); overflow:auto; min-width:150px; }
  .pophd { font-weight:600; margin-bottom:5px; position:sticky; top:0; background:var(--bg); }
  .pop .v { font:var(--mono); white-space:nowrap; }
  .pnone { color:var(--dim); font:var(--mono); }
  .hl-rem { background:#ffd7d5; color:#cf222e; border-radius:3px; }
  .hl-add { background:#ceffd6; color:#1a7f37; border-radius:3px; }
</style></head>
<body>
  <aside id="side">
    <div id="sidehead">
      <div class="title">apc-optimizer benchmark report</div>
      <div class="meta">__BENCH__ · __N__ cases</div>
      <div id="summary"></div>
    </div>
    <div id="cases"></div>
  </aside>
  <main id="main">
    <div id="bar">
      <div class="caption" id="caption"></div>
      <div class="tabs"><button id="tab-apc-optimizer">apc-optimizer</button><button id="tab-powdr">powdr</button></div>
    </div>
    <div id="content"></div>
  </main>
<script>
const DATA = __DATA__, SUM = __SUMMARY__;
let cur = 0, tab = "apc-optimizer";
const collapsed = { asm: false, orig: true, opt: false };

// Shrink factor of measure `key` (o=original, x=optimized). Guards the zero-denominator case.
function effBy(o, x, key) { return x[key] ? o[key] / x[key] : (o[key] ? Infinity : 1); }
function effOf(o, x) { return effBy(o, x, "vars"); }   // primary metric
function fmtEff(v) { return v === Infinity ? "∞" : v.toFixed(2); }
// Size measures in priority order: [json key, short label].
const METRICS = [["vars", "vars"], ["bus", "bus"], ["constraints", "constraints"]];
function statLine(x) { return x.vars + " vars · " + x.constraints + " constraints · " + x.bus + " bus"; }
function esc(s) { return s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;"); }
function varDiffHTML(orig, opt) {
  const O = new Set(orig.vars_list), P = new Set(opt.vars_list);
  const removed = orig.vars_list.filter(function(v) { return !P.has(v); });
  const added = opt.vars_list.filter(function(v) { return !O.has(v); });
  function col(arr, cls, label) {
    const items = arr.length
      ? arr.map(function(v) { return '<div class="v ' + cls + '">' + esc(v) + '</div>'; }).join("")
      : '<div class="pnone">none</div>';
    return '<div class="popcol"><div class="pophd ' + cls + '">' + label + ' (' + arr.length + ')</div>' + items + '</div>';
  }
  return '<span class="vardiff" onclick="event.stopPropagation()">' +
    '<span class="rem">−' + removed.length + '</span> / <span class="add">+' + added.length + '</span> vars' +
    '<span class="pop">' + col(removed, "rem", "removed") + col(added, "add", "added") + '</span></span>';
}
// Escape a render and wrap any variable token that is in `set` with a highlight span.
function highlightRender(text, set, cls) {
  if (!set.size) return esc(text);
  let out = "", last = 0, m;
  const re = /[A-Za-z_][A-Za-z0-9_@]*/g;
  while ((m = re.exec(text)) !== null) {
    out += esc(text.slice(last, m.index)) +
      (set.has(m[0]) ? '<span class="' + cls + '">' + esc(m[0]) + '</span>' : esc(m[0]));
    last = re.lastIndex;
  }
  return out + esc(text.slice(last));
}
// How this optimizer's output differs from the other's: +added / -removed, relative to `other`.
function diffToOtherHTML(opt, other, otherName) {
  const O = new Set(other.vars_list), S = new Set(opt.vars_list);
  const added = opt.vars_list.filter(function(v) { return !O.has(v); });    // in this opt, not the other
  const removed = other.vars_list.filter(function(v) { return !S.has(v); }); // in the other, not this opt
  function col(arr, cls, label) {
    const items = arr.length
      ? arr.map(function(v) { return '<div class="v ' + cls + '">' + esc(v) + '</div>'; }).join("")
      : '<div class="pnone">none</div>';
    return '<div class="popcol"><div class="pophd ' + cls + '">' + label + ' (' + arr.length + ')</div>' + items + '</div>';
  }
  return '<span class="vardiff" onclick="event.stopPropagation()">diff to ' + otherName + ': ' +
    '<span class="add">+' + added.length + '</span> / <span class="rem">−' + removed.length + '</span> vars' +
    '<span class="pop">' + col(added, "add", "added vs " + otherName) +
    col(removed, "rem", "removed vs " + otherName) + '</span></span>';
}

// Aggregate effectiveness per measure (priority order), apc-optimizer vs powdr; geomean in the tooltip.
document.getElementById("summary").innerHTML =
  '<div class="srow shead"><span class="slbl"></span><span class="el">apc-optimizer</span><span class="ep">powdr</span></div>' +
  METRICS.map(function(mt) {
    var k = mt[0];
    return '<div class="srow" title="geomean — apc-optimizer ' + SUM["apc-optimizer_" + k + "_geo"].toFixed(2) +
      '× · powdr ' + SUM["powdr_" + k + "_geo"].toFixed(2) + '×">' +
      '<span class="slbl">' + mt[1] + '</span>' +
      '<span class="el">' + SUM["apc-optimizer_" + k + "_agg"].toFixed(2) + '×</span>' +
      '<span class="ep">' + SUM["powdr_" + k + "_agg"].toFixed(2) + '×</span></div>';
  }).join("") +
  '<div class="dim">agg = Σbefore ⁄ Σafter · apc-optimizer wins ' + SUM.wins + ' / loses ' + SUM.losses +
  ' (by vars)</div>';

const casesEl = document.getElementById("cases");
DATA.forEach(function(c, i) {
  const le = effOf(c.original, c["apc-optimizer"]), pe = effOf(c.original, c.powdr);
  const b = document.createElement("button");
  b.id = "case" + i; b.className = "caseb";
  b.innerHTML =
    '<div class="crow"><span class="rank">#' + c.rank + '</span><span class="pc">pc' + c.pc + '</span></div>' +
    '<div class="ceff"><span class="ep' + (pe > le ? " win" : "") + '">powdr ' + pe.toFixed(2) + '×</span> · ' +
    '<span class="el' + (le > pe ? " win" : "") + '">apc-optimizer ' + le.toFixed(2) + '×</span></div>';
  b.onclick = function() { cur = i; render(); };
  casesEl.appendChild(b);
});

function makePanel(kind, cls, label, statsHTML, body) {
  const wrap = document.createElement("div");
  wrap.className = "panel " + cls + (collapsed[kind] ? " collapsed" : "");
  const h = document.createElement("div"); h.className = "phead";
  h.innerHTML = '<span class="caret"></span><span class="plabel">' + label + '</span>' +
    (statsHTML ? '<span class="pstats">' + statsHTML + '</span>' : "");
  h.onclick = function() { collapsed[kind] = !collapsed[kind]; wrap.classList.toggle("collapsed"); };
  const pre = document.createElement("pre"); pre.innerHTML = body;
  wrap.appendChild(h); wrap.appendChild(pre);
  return wrap;
}

function render() {
  document.querySelectorAll(".caseb").forEach(function(b, i) { b.classList.toggle("sel", i === cur); });
  document.getElementById("tab-apc-optimizer").classList.toggle("active", tab === "apc-optimizer");
  document.getElementById("tab-powdr").classList.toggle("active", tab === "powdr");
  const c = DATA[cur], opt = tab === "apc-optimizer" ? c["apc-optimizer"] : c.powdr;
  const other = tab === "apc-optimizer" ? c.powdr : c["apc-optimizer"], otherName = tab === "apc-optimizer" ? "powdr" : "apc-optimizer";
  const optSet = new Set(opt.vars_list), origSet = new Set(c.original.vars_list);
  const removedSet = new Set(c.original.vars_list.filter(function(v) { return !optSet.has(v); }));
  const addedSet = new Set(opt.vars_list.filter(function(v) { return !origSet.has(v); }));
  document.getElementById("caption").innerHTML = "block <b>#" + c.rank + "</b> · pc" + c.pc;
  const content = document.getElementById("content");
  content.innerHTML = "";
  content.appendChild(makePanel("asm", "asm", "assembly", "", esc(c.asm || "(no assembly available)")));
  content.appendChild(makePanel("orig", "circuit p-orig", "original", statLine(c.original),
    highlightRender(c.original.render, removedSet, "hl-rem")));
  const effHTML = METRICS.map(function(mt) {
    return fmtEff(effBy(c.original, opt, mt[0])) + "× " + mt[1];
  }).join(" · ");
  content.appendChild(makePanel("opt", "circuit " + (tab === "apc-optimizer" ? "p-apc-optimizer" : "p-powdr"), tab,
    statLine(opt) + "  ·  " + effHTML + " fewer  ·  " +
      varDiffHTML(c.original, opt) + "  ·  " + diffToOtherHTML(opt, other, otherName),
    highlightRender(opt.render, addedSet, "hl-add")));
}

document.getElementById("tab-apc-optimizer").onclick = function() { tab = "apc-optimizer"; render(); };
document.getElementById("tab-powdr").onclick = function() { tab = "powdr"; render(); };
document.addEventListener("keydown", function(e) {
  if (e.key === "ArrowDown" && cur < DATA.length - 1) cur++;
  else if (e.key === "ArrowUp" && cur > 0) cur--;
  else return;
  e.preventDefault(); render();
});
// Position the (fixed) var-diff popover next to its badge, flipping up near the viewport bottom.
document.addEventListener("mouseover", function(e) {
  const vd = e.target.closest ? e.target.closest(".vardiff") : null;
  if (!vd) return;
  const pop = vd.querySelector(".pop"); if (!pop) return;
  const r = vd.getBoundingClientRect();
  pop.style.right = (window.innerWidth - r.right) + "px";
  if (window.innerHeight - r.bottom > 240) { pop.style.top = (r.bottom - 2) + "px"; pop.style.bottom = "auto"; }
  else { pop.style.bottom = (window.innerHeight - r.top - 2) + "px"; pop.style.top = "auto"; }
});
render();
</script>
</body></html>"""


if __name__ == "__main__":
    main()
