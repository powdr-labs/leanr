#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.9"
# dependencies = ["tqdm"]
# ///
"""Benchmark the leanr optimizer against powdr over the openvm-eth set.

For each apc_<rank>_pc<pc>.json.gz in this directory, run `leanr compare` (the
same optimizer run as the autoopt loop; --iters 32 by default) and aggregate
effectiveness -- distinct variables before / after -- for leanr vs powdr. Cases
run in parallel with a progress bar.

Run it directly (uv installs tqdm automatically):

    Leanr/OpenVM/Benchmark/benchmark.py                 # all cases
    Leanr/OpenVM/Benchmark/benchmark.py --n 20          # top 20 by cost rank
    Leanr/OpenVM/Benchmark/benchmark.py --n 10 --report report.html

With --report, writes a self-contained interactive HTML page to click through
each block and compare the original, powdr, and leanr circuits.
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

HERE = Path(__file__).resolve().parent           # the benchmark dir itself
REPO = Path(__file__).resolve().parents[3]        # Leanr/OpenVM/Benchmark -> repo root
NAME_RE = re.compile(r"apc_(\d+)_pc(.+)\.json\.gz$")
VARS_RE = {  # `leanr compare` lines: "  before: 62 vars, ...", "  leanr : 28 vars, ...", "  powdr : ..."
    "before": re.compile(r"^\s*before:\s*(\d+)\s+vars"),
    "leanr": re.compile(r"^\s*leanr\s*:\s*(\d+)\s+vars"),
    "powdr": re.compile(r"^\s*powdr\s*:\s*(\d+)\s+vars"),
}


def parse_compare(text):
    got = {}
    for line in text.splitlines():
        for key, rx in VARS_RE.items():
            m = rx.match(line)
            if m:
                got[key] = int(m.group(1))
    if {"before", "leanr", "powdr"} <= got.keys():
        return got["before"], got["leanr"], got["powdr"]
    return None


def run_one(binary, iters, unopt, want_report):
    name = unopt.name
    opt = unopt.with_name(unopt.name.replace(".json.gz", ".powdr_opt.json.gz"))
    if not opt.exists():
        return name, None, None, "no .powdr_opt"
    sub = "report" if want_report else "compare"
    try:
        out = subprocess.run([str(binary), sub, "--iters", str(iters), str(unopt), str(opt)],
                             capture_output=True, text=True, check=True).stdout
    except subprocess.CalledProcessError:
        return name, None, None, "leanr failed"
    if want_report:
        try:
            j = json.loads(out)
            stats = (j["original"]["vars"], j["leanr"]["vars"], j["powdr"]["vars"])
        except Exception:
            return name, None, None, "report parse failed"
        return name, stats, j, None
    parsed = parse_compare(out)
    return name, parsed, None, None if parsed else "parse failed"


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("dir", nargs="?", default=str(HERE),
                    help="benchmark directory (default: this script's directory)")
    ap.add_argument("--iters", type=int, default=32, help="optimizer cleanup-cycle cap (default: 32)")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4,
                    help="cases to run in parallel (default: number of cores)")
    ap.add_argument("--n", type=int, default=None, metavar="N",
                    help="only the top N cases by cost rank (default: all)")
    ap.add_argument("--report", type=Path, default=None, metavar="OUT.html",
                    help="also write a self-contained interactive HTML report to this path")
    args = ap.parse_args()

    os.chdir(REPO)
    print("building leanr...", file=sys.stderr)
    subprocess.run(["lake", "build"], check=True)
    binary = REPO / ".lake" / "build" / "bin" / "leanr"
    if not binary.exists():
        sys.exit(f"error: {binary} missing after build")

    cases = sorted(f for f in Path(args.dir).glob("apc_*_pc*.json.gz")
                   if not f.name.endswith(".powdr_opt.json.gz"))
    if not cases:
        sys.exit(f"no benchmark cases in {args.dir}")
    if args.n is not None:
        cases = cases[: args.n]

    want_report = args.report is not None
    results, reports, skipped = [], {}, []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(run_one, binary, args.iters, c, want_report) for c in cases]
        for fut in tqdm(as_completed(futures), total=len(futures),
                        desc=f"leanr compare (iters={args.iters})", unit="case"):
            name, stats, report, err = fut.result()
            if stats is None:
                skipped.append((name, err))
                continue
            results.append((name, *stats))  # (name, before, leanr, powdr)
            if report is not None:
                reports[name] = report

    if not results:
        sys.exit("no results produced")

    n = len(results)
    sum_before = sum(r[1] for r in results)
    sum_leanr = sum(r[2] for r in results)
    sum_powdr = sum(r[3] for r in results)
    summary = {
        "n": n,
        "leanr_agg": sum_before / sum_leanr,
        "powdr_agg": sum_before / sum_powdr,
        "leanr_geo": math.exp(sum(math.log(r[1] / r[2]) for r in results) / n),
        "powdr_geo": math.exp(sum(math.log(r[1] / r[3]) for r in results) / n),
        "wins": sum(1 for r in results if r[2] < r[3]),
        "losses": sum(1 for r in results if r[2] > r[3]),
    }

    print(f"\n=== leanr vs powdr over {n} cases (--iters {args.iters}) ===")
    print(f"leanr : {summary['leanr_agg']:.3f}x aggregate (sum before / sum after)   {summary['leanr_geo']:.3f}x geomean")
    print(f"powdr : {summary['powdr_agg']:.3f}x aggregate                            {summary['powdr_geo']:.3f}x geomean")
    print(f"diff  : {summary['leanr_agg'] - summary['powdr_agg']:+.3f}x aggregate   "
          f"{summary['leanr_geo'] - summary['powdr_geo']:+.3f}x geomean   (leanr - powdr)")
    print(f"per-case: leanr wins {summary['wins']}, loses {summary['losses']}, "
          f"ties {n - summary['wins'] - summary['losses']}")
    if skipped:
        print(f"\nskipped {len(skipped)}:", file=sys.stderr)
        for name, err in skipped:
            print(f"  {name}: {err}", file=sys.stderr)

    if want_report:
        html_cases = []
        for name, before, leanr, powdr in sorted(results, key=lambda r: r[0]):
            m = NAME_RE.search(name)
            rank, pc = (m.group(1), m.group(2)) if m else ("?", name)
            r = reports[name]
            html_cases.append({"rank": rank, "pc": pc, "name": name,
                               "original": r["original"], "powdr": r["powdr"], "leanr": r["leanr"]})
        html = build_html(html_cases, args.iters, summary)
        args.report.write_text(html)
        print(f"\nwrote report ({len(html_cases)} cases) to {args.report}", file=sys.stderr)


def build_html(cases, iters, summary):
    data_js = json.dumps(cases).replace("</", "<\\/")
    summary_js = json.dumps(summary)
    return (HTML_TEMPLATE
            .replace("__N__", str(len(cases)))
            .replace("__ITERS__", str(iters))
            .replace("__SUMMARY__", summary_js)
            .replace("__DATA__", data_js))


HTML_TEMPLATE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>leanr benchmark report</title>
<style>
  :root {
    --bg:#ffffff; --bg2:#f6f8fa; --fg:#1f2328; --dim:#656d76; --line:#d0d7de;
    --accent:#0969da; --accent-bg:#ddf4ff; --powdr:#9a6700; --leanr:#1a7f37;
    --add-bg:#e6ffec; --add-fg:#1a7f37; --del-bg:#ffebe9; --del-fg:#cf222e;
    --mono:12.5px/1.55 ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;
  }
  * { box-sizing:border-box; }
  body { margin:0; height:100vh; display:flex; flex-direction:column;
         font:14px/1.5 -apple-system,BlinkMacSystemFont,"Segoe UI",Helvetica,Arial,sans-serif;
         background:var(--bg); color:var(--fg); }
  header { padding:16px 22px; border-bottom:1px solid var(--line); background:var(--bg2); }
  header h1 { margin:0 0 6px; font-size:17px; font-weight:600; letter-spacing:-.01em; }
  header h1 span { color:var(--dim); font-weight:400; font-size:14px; }
  #summary { color:var(--dim); font-size:13px; }
  #summary b { color:var(--fg); }
  #wrap { flex:1; display:flex; min-height:0; }

  #side { width:260px; flex:none; border-right:1px solid var(--line); overflow:auto; padding:8px; }
  .caseb { display:block; width:100%; text-align:left; background:none; border:1px solid transparent;
           border-radius:8px; color:var(--fg); padding:10px 12px; margin-bottom:4px; cursor:pointer; }
  .caseb:hover { background:var(--bg2); }
  .caseb.sel { background:var(--accent-bg); border-color:#b6e3ff; }
  .crow { display:flex; align-items:baseline; gap:8px; margin-bottom:3px; }
  .crow .rank { font-weight:600; font-size:13px; }
  .crow .pc { color:var(--dim); font-size:11px; }
  .ceff { font-size:12px; color:var(--dim); }
  .ceff .ep { color:var(--powdr); } .ceff .el { color:var(--leanr); }
  .ceff .win { font-weight:700; }

  #main { flex:1; display:flex; flex-direction:column; min-width:0; }
  #bar { display:flex; align-items:center; justify-content:space-between; gap:12px;
         padding:10px 16px; border-bottom:1px solid var(--line); }
  .caption { font-size:13px; color:var(--dim); }
  .caption b { color:var(--fg); }
  .group { display:inline-flex; border:1px solid var(--line); border-radius:8px; overflow:hidden; }
  .group button { border:0; background:var(--bg); color:var(--dim); padding:6px 14px; cursor:pointer;
                  font-size:13px; border-right:1px solid var(--line); }
  .group button:last-child { border-right:0; }
  .group button:hover { background:var(--bg2); }
  .group button.active { background:var(--accent); color:#fff; font-weight:600; }

  #content { flex:1; display:flex; flex-direction:column; min-height:0; padding:14px; gap:14px; }
  .panel { flex:1; display:flex; flex-direction:column; min-height:0;
           border:1px solid var(--line); border-radius:10px; overflow:hidden; background:var(--bg); }
  .phead { display:flex; align-items:baseline; gap:12px; padding:9px 14px;
           border-bottom:1px solid var(--line); background:var(--bg2); }
  .phead .plabel { font-weight:600; font-size:13px; }
  .p-orig .plabel { color:var(--dim); }
  .p-leanr .plabel { color:var(--leanr); } .p-powdr .plabel { color:var(--powdr); }
  .phead .pstats { color:var(--dim); font-size:12px; }
  .panel pre { flex:1; margin:0; padding:12px 14px; overflow:auto; font:var(--mono); white-space:pre; tab-size:2; }
  .panel.diff pre { padding:0; }
  .diff .dline { padding:0 14px; white-space:pre; }
  .diff .dctx { color:#57606a; } .diff .dadd { background:var(--add-bg); color:var(--add-fg); }
  .diff .ddel { background:var(--del-bg); color:var(--del-fg); }
  .diff .dnote { padding:12px 14px; color:var(--dim); }
</style></head>
<body>
<header>
  <h1>leanr benchmark report <span>· __N__ cases · --iters __ITERS__</span></h1>
  <div id="summary"></div>
</header>
<div id="wrap">
  <aside id="side"></aside>
  <main id="main">
    <div id="bar">
      <div class="caption" id="caption"></div>
      <div style="display:flex; gap:10px;">
        <div class="group" id="tabs">
          <button id="tab-leanr">leanr</button><button id="tab-powdr">powdr</button>
        </div>
        <div class="group" id="views">
          <button id="view-split">split</button><button id="view-diff">diff</button>
        </div>
      </div>
    </div>
    <div id="content"></div>
  </main>
</div>
<script>
const DATA = __DATA__, SUM = __SUMMARY__;
let cur = 0, tab = "leanr", view = "split";

function effOf(o, x) { return o.vars / x.vars; }
function statLine(x) { return x.vars + " vars · " + x.constraints + " constraints · " + x.bus + " bus"; }

document.getElementById("summary").innerHTML =
  "leanr <b>" + SUM.leanr_agg.toFixed(3) + "×</b> agg / <b>" + SUM.leanr_geo.toFixed(3) + "×</b> geomean" +
  " &nbsp;vs&nbsp; powdr <b>" + SUM.powdr_agg.toFixed(3) + "×</b> agg / <b>" + SUM.powdr_geo.toFixed(3) + "×</b> geomean" +
  " &nbsp;·&nbsp; leanr wins " + SUM.wins + ", loses " + SUM.losses;

const side = document.getElementById("side");
DATA.forEach(function(c, i) {
  const le = effOf(c.original, c.leanr), pe = effOf(c.original, c.powdr);
  const b = document.createElement("button");
  b.id = "case" + i; b.className = "caseb";
  b.innerHTML =
    '<div class="crow"><span class="rank">#' + c.rank + '</span><span class="pc">pc' + c.pc + '</span></div>' +
    '<div class="ceff"><span class="ep' + (pe > le ? " win" : "") + '">powdr ' + pe.toFixed(2) + '×</span> · ' +
    '<span class="el' + (le > pe ? " win" : "") + '">leanr ' + le.toFixed(2) + '×</span></div>';
  b.onclick = function() { cur = i; render(); };
  side.appendChild(b);
});

function panel(label, cls, data, orig) {
  const wrap = document.createElement("div"); wrap.className = "panel " + cls;
  const h = document.createElement("div"); h.className = "phead";
  let stats = statLine(data);
  if (orig) stats += "  ·  " + effOf(orig, data).toFixed(2) + "× fewer vars";
  h.innerHTML = '<span class="plabel">' + label + '</span><span class="pstats">' + stats + '</span>';
  const pre = document.createElement("pre"); pre.textContent = data.render;
  wrap.appendChild(h); wrap.appendChild(pre);
  return wrap;
}

// LCS line diff (guarded so huge circuits don't blow up the browser).
function diffLines(a, b) {
  const n = a.length, m = b.length;
  if (n * m > 8000000) return null;
  const dp = Array.from({length: n + 1}, function() { return new Uint32Array(m + 1); });
  for (let i = n - 1; i >= 0; i--)
    for (let j = m - 1; j >= 0; j--)
      dp[i][j] = a[i] === b[j] ? dp[i + 1][j + 1] + 1 : Math.max(dp[i + 1][j], dp[i][j + 1]);
  const out = []; let i = 0, j = 0;
  while (i < n && j < m) {
    if (a[i] === b[j]) { out.push([" ", a[i]]); i++; j++; }
    else if (dp[i + 1][j] >= dp[i][j + 1]) { out.push(["-", a[i]]); i++; }
    else { out.push(["+", b[j]]); j++; }
  }
  while (i < n) out.push(["-", a[i++]]);
  while (j < m) out.push(["+", b[j++]]);
  return out;
}

function diffPanel(orig, opt, name) {
  const wrap = document.createElement("div"); wrap.className = "panel diff p-" + (name === "leanr" ? "leanr" : "powdr");
  const h = document.createElement("div"); h.className = "phead";
  const d = diffLines(orig.render.split("\n"), opt.render.split("\n"));
  let adds = 0, dels = 0;
  if (d) d.forEach(function(x) { if (x[0] === "+") adds++; else if (x[0] === "-") dels++; });
  h.innerHTML = '<span class="plabel">original → ' + name + '</span>' +
    '<span class="pstats">' + (d ? ('<span style="color:var(--del-fg)">−' + dels + '</span>  ' +
      '<span style="color:var(--add-fg)">+' + adds + '</span> lines') : "") + '</span>';
  const pre = document.createElement("pre");
  if (!d) {
    const note = document.createElement("div"); note.className = "dnote";
    note.textContent = "(circuit too large to diff in the browser)";
    pre.appendChild(note);
  } else {
    const frag = document.createDocumentFragment();
    d.forEach(function(x) {
      const line = document.createElement("div");
      line.className = "dline " + (x[0] === "+" ? "dadd" : x[0] === "-" ? "ddel" : "dctx");
      line.textContent = (x[0] === " " ? "  " : x[0] + " ") + x[1];
      frag.appendChild(line);
    });
    pre.appendChild(frag);
  }
  wrap.appendChild(h); wrap.appendChild(pre);
  return wrap;
}

function render() {
  document.querySelectorAll(".caseb").forEach(function(b, i) { b.classList.toggle("sel", i === cur); });
  document.getElementById("tab-leanr").classList.toggle("active", tab === "leanr");
  document.getElementById("tab-powdr").classList.toggle("active", tab === "powdr");
  document.getElementById("view-split").classList.toggle("active", view === "split");
  document.getElementById("view-diff").classList.toggle("active", view === "diff");
  const c = DATA[cur], opt = tab === "leanr" ? c.leanr : c.powdr;
  document.getElementById("caption").innerHTML = "block <b>#" + c.rank + "</b> · pc" + c.pc;
  const content = document.getElementById("content");
  content.innerHTML = "";
  if (view === "split") {
    content.appendChild(panel("original", "p-orig", c.original, null));
    content.appendChild(panel(tab, tab === "leanr" ? "p-leanr" : "p-powdr", opt, c.original));
  } else {
    content.appendChild(diffPanel(c.original, opt, tab));
  }
}

document.getElementById("tab-leanr").onclick = function() { tab = "leanr"; render(); };
document.getElementById("tab-powdr").onclick = function() { tab = "powdr"; render(); };
document.getElementById("view-split").onclick = function() { view = "split"; render(); };
document.getElementById("view-diff").onclick = function() { view = "diff"; render(); };
document.addEventListener("keydown", function(e) {
  if (e.key === "ArrowDown" && cur < DATA.length - 1) { cur++; render(); }
  else if (e.key === "ArrowUp" && cur > 0) { cur--; render(); }
  else return;
  e.preventDefault();
});
render();
</script>
</body></html>"""


if __name__ == "__main__":
    main()
