# Verified Constraint System Optimizer

## Benchmark CLI

The `leanr` executable measures the optimizer on powdr `SymbolicMachine`
exports (`ApcWithBusMap` JSON, plain or gzipped — the format of
`OpenVm/Benchmark/*.json.gz` and `apc_reth_op_bug.json.gz`):

```bash
lake build

# Run the leanr optimizer on a test case and report effectiveness
lake exe leanr run [--iters N] OpenVm/Benchmark/apc_003_pc2099976.json.gz

# Report powdr's effectiveness from its serialized optimizer output
lake exe leanr powdr OpenVm/Benchmark/apc_003_pc2099976.json.gz \
                     OpenVm/Benchmark/apc_003_pc2099976.powdr_opt.json.gz

# Both, side by side
lake exe leanr compare [--iters N] <unopt.json.gz> <unopt.powdr_opt.json.gz>
```

Effectiveness = distinct variables before / after (see `Leanr/Utils/Size.lean`).
`--iters` bounds the optimizer's cleanup cycles (default 32); each cycle
substitutes only a bounded number of variables, so large machines need more
iterations to converge.

Batch over the whole benchmark set:

```bash
for f in OpenVm/Benchmark/apc_*_pc*.json.gz; do
  case "$f" in *.powdr_opt.json.gz) continue;; esac
  echo "== $f"
  lake exe leanr compare --iters 64 "$f" "${f%.json.gz}.powdr_opt.json.gz"
done
```

## Benchmark data (`OpenVm/Benchmark/`)

Pairs of `apc_<rank>_pc<pc>.json.gz` (the machine exactly as it enters powdr's
`optimize()`, with its bus map) and `apc_<rank>_pc<pc>.powdr_opt.json.gz`
(powdr's optimized result), ranked by cost = columns × execution frequency;
`manifest.json` records provenance and per-block stats.

The current set is an **interim** one (top 20 of a small keccak guest, default
bus map — see `manifest.json`). The intended set is the 100 costliest blocks
of the openvm-eth benchmark, which needs ≥ 16 GB RAM to generate. On a big
machine:

```bash
git clone -b leanr-benchmark-export git@github.com:powdr-labs/openvm-eth.git
cd openvm-eth && RPC_1=<archive rpc url> ./scripts/export_leanr_benchmark.sh
# then copy leanr-benchmark/* into OpenVm/Benchmark/ here
```

The branch commits the prebuilt guest ELF (no cargo-openvm needed); the block
witness is fetched from `RPC_1` once and cached under `rpc-cache/` (omit
`RPC_1` if the cache is already populated). See the script header for
tunables.
