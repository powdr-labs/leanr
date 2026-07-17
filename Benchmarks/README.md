# Benchmarks

apc-optimizer benchmark inputs and the scripts that run them.

- [`benchmark.py`](./benchmark.py) — sweep a set and report aggregate apc-optimizer-vs-powdr
  **effectiveness** (circuit size before / after). `--vm {openvm,sp1}` picks the VM (default
  `openvm`), the positional argument picks the set (default `openvm-eth` / `rsp`).
- [`runtime_bench.py`](./runtime_bench.py) — bench the optimizer's **runtime** (OpenVM only).

Sets are grouped by VM, each with its own README:

- [`OpenVM/`](./OpenVM/) — BabyBear; main set `openvm-eth`.
- [`SP1/`](./SP1/) — KoalaBear; main set `rsp`.

```bash
Benchmarks/benchmark.py                 # all openvm-eth cases
Benchmarks/benchmark.py --vm sp1        # all rsp (SP1) cases
Benchmarks/benchmark.py --n 10 --report report.html   # + interactive HTML report
```
