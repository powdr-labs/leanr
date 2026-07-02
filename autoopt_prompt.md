Go into leanr. You'll find a lean repository with a circuit optimizer. There is also a notion of optimizer correctness, which is proven for the current optimizer. There is also a snapshot test for a real-world example that I care about, measuring effectiveness.

Your task is to improve the optimizer as much as you can to maximize effectiveness on this example, while maintaining correctness. At any point, the optimizer must have a proof of correctness, as it does now.

There is a large benchmark that you can run on, e.g.:
```
lake exe leanr run Leanr/OpenVm/Benchmark/apc_001_pc3647036.json.gz
warning: mathlib: repository '/Users/georg/coding/leanr/.lake/packages/mathlib' has local changes
Parsed 486 constraints, 232 bus interactions, 6 bus types
  before: 511 vars, 486 constraints, 232 bus interactions
  leanr : 444 vars, 359 constraints, 227 bus interactions
leanr effectiveness (vars before / after): 511/444 ≈ 1.150901
  (32 iters, 3679 ms)
```

Note that optimization time is relatively slow, but in each iteration, it is probably enough to sample just a few examples. The final evaluation will be on all 100 test cases. ignore the powdr_opt files.

This is not the first time the loop is run. Read the log and check the commit history to see what happened before.

DO NOT:
- Change anything in the spec (including the bus semantics and the test)
- Overfit to the one test case: I'm interesting in a good general algorithm, not in a small circuit for this particular example. It should also work in a completely different VM, with different bus semantics. Prioritize general optimization over overly specific ones.
- Use sorry, admit in the proofs, or introduce any axioms or native_decide. Verify with `grep -rn "sorry\|admit\|axiom" Leanr/` before each commit. If you can't prove it, either break it down or try a simpler idea. Every commit must `lake build`.

Maintain a log.md (committed on each commit), where you only append and report the general idea, whether it worked and what the impact was (which benchmark, how the effectiveness changed).