Go into leanr. You'll find a lean repository with a circuit optimizer. There is also a notion of optimizer correctness, which is proven for the current optimizer. There is also a snapshot test for a real-world example that I care about, measuring effectiveness.

Your task is to improve the optimizer as much as you can to maximize effectiveness on this example, while maintaining correctness. At any point, the optimizer must have a proof of correctness, as it does now.

A session of this was running before, so these are some notes:
- Read the existing logs and past commits for context if needed.
- You CAN use the fact that p is prime, and even if your optimization only works for the Baby Bear prime it is fine. Typically, it would be be some prime around ~2^30 or ~2^64.
- The last session stopped to early. Make sure that the workflow ensures that you don't stop unless you're fully out of ideas on how this circuit could be optimized further. Do prioritize more general optimizations, so I can decide to roll back a few commits if they get too specific.

DO NOT:
- Change anything in the spec (including the bus semantics and the test)
- Overfit to the one test case: I'm interesting in a good general algorithm, not in a small circuit for this particular example. It should also work in a completely different VM, with different bus semantics. Prioritize general optimization over overly specific ones.
- Use sorry, admit in the proofs, or introduce any axioms or native_decide. Verify with `grep -rn "sorry\|admit\|axiom" Leanr/` before each commit. If you can't prove it, either break it down or try a simpler idea. Every commit must `lake build`.

Maintain a log.md (committed on each commit), where you only append and report the general idea, whether it worked and what the impact was.