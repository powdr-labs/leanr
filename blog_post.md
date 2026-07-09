# Rebuilding autoprecompiles in a week, formally verified

A week ago, I was looking for my first [Lean](https://lean-lang.org/) project. I turned to [leanr](https://github.com/powdr-labs/leanr), a project my colleague Christian Reitwiessner started 9 months ago to experiment with formally verifying powdr's [autoprecompile](https://powdr.org/blog/accelerating-ethereum-with-autoprecompiles) pipeline.

I was interested in a new paradigm for software development: Write the spec in a formal language, let AI write both the code and the proofs that it adheres to the spec. The core of the autoprecompile pipeline is a constraint system optimizer. It turns out not to be too hard to specify what it means for it to be correct: If you consider the *input* and *output* constraint system, we basically want:
- **Soundness**: For each satisfying assignment on the *output* constraint system, there must be a satisfying assignment on the *input* constraint system *with the same side effects*. Side effects are things like memory operations -- things that actually change the state of the zkVM. Under the assumption that the *input* constraint system enforces correct state transitions, this property ensures that the optimized one does as well.
- **Completeness**: For each satisfying assignment on the *input* constraint system, there must be a satisfying assignment on the *output* constraint system. This ensures that the prover can use the *output* chip in all cases. It also prevents a trivial "optimizer": One that always returns a minimal unsatisfiable circuit.

This is what this looks like in Lean:

:::warning
**TODO: Make this section in `Spec.lean` perfect & cite it here**
:::

## Zero-reviewed, AI-generated code

In this repository, the setup is the following:
- There are roughly ~400 LOC of spec, see [this section of the readme](https://github.com/powdr-labs/leanr#auditing-correctness). This code is thoroughly reviewed, and agents are instructed not to change it unless explicitly asked.
- There is some vibe-coded boilerplate to benchmark the system on [real-world inputs](https://github.com/powdr-labs/leanr/tree/main/OpenVmBenchmarks). For example, we're measuring optimizer effectiveness on the 100 costliest basic blocks on the [`openvm-eth`](https://github.com/powdr-labs/openvm-eth) guest program -- a program that verifies Ethereum blocks.
- The core optimizer implementation is hidden in the [`Implementation` module](https://github.com/powdr-labs/leanr/tree/main/Leanr/Implementation). I barely looked at it and do not review changes to it.
- A [Skill](https://github.com/powdr-labs/leanr/blob/main/.claude/skills/autoopt/SKILL.md) describes how to approach improving the optimizer.

All that's left for me to do is to open up Claude and prompt: "Improve the optimizer".

## The result: on par with powdr autoprecompiles + formally verified

:::warning
**TODO: Report results, link report**
:::

## Integration into powdr autoprecompiles

This project is designed to be a drop-in replacement for the [`powdr_autoprecompiles::optimizer::optimize`](https://github.com/powdr-labs/powdr/blob/5395a66442c82abc3c095d758f170773c4b5857d/autoprecompiles/src/optimizer.rs#L31-L41) function, so we went ahead and replaced it.

:::warning
**TODO: Describe integration, nightly results?**
:::

## Conclusion

What this experiment shows is that a new programming paradigm -- writing a formal spec, then letting AI handle everything else -- is completely practical today. It solves a key bottleneck in AI-driven software development: Reviews. Since models are still too 