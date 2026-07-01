# Optimizer improvement log

Append-only. Each entry: the idea, whether it worked, and its impact on the snapshot
(`Leanr/OpenVM/Snapshot.lean`, single OpenVM ADD-immediate). **Effectiveness** = distinct
variables in the input / distinct variables in the optimizer output (`≥ 1`; higher is better).
The input has **36** distinct variables, so effectiveness `1` = 36 output variables.

Invariants held for every commit: `lake build` succeeds, `optimizer_maintainsCorrectness` is
proven (no `sorry`/`admit`/`axiom`/`native_decide`), and the frozen spec/bus-semantics/test input
are untouched (only the recorded snapshot *string* is regenerated as the output changes).

---

## Architecture

The optimizer is a pipeline of **verified passes** (`Leanr/OptimizerPasses/Basic.lean`): each pass
is a function `cs → bs → { out // PassCorrect cs out bs }`, i.e. it carries its own proof that the
output is equivalent to the input and preserves invariants. Passes compose with `.andThen`
(correctness by transitivity), so the whole `optimizer` is correct by construction and the public
`optimizer_maintainsCorrectness` is just a projection.

Reusable, proven equivalence machinery (the hard proofs live here once; passes are thin):

- **`OptimizerPasses/Subst.lean`** — substitution `x := t`. If satisfying assignments force
  `x = t`, substituting everywhere is equivalence-preserving (`ConstraintSystem.subst_correct`).
  This is the workhorse for *variable elimination* (the only thing that moves the effectiveness
  metric, which counts distinct variables). Purely equational — no field assumptions.
- **`OptimizerPasses/Rewrite.lean`** — (a) `mapExpr`: any *eval-preserving* expression rewrite
  (constant folding, algebraic simplification) is automatically correct (`mapExpr_correct`);
  (b) `filterConstraints`: dropping *identically-zero* algebraic constraints is correct
  (`filterConstraints_correct`).

A pass = a decidable *detection* (find an `(x, t)` / a rewrite / a removable constraint) + supply
the entailment hypothesis to the relevant core lemma. In the `none`/not-applicable case a pass
falls back to the identity.

`babyBear = 2013265921` is prime; `Nat.Prime babyBear` is provable by `norm_num` (no axiom / no
`native_decide`), so field structure is available to passes that need it (e.g. dividing by a
nonzero constant coefficient). Introduced only when a pass requires it.

---

## Entries

### 0. Setup (infrastructure only; effectiveness unchanged at 1)
Added the reusable proof cores above (`Subst.lean`, `Rewrite.lean`) and this log. Pipeline is
still the identity, so the snapshot and effectiveness (`1`) are unchanged; this commit only lays
the foundation. The substitution correctness proof (the linchpin) is complete and general.
**Impact: none yet (36 → 36 variables).** Worked: yes (builds, cores proven).
