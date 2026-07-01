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

### 1. Constant folding / algebraic normalization (`ConstantFold.lean`) — enabler
Idea: a bottom-up eval-preserving rewrite (`Expression.fold`) that folds `const∘const`, drops
`+0`, and handles `*0`/`*1`, applied to every expression via the proven `mapExpr_correct`. Ranked
#1 by the idea workflow purely as an *enabler*: it removes no variable directly, but canonicalizes
the DSL sugar (`x - c` = `x + (-1)*c`, `2013265920 * 1`, `0 + …`) into the normal forms the later
detection passes rely on, and collapses `c * 0` to a literal `0` once substitution plants a zero.
Worked: yes — the snapshot is now visibly folded (e.g. `0 + opcode_add_flag_0 + …` → `opcode_add_flag_0 + …`,
`2013265920 * 1` → `2013265920`). Correctness is free from `mapExpr_correct` (only `fold_eval`, one
induction, no field). **Impact: effectiveness still 1 (36 → 36); shape only, as expected for an enabler.**

### 2. Constant substitution (`ConstantSubst.lean`) — first real reduction
Idea: after folding, a variable pinned to a constant shows up as `x` (⇒ `x=0`) or `x + const d`
(⇒ `x=-d`). `solveConst` detects these; `substFromConstraint` (a generic combinator: find the first
solvable constraint, substitute via the proven `subst_correct`, else identity) turns it into a pass.
The entailment `env x = c` comes from the constraint being `0` under `satisfies`, proved by
`linear_combination`. Pipeline now folds, then iterates "substitute one constant, re-fold" to a
fixpoint (`VerifiedPass.iterate`). No field/primality — works over any commutative ring.
Worked: yes. Eliminates exactly the 5 constant-pinned variables `from_state__pc_0=0`, `rd_ptr_0=8`,
`rs1_ptr_0=8`, `rs2_0=1`, `rs2_as_0=0` (the last is the cascade trigger). **Impact: 36 → 31,
effectiveness 36/31 ≈ 1.16.** `reads_aux__1__…` now survive only inside interactions whose
multiplicity became `0` (removed once zero-mult bus dropping lands).

### 3. Trivial-constraint removal (`TrivialConstraint.lean`) — cascade enabler
Idea: drop algebraic constraints whose fold is the literal `0` (via `filterConstraints_correct`);
`Expression.isConstZero` is the decidable check, and the dropped-are-zero obligation is discharged
by `fold_eval` + `isConstZero_sound`. Added into the fixpoint loop (fix → fold → drop-trivial).
Worked: yes — output algebraic constraints dropped from 32 to 21 (removed `1-1`, `0-0`, the five
now-satisfied `x=const` defining constraints, and the `rs2_as_0 * (…)` constraints that folded to
`0`). Field-free. **Impact: effectiveness unchanged at 36/31 (no variable is removed by this pass
alone — the freed aux variables still live in zero-multiplicity interactions), but it is the
prerequisite that isolates them for the next pass.**

### 4. Zero-multiplicity bus removal (`ZeroMultBus.lean`) — realizes the cascade
Idea: drop bus interactions whose multiplicity folds to the literal `0`, via a new proven core
`filterBus_correct`. The correctness has two parts: the dropped interaction's `violatesConstraint`
obligation is vacuous (multiplicity `≠ 0` is false), and a `0`-multiplicity stateful entry adds `0`
to every message's net multiplicity so the bus states stay `≈`-equal (`multiplicitySum_filterBus`,
by induction on the interaction list). This is the *only* spec-safe bus removal — cancelling
opposite-sign pairs is rejected as unsound for arbitrary bus semantics (it would drop real
`violatesConstraint` obligations). Field-free. Added last in the fixpoint cycle.
Worked: yes. Once `rs2_as_0 := 0` zeroes the second read's multiplicities, those interactions are
dropped, removing the last occurrences of `reads_aux__1__base__prev_timestamp_0` and the two
`reads_aux__1__…lower_decomp…` limbs. **Impact: 31 → 28, effectiveness 36/28 = 9/7 ≈ 1.29.** This
completes the general, field-free portion (8 variables eliminated from 36).
