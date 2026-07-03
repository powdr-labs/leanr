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

### 5. Affine substitution / linear elimination (`Affine.lean`) — generalizes constant substitution
Idea: the general form of variable elimination. Normalize a constraint to a linear form
`a₀ + Σ aᵢ·vᵢ` (`linearize`, with `linearize_eval` proving it eval-preserving; returns `none` on a
genuine variable×variable product). If some variable `x` has a unit coefficient (`±1`), solve
`x = ∓(a₀ + rest)` and substitute via the proven `subst_correct`. The entailment `env x = t`
comes from `LinExpr.eval_split` (coefficient/remainder decomposition) + the constraint being `0`.
Fed to the same `substFromConstraint` combinator; replaces `constantFixPass` in the pipeline (a
constant is the 0-term affine case). Purely equational — unit coefficients are units in **any**
commutative ring, so still no field/primality needed (a generality strength: works over any modulus).
Worked: yes. Beyond the 5 constants it eliminates `c__2_0` (`c2 = c3`), `c__0_0`
(`c0 = 1 - 256·c1 - 65536·c2`), `opcode_add_flag_0` (`Σ flags = 1`) and `opcode_sub_flag_0`
(weighted-flag sum `= 0`). Since substitution is *degree-preserving* (a linear variable becomes a
linear expression), this reduces the column count — the dominant proving cost the metric tracks —
without raising constraint degree, though it does grow some expression sizes (the selectors appear
in many multiplicities). **Impact: 28 → 24, effectiveness 36/24 = 3/2 = 1.5.**

### 6. Affine normalization / collect-like-terms (`Normalize.lean`) — cascade unlock + de-bloat
Idea: `linearize` only *concatenates* terms, so after affine inlines a flag, a selector sum like
`add + sub + xor + or + and` carries cancelling terms (`x + (-1)·x`) that never collapse. Add a
term-**merge** (`mergeTerms`, via an incremental `addCoeff` with a local eval lemma — sidestepping a
"regroup-sum-by-key" proof) plus zero-dropping, giving `LinExpr.norm`. `Expression.normalize` then
replaces each maximal affine subexpression by its merged form; correct for free via `mapExpr_correct`
(only `normalize_eval`). Field-free.
Worked: yes, with a compounding effect. (a) The selector sum collapses to the constant `1`, so a
constraint `selector * X = 0` folds to `1 * X` → `X`, exposing the previously non-linear timestamp
constraints as affine — the affine pass then eliminates `from_state__timestamp_0` and a second
timestamp variable. (b) Merging also *undoes* the expression bloat from step 5's selector inlining:
the rendered circuit shrinks from ~16 KB to ~7.6 KB (smaller than before step 5). **Impact: 24 → 22,
effectiveness 36/22 = 18/11 ≈ 1.64, with a cleaner (smaller) circuit than any previous step.**

### 7. Concrete correctness capstone (`OpenVM/SnapshotCorrect.lean`)
Not an optimization — a machine-checked instance of `optimizer_maintainsCorrectness` for the exact
snapshot circuit: `addiOptimized.equivalentTo addiInput (openVmBusSemantics babyBear)` and invariant
preservation. Depends only on the three standard Mathlib axioms (`propext`, `Classical.choice`,
`Quot.sound`) — no `sorry`/`native_decide`/custom axiom. Notably it needs **no** primality instance:
every pass is field-agnostic, so correctness holds over any modulus (stronger than the prime-field
setting). **Impact: effectiveness unchanged; adds a concrete verified equivalence for the test case.**

---

### 8. Finite-domain propagation / boolean case analysis (`DomainProp.lean`) — first prime-field pass
Idea: many variables are pinned to a *finite domain* by a product-of-affine-factors constraint
(`x·(x−1)` ⇒ `x ∈ {0,1}`, `c·(255−c)` ⇒ `c ∈ {0,255}`); over an integral domain a product is zero
only if a factor is, and an affine factor has one root — the first place primality is genuinely
needed (`p.Prime` is *decided at runtime* via the compiler-fast `Nat.decidablePrime`; for composite
`p` the pass is the identity, so the optimizer's signature and every existing statement stay
modulus-agnostic). Any constraint whose variables all have finite domains is then decided by
exhaustive enumeration over the domain product (capped at 4096): if every satisfying assignment
gives `x = c`, substitute via the proven `subst_correct`. The enumeration certificate
(`checkForced`) is decidable and is all the proof consumes — the candidate search is proof-free.
This is SAT-style unit propagation on field elements, and it resolves what no affine reasoning can:
from `xor, or, and ∈ {0,1}` and `(1 + xor + 2·or + 3·and)·(xor + 2·or + 3·and) = 0` (the residue of
the one-hot selector constraints after affine elimination of `add`/`sub`), only `(0,0,0)` survives,
so all three remaining opcode flags are 0. Pipeline: inserted after `affineSubstPass` in the cycle;
iterate bumped 16 → 24 (now ~14 substitutions to fixpoint). Worked: yes. The cascade also folds the
bitwise-lookup payloads to `[a_i, a_i, 0, 1]`, drops all five boolean/one-hot constraints and the
four `sub`-carry constraints, leaving 5 algebraic constraints (4-limb add-carry chain + the
`c ∈ {0,255}` immediate-limb constraint). **Impact: 22 → 19, effectiveness 36/19 ≈ 1.89.**
An idea-panel + adversarial-verification workflow over the remaining circuit found no sound,
provable idea with variable impact beyond this pass: the surviving 19 (a/b limbs, prev-data limbs,
prev-timestamps, range-decomposition limbs, c-limbs) are pinned by stateful side effects or by
lookup-table facts whose generic derivation would require enumerating the whole field.

### 9. Affine solving generalized to unit coefficients (`Affine.lean`)
Idea: `trySolve` only pivoted on `±1` coefficients, so a constraint like `2x + 4y + 6 = 0` (no
unit-normalized variable) was unsolvable even over a field where any nonzero coefficient invertible.
Added `trySolveUnit`: pivot on any coefficient `a` passing the decidable re-check `a * a⁻¹ = 1`
(the ring's `Inv`, so soundness never trusts inversion — still field-free: over `ZMod n` exactly
the gcd-1 residues qualify, over a prime field everything nonzero). `solveAffineLin` prefers a
`±1` pivot (substitutes without rescaling, keeping expressions small) and falls back to a unit
pivot. With primality this makes single-constraint linear elimination *complete*: combined with
the iterate-to-fixpoint loop, any variable eliminable by linear reasoning is eliminated.
Worked: yes (proof via `linear_combination` from `eval_split` + the unit certificate).
**Impact: snapshot unchanged (36/19 ≈ 1.89) — every solvable constraint here already had a `±1`
pivot; this is a generality/completeness improvement for other circuits.**

### 10. Satisfied-constant-lookup removal (`TautoBus.lean`)
Idea: a *stateless* interaction whose evaluated message is the same under every assignment
(multiplicity **and** payload all fold to constants — the multiplicity is part of the message
`violatesConstraint` sees, so it must be constant too, a subtlety surfaced by the adversarial
review) and whose constant message the bus table accepts (`violatesConstraint` probed once,
generically, on that message) imposes no obligation and no side effect; dropping it is proven by a
new core, `filterBusStateless_correct` (side effects stay *equal* — stateless interactions never
enter `sideEffects`). This is the first pass that *calls into* the opaque bus semantics, and it is
still fully generic in it. Field-free. Added at the end of the fixpoint cycle.
Worked: yes. On the snapshot it removes the PC-lookup row `[0, 512, 8, 8, 1, 1, 0, 0, 0]`, whose
tuple became fully constant back when the constant/affine passes pinned `pc`, `rd_ptr`, `rs1_ptr`,
`rs2`, `rs2_as` (16 → 15 interactions). In general it removes any lookup that substitution turns
into a satisfied table row (e.g. range checks on values that became in-range constants).
**Impact: variables unchanged (19, effectiveness 36/19 ≈ 1.89); one interaction and its 9-tuple
gone from the circuit.**

### 11. Occurrence-aware pivot selection (`Affine.lean`: `bestAffinePivot`)
Idea: `substFromConstraint` substituted the *first* solvable pivot, which inlined the timestamp
into five stateful payloads (a 4-term expression copied per occurrence). Now the pass enumerates
*all* solvable pivots `(x, t)` of all constraints (`solvableFrom`, each candidate carrying the
same per-constraint entailment as before — the heuristic choice adds zero proof burden) and picks
the one minimizing `(occurrences(x) − 1) · (1 + |vars(t)|)`, i.e. the least expression
duplication; a variable occurring only in its defining constraint costs 0. Field-free.
Worked: yes, with a visibly better circuit: `from_state__timestamp_0` stays a plain variable in
the execution-bridge/memory payloads, `c__2_0` is eliminated through the rs2 decomposition (a
`65536`-coefficient unit pivot — entry 9 paying off), the bitwise lookup becomes the literal
`[c__0_0, c__1_0, 0, 0]`, and the carry chain reads directly over `a/b/c` limbs. **Impact:
variables unchanged (19, effectiveness 36/19 ≈ 1.89); rendered circuit 3041 → 2470 bytes (−19%),
now structurally what a hand optimizer would write.**

### 12. Idempotent normalization + deterministic tie-breaking (`Normalize.lean`, `Affine.lean`)
Found by an adversarial completeness panel and reproduced independently: `mergeTerms` used
`foldr` while `addCoeff` appends unseen variables at the tail, so every `normalize` *reversed*
each affine form's term order. The pipeline never reached a structural fixpoint — it was a
period-2 oscillator (variables stable from cycle ~9, term order flipping forever), so the stored
snapshot silently depended on the *parity* of the iterate cap (24 passed, 25 failed, 26 passed —
a trap for cap changes and for the auto-merge vision), and the flipping order leaked into
`bestAffinePivot`'s first-on-tie `argmin`: the structurally identical read/write timestamp
constraints broke their cost-4 ties to *different* pivot kinds, planting `131072⁻¹`-rescaled
constants into a bus-3 payload. Fixes: (a) `mergeTerms` now folds *left* (first-occurrence order,
idempotent; eval-preservation re-proved by an accumulator-generalized induction — same
`addCoeff_eval` core); (b) `solvableFrom` lists all `±1` pivots before general unit pivots, so on
a cost tie the non-rescaling pivot wins deterministically. Verified: one extra full cycle on the
output is now a strict no-op (previously false), the whole optimizer is idempotent, and the
reads/writes halves come out symmetric — all four bus-3 range checks are plain variables again
and the inverse-constant artifacts are gone. **Impact: variables unchanged (19, effectiveness
36/19 ≈ 1.89); output is now a true, cap-independent fixpoint and the circuit is cleaner
(2470 → 2519 bytes: the two memory receive rows now carry the full timestamp decomposition
symmetrically instead of one asymmetric range-check row).**

### 13. Monic scaling of constraint factors (`MonicScale.lean`) — canonicalization
Idea (from the same panel): an algebraic constraint matters only through its zero set, so it may
be rescaled by any *unit* — unlike bus expressions, whose values are observable. A new small core
(`mapConstraintsIff_correct`: rewriting constraints with any pointwise zero-set-preserving map is
`PassCorrect`) plus a product-tree walk that scales every affine factor to monic form, each step
carrying a checked unit certificate (`u * v = 1`; the ring's `Inv` only *proposes* the scale, so
soundness is field-free and holds over any modulus). Runs once after the fixpoint loop, followed
by a fold. Worked: yes. The carry-chain booleanity constraints shed their `256⁻¹` leading
coefficients — the first one now renders literally as `(b₀ + c₀ − a₀) · (b₀ + c₀ − a₀ − 256) = 0`,
the immediate-limb constraint as `(c₀ + 256·c₁ − 1) · (…) = 0` — exactly the form a hand-written
circuit would use. **Impact: variables unchanged (19, effectiveness 36/19 ≈ 1.89); rendered
circuit 2519 → 2402 bytes; whole-optimizer idempotence retained.**

## Summary

Starting from the identity (effectiveness `1`, 36 variables), the optimizer now reduces the
ADD-immediate circuit to **11 variables, effectiveness 36/11 ≈ 3.27**, with 12 bus interactions
and 4 monic algebraic constraints (the `a = b + 1` carry chain) — every step proven
`PassCorrect` with no `sorry`/`admit`/`axiom`/`native_decide`; the concrete correctness
theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.

Three knowledge tiers feed the pipeline (design: `DESIGN-bus-knowledge.md`):
1. **Field-agnostic passes** (entries 1–13): constant folding, occurrence-cost affine
   substitution with unit pivots, normalization (a true fixpoint), trivial/zero-multiplicity/
   tautology dropping, monic canonicalization.
2. **Proven `BusFacts`** (entry 16, zero audit surface): per-slot bounds and functional
   dependences proven against the concrete semantics unlock fact-domain enumeration and
   pointwise `violatesConstraint` probing — the `c` limbs.
3. **The audited memory discipline** (entries 17–18, one declaration per VM): order-free
   last-write-wins clauses in `satisfies` entail receive-equals-send equations, eliminating the
   write-witness variables and their decomposition limbs.

The remaining 11 variables (`a×4, b×4, from_ts, rdec₀, rdec₁`) are the floor under this
knowledge: all are observable in stateful side effects except the read-decomposition limbs,
which parameterize the read's previous access — genuinely the context's choice. Known
quality-only follow-ups (no variable impact): dropping the now-net-zero cancelled send/receive
pair (needs a pair-drop discipline lemma; the earliest-send side condition makes it provable),
and the `slotFun` affine-interpolation pass (verified `NOT(x) = 0xff − x` rewriting) for
circuits that use the XOR table.

### Hints from Georg

#### Memory optimizer

If you look at this pair of bus interactions on the memory bus (1):
```
mult=1, args=[1, 8, b__0_0, b__1_0, b__2_0, b__3_0, from_state__timestamp_0]
mult=2013265920, args=[1, 8, writes_aux__prev_data__0_0, writes_aux__prev_data__1_0, writes_aux__prev_data__2_0, writes_aux__prev_data__3_0, writes_aux__base__prev_timestamp_0]
```

They could cancel out if you set `writes_aux__prev_data__*_0 = b__*_0` and `writes_aux__base__prev_timestamp_0 = from_state__timestamp_0`. This is possible without violating any constraints. That's also a general pattern that often works on the memory bus: Each "access" receives the previous value and sends the new value. If in within one circuit the same address is accessed twice, the first send and second receive can cancel out. This can also be applied iteratively if there are more accesses to the same address.

The received timestamp is usually asserted to be smaller than the current timestamp. That should be the case if you set `writes_aux__base__prev_timestamp_0 = from_state__timestamp_0`.
Your algorithm can be such that it only considers consecutive pairs of interactions *to the same address*. In theory, this could miss opportunities, because they could be out of order, but in practice, the memory bus interactions are already sorted.

#### Figuring out `c`

You should be able to figure out *all* limbs of `c`.

These are the original constraints (written in a more readable way and ordered differently):
```
// The rs2 address space is 0
rs2_as_0 = 0
// The rs2 "address" is 1. Turns out, that's actually the *value* of c!
rs2_0 = 1

// Bus 6 (tuple range checker)
// => c__0_0 and c__1_0 are bytes!
mult=0 + opcode_add_flag_0 + opcode_sub_flag_0 + opcode_xor_flag_0 + opcode_or_flag_0 + opcode_and_flag_0 + 2013265920 * rs2_as_0, args=[c__0_0, c__1_0, 0, 0]

// c__2_0 is either 0 or 255
(1 - rs2_as_0) * (c__2_0 * (255 - c__2_0)) = 0

// c__2_0 == c__3_0
(1 - rs2_as_0) * (c__2_0 - c__3_0) = 0

// Putting everything together, we have:
// c__0_0 + c__1_0 * 2^8 + c__2_0 * 2^16 = 1
// With all the constraints in place, the only solution is c__0_0 = 1, c__1_0 = 0, c__2_0 = 0, c__3_0 = 0!
(1 - rs2_as_0) * (rs2_0 - (c__0_0 + c__1_0 * 256 + c__2_0 * 65536)) = 0
```
### 14. Assessment of hint "Memory optimizer" — blocked by the frozen equivalence (no commit)
The transformation is a *witness choice*, not an entailment: nothing in the circuit forces
`writes_aux__prev_data__* = b__*` — the optimizer must *pin* locally-free variables that occur in
a **stateful** payload. Under the frozen spec this is provably impossible, by a countermodel that
fits in five lines. Take any satisfying `env` with `writes_aux__prev_data = g ≠ b(env)` and
`W(env) = 42` (locally satisfiable: the prev-data limbs are unconstrained). Then
`orig.sideEffects env` contains **four distinct** bus-1 messages with net multiplicities
`⟨(b,R):−1, (b,T):+1, (g,42):−1, (a,T+2):+1⟩`. Any output in which the pair is cancelled (pinned,
substituted, dropped, or merged) has only two bus-1 interactions, and a list of two stateful
entries supports at most two distinct messages with nonzero net multiplicity — so no `env'` can
satisfy `orig.sideEffects env ≈ out.sideEffects env'`, and the `original.implies optimized`
direction of `equivalentTo` fails. (The support-cardinality of the reachable side-effect set is
an invariant of `≈`-equivalence; eliminating observable witness freedom shrinks it.) The same
argument blocks *adding* the constraints `wprev = b` instead of substituting. This is a real gap
between the frozen spec and powdr's de-facto notion: powdr's cancellation is justified
*contextually* (a dangling receive can never balance in any global system, so assignments like
the countermodel's are globally irrelevant — but they are locally satisfying, and the spec
quantifies over all of them). Licensing this optimization requires a spec-level decision, e.g.
comparing side effects only up to balanced global completions, or a bus-discipline-aware
`satisfies`. Deliberately **not** implemented: no `PassCorrect` proof can exist for it.

### 15. Assessment of hint "Figuring out c" — entailment is real, generic derivation is Ω(p) (no commit)
The chain (`c₂ ∈ {0,255}` ⇒ two affine lines for `(c₀,c₁)`; the bus-6 row `[c₀,c₁,0,0]` with
multiplicity 1 obliges `violatesConstraint = false`, i.e. bytes; bytes kill the `c₂ = 255` line
and pin `(c₀,c₁) = (1,0)` on the other) is a genuine entailment of `satisfies` — verified
pointwise against the real semantics, and it is the first derivation that needs the *bus*
half of `satisfies`, which the substitution core supports fine. The wall is decidable
*derivation* inside the optimizer: `violatesConstraint` is an opaque function, so "bytes" can
only be learned by pointwise probing, and soundness needs the whole solution lines covered — an
adversarial semantics agreeing with all probes but accepting one unprobed point admits a
satisfying assignment with a different `c`, so any sound pass must make ~2^32 probes. Measured
probe cost in the elaboration-time interpreter (which is what runs the snapshot `#guard`):
2.7 µs ⇒ ≈ 2 × 98 min per optimizer evaluation. Infeasible; deliberately not implemented.
What would unfreeze it: structured table metadata on `BusSemantics` (a machine-readable range/
tuple spec per bus id, with `violatesConstraint` proven consistent with it) — then the byte facts
become O(1) entailments, the line-enumeration pass is cheap (65 536 points), fully general, and
would take the snapshot to **17 variables (36/17 ≈ 2.12)**; combined with a spec resolution for
entry 14 (**19 → 13** on its own), the two compose to **11 variables (36/11 ≈ 3.27)**. The same
opaque-table wall blocks the related decomposition-limb fusion (`wdec0 + 2^17·wdec1 → w` with a
single 29-bit check, −1 variable): it needs `V([a,17]) = V([b,12]) = false ↔ V([a+2^17·b,29]) =
false`, unknowable without table knowledge.

### 16. Layer 1: proven bus facts + fact-aware domain propagation (`BusFacts.lean`, `OpenVM/Facts.lean`, `FactPass.lean`, `DomainProp.lean`) — 19 → 17
Implements the first layer of `DESIGN-bus-knowledge.md`. `BusFacts p bs` carries proven claims
about a semantics — per-slot value bounds and functional dependences keyed by (busId, constant
pattern), plus table-free buses — so supplying them adds nothing to the audit surface (a wrong
fact would not compile; `openVmFacts`' proofs against the concrete `violates` are ~6 lines
each). `VerifiedPassW` threads facts through the pipeline (`BusFacts.trivial` recovers the
fact-free `optimizer` and its unchanged `optimizerMaintainsCorrectness`; the snapshot now tests
`optimizerWith … openVmFacts`, with `optimizerWith_correct` giving the same two correctness
clauses per instance). Domain propagation gains two new sources of deductions: (a) *fact
domains* — an interaction with constant nonzero multiplicity carrying `x` in a fact-bounded slot
gives `x ∈ [0, bound)`; (b) *probed obligations* — a bus interaction whose variables all have
finite domains is enumerated like a constraint, each point checked directly against the opaque
`violatesConstraint` (small domains make the previously-infeasible probing cheap: 256–65536
calls). Worked: yes. The byte bounds on `c__0_0, c__1_0` (from the bitwise row) let the two-line
constraint enumeration pin `(c₀, c₁) = (1, 0)`; the substitution folds the bitwise row to the
constant `[1, 0, 0, 0]`, which the tautology pass drops, and the carry chain specializes to
literal `b + 1 = a` form: `(b₀ + 1 − a₀) · (b₀ + 1 − a₀ − 256) = 0`. **Impact: 19 → 17
variables, effectiveness 36/17 ≈ 2.12; interactions 15 → 14; the c-limbs, their two-value
constraint, and the immediate lookup are all gone.**

### 17. Layer 2a: last-write-wins memory discipline in the spec (audited; no snapshot change)
Implements the audited half of `DESIGN-bus-knowledge.md`. `Spec.lean` gains `MemoryBusShape`
(`addressFields`/`tsField`/`tsBound` — payload positions, so any layout works), the
`BusSemantics.memoryBus` declaration field, and `ConstraintSystem.memoryDiscipline`: three
**order-free** clauses over evaluated messages (matching by `(address, timestamp)`; in-window
consumption of the earlier of two timestamp-adjacent sends; timestamp range), conjoined into
`satisfies`. Order-freedom is deliberate: a fragment listing its accesses out of time order can
only cost optimizations, never correctness (log entry 14's countermodel dies because garbage
witnesses now violate in-window consumption, not because of any list convention). OpenVM
declares bus 1 with `{ addressFields := [0,1], tsField := 6, tsBound := 2^29 }` — the audited
assumption, justified by offline memory checking (Blum et al.) plus per-instruction exclusive
timestamp windows. All satisfies-transfer proofs were extended: substitution and eval-preserving
rewrites transport the discipline pointwise; zero-multiplicity bus removal preserves it because
inactive messages are invisible to all three clauses (now gated to be the identity in the
degenerate `ZMod 1`, where `1 = 0` breaks that argument); tautology removal now also requires
the dropped bus to have no declared discipline. **Impact: none yet (17 variables, snapshot
byte-identical) — this commit only makes the unification entailments derivable.**

### 18. Layer 2b: memory send/receive unification (`MemoryUnify.lean`) — 17 → 11
The consumer of the discipline (entry 17). On a declared last-write-wins bus with exactly two
active constant-multiplicity sends to the same constant address and a *constant* timestamp gap
(within `tsBound`, so `.val` arithmetic cannot wrap), the in-window-consumption clause entails
that some in-fragment receive carries the earlier send's exact tuple. The pass identifies it by
refuting every other candidate — non-`-1` constant multiplicity, or a timestamp differing from
the send's by a certified never-zero affine form (constant plus fact-bounded negative terms:
`-1 - rdec₀ - 2^17·rdec₁` can never be `0` because the bounded sum stays below `(-1).val`; the
bounds come from Layer 1's range facts, the value reasoning from `ZMod.val_{add,mul}_of_lt`) —
and **adds the entailed slot-wise equalities** `receive[i] = send[i]` as constraints (via the
small new `addConstraints_correct`; re-adding is prevented by a normalize-triviality filter, so
the pass is idempotent). The proven affine/domain machinery then does all the elimination:
`writes_aux__prev_data__* := b__*`, and the timestamp equation collapses `wdec₀ + 2^17·wdec₁ = 1`
— affine solves `wdec₀`, the probed-obligation enumeration pins `wdec₁ = 0` from its rewritten
range lookup, and the write's range-check rows fold to accepted constants and are dropped.
Iterate budget 24 → 32 for the longer cascade. Worked: yes, end to end. **Impact: 17 → 11
variables, effectiveness 36/11 ≈ 3.27; interactions 14 → 12; the cancelled send/receive pair
remains rendered with net multiplicity zero (dropping it is a possible follow-up needing a
pair-drop discipline lemma; it carries no variables).** The remaining 11 (`a×4, b×4, from_ts,
rdec₀, rdec₁`) are the floor predicted in `DESIGN-bus-knowledge.md`: all observable in side
effects except the read-decomposition limbs, which encode genuine witness freedom (the read's
previous access belongs to the context).

### 19. Batch linear elimination — `SubstMap.lean` + `Gauss.lean` (new benchmark focus)
The focus shifts from the snapshot to the real benchmark set (`Leanr/OpenVm/Benchmark/`,
top-100 openvm-eth APCs; measured effectiveness below is on those). Diagnosis: the pipeline
eliminated ~2 variables per cleanup cycle (one `affineSubstPass` pivot + one `domainPropPass`
substitution), each cycle costing a full-system rescan — case 1 (511 vars) needed 400 cycles
/ 197 s to reach its 314-var fixpoint, and the 5000-var cases are unreachable. Two additions:
(a) **`SubstMap.lean`** — the batch substitution core: `Expression.substF` substitutes a whole
map `String → Option (Expression p)` in one traversal, with `ConstraintSystem.substF_correct`
mirroring `subst_correct` (entailment hypothesis per mapped pair). (b) **`Gauss.lean`** —
batch Gaussian elimination: two sweeps over the constraints, each constraint *reduced* by the
solutions found so far (`substF` + `normalize`) and solved for a unit-coefficient pivot (the
proven `pm1PivotsOf`/`unitPivotsOf` candidates), pivots chosen by duplication cost
(occurrence map precomputed once) with a penalty for rewriting a raw stateless-bus payload
slot into a compound expression (that would destroy fact-derivable range knowledge). The
solution map is kept *resolved* (new pivots substituted into stored solutions), carried in a
proof-bundled `Std.HashMap` (`Solved`, built on `getElem?_insert` /
`mem_toList_iff_getElem?_eq_some`), and applied in a **single** system traversal. Replaces
`affineSubstPass` in the cycle (that pass's machinery is still the proof backbone).
Worked: yes. Case 1: 511→324 vars in 32 cycles / 5.0 s (before: 511→444 in 32 cycles / 3.5 s;
the old passes needed 400 cycles / 197 s for their 314 fixpoint, which the new pipeline
reaches at ~100 cycles / 43 s — the remaining slow tail is `domainPropPass`, still
one-variable-per-cycle, next entry). Cases 2/3 unchanged (134→69, 108→78 — already at the
old fixpoint; their gap is memory unification). Snapshot unaffected (36/11).
**Impact: benchmark case 1 effectiveness 1.15 → 1.58 at default iters.**

### 20. Batch finite-domain propagation (`DomainBatch.lean`)
Same batching treatment for `domainPropPass`, which substituted one forced variable per cycle
and re-derived every domain by a quadratic scan. `DomainTable` (a proof-carrying
`Std.HashMap`, built once per cycle) collects domains from product-of-affine constraints
(`rootsIn`) and fact-bounded raw payload slots (`interactionDomain`), keeping the smallest
domain per variable; the existing checked certificates (`checkForced`/`checkForcedBi`) are
then evaluated for *every* constraint and bus obligation against the table, and all forced
constants are substituted in one `substF` traversal (via the `Solved` machinery from entry
19 — constants need no resolution). Enumeration caps unchanged. Replaces `domainPropPass` in
the cycle. Worked: yes. Case 1: 511→284 vars at 32 cycles (was 324; the old passes' 400-cycle
ceiling was 314 — batch pinning cascades further because all forced values land within one
cycle). Cases 2/3 unchanged (memory-bound). Snapshot unaffected (36/11). Cycle time rose
(5.0 s → 11.8 s on case 1: the enumeration now runs every cycle even when converged) — to be
recovered by fixpoint early-exit. **Impact: case 1 effectiveness 1.58 → 1.80.**

### 21. Generalized batch memory unification (`MemoryUnifyBatch.lean`) + fixpoint early-exit
Entry 18's pass required *exactly two* active sends on the whole bus — never true on real
blocks. `checkMemMatchG` generalizes the certificate: for a send pair `(S, S')` to the same
constant address, **each** other interaction on the bus is individually excluded as an
in-between send — by being `S`/`S'`, a constant multiplicity ≠ 1, a provably different
constant address (`addrConstsNeq`, new), or a constant timestamp offset placing it outside
the open window (`notBetweenTs`, new: `ts S = ts bi + e` with `tsBound + e.val ≤ p`, or
`ts bi = ts S + d` with `gap ≤ d.val` — exact `ZMod.val` arithmetic via the discipline's
range clause). Receive identification as before plus the different-address refutation. The
search pairs each send with its closest later same-address send; all matches found in one
invocation are certified and their equalities added at once. Chains resolve back-to-front,
one pair per pipeline cycle. Also: `VerifiedPassW.iterateStable` stops the cleanup loop at a
structural fixpoint, making generous iteration budgets free (case 3 now converges in 0.1 s),
and the CLI gains `vars`/`render` diagnostic subcommands.
Worked: yes. Case 2: 69 → 57 vars (2.35×; the three ALU instructions have rd = rs1, so the
register-read send and the same-register write pair up within each instruction — the write's
`prev_data` and timestamp decomposition all collapse); case 4: 468 → 240 (1.95×). Cases 1/3
unchanged — diagnosis (via `leanr vars`): their remaining gap vs powdr is dominated by two
*frozen-spec* walls, (i) cross-instruction timestamp linkage lives on the execution bridge,
which has no declared discipline, and pinning `ts_{i+1} = ts_i + 3` is provably not
equivalence-preserving (entry 14's countermodel: a satisfying assignment exists in which a
later instruction's register write is consumed by an *earlier* receive), and (ii) the pc
lookup is modeled as never-violating, so opcode/flag/immediate knowledge that powdr reads
off the program table (load/store `flags`, `is_load`) is underivable. Both would need
spec-level decisions (like entry 17's audited memory declaration, e.g. declaring the
execution bridge as a `MemoryBusShape` with empty address — deliberately not done here).
**Impact: case 2 effectiveness 1.94 → 2.35, case 4 baseline 1.95; snapshot unchanged
(36/11).**

### 22. Joint domain enumeration + wider fact domains (`DomainBatch.lean`)
Two upgrades found by diffing residual variable classes against powdr's outputs (apc_033:
shift-heavy block, powdr 7.85× vs leanr 1.76×). (a) **Joint enumeration**: single-constraint
enumeration cannot resolve coupled systems like one-hot selectors — the booleanity
constraints, the sum residue, and the weighted-sum residue only force the flags *together*.
`forcedOver` now enumerates a target's domain box against **all** constraints and bus
obligations whose variables lie inside the target's variable set (`coveredCs`/`coveredBis`),
and collects *every* variable the survivors agree on; the checked certificate
(`checkForcedM`) and its soundness proof generalize the per-constraint versions.
(b) `maxDomainBound` 4096 → 65536: a `2^16`/`2^14` range fact now yields a usable domain, so
after Gauss eliminates one digit of a base-`2^16` decomposition (`to_pc_limbs`, `pc_limbs`),
probing the *rewritten* range lookup pins the other digit. Cost control (first attempt was
6–50× slower): targets deduplicated by variable set, *uninformative* targets skipped (a box
constrained only by the raw range checks that produced its domains can never force
anything), and a work cap `boxSize × #covered ≤ 2^19`.
Worked: yes. apc_033: 588 → 436 vars (1.76× → 2.38×; all 104 shift markers/carries pinned),
case 1: 284 → 274, case 19: 950 → 934; runtimes back at or below the pre-change level
(case 19: 3.6 s). Snapshot unchanged (36/11). **Impact: shift-heavy cases gain ~0.3–0.6×
effectiveness; full-sweep aggregate re-measured next.**

### 23. Full-benchmark measurement (top-100 openvm-eth set)
Complete sweep at default settings (`leanr run`, 32 stable-iterated cycles), all 100 cases,
~22 minutes total, slowest single case 159 s (apc_095, 7202 vars):

- **leanr: 150323 → 88195 variables, aggregate effectiveness 1.704× (geometric mean of
  per-case ratios 1.773×).** Session start was ≈1.15× on case 1 and structurally unable to
  finish the 5000-var cases.
- powdr on the same inputs: 150323 → 34766 (4.324× aggregate, 3.943× geomean).
- Per-case highlights: case 1 511→274 (1.86×), case 2 134→57 (2.35×), apc_033 1036→436
  (2.38×), largest case apc_034 9563→5230 (1.83×). No case regressed; the optimizer never
  grew a circuit.

The remaining leanr-vs-powdr gap is dominated by knowledge the frozen spec deliberately does
not license (all analyzed before changing anything, see entries 14/15/21): (i) the execution
bridge carries the `pc`/`timestamp` chaining between instructions, but has no declared
discipline, and pinning `ts_{i+1} = ts_i + 3` is provably not equivalence-preserving under
`sideEffects`-equality (explicit countermodel); this blocks *cross-instruction* memory
chaining — the bulk of powdr's `b := earlier a` eliminations; (ii) the pc lookup is modeled
as a never-violating bus, so program-table knowledge (load/store `flags`, `is_load`,
non-pinned immediates) is underivable, while powdr reads the concrete program; (iii) powdr
additionally performs optimistic eliminations (serialized `optimistic_constraints`) that are
not equivalence-preserving in any static sense. Unlocking (i)/(ii) would need audited
spec-level declarations in the style of entry 17 (e.g. declaring the execution bridge as an
address-free `MemoryBusShape`, and structured table metadata for the pc lookup) — both are
one-declaration extensions of existing, already-consumed machinery, deliberately left as
spec decisions.

### 24. Correction to entries 21/23: the pc lookup is not a wall (no commit yet)
Investigating Georg's question about the generator-added pins showed the "pc-lookup
opacity" attribution in entries 21/23 was wrong. The exports contain constraints pinning
*every* pc-lookup field, including the opcode expression (powdr's
`symbolic_machine_generator` adds them); the load/store `flags` that survive are *runtime*
witnesses — the opcode pin leaves exactly four valid flag encodings (the load's shift
amount, a function of the accessed address), and powdr keeps them too (512 on case 5,
identical to our output). `is_load`, which the constraints do force, has been eliminated
since entry 22's joint enumeration (the earlier diagnosis cited a stale render). So the
remaining leanr-vs-powdr gap reduces to essentially **one** spec decision: the
execution-bridge discipline (cross-instruction chaining — e.g. case 5 keeps 520 `rsN_data`
vs powdr's 8). Proposal left uncommitted for review in `SPEC-PROPOSAL-chaining.md`; the
pc-lookup-table idea is withdrawn there with the evidence.

### 25. Spec extension (Georg-approved): execution-bridge discipline + timestamp uniqueness
Implements `SPEC-PROPOSAL-chaining.md` after review. (a) `MemoryBusShape.disciplineOn` gains
a fourth conjunct (stated as two clauses): two active sends — dually, two active receives —
to the same address with the same timestamp *value* carry the same payload. This is the
same global-uniqueness assumption clause 1 already relies on, stated send-to-send; for the
memory bus the audit story is unchanged (offline checking gives per-address timestamp
uniqueness). (b) `openVmBusSemantics.memoryBus` now also declares the **execution bridge**
as a linear-consumption instance of the shape: payload `[pc, timestamp]`, *empty* address
(one global cell — the execution state), `tsBound 2^29`. Audited assumption documented at
the declaration: each `(pc, ts)` state is produced/consumed exactly once, at most one
instruction starts per timestamp, and the fragment runs in an exclusive contiguous
timestamp window. Proof threading: `memoryDiscipline_filterBus_zero` (Rewrite.lean) handles
the new clauses with the same active/sub-list machinery; the substitution/mapExpr transfer
lemmas rewrite the message list wholesale and needed no change; the two memory-unify
soundness proofs only destructure two more conjuncts. No optimizer behavior change yet
(`checkMemMatchG` needs constant timestamp gaps, which the bridge never has — the consuming
pass is the next entry). Snapshot unchanged (36/11); full build green.

### 26. Execution-chain unification (`ExecChain.lean`) — the cross-instruction unlock
The consumer of entry 25's declaration. `MemoryUnifyBatch`'s certificate needs a constant
timestamp gap between two sends, which execution-bridge sends never have (the gaps are the
unknowns). New **anchored-maximum** certificate instead: an *anchor* send whose payload is
refuted against every possible receive (three never-zero routes per slot: difference
normalizes to a nonzero constant; the `linNeverZero` bounded-negative certificate; capped
enumeration over `DomainTable` domains — the last handles branch targets like
`pc + cmp·imm + (1−cmp)·4` with boolean `cmp`) has no in-fragment consumer, so by the
in-window clause nothing lies strictly above it: it is the timestamp maximum. Any other send
whose payload is refuted against the anchor's sits *strictly* below it (timestamp-uniqueness
clause), so — taking the least send above it via `Nat.sInf` — the in-window clause hands it
an in-fragment consumer, identified among receives by payload refutation. The entailed
payload equalities are `pc_{k+1} = pc_k + 4` and `ts_{k+1} = ts_k + kₖ`; Gauss substitutes
them, and from the next cycle on every memory-bus timestamp is a constant offset of `ts_0`,
so the existing memory unification chains registers **across instructions**. Self-targeting
loop blocks have no certifiable anchor and are soundly left alone.
Worked: yes, dramatically. Case 2: 57 → 42 vars (2.35× → **3.19×**; powdr 3.72×), case 1:
274 → 172 (1.86× → **2.97×**; powdr 3.87×), case 3: 76 → 74 (heap chaining needs
expression-equality addresses, next entry). Snapshot unchanged (36/11). Runtime fine
(case 1: 10 s at default iters).

### 27. Syntactic address equality in memory unification
`addrConstsEq` now also accepts an address slot where both payloads carry the *same
expression* (syntactic equality ⇒ evaluated equality) — non-constant heap pointers
(`mem_ptr_limbs` sums) can then pair, with in-between exclusion falling back to
`notBetweenTs`, which works post-entry-26 because all memory timestamps are constant
offsets of `ts_0`. Sound and free; fires on blocks that access one heap address twice
(store-then-load). No change on cases 1/3/4 (their heap addresses are all distinct);
case 12: 464 → 433 (from entry 26's chaining). Also recorded here: entry 26 does **not**
fire on blocks ending in an *indirect* jump (`ret`/JALR — e.g. case 5): the unknown target
admits a satisfying "glued execution" assignment (the block re-entered at its own start
within the window) that breaks any single chosen link while satisfying every order-free
clause — verified against several candidate clause strengthenings (strict send
distinctness, matched-but-one, dual receive-side consumption). The only fix found is an
*order-dependent* audited clause (interactions in program order carry non-decreasing
timestamps — what powdr assumes de facto); left as a spec question.

### 28. Witness re-encoding (`Reencode.lean`) — Georg's hint, a new optimization class
All previous passes eliminate variables whose values are *entailed*; this one compresses
variables that are genuine witnesses but *inefficiently encoded*. If the constraints covered
by a small variable group (2–8 variables, all constraints whose variables lie inside it)
restrict the group to `m ≥ 2` joint values over its constraint-derived domains, the group is
replaced by `⌈log₂ m⌉` fresh boolean variables: each original variable is substituted by an
interpolation polynomial over the bits, the covered constraints are dropped (every bit
pattern maps into the valid set — padding repeats the first survivor), and booleanity
constraints are added. This handles exactly what powdr does not (per Georg): OpenVM's
load/store `flags` (4 variables, 4 runtime shift encodings → 2 bits) and runtime one-hot
selectors (width `w` → `⌈log₂ w⌉` bits).
Correctness is a new transport core, `reencode_correct`: witnesses do not extend each other
in either direction, so the proof transports satisfying assignments both ways under
*expression-wise evaluation equality* (which carries constraints, bus obligations, side
effects, and the memory discipline all at once). The instantiation's certificates are
index-free and decidable: survivors enumerated over `groupDoms` (constraint roots), bit
patterns over `{0,1}` boxes, plus completeness ("every survivor is hit by some pattern"),
image-soundness ("every pattern's image satisfies the dropped constraints"), freshness (no
bit occurs in the system), and bit-only interpolation ranges. Prime `p` only (booleanity
needs an integral domain). `Expression.hasVar`/`varsIn` keep the per-cycle coverage scan
allocation-free.
Worked: yes. Case 3: 74 → 70 (the 8 load flags → 4 bits — **below powdr's 54-var output on
that class**, powdr keeps all 8); case 5: 3786 → 3530 (−256: 512 flags → 256 bits, 54 s);
case 1: 172 → 169 (shift markers). Snapshot unchanged (36/11).

### 29. Whole-chain unification + memoized bounds (`ChainUnify.lean`, `BoundsMap`)
Two fixes for the unrolled-loop cases (case 7: 140 accesses to one register — entry 27's
pair-per-cycle resolution needed one full pipeline cycle per link and timed out).
(a) **`BoundsMap`**: the refutation certificates derived variable bounds via `findVarBound`,
a full interaction scan *per query*; the chain passes issue millions of queries per cycle.
The bounds are now precomputed once per pass invocation into a proof-carrying hash map, and
`boundedSumMax`/`linNeverZero`/`tsRefuted`/`exprNeverZeroBounded` take the map plus a
lookup-soundness hypothesis (threaded from `BoundsMap.sound`). (b) **`ChainUnify.lean`**:
certifies an *entire* same-address chain in one invocation. Sends are processed top-down
(sorted by constant timestamp offsets); each link's receive is identified by refuting all
others — receives below by the never-zero timestamp difference as before, and receives
already claimed *above* via the accumulated payload equality plus the constant in-range gap
between their send and the current one (equal payloads would force equal timestamp values —
the descending induction carries the claims as an accumulator, `checkChainRev_sound`). Link
adjacency reuses `sendExcluded` unchanged. The pair pass stays in the cycle after the chain
pass as a mop-up for links below a truncated ambiguity (removing it regressed case 1
169 → 223), with its receive search pre-filtered by the memoized refutation.
Worked: yes. Case 7: **timeout (>30 min) → 5464 → 2171 vars (2.52×) in 4.4 min**; case 1
unchanged at 169 (9.9 s), case 2 at 42, case 5 at 1765 (50 s). Snapshot unchanged (36/11).

### 30. Spec extension (Georg-requested): degree bounds
`Spec.lean` gains `DegreeBound` (`identities`, `busInteractions`), `Expression.degree`
(const 0 / var 1 / add max / mul sum), `ConstraintSystem.withinDegree` (+ decidable twin and
equivalence lemma), and the new top-level property `optimizerRespectsDegree`: an optimizer
never pushes a within-bound circuit past the zkVM's bound. `BusSemantics` carries the bound;
OpenVM sets powdr's `DEFAULT_DEGREE_BOUND` = `{identities := 3, busInteractions := 2}`.
Enforcement is compositional with zero per-pass proof burden: `VerifiedPassW.guardDegree`
wraps every pipeline pass (checked output, fall back to the unchanged input), `RespectsDeg`
propagates through `andThen`/`iterate`/`iterateStable`, and `optimizer_respectsDegree` /
`optimizerWith_respectsDegree` are projections. `reencodeStep` additionally guards per
group, so one violating group doesn't discard the others. The CLI prints an input/output
degree verdict. Measured: all benchmark inputs are within the bound, all outputs remain so;
the only optimization the guard actually bites is entry 28's re-encoding (interpolation
polynomials have degree = bit count, and composing them into degree-2 payload slots or
degree-3 constraints overshoots): case 3 loses its 4-bit flags win (70 → 74), case 1 3 vars
(169 → 172), case 5 its −256. Recovering those legally needs interpolation at the *maximal
wholly-in-group subexpression* level (a function of k bits is multilinear of degree ≤ k) —
next entry.

### 31. Degree-aware subexpression interpolation (`groupRewrite`)
Recovers entry 28's wins under the new degree bound, and more. Instead of substituting the
interpolation polynomials variable-by-variable (whose degree composes with the surrounding
expression), the re-encoding now replaces every **maximal wholly-in-group subexpression** by
its own interpolation over the bit patterns — any function of `k` bits is multilinear of
degree ≤ `k`, so a degree-2 flag polynomial inside a degree-2 payload slot becomes a
degree-2 bit expression instead of a degree-4 composition. The rewrite is *self-checking*:
the folded candidate is accepted only if its variables lie in the bits and it agrees with
the plain substitution on **every** bit pattern (a decidable exhaustive check inside the
definition, consumed by `groupRewriteCand_agree` by case-splitting the definition — no
external certificate); otherwise it falls back to plain substitution and the step-level
degree guard decides. The transport core was generalized from `substF` to an arbitrary
expression rewrite (`reencode_correct` now takes `rw` with the same two agreement
hypotheses), which `groupRewrite_agree`/`groupRewrite_bi_agree` instantiate.
Worked: better than before the bound existed — the whole-subexpression interpolations are
also *smaller*: case 3: 108 → 64 (was 70 pre-degree; powdr: 54 and keeps all 8 flags where
we keep 4 bits), case 1: 511 → 167 (3.06×), case 5: 5406 → 3338 (was 3530). All outputs
verified within `{identities := 3, busInteractions := 2}`.

### 32. Full sweep at degree-bound state; JALR/order-freedom is the dominant remaining gap
Full 100-case sweep at the degree-aware commit: **leanr 150323 → 59241 vars = 2.537×
aggregate (2.667 geomean)**, all outputs within `{identities := 3, busInteractions := 2}`;
powdr 4.324×. (Session start was 1.15× on case 1 with the 5000-var cases unreachable.)

Root-caused the remaining gap by class-diffing the largest laggards (apc_012/031/033/041)
against powdr. It is **one lever**: `from_state__timestamp` survives ~once per instruction
(apc_012: 21 vs powdr's 1). Every other large residual class — `rsN_data`, `read_data`,
`prev_data`, and all the `_timestamp_lt_aux__lower_decomp` / `_prev_timestamp` limbs — is
*downstream* of it: register/heap chaining across instructions needs a **constant** timestamp
gap between the two accesses, which requires the execution-bridge timestamps chained to
`ts_0 + const` first. Diagnosis of why exec-chaining doesn't fire: the block's terminal
instruction is a control-flow op (jump/branch) whose send targets a **symbolic** pc
(`2·to_pc_limbs_0 + 65536·to_pc_limbs_1`). `ExecChain`'s anchored-maximum certificate needs
one send whose payload differs from every receive; the symbolic-target send cannot be proven
`≠` the in-block receive pcs, so there is **no anchor**, and the entire chain fails — even
though the other 20 links are clean straight-line pc-adjacent sends. Since essentially every
real basic block ends in a control-flow instruction, this blocks timestamp chaining on the
majority of cases.

This is **not** fixable under the frozen spec: `MemoryBusShape.disciplineOn` is deliberately
*order-free* (entry 17: "a fragment listing its accesses out of time order can only cost
optimizations, never correctness"), so nothing lets the pass treat the terminal send as the
timestamp maximum. powdr collapses these timestamps because it assumes **program-order
timestamp monotonicity** (interactions listed in execution order, timestamps non-decreasing)
— a de-facto property of the APC generator, but an *additional audited assumption* that would
reverse Georg's explicit order-freedom choice. **This is a spec-level decision for Georg**
(see the report): granting it (e.g. a `MemoryBusShape` flag "sends are listed in
non-decreasing timestamp order", making the last active send the maximum) would let
`ExecChain`/`ChainUnify` collapse the timestamps and cascade into register/heap/limb
chaining — projected to close most of the 2.54×→4.32× gap. Deliberately not implemented
unilaterally.

### 33. Digit-uniqueness equality pass (`DigitEq.lean`) — proven, general, not wired
Built the bounded-decomposition-matching pass hypothesized to unlock heap-address chaining:
a linear constraint whose normalized terms pair as `Σᵢ magᵢ·(xᵢ − yᵢ) = 0` with all
variables fact-bounded and the magnitudes dominating the lower partial sums entails `xᵢ = yᵢ`
pairwise (the top-digit argument, carried out over ℕ with a `ZMod.val` bridge; fully proven,
`digitCheck_sound`). Sound and VM-general. Measured impact on the sampled OpenVM cases
(12/33/41): **none** — the two accesses' pointer-limb decompositions are not linked by such a
constraint in these circuits (the heap-chaining blocker is the timestamp/JALR issue above,
not decomposition matching). Kept in the tree (imported by `Leanr.lean`, so `lake build`
verifies it) but **not** in the pipeline, since it fires on no benchmark case and would only
add per-cycle cost. Available if a VM emits the matching constraint shape.

### 34. Program-order timestamp monotonicity — spec clause added (Georg-approved)
Added clause 5 to `MemoryBusShape.disciplineOn`: active messages on a declared bus are listed
in non-decreasing timestamp order (`msgs.Pairwise (fun a b => a.mult ≠ 0 → b.mult ≠ 0 →
tsVal a ≤ tsVal b)`). This is the audited assumption from `SPEC-PROPOSAL-order-monotonicity.md`
— powdr's de-facto ordering, and (per the concrete `EXEC` walk-through with Georg) exactly
what rules out the phantom out-of-time-order countermodel that currently forces leanr to keep
`t2` when a block ends in a computed jump. It **reverses** the entry-17 order-freedom choice
for the optimizations it enables, hence Georg's explicit sign-off.
Threading: the substitution / `mapExpr` discipline-transfer lemmas rewrite the whole evaluated
message list, so the new clause transfers for free; zero-multiplicity bus removal needed a new
`List.pairwise_of_filter_pairwise` (dropped messages have multiplicity 0, so any pair touching
one is vacuously ordered — both un-filter and re-filter directions). The four unify passes
destructure the clause as `cmono` but don't yet consume it. **No behavior change: snapshot
byte-identical (36/11), `SnapshotCorrect` re-proven, both `optimizer_maintainsCorrectness` and
`optimizer_respectsDegree` still `{propext, Classical.choice, Quot.sound}`-only.**

Consumption (next, pending Georg's spec review + a design discussion): `ExecChain` should pick
the **last active send in list order** as its anchor (the timestamp maximum, by clause 5) in
place of the current payload-refutation anchor — this is what unblocks the symbolic-jump case.
The proof route is clean: split the bus list `L = pre ++ anchor :: post` with `post` all
provably-not-active-sends (`notSend`), then `List.pairwise_append` on the monotonicity clause
gives `tsVal (S.eval) ≤ tsVal (anchor.eval)` for every active send `S` before the anchor, and
the `post` elements can't be active sends — so the anchor is the maximum with no proof about
its symbolic pc. Open design points for the discussion: whether to require all bus mults
constant (simplest) or handle symbolic multiplicities, and whether the anchor rule lives in
`checkExecChain` (replacing the payload-refutation clause, more general) or as an added path.
