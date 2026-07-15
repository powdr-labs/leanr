# Optimizer improvement log

Append-only history of optimizer changes. Each entry records the idea, whether it worked, and its
impact on effectiveness (distinct variables before / after; higher is better). **Earlier entries
describe designs and files that have since been superseded** — for the current architecture see
[`design/architecture.md`](design/architecture.md); for recent work read the last few entries
(e.g. `tail -100 docs/log.md`).

Every commit keeps `lake build` green and `optimizer_maintainsCorrectness` proven with no
`sorry`/`admit`/`axiom`/`native_decide` (enforced by CI), leaving the audited spec and bus
semantics untouched.

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
The focus shifts from the snapshot to the real benchmark set (`ApcOptimizer/OpenVm/Benchmark/`,
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
unchanged — diagnosis (via `apc-optimizer vars`): their remaining gap vs powdr is dominated by two
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
shift-heavy block, powdr 7.85× vs apc-optimizer 1.76×). (a) **Joint enumeration**: single-constraint
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
Complete sweep at default settings (`apc-optimizer run`, 32 stable-iterated cycles), all 100 cases,
~22 minutes total, slowest single case 159 s (apc_095, 7202 vars):

- **apc-optimizer: 150323 → 88195 variables, aggregate effectiveness 1.704× (geometric mean of
  per-case ratios 1.773×).** Session start was ≈1.15× on case 1 and structurally unable to
  finish the 5000-var cases.
- powdr on the same inputs: 150323 → 34766 (4.324× aggregate, 3.943× geomean).
- Per-case highlights: case 1 511→274 (1.86×), case 2 134→57 (2.35×), apc_033 1036→436
  (2.38×), largest case apc_034 9563→5230 (1.83×). No case regressed; the optimizer never
  grew a circuit.

The remaining apc-optimizer-vs-powdr gap is dominated by knowledge the frozen spec deliberately does
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
remaining apc-optimizer-vs-powdr gap reduces to essentially **one** spec decision: the
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
Full 100-case sweep at the degree-aware commit: **apc-optimizer 150323 → 59241 vars = 2.537×
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
not decomposition matching). Kept in the tree (imported by `ApcOptimizer.lean`, so `lake build`
verifies it) but **not** in the pipeline, since it fires on no benchmark case and would only
add per-cycle cost. Available if a VM emits the matching constraint shape.

### 34. Program-order timestamp monotonicity — spec clause added (Georg-approved)
Added clause 5 to `MemoryBusShape.disciplineOn`: active messages on a declared bus are listed
in non-decreasing timestamp order (`msgs.Pairwise (fun a b => a.mult ≠ 0 → b.mult ≠ 0 →
tsVal a ≤ tsVal b)`). This is the audited assumption from `SPEC-PROPOSAL-order-monotonicity.md`
— powdr's de-facto ordering, and (per the concrete `EXEC` walk-through with Georg) exactly
what rules out the phantom out-of-time-order countermodel that currently forces apc-optimizer to keep
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

### 35. ExecChain consumes the monotonicity clause — cross-instruction chaining unblocked
`ExecChain` now anchors via clause 5 instead of payload-refutation. For each send `S`, it
uses the **next payload-different send `W` after `S` in list order** as a witness: the
monotonicity clause gives `tsVal S ≤ tsVal W` (list order = time order), and `payloadNeq W S`
+ the uniqueness clause make it strict, so `S` is not the timestamp maximum and the in-window
clause hands it an in-fragment consumer (identified as `Rt`). This needs no fact about the
block's terminal send, so a computed-jump terminal no longer blocks the chain — every send
except the last constant-pc one (whose only later send is the symbolic terminal) chains.
`checkExecChain` takes the split `L = pre ++ S :: post` (checked by `decide`) with `W ∈ post`;
`tsMax_of_split` was replaced by the direct `pairwise_append`/`pairwise_cons` extraction.
Worked: yes. apc_012 (was blocked, 21 surviving `from_state__timestamp`): **852 → 290 vars,
now only 2 timestamps survive** (`ts_0` and the post-terminal `ts_20`); the register/heap
data and decomposition limbs riding on the timestamps collapse with them. Cases 1/2 unchanged
(already handled / single-instruction). Snapshot byte-identical (36/11), `SnapshotCorrect`
re-proven, both correctness theorems still 3-axiom, all outputs within the degree bound.

### 36. Memory pair-unification consumes the monotonicity clause (after-successor exclusion)
`memoryUnifyBatchPass` identifies a send `S`'s consumer receive by refuting every other
interaction, previously only via multiplicity / constant-timestamp-difference / address
(`notMatchG`). On a block that ends in a **computed jump** (JALR), the terminal instruction
re-reads a register at a timestamp on a *separate, un-chained* `from_state` (the exec chain
can't link it — its send targets a symbolic pc). That later read has a timestamp with no
constant difference from `S`, so it could not be refuted, leaving *two* candidate receives for
the same send → the pair match was abandoned and the whole register/data chain stalled (this
is why apc_003/015/019 lagged: the `rs1_data`/`read_data`/`prev_data`/`lower_decomp` limbs of
every register never collapsed).

Fix: consume the discipline's **program-order monotonicity clause** (clause 5, added in entry
34, until now unused by the unify passes). `checkMemMatchG` now takes the split
`L = preS' ++ S' :: postS'` around the successor send `S'`; any receive listed in `postS'` is
refuted because monotonicity gives it `tsVal ≥ tsVal S' > tsVal S`, whereas the consumer
carries `S`'s timestamp — so it cannot lie after `S'`. Proof: `List.pairwise_append`/
`pairwise_cons` on the evaluated split (mirroring `ExecChain`'s extraction) plus
`tsVal (bi.eval) = tsVal (S.eval)` from the consumer's payload equality; `omega` closes it.
Search-side threads the split and pre-filters candidates by `r ∉ postS'`. Only *adds* a
refutation route, so it never drops a previously-found match.
Worked: yes, no regressions. apc_019 153→129 (1.79→2.12×), apc_003 138→126 (1.86→2.04×),
apc_015 205→169 (1.83→2.22×), apc_008 265→193 (2.03→2.79×); others unchanged. Snapshot
byte-identical (36/11), `SnapshotCorrect` re-proven, both correctness theorems still
`{propext, Classical.choice, Quot.sound}`-only, all outputs within the degree bound.

**Aggregate (tracked keccak top-20 set, 19 cases excl. the 27521-var apc_001 megacase which
doesn't converge in reasonable wall-clock at `--iters 32` in either version):** aggregate
effectiveness (Σvars_before / Σvars_after) **3.48× → 3.61×**, geomean **2.95× → 3.07×**. Gains
concentrated in the register-heavy blocks that end in a computed jump (apc_008 2.03→2.79×,
apc_015 1.83→2.22×, apc_019 1.79→2.12×, apc_003 1.86→2.04×); every other case byte-identical.
The dominant *remaining* residual on these is the timestamp-difference **high limb**
(`…_lt_aux__lower_decomp__1`): it has no algebraic constraint (only a range-check bus slot + a
memory-ts arg), so Gauss can't touch it, and the pivot heuristics that would keep the
timestamp slot to let the limb fold also (unavoidably) block the beneficial `from_state`
collapse — the two are coupled through the same constraints (tried, reverted). powdr eliminates
these by solving the less-than gadget for the limb instead of the timestamp; matching that
without regressing timestamp collapse is the next lever.

### 37. Re-encode emits a constant when the interpolated value is pattern-independent
Root-caused the residual register/data gap (apc-optimizer keeps per-instruction copies of `a_`/`b_`/
`rs1_data`/`read_data` that powdr forwards across instructions). The blocker was **self-
inflicted**: the re-encoding pass (`Reencode.interpOf`) replaces a maximal in-group
subexpression by its one-hot interpolation `Σ indicator(β)·value(β)` over the flag bit
patterns. When that subexpression is a **register index that doesn't depend on the flags**
(e.g. `52` for every opcode), the interpolation is `Σ indicator·52` — semantically `52`, but
syntactically a degree-2 expression in the fresh `rnc` bits. `MemoryUnify`'s `addrConstsEq`
then no longer sees a constant address, so those register accesses stop matching each other
(and differ syntactically across instructions, each with its own `rnc` group) — the whole
register chain fails to form.

Fix: `interpOf` now checks whether the subexpression takes the **same value on every bit
pattern** and, if so, emits that bare constant instead of the one-hot polynomial. This keeps
constant addresses literally constant (chaining resumes) and lowers degree. It's transparent
to the correctness proof: `groupRewriteCand` only consumes `interpOf` through its
`varsIn bits` + agrees-on-every-pattern check, and a constant passes both (no variables;
equals the shared value everywhere) — so `groupRewriteCand_agree` is unchanged and
`reencode_correct` still holds.
Worked: large, no regressions. **aggregate 3.61× → 3.76×, geomean 3.07× → 3.28×** on the
tracked 19-case set. apc_003 126→84 (3.06×, vs powdr 3.10× — essentially matched),
apc_015 169→115 (3.27×), apc_019 129→93, apc_008 193→175; all others byte-identical. Snapshot
still 36/11 (`SnapshotCorrect` re-proven), both correctness theorems still
`{propext, Classical.choice, Quot.sound}`-only, all outputs within the degree bound.

Cumulative this session: **3.48× → 3.76× aggregate, 2.95× → 3.28× geomean** (entries 36–37).

### 38. Spec restructure (Georg-approved): completeness-gating instead of discipline-in-`satisfies`
Reworked the correctness spec so it reads honestly and stays minimal, without weakening any
result. Previously the whole memory/exec discipline was a conjunct of `satisfies`, so both
directions of the symmetric `equivalentTo` carried it. First-principles reframe (Georg): these
passes only ever *remove* witnesses (`t2 := t1+3`), so **soundness** (output ⟹ input) is never
at risk and needs no discipline; only **completeness** (input ⟹ output) is, and only for the
prover's *intended* (real-trace) executions — for spurious witnesses (a fragment proving a
non-consecutive cycle) completeness legitimately fails and we don't care. That the intended
trace is additionally *forced* for memory (offline memory checking, Blum et al.) is real but
out of scope to verify.

Spec changes (`Spec.lean`): `satisfies` is now minimal (algebraic + bus obligations); the old
`memoryDiscipline` conjunct became a standalone `ConstraintSystem.isIntended` (same
`disciplineOn` body). New `impliesIntended` = `implies` gated on `self.isIntended`, and it
*delivers* an intended witness (`other.isIntended env'`) so it composes. `equivalentTo` →
`refines self other := self.implies other ∧ other.impliesIntended self` — deliberately
asymmetric (no `refines_symm`). `optimizerMaintainsCorrectness`/`PassCorrect` now use `refines`.

Plumbing: `Basic.lean` glue is `impliesIntended_{refl,trans}` + `refines_{refl,trans}`
(dropped `equivalentTo_symm`). Each transfer core split its `satisfies_X` biconditional
(discipline dropped → minimal) from a renamed `isIntended_X`, and each `_correct` proves
`refines` (soundness via minimal `implies`; completeness re-establishes `isIntended` on the
output). Net effect on proofs: discipline now transfers through **one** direction instead of
both, and the soundness transfer lemmas drop it entirely. `addConstraints_correct`'s entailment
hypothesis gained `cs.isIntended` (the discipline is now an explicit completeness-only input);
the four consumer sound-lemmas (`checkMemMatch`, `checkMemMatchG`, `checkExecChain`,
`checkChainRev`/`checkMemChainG`) take `isIntended` in place of destructuring it out of
`satisfies`.

Worked: whole library builds. **No behavior change** — the optimizer function is untouched, so
the snapshot is byte-identical (36/11), `SnapshotCorrect` re-proven (renamed
`addiOptimized_refinesInput`), and `optimizer_maintainsCorrectness`, `optimizer_respectsDegree`,
and the snapshot theorem are all still `{propext, Classical.choice, Quot.sound}`-only. This is
the spec shape intended for `main`.

### 39. Spec made VM-agnostic: abstract `admissible` predicate (Georg-requested "simplify directly")
Follow-up to entry 38. Georg's goal: the audited spec should be small and VM-agnostic, carrying
the memory knowledge as one *abstract* predicate rather than the enshrined `MemoryBusShape`/
`disciplineOn`. Chosen scope: "simplify directly" — the VM predicate is the simple
consecutive-match statement, name `admissible`.

**Spec (`Spec.lean`), now VM-agnostic:** removed `MemoryBusShape`/`disciplineOn`/`address`/`tsVal`/
`memoryBus`. `BusSemantics` gains `admissible : List (BusInteraction (ZMod p)) → Prop`;
`ConstraintSystem.admissible` = `bs.admissible` of the messages pre-filtered to **active∧stateful**
(the pre-filter is what makes every transfer lemma generic). `isIntended→admissible`,
`impliesIntended→impliesAdmissible`; `refines` unchanged in shape.

**New `ApcOptimizer/MemoryBus.lean`:** the concrete last-write-wins discipline (shared, not in the spec):
`MemoryBusShape := {addressFields}`, `admissibleBus` = *consecutive same-address send→receive
pairs match* (split form), and `admissibleBus.consecutive` — the consumption helper that lifts a
raw per-bus split to the active sublist. Timestamps are gone from the predicate entirely.

**Plumbing:** transfer lemmas collapsed to generics (`admissible_subst`/`substF`/`mapExpr`, and one
`admissible_filterBus` replacing both the zero-mult and stateless-drop lemmas — the whole 6-clause
`isIntended_filterBus_zero` and the `memoryBus`-based TautoBus lemma deleted). `BusFacts` gains
`memShape`/`memShape_stateful`/`admissible_sound` (OpenVM proves them; `admissible_sound` is
definitional). `OpenVM/Semantics` `memShapeOf` + concrete `admissible`; `OpenVM/Facts`
`openVm_isStateful_of_memShape`. `addConstraints_correct`'s entailment now takes `cs.admissible`.

**Status: build GREEN, but the 4 memory/exec consuming passes are TEMPORARILY STUBBED to
identity** (`MemoryUnifyBatch`/`ExecChain`/`ChainUnify`; the entry-18 reference `memoryUnifyPass`
and its timestamp-refutation machinery were removed from `MemoryUnify`, which is now shared
helpers only). So memory/exec unification is off: **snapshot 36/17 (was 36/11)**, effectiveness
reduced until the passes are rewritten to positional matching via `admissibleBus.consecutive`.
`optimizer_maintainsCorrectness`, `optimizer_respectsDegree`, `addiOptimized_refinesInput` all still
`{propext, Classical.choice, Quot.sound}`-only. Committed as a WIP savepoint; the positional
rewrites (turnkey plan in `~/.claude/plans/`) are the next step and restore 36/11+.

### 40. One unified `busUnifyPass` replaces the three unify passes (spec simplification → pass simplification)
Consequence of entry 39's uniform `admissibleBus` predicate (Georg: "check whether it can be done
in one pass"). The three former passes — `memoryUnifyBatchPass` (memory pairs), `execChainPass`
(exec bridge), `chainUnifyPass` (whole chains) — were all doing the *same* thing under the new
predicate: pair each active send with the next active same-address receive and emit the slot
equalities. They collapse into a single `ApcOptimizer/OptimizerPasses/BusUnify.lean`:

- `admissibleBus.consecutive` (in `MemoryBus.lean`) turns a raw per-bus split `pre ++ S :: mid ++
  R :: post` (S a send, R a receive, same address, no active same-address message in `mid`) into
  `S.payload = R.payload`, lifting to the active sublist internally.
- `checkPair` certifies a candidate positionally: constant send/receive multiplicities,
  `addrConstsEq S R`, and every `mid` message provably inactive (`multConst = 0`) or
  different-address (`addrConstsNeq`, re-added with soundness). `consecutivePayloadEq` bridges
  `cs.admissible` → `admissibleBus` via `facts.admissible_sound` (+ a `map_eval_filter_busId`
  commute). `checkPair_sound` → `memEqConstraints` eval to 0.
- The pass enumerates candidate splits per declared bus, collects, and adds via
  `addConstraints_correct`. Gated on `(1:ZMod p) ≠ 0` (identity otherwise).

The empty-address execution bridge is just the special case (consecutive pairs are list-adjacent),
so it needs no anchored-maximum and a **symbolic terminal jump no longer blocks the straight-line
links** — the unified pass is anchor-free by construction, so it should match or beat the old
`ExecChain` on computed-jump blocks (full top-100 re-measurement pending).

`MemoryUnify.lean` reduced to shared helpers; `MemoryUnifyBatch`/`ExecChain`/`ChainUnify` deleted;
`DigitEq` re-pointed to `MemoryUnify`. Worked: **snapshot byte-identical (36/11)** — the single
pass reproduces the old three-pass output exactly on the ADD case. Full `lake build` green;
`optimizer_maintainsCorrectness`, `optimizer_respectsDegree`, `addiOptimized_refinesInput` all
still `{propext, Classical.choice, Quot.sound}`-only. Net: the spec refactor (entries 38–39) and
this pass unification remove ~1500 lines while preserving effectiveness and the 3-axiom proof.

### 41. Full top-100 sweep after the unification refactor — near-parity with powdr
Full 100-case openvm-eth sweep (same set as entry 32), apc-optimizer vs powdr's serialized output:

- **apc-optimizer: 150323 → 36233 vars = 4.149× aggregate (3.650× geomean)**
- **powdr: 150323 → 34766 vars = 4.324× aggregate (3.943× geomean)**
- Per-case: apc-optimizer keeps fewer vars on **13**, powdr fewer on **87**, no ties. But the aggregate gap
  is only 1467 vars (apc-optimizer 4.2% above powdr).

This is the payoff of entries 38–40: from **2.537×/2.667× (entry 32) to 4.149×/3.650×**. The
single anchor-free `busUnifyPass` (consecutive same-address match) chains cross-instruction
timestamps/pc *everywhere* — the symbolic-jump blocker that entry 32 identified as the dominant
gap is gone (a terminal computed jump just has no consecutive receive, so the straight-line links
still resolve), and that cascades into register/heap/decomposition chaining.

**Where apc-optimizer beats powdr:** the large load/store-heavy repeated blocks (the 5406-var class:
apc-optimizer 1683 vs powdr 1809, ×6 such blocks). The uniform consecutive-match chains these more
completely than powdr's `optimize_exec_bus` + memory handling.

**Where powdr still wins (the 87 small losses, typically +8…+24 vars; apc_095 7202-var: +129):**
attributable to powdr passes we don't have (`autoprecompiles/src/optimizer.rs`):
1. `inline_everything_below_degree_bound` — inlines *any* witness column expressible within the
   degree bound, not only fully-solved variables (our gauss/affine substitute only when a var is
   pinned). Likely the bulk of the long-tail var gap.
2. Disconnected/dead-column removal — a dedicated sweep for columns with no effect on constraints
   or bus interactions; we only drop such vars when substitution happens to eliminate them.
3. `rule_based_optimization` — a broader algebraic rewrite-rule library than our
   fold/normalize/monic-scale.
4. PC-lookup removal ("confirms all PC lookups removed") — reduces *bus interactions*, not vars,
   so it doesn't move our var-based metric; we keep them (never-violating model).
5. `optimistic_constraints` — eliminations justified by assumptions checked at proving time, **not
   statically sound**. powdr's headline number includes some of these; we deliberately don't (this
   is the honest-vs-optimistic gap, a spec decision, out of scope).

> *Note (added later): the claim that these benchmark exports include `optimistic_constraints` is
> unverified and, per Georg, incorrect — they are produced without the optimistic pass. The
> apc-optimizer-vs-powdr var gap is accounted for by the sound items (1)–(3) above.*

**What closing the remaining sound gap would take:** a degree-aware inlining pass (subst-like, but
inlining any below-degree-bound column, not just pinned vars) + a dead-column sweep (a `filterBus`/
constraint-filter over provably-unused witnesses). Both are sound and mechanical; together they'd
plausibly close most of the ~4% var gap. (3) is incremental rule additions. (4)/(5) are either
metric-neutral or out of scope. No spec changes needed for the sound items.

### 42. Bus-interaction and algebraic-constraint effectiveness metrics (measurement only)
Tooling, not a pass. Added two effectiveness measures alongside the existing variable one, so the
CLI and benchmark now report the shrink factor (`count before / count after`) for **variables**,
**bus interactions**, and **algebraic constraints** — for both apc-optimizer and powdr. Formalized as
`busInteractionEffectiveness` / `constraintEffectiveness` (via a shared `effectivenessBy` over a
size measure) in `ApcOptimizer/Utils/Size.lean`; surfaced in `apc-optimizer run`/`compare`, the
`OpenVmBenchmark/benchmark.py` terminal summary (agg + geomean per measure), and the HTML report.
The priority order **variables > bus interactions > constraints** is documented in `CLAUDE.md` and
the `autoopt` skill.

The new bus metric immediately makes entry 41's item (4) quantitative. On a 4-case sample: apc-optimizer
bus effectiveness **1.43× agg** vs powdr **2.52×** — powdr's PC-lookup removal (and broader
interaction cleanup) is a large, previously-invisible gap. apc-optimizer already leads on constraints
(**8.63×** vs **7.47×**). This suggests a sound, variable-neutral win is available: dropping
never-violating stateless lookups (e.g. pinned PC lookups) would raise bus effectiveness toward
powdr without regressing variables. Added to `docs/ideas.md`.

### 43. Disconnected-component removal (`disconnectedComponentPass`)
New pass `ApcOptimizer/Implementation/OptimizerPasses/DisconnectedComponent.lean`: drop a *disconnected
component* — a set of constraints and stateless interactions whose variables never reach a
**stateful** bus interaction — **provided the subcircuit is satisfiable**. Soundness must
reconstruct a full satisfying assignment of the input from one of the output, so it needs a witness
for the dropped variables; the pass tries the concrete all-zero witness and drops a component only
if that witness certifies it: every dropped constraint evaluates to `0` (`decide (c.eval 0 = 0)`)
and every dropped (stateless) interaction is non-violating (`bs.violatesConstraint (bi.eval 0) =
false`), both checked against the semantics *at run time* — the same branch-on-a-decidable-check
trick `guardDegree` uses, so it stays VM-agnostic and needs no `BusFacts`.

Correctness (`dropComponent_correct`, field-free, VM-agnostic): given the partition, a witness `w`,
and the checkable facts that every removed item is witness-satisfied, stateless, and shares no
variable with the kept part — soundness extends an output assignment by `w` on the removed variables
(valid by `eval_congr` since those variables occur nowhere else); completeness (`env' = env`) and
side-effect/`admissible` preservation follow because the removed interactions are stateless
(`sideEffects_drop_eq`, `admissible_filterBus`). Removal is **per-component** (BFS `bfsClosure`; the
co-occurrence closure of any witness-failing disconnected item is kept too, so one uncertifiable
component never blocks the others); the induced partition is re-checked, so correctness never
depends on the (`partial`) search.

Correctness axioms unchanged (`{propext, Classical.choice, Quot.sound}`); snapshot intact. Measured
on the pre-rename benchmark data (before the #48 variable-rename refactor this rebased onto): apc-optimizer
**4.016× → 4.023× aggregate**, monotonic (the pass only removes variables, so no case regresses;
~65 vars over several cases). Largest single case apc_100 (dead range-checked `bit_shift_carry`
shift-limbs): 1027 → 1003 vars. The dominant *unremoved* pattern is the orphaned register read
(data limbs in a bitwise byte-check `[K − Σ256ⁱ·limbᵢ, …]`): all-zero is not a satisfying witness
there (the affine slot is a large constant, not a byte) — left for a smarter witness finder (see
`docs/ideas.md`).

### 44. Remove the `iters` parameter: provably-terminating fixpoint cleanup loop

The optimizer no longer takes an iteration count (`iters` / `--iters` / the fixed default 32).
`cleanupCycle` is run to a fixpoint by `iterateToFixpoint` (`FactPass.lean`): it recurses while each
cycle strictly lowers the **lexicographic size key** `sizeKey = (distinct vars, bus interactions,
constraints)` — variables most significant, matching the effectiveness priority — and stops
otherwise. `sizeKey : Nat ×ₗ Nat ×ₗ Nat` is well-founded (`sizeKey_wf`, the inverse image of `<` on
the Mathlib lex product), and the recursion is guarded by exactly the strict decrease it needs, so
`decreasing_by exact h` discharges termination — no fuel, no cap a large basic block could exceed.
This mirrors the pattern the pre-rewrite `solve_pure` used (`termination_by constraints.size`), now
generalized to the lexicographic priority order. Distinct-var count uses a `HashSet` (not
`ConstraintSystem.size`'s quadratic `dedup`) to keep the per-cycle measure cheap.

Two corollaries, by strong induction on `sizeKey`: `iterateToFixpoint_respectsDeg` (degree bound
preserved) and **`iterateToFixpoint_monotone`** — the loop's output never has a larger size key than
its input, i.e. the optimizer can only shrink the circuit ("passes only improve"). Removed the
now-dead `iterateStable`; the audited correctness theorems in `ApcOptimizer/Optimizer.lean` lose their
`iters` argument (they were already `∀ iters`, so this is a one-line change).

Correctness axioms unchanged (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`.
Validated the count-based stop against the old structural no-op by tracing per-cycle
`(vars, bus, constraints)` on 10 cases: the triple is monotonically non-increasing, each non-final
cycle strictly lex-decreases, and the first non-decreasing cycle *is* the structural fixpoint — the
two stops coincide, so zero effectiveness change (outputs reproduce exactly, e.g. apc_069 28/6/22,
apc_001 42/18/38, apc_100 1003/601/1866). Also removed the `iters`/`--iters` CLI flag and updated
`benchmark.py`, the READMEs, the architecture doc, and CLAUDE.md. The FFI entry point `ApcOptimizer/Ffi.lean`
drops its now-stale `openVmOptimizer … 32 …` iters argument (the serializer's own `Variable`-struct
reconciliation landed separately on `main`).

### 45. Optimizer runtime: profile-guided speedups (effectiveness unchanged)

Pure **performance** work — the optimizer's *output* is unchanged (every change is
output-preserving, verified by re-running the whole benchmark and comparing `vars/constraints/bus`
per case: identical on all 100, e.g. apc_100 stays `1003/601/1866`), so effectiveness is identical
and only the wall-clock cost of running the optimizer drops. Nothing in the audited surface,
`Basic.lean`, or the spec changed; correctness axioms stay `{propext, Classical.choice, Quot.sound}`;
`lake build` green, no `sorry`/`native_decide`.

Profiled per-pass on the slowest cases (added a `apc-optimizer profile <file>` CLI command that times each
pass across the fixpoint loop). Three passes dominated — `domainBatch`, `reencode`, `busUnify` — and
each turned out to be paying for a *recomputation inside a loop* rather than doing irreducible work.
Fixes, each preserving the exact output:

1. **`coveredCs`/`coveredBis` allocation (`DomainBatch.lean`)** — the per-target covered-item scan used
   `c.vars.all (· ∈ xs)`, which *materializes* every constraint/interaction's variable list once per
   target. Replaced with an allocation-free `Expression.varsIn`/`BusInteraction.varsIn` (added to
   `DomainProp.lean`, shared with `Reencode`, which dropped its private copy); same boolean, so the
   filtered list — hence the output — is identical.
2. **`reencode` target dedup (`Reencode.lean`)** — the target variable-sets were deduped with the
   quadratic `List.dedup`; replaced with a linear hash-set `dedupHash` returning the identical list
   (each element kept at its last-occurrence position, exactly `List.dedup`).
3. **`domainBatch` enumeration (`forcedOver`)** — `checkForcedM` re-enumerated the domain box and
   re-ran `survivesAllM` *once per candidate variable*. Now the surviving assignments are computed
   **once** per target (`forcedFromSurvivors` + `forcedFromSurvivors_sound`) and every candidate is
   checked against that precomputed list; `forcedFromSurvivors` reproduces the old candidates exactly.
   Removed the now-dead `pickForcedM`/`checkForcedM`/`checkForcedM_sound`.
4. **recompute-in-lambda hoists (`Reencode.lean`)** — `groupSurvivors` rebuilt `coveredCsOf cs xs`
   *inside* its filter (once per enumerated assignment, ≤256×); `checkReencode` recomputed
   `groupSurvivors`, `assignments (bitBox …)` (twice each) and `coveredCsOf` (once per bit pattern).
   Bound each once with a `let`; the `let` zeta-reduces during elaboration, so the soundness proofs are
   untouched. Also compute `reencodeOut` once (it was built twice for accepted groups).
5. **`busUnify` (`BusUnify.lean`)** — the new-equation filter tested `z ∈ cs.vars` per variable, and
   `cs.vars` rebuilds the whole ~10⁵-entry occurrence list on every reference. Bound `cs.vars` once
   with a `let` (zeta-transparent in the proof) — the single biggest per-pass win.

**Impact (openvm-eth, all 100 cases, optimizer time only, `apc-optimizer run`):**
total **3,393,648 ms → 1,978,903 ms (1.72×, −41.7%)**; geometric-mean per-case speedup **1.64×**;
slowest case apc_037 **258,362 ms → 165,964 ms (1.56×, −35.8%)** (apc_100 229,950 → 171,924). Per-pass
on apc_100 (profiler): domainBatch 135.7s→94.0s, reencode 78.3s→59.1s, busUnify 18.3s→3.4s.

Remaining bottleneck (documented for future work): `domainBatch`/`reencode` spend the balance in the
finite-domain **enumeration** — building `assignments doms` and evaluating covered constraints under
the list-based `envOf`, whose lookup is linear in the assignment size. The expensive targets are large
variable-sets that are mostly *pinned* (domain-1) with a few free vars, so each `envOf` lookup is over
a long assignment. Excluding pinned domain-1 vars from the enumerated box (substituting their constants
into the covered constraints, enumerating only the free vars) would shrink the assignments sharply, but
needs `forcedOver`'s soundness reproven against the reduced box — left as a follow-up.

### 46. Memory/exec-bus send↔receive pair cancellation (`BusPairCancel.lean`) — bus-interaction effectiveness

Georg's "Memory optimizer" hint (log entry 14), realizable under the entry-38+ `refines`/`admissible`
spec (its earlier block is gone). After `busUnifyPass` unifies a consecutive send `S` (mult `1`) and
receive `R` (mult `-1`) on a memory bus to the **same payload**, the two are the same message with
opposite multiplicity — net-zero on the bus — so dropping **both** is equivalence-preserving. Exactly
powdr's memory-interaction cancellation; it improves the **bus-interaction** metric (entry 42) without
touching the variable count.

Why it is sound (no audit-surface change — `Spec.lean`, `OpenVmSemantics.lean`, `MemoryBus.lean`
untouched):
- **soundness** (`out.implies cs`): the pair is on a `neverViolates` bus, so re-adding it to build a
  `cs` witness imposes no `violatesConstraint` obligation, and the identical-payload/opposite-mult
  pair adds `0` to every message's net multiplicity (`≈` preserved).
- **completeness** (`cs.impliesAdmissible out`): removing the pair preserves the VM's `admissible`
  predicate — **provided `S` is the earliest active send to its address** (else the drop could expose a
  fresh consecutive send→receive pair with mismatched payloads). Proved at the `admissibleMemoryBus`
  level (`admissibleMemoryBus_dropPair` in `Implementation/MemoryBusDrop.lean`, a single-element
  `dropOne` applied twice), bridged to the abstract `bs.admissible` by a new proven `BusFacts` field
  `admissible_dropPair` (definitional for OpenVM; vacuous for `trivial`, gated on `memShape`).

The pass drops no variables, so it is a `PassCorrect.ofEnvEq` (env' = env) with **no derivations**;
`out.vars ⊆ cs.vars` because the pair is removed. It scans each declared `neverViolates` memory bus
for the earliest cancelable pair (fused linear scan; the O(n) split-equation `decide` runs only for
the chosen candidate) and is drained to a fixpoint within one cleanup cycle via
`iterateToFixpoint busPairCancelPass` (bus length strictly decreases each drop). A whole access chain
collapses to its endpoints (first receive `R1` reading the context's prior value; last send `Sn`, the
final write — neither can cancel). Also fires on the execution bridge (empty-address shape),
cancelling the pc/timestamp chain likewise.

`lake build` green; `openVmOptimizer_maintainsCorrectness` (and the `simpleOptimizer`/`optimizerWithBusFacts`
variants) still `{propext, Classical.choice, Quot.sound}`-only; no `sorry`/`admit`/`axiom`/`native_decide`;
all outputs within the degree bound.

**Impact (bus interactions; variables unchanged):** apc_003 209 → **96** (2.18×; was 150 before this
pass, powdr 85). Across a sample (apc_001–008; the small cases re-confirmed identical post-rebase),
bus interactions total 5839 → **apc-optimizer 1894** (3.08×) vs **powdr 1637** (3.57×), with variables
unchanged (apc-optimizer keeps ≤ powdr's on every sampled case). The remaining apc-optimizer-vs-powdr bus gap is the PC lookups (bus 2),
which powdr removes and apc-optimizer keeps (never-violating model) — a separate follow-up (`docs/ideas.md`).

### 47. Investigation (Georg): where does `reencode`'s effectiveness actually come from? (no code change)
Georg asked why `reencode` drives so much effectiveness when powdr has no such pass, and whether a
powdr-inspired pass could get there without it. Measured with two binaries (reencode on/off in
`cleanupCycle`), diffed variable families, and compared against powdr's serialized output.

**Finding 1 — concentrated, not broad.** reencode is *identity* on register-only blocks (apc_003
133=133, apc_069/056/092/093/007/011/018/032/039/090/091 all byte-identical with/without) and huge on
load/store-heavy blocks (apc_005/009 **3619 → 1683**, apc_006 1781→889, apc_012 1497→749, apc_020
1411→818, apc_010 844→480). Over the first 22 cases (a load/store-rich slice) it removes **6826/15624 =
44% of the vars that survive every other pass** (1.78×), and nearly halves bus interactions
(10353→5490, via the `busPairCancel` it unblocks).

**Finding 2 — the win is ~87% *indirect*.** On apc_005 the family diff is: `flags` 512 → 0 (replaced by
256 `rnc` bits) = **−256 direct** binary-compression of the ternary load/store variant selector; and
`rs1_data` 516→8, the `…lower_decomp` timestamp limbs 770→276, `write/read/prev_data` collapses =
**≈ −1680 indirect** register/memory chaining. Only the −256 is what reencode is nominally "for".

**Finding 3 — the indirect part is a constant-fold that powdr also does, keeping the flags.** OpenVM's
memory address is `addressFields = [0,1]` = (space, offset). The destination-register write is
`[1, 52 − flag_poly, …]` — same address space as the source reads `[1, 40, …]`, offset a degree-2 flag
polynomial that is **identically 52 on the flags' constrained domain**. `busUnify`/`addrConstsNeq` can
only prove two accesses differ when *both* offsets are syntactic constants, so the symbolic offset blocks
chaining the source reads across it. reencode folds `52 − flag_poly → 52` as a *side effect* (entry 37's
constant emission), which unblocks the chain. **powdr reaches 1808 on apc_005 with all 512 flags intact
and 20/20 register offsets folded to constants (0 symbolic; heap offsets stay symbolic in both)** — i.e.
powdr gets the same collapse by ordinary range/domain simplification, no re-encoding.

**Answer.** Yes, a powdr-inspired pass recovers most of it: **domain-constant subexpression folding** —
over the small enumerable group `reencode`/`domainBatch` already build, replace any subexpression that is
constant on every domain survivor by that constant, *keeping* the group (no bits). Sound as a pure rewrite
(`e − c = 0` entailed by the group-local constraints, which must stay in the output to pin the domain —
so fold in bus interactions / non-covered constraints), env'=env, no derivations; strictly simpler than
`reencode` and a strict generalization of `domainBatch`/`ConstantFold`. It would recover the ~87% chaining
collapse (powdr's 1808 is the rough target; apc-optimizer's chaining is if anything stronger) but not the ~13%
flag compression, which is genuinely reencode-only (it's why apc-optimizer *beats* powdr here: 1683 < 1808). Full
proposal + the keep-both-vs-replace decision in `docs/ideas.md`. No optimizer/spec change in this entry.

### 48. Domain-constant subexpression folding (`DomainFold.lean`) — the entry-47 pass, kept alongside `reencode`
Implemented the entry-47 proposal (Georg chose "keep both"): a new `domainFoldPass`, placed **before**
`busUnifyPass` in `cleanupCycle`. For each constraint's small variable group (2–8 vars, same targets as
`reencode`), enumerate the surviving joint values over the group's constraint-derived domains
(`groupDoms`/`groupSurvivors`, shared with `reencode`) and replace every *maximal wholly-in-group*
**compound** subexpression that is constant on all survivors by that constant — **keeping** the group's
variables (no bits, no group substitution). This folds the flag-polynomial memory offsets
(`52 − flag_poly → 52`) that block `busUnify`'s `addrConstsNeq`, so the register/timestamp chains
collapse in the *same* cleanup cycle — exactly powdr's range/domain simplification, made explicit.

Correctness is a pure rewrite via `PassCorrect.ofEnvEq` (`env' = env`, no new variables, no derivations):
the folded subexpression's defining equation `e − c = 0` is entailed by the group's covered constraints,
which are kept **verbatim** in the output, so any assignment satisfying the output pins the group to a
survivor under which `foldRewrite` agrees with the identity (`foldRewrite_agree_covered`). Soundness,
completeness, admissible/side-effect preservation and `out.vars ⊆ cs.vars` all follow from that one
agreement. Strictly simpler than `reencode` (no witness transport / backward direction); a `systemHasFoldable`
Bool gate keeps it identity when nothing folds. Folding only lowers degree, so the guard never bites.

`lake build` green; `optimizerWithBusFacts_maintainsCorrectness`, `simpleOptimizer_maintainsCorrectness`,
`openVmOptimizer_maintainsCorrectness` all still `{propext, Classical.choice, Quot.sound}`-only; no
`sorry`/`admit`/`axiom`/`native_decide` (`check-proof-integrity.sh` passes).

**Measured (apc_005, the 5406-var load/store class).** Isolating the pass by toggling `reencode`:
- other passes only (no reencode, no fold): **3619** vars, 1801 constr, 1951 bus.
- **fold only (no reencode): 1939** vars, 1481 constr, **831** bus.
- reencode only, and fold+reencode (kept config): **1683** vars, 841 constr, 831 bus (byte-identical).
- powdr: 1808 vars.

So the fold pass **alone** recovers 3619 → 1939 (−1680, the full chaining collapse — bus already down to
831, matching reencode) and the residual 1939 → 1683 (−256) is exactly the flag compression only
`reencode` does. This confirms entry 47's 87%/13% split almost to the variable. With **both** passes the
result is byte-identical to reencode-only on every case sampled (apc_002/003/004/008/010/014/023/025/028/030/069),
i.e. effectiveness-neutral but more general (and slightly fewer fixpoint cycles: apc_005 62.3 s → 58.4 s).
The pass stands on its own if `reencode` is ever dropped (entry-47 option B → ~1939 on this class, keeping
all flags, close to powdr's 1808).

### 49. Byte-check packing (`BytePack.lean`) — bus-interaction effectiveness

Closes most of the bitwise-lookup bus gap identified in entry 42/46. On OpenVM's `BitwiseLookup`
bus a single value `e` is byte-range-checked by the self-XOR message `[e, e, 0, 1]` (op 1: asserts
`e ⊕ e = 0`, forcing `e` to be a byte). powdr packs **two** such checks into one pair check
`[e₁, e₂, 0, 0]` (op 0: range-check both operands), checking two bytes per interaction where apc-optimizer
kept one per limb — so apc-optimizer carried ~2× powdr's bitwise interactions (e.g. apc_001 12 vs 6,
apc_008 36 vs 10). `bytePackPass` performs the same packing.

Why it is sound (no audited-surface change — `Spec.lean`, `OpenVmSemantics.lean`, `MemoryBus.lean`,
`ApcOptimizer/Optimizer.lean` untouched):
- The two single checks and the packed check impose the **identical** obligation ("both operands
  are bytes"), so the satisfying set is unchanged. This table equivalence — `violates [x,y,0,0] =
  false ↔ violates [x,x,0,1] = false ∧ violates [y,y,0,1] = false` — is a new **proven `BusFacts`
  field** `bytePairBus` (discharged for the bitwise bus in `OpenVmFacts.lean` against the concrete
  `violates`; `trivial` sets it `false`, so the pass is a no-op without facts and stays
  VM-agnostic). The field also carries `breaksInvariant [x,y,0,0] (mult 1) = false` (the new packed
  interaction preserves invariants).
- The three interactions are **stateless** (`isStateful = false`), so the swap leaves every stateful
  side effect and the `admissible` discipline untouched (the stateful-filtered lists coincide). The
  core `mergeBytePair_correct` is a `PassCorrect.ofEnvEq` (env' = env, no derivations); `out.vars ⊆
  cs.vars` because the packed check's operands come from the two originals. One pair is packed per
  invocation, drained by `iterateToFixpoint` (bus length strictly drops by one each step); the
  candidate scan mirrors `busPairCancel` (the O(n) split-equation `decide` runs only for the chosen
  candidate).

`lake build` green; `openVmOptimizer_maintainsCorrectness` (and the `simpleOptimizer` /
`optimizerWithBusFacts` variants) still `{propext, Classical.choice, Quot.sound}`-only; no
`sorry`/`admit`/`axiom`/`native_decide`; all outputs within the degree bound (the packed check has
degree ≤ the originals).

**Impact (openvm-eth, top-12 `benchmark.py`, variables and constraints unchanged):** bus-interaction
effectiveness **3.056× → 3.109× aggregate**, **2.406× → 2.559× geomean** (gap to powdr's 3.552× /
2.888× narrowed from −0.496 to −0.443 aggregate). Variables **3.997× / 3.403×** and constraints
**8.784× / 8.546×** are byte-for-byte identical (the pass touches neither). Per case: apc_001 bus
**30 → 24**, reaching **full parity with powdr (24)**; apc_003 96 → 90; apc_008 89 → 77 (bitwise
36 → 24). The residual bitwise gap on some blocks (apc_008) is non-self-XOR byte checks the
recogniser skips; the remaining bus gap is otherwise the tuple-range packing and the memory-pointer
13-bit checks (see `docs/ideas.md`). Note: variables are ~tied with powdr on this sample (apc-optimizer wins
the aggregate, powdr the geomean and 7/12 cases), so bus interactions are the systematic gap this
targets.

### 50. Spec change (Georg's request): received memory words are byte-range-checked — plus the optimizations it enables

**The spec change (audited surface — needs human review).** Fixed the long-standing TODO in
`ApcOptimizer/OpenVmSemantics.lean`: `violates` now rejects a memory-bus *receive* (multiplicity `-1`)
from the register / main-memory address spaces (1 and 2) whose data limbs are not all bytes. The
justification (documented at the `violates` arm and as a new README assumption): the bus must
balance, a receive's tuple can only be matched by a send of the same tuple, and every send into
these address spaces — from any chip of the deployed system, including the initial-memory
boundary — carries byte-range data limbs (the invariant `breaksInvariant` demands). So a non-byte
receive conflicts with the rest of the system exactly like a failing lookup, and the optimizer may
*assume* received words are bytes. This also makes `guaranteesInvariants` genuinely hold for
load-type circuits (a LOADW's register write is byte-range *because* its heap read is), where
before the input-side assumption was silently false. The only other audited edits are cosmetic:
`isByte` lost its `private` (so implementation-layer facts can be proven about it) and the README
assumption bullet.

**The framework caught a real soundness subtlety.** Under the new semantics the memory bus is no
longer `neverViolates`, and `busPairCancelPass`'s old justification broke — *correctly so*:
dropping a matched send/receive pair whose receive was the **only** byte guarantee for a data limb
would widen the satisfying set (e.g. a loaded byte written to a register and re-read; nothing else
bounds it). powdr cancels these pairs unconditionally while also assuming receive-byte ranges —
apc-optimizer's `refines` proof obligation is what surfaced the tension.

**Adaptation + enabled optimizations (all in `ApcOptimizer/Implementation/`, zero new audit surface):**
- `BusFacts.slotBound` is now **multiplicity-aware**, and the OpenVM instance proves byte bounds
  for slots 2–5 of a memory *receive* with a constant address space 1/2 — so `domainPropPass`
  picks up `[0,256)` domains for received limbs with no further changes.
- New proven facts: `recvByteSlots` (sends on a memory-style bus never violate; receives don't
  provided the declared byte slots hold bytes) and `byteCheck` (a bitwise-bus self-check
  `[x,x,0,1]` is accepted **iff** `x` is a byte, and never breaks an invariant).
- `busPairCancelPass` justifies the dropped receive's byte obligation from the remaining system:
  a payload entry is a constant `< 256`, a variable with a bus-fact bound `≤ 256` from a remaining
  interaction (`byteJustified` — e.g. the chain's surviving first receive, or an explicit byte
  check), or — the **deep** case, prime `p` only — a variable whose defining constraint pins it to
  a byte on every point of its selector flags' proven finite domains (`deepBoundOk`: enumerate
  `findDomain` domains, substitute + fold + linearize, each branch must yield a re-checked byte
  root or `x = y` with `y` byte-bounded). This resolves the one-hot byte-*selection* shape
  `x = Σ flagpoly·yⱼ` that unaligned sub-word loads leave behind. If justification still fails,
  the pass **materializes** the obligation as one explicit `[e,e,0,1]` self-check on the
  `byteCheck` bus while dropping the pair (net −1 bus interaction, re-verified by `emitOk`;
  later `bytePackPass` packs such singles pairwise) — with deep justification on, no benchmark
  case currently needs the fallback.

**Measured (vs. the pre-change baseline).** apc_001 (42/18/24), apc_003 (133/45/90) and the
load/store-heavy apc_005 (1683 vars / 841 constr / 829 bus, ~74s vs ~58s — the deep-justification
cost) are byte-for-byte identical; apc_008 improves on **all three axes**: 128→**121** vars,
79→**78** constraints, 77→**75** bus (the new receive-limb domains let `domainProp` force more
values). The full `benchmark.py` sweep was still running at commit time; its aggregate numbers
are reported in the follow-up entry. `lake build` green;
`optimizerWithBusFacts_maintainsCorrectness`, `simpleOptimizer_maintainsCorrectness`,
`openVmOptimizer_maintainsCorrectness` still `{propext, Classical.choice, Quot.sound}`-only; no
`sorry`/`admit`/`axiom`/`native_decide`.

### 51. seqz/beqz: hardwired-`x0` admissibility + fixed-zero-register pinning (`ZeroRegister.lean`) — closes ~⅓ of the variable gap to powdr on branch blocks

**⚠ Audited spec change (flagged for review).** This is the first entry that edits the audited
surface. An earlier session correctly found that powdr's `seqz`/`beqz` reduction is **impossible
under the frozen spec**, and this entry adds the minimal spec change that unblocks it.

**The obstruction (re-verified).** An OpenVM `beqz`/`bnez` compares register `a` against `x0`. `x0`
is read and written back on the memory bus with a *free* value `b` at two different timestamps, so
`b` is observable in stateful side effects; the last-write-wins discipline cannot pin it (both
accesses dangle within the block). powdr sets `b = 0` (RISC-V hardwires `x0 = 0`) and thereby (i)
drops the four operand limbs `b₀..b₃` and (ii) collapses the four `diff_inv_marker` inverse-hint
limbs to one (`Σaᵢ = 0 ⟺ a = 0` for bytes). Both hinge on `x0 = 0` — a *global* register-file fact a
single chip cannot see, and pinning it locally would change a stateful memory payload, which the
spec's side-effect soundness (`≈`) forbids. So the frozen spec genuinely cannot license it.

**Minimal spec change (`ApcOptimizer/OpenVmSemantics.lean`).** Add `zeroRegisterReads` — a
**completeness-only** `admissible` conjunct, same flavor as the memory discipline: every *active*
memory message at address `(as, ptr) = (1, 0)` carries zero in its four data limbs. Faithful (real
RISC-V traces never read a nonzero `x0`), and it constrains **only** which inputs completeness must
reproduce — soundness (all assignments) is untouched. The whole audited delta is one `def` plus one
`∧`-conjunct.

**Why passes don't need re-proving.** Generic passes preserve `admissible` by preserving the
evaluated message list (`admissible_subst`/`admissible_mapExpr`/…), so they transfer *any*
`admissible`. Only `Implementation/OpenVmFacts.lean` unpacks the concrete predicate: `admissible_sound`
projects the discipline conjunct (`.1`); `admissible_dropPair` rebuilds the `∧` (discipline as before;
`zeroRegisterReads` survives dropping a pair because `A++B++C ⊆ A++S::B++R::C`). A new proven `BusFacts`
field `zeroCell` (+ `zeroCell_sound`) exposes the fact to passes; `trivial` declares none, so the
fact-free optimizer and `simpleOptimizer_maintainsCorrectness` are unchanged.

**The pass (`Implementation/OptimizerPasses/ZeroRegister.lean`, `VerifiedPassW`).** For every *active*
memory message (constant nonzero multiplicity) whose address is a declared `zeroCell` matched
syntactically to constants `(1, 0)`, it **adds** the constraints `dataᵢ = 0`, via
`addConstraints_correct`: soundness is free (added constraints only shrink the accepted set; buses
untouched ⇒ side effects unchanged), completeness discharges them from `zeroCell_sound`. It introduces
no variable (data limbs are existing columns) and skips already-trivial/duplicate equalities, so it
is idempotent (once `b` folds to literal `0` it fires no more). Wired into `cleanupCycle` after
constant-fold; the existing Gauss/subst passes then propagate `b → 0`, eliminating the operand limbs.

`lake build` green; `openVmOptimizer_maintainsCorrectness` (+ `simpleOptimizer`/`optimizerWithBusFacts`)
still `{propext, Classical.choice, Quot.sound}`-only; no `sorry`/`admit`/`axiom`/`native_decide`; all
outputs within the degree bound.

**Impact (variables).** On the 37 branch-bearing (`diff_inv_marker`) benchmark files, apc-optimizer drops
**5206 → 5083 vars** (−123), shrinking the variable gap to powdr from **387 → 264**. Examples:
apc_001 42→38, apc_028 35→28 (now beats powdr 30), apc_056 28→24, apc_010 480→476 (beats powdr 498),
apc_014 272→268 (beats powdr 274). Full `openvm-eth` aggregate variable effectiveness is now
**4.064× (geo 3.522×)** vs powdr **4.092× (geo 3.787×)** — near parity on the top-priority metric;
constraints 8.77× stay well ahead of powdr's 5.85×. The residual per-branch gap is the inverse-hint
collapse (4 hints → 1), which needs **no** further spec change — see `docs/ideas.md`.

### 52. Collapse the multi-limb reciprocal-witness group to one hint (`HintCollapse.lean`) — finishes powdr's `seqz`/`beqz`

Entry 51 pinned `x0 = 0`, leaving a `beqz`/`bnez` block with the gadget `cmp·(cmp−1)=0`,
`(cmp−1)·aᵢ=0`, and one *bilinear* constraint `Σᵢ aᵢ·dimᵢ = cmp` carrying **four** fresh
inverse-hint witnesses `dimᵢ` (the `diff_inv_marker` limbs). powdr keeps only **one** inverse hint.
This pass performs that collapse — and it is a *general* transformation, not tied to the gadget.

**The pass (`Implementation/OptimizerPasses/HintCollapse.lean`, `VerifiedPassW`).** Whenever a
constraint is `Σᵢ aᵢ·dimᵢ + t = 0` with (a) each `dimᵢ` a **distinct variable occurring exactly
once in the whole system** (a pure witness — `occursOnlyInTarget`), (b) each coefficient `aᵢ` a
**single byte-bounded variable** (`coeffVar ∘ fold`, bound `≤ 256` from `BusFacts.slotBound` via
`BoundsMap`, with `n·(B−1) < p` so the sum cannot wrap), and (c) `t` and the `aᵢ` reading only input
(powdr-ID) columns, it is replaced by `(Σᵢ aᵢ)·inv + t = 0` with a single fresh derived witness
`inv = QuotientOrZero(−t, Σᵢ aᵢ)`, dropping every `dimᵢ` (−(n−1) variables).

**Correctness (`collapse_correct [Fact p.Prime]`, via the `reencode` rewrite
`rw = fun x => if x = E then E' else x`).** *Soundness* sets every `dimᵢ := inv`, so
`Σ aᵢ·dimᵢ = (Σaᵢ)·inv = −t`. *Completeness* computes `inv` by `QuotientOrZero`; the `Σaᵢ = 0`
branch closes because byte-bounded coefficients summing to `0` are all `0` (`sum_zero_all_zero`),
forcing `t = 0`. Neither branch touches a bus, so side effects and `admissible` are unchanged. The
derived `inv`'s method reads only `denom`/`rest` columns, which are powdr-ID inputs, so it satisfies
the `Derivations.cover`/`reconstructs` obligation. With `BusFacts.trivial` (no `slotBound`) the pass
never fires, so the fact-free optimizer and `simpleOptimizer_maintainsCorrectness` are unaffected.
Wired into `cleanupCycle` right after `zeroRegisterPass`; the fresh `inv` and the dropped hints then
propagate through the following Gauss/fold passes.

`lake build` green; `optimizerWithBusFacts_maintainsCorrectness`, `simpleOptimizer_maintainsCorrectness`
and `ApcOptimizer.OpenVM.openVmOptimizer_maintainsCorrectness` all still
`{propext, Classical.choice, Quot.sound}`-only; no `sorry`/`admit`/`axiom`/`native_decide`; all
sampled outputs within the degree bound.

**Impact (variables).** The collapse fires on the `seqz`/`beqz` blocks whose operand limbs are
byte-range-checked *within the block* (so `Σaᵢ = 0 ⇒ all aᵢ = 0` is available from `slotBound`),
removing the 3 surplus inverse-hint witnesses there; it is a **sound no-op** on blocks whose limbs
are byte-bounded only through the memory invariant (no in-block range check). Verified on top of
entry 51: apc_001 38→35, apc_047 94→91; no change on apc_010/apc_028/apc_056/apc_069. The
full-benchmark aggregate is left to the maintainer's run.

### 53. Optimizer runtime: kill the per-constraint full-system rescans in `hintCollapse` and `reencode` (effectiveness unchanged)

Pure **performance** work in the entry-45 style — every change is output-preserving, so
effectiveness is untouched and only the optimizer's wall-clock cost drops. Verified by running
baseline (pre-change) and new binaries on 13 benchmark cases spanning all size classes
(apc_001/003/005/006/008/010/014/028/047/056/069/092/100): `vars/constraints/bus` are **identical
on every case**. Nothing in the audited surface or `Basic.lean` changed; correctness axioms stay
`{propext, Classical.choice, Quot.sound}`; `lake build` green, `check-proof-integrity.sh` passes.

Re-profiled per-pass at HEAD (the `apc-optimizer profile` pass list was stale — it predated
`zeroRegister`/`hintCollapse`/`domainFold`/`busPairCancel`/`bytePack`; synced it to the current
`cleanupCycle` in `Main.lean`). The entry-52 `hintCollapse` dominated everything: 183 s of
apc_005's 280 s (65%), 129 s of apc_100's 347 s (37%), with `reencode` second (38 s / 106 s).
Both were paying for *recomputation inside the per-candidate scan*:

1. **`hintCollapse` (`HintCollapse.lean`)** — `tryOne` runs once per constraint, and each call (a) rebuilt
   `BoundsMap.build facts` (a full bus-interaction sweep), (b) decided `occursOnlyInTarget` per
   variable by materializing every expression's `.vars` list (a full-system allocation storm per
   `(E, d)` pair), and (c) eagerly evaluated the whole `Decidable` certificate conjunction —
   including an `inv ∉ cs.vars` membership scan that rebuilds the ~10⁵-entry occurrence list —
   even when the very first conjunct `2 ≤ D.length` already failed (it fails on essentially every
   constraint). Fixes, each output-preserving: hoist `BoundsMap.build` and a new `busVars` hash set
   (all variables occurring in any bus interaction) to the pass level, built once per invocation;
   gate `occursOnlyInTarget` behind `!busVars.contains v` (a variable in any bus interaction can
   never pass it, so the gate never changes the filter's value — it only skips the scan); decide
   `occursOnlyInTarget` with the allocation-free `Expression.mentions` instead of `d ∉ ·.vars`;
   and turn the certificate into one short-circuiting `&&` chain (`decide`d conjuncts) so nothing
   after `2 ≤ D.length` is evaluated on unsuitable constraints. The proof consumes the same
   certificates (`Bool.and_eq_true`/`decide_eq_true_eq` split them back into the six hypotheses).
2. **`reencode` (`Reencode.lean`)** — `reencodeStep` checked `xs.all (· ∈ cs.vars)` *before*
   `buildReencode`, so every candidate group (hundreds per invocation, ×8 variables each)
   materialized the full occurrence list; `buildReencode` rejects almost all of them anyway.
   Moved the check after `buildReencode` succeeds (all failure branches return the same identity
   `PassResult`, so this is a pure branch reorder) and bound `cs.vars` once with a `let`.

**Impact (solo runs, same machine, output identical):** apc_005 **280.5 s → 75.3 s (3.7×)**,
apc_100 **320.0 s → 155.7 s (2.1×)**, apc_010 14.6 s → 8.8 s (1.7×), apc_008 17.2 s → 16.5 s;
small register-only cases unchanged (they never hit the hot paths). Per-pass on apc_005
(profiler): `hintCollapse` **182.9 s → 0.2 s (~900×)**, `reencode` **37.7 s → 5.2 s (7.3×)**.

Remaining bottlenecks (documented for future work): `domainBatch` (24.7 s on apc_005) — the
entry-45 note still applies (enumerate only the non-pinned variables of the domain box, needs
`forcedFromSurvivors_sound` reproven against the reduced box); and `busPairCancel` (23.6 s) —
it drops one send/receive pair per invocation and rescans the system per drop, so a chain of
`k` cancellations costs `k` full `findCancel` sweeps (a batched variant would cancel a whole
chain per sweep).

### 54. Optimizer runtime: early-abort box scans and hoisted `ZMod` operations in `domainBatch`/`reencode` (effectiveness unchanged)

Pure **performance** work in the entry-45/53 style — every change is output-preserving, so
effectiveness is untouched. Closes entry 53's `domainBatch` bottleneck. Found by per-stage
instrumentation, then `perf record` and reading the generated C: the decisive discovery is that
every `+`/`*`/`decide (· = 0)` on `ZMod p` with a **runtime** `p` re-invokes `ZMod.commRing p`
and re-projects the instance chain **per expression node** — `perf` attributed the bulk of
`domainBatch` to the allocator building and freeing instance records (plus ~10% in
`ZMod.commRing` and its projections directly). The other structural finds: the box enumeration
paid the full `box × items` evaluation even for targets that force nothing (the entire final
fixpoint-check iteration was wasted), and `reencode` rebuilt and re-evaluated its interpolation
candidates ~3× per bit pattern for the ~52 candidate groups that `checkReencode` accepts but the
degree guard rejects — every cleanup iteration again.

1. **`domainBatch` (`DomainBatch.lean`)** — replace the survivor-list enumeration
   (materialize box → filter → read off candidates → re-check per candidate) with the
   single-pass `scanInit`/`scanWith` fold: it keeps the list of candidates every survivor so far
   agrees on and **aborts as soon as it is empty** — claiming nothing needs no certificate, and
   a completed scan *is* the checked certificate (`scanInit_some`, consumed by
   `scanForced_sound`/`scanNone_unsat`). Cache the materialized range domains per bound
   (`RangeCache`; `interactionDomainC_fst` proves the table identical). Compare `powdrId?`
   before the name String in the covered-item scans (`varsInF`/`containsFast`, extensionally
   equal). Compile the covered items per target to positional leaves and extract `add`/`mul`/
   `decide` from the instances once (`IExpr.evalWith`/`survivesAllCW`/`compiledSurv`, whose
   bundled pointwise equality with `survivesAllM` is all the certificates consume).
2. **`reencode` (`Reencode.lean`)** — bind the substituted expression, its per-pattern values,
   and the folded interpolation once (`interpOfV`/`candSelect`); evaluate the pattern/survivor
   loops through `Expression.evalFast` (field operations hoisted per call, `evalFast_eq`);
   reuse the covered set for the survivor filter (`groupSurvivorsE`); `powdrId?`-first
   comparisons in `coveredBy`/`groupSubst`/`groupRewrite` and the freshness sweep
   (`Expression.mentionsF`).

**Impact (solo runs, same machine, output identical; A/B against current `main`):** apc_006
`profile` total **101.2 s → 32.1 s (3.2×)** — `domainBatch` **67.2 s → 5.5 s (12.2×)**,
`reencode` **9.8 s → 2.8 s (3.5×)**; all other passes unchanged. Verified output-identical
(`vars/constraints/bus`) against the `main` binary on the entry-53 13-case list
(apc_001/003/005/006/008/010/014/028/047/056/069/092/100) plus 10 random cases (seed 42) —
20 distinct cases, identical on every one; before the repo-rename rebase additionally
byte-identical `run` output on apc_006 and exact stats on apc_001–010 plus 10 more sampled
cases against the pre-change binary. The passes'
internal decision counters (forced values, candidate groups found/built/checked/accepted per
iteration) are identical throughout. Nothing in the audited surface changed; correctness axioms
stay `{propext, Classical.choice, Quot.sound}`; `lake build` green;
`check-proof-integrity.sh` passes.

Remaining bottlenecks (documented for future work): `busPairCancel` is now the top pass on
apc_006 (18.5 s; entry 53's batching idea still applies); `domainFold` evaluates through the
plain per-node-instance `Expression.eval` (~1.7 s on apc_006 — the `evalFast` treatment applies
almost verbatim); the degree-rejected `reencode` candidate groups still pay a (now much
cheaper) full-system rewrite every iteration; and the entry-45 pinned-variable box reduction
for `domainBatch` remains open.

### 55. Optimizer runtime: hash-index `busPairCancel`'s receive search (effectiveness unchanged)

Pure **performance** work in the entry-53/54 style, closing entry 53's `busPairCancel`
bottleneck note. After entry 54, `busPairCancel` was the top pass (apc_036: 17.4 s of 27.3 s,
64%; apc_006: 18.5 s). Stage instrumentation of the fixpoint loop showed **~90% of the pass in
`findMatchRecv`** (apc_036: 13.9 s of 15.4 s) — every invocation re-probes every send against
the whole remaining interaction list with structural payload comparisons (51k probes at ~200 µs
in one cleanup iteration alone), once per dropped pair.

1. **Hash-indexed receive search** — index the candidate receives (constant `-1` multiplicity,
   on the bus) once per invocation by a structural payload hash (`recvIndex`/`payloadHash`),
   and scan sends over an `Array`, resolving each probe by hash lookup plus an exact payload
   comparison on the rare hash hits (`firstMatchAt`); `A`/`B`/`C` come from `Array.extract`
   slices. Hash inequality proves payload inequality and hits are re-verified structurally, so
   exactly the same first matching receive is found in the same send order; correctness never
   depended on the search (the accepted candidate is re-verified by `checkCancel` and the
   decided split equation, as before). `findMatchRecv`: 13.9 s → 0.33 s on apc_036.
2. **Single-pass byte justification** — each accepted drop paid the justification scan twice
   (`unjustifiedSlots`, then `checkCancel`'s `recvSlotsJustified` re-verification). Try the
   certificate with `checks := []` first: every non-justification conjunct is guaranteed by the
   scan's own gates, so it passes iff every declared byte slot is justified — exactly what
   `unjustifiedSlots = []` decides. Only candidates with an unjustified slot fall back to
   computing `unjustifiedSlots` and emitting the single self-check as before.

**Impact (solo runs, same machine, output identical):** apc_036 `busPairCancel`
**17.4 s → 3.1 s (5.6×)**, case total **27.3 s → 12.9 s (2.1×)**; the instrumented replica's
per-stage counts (send probes, matches, region passes, drops per iteration) are identical
before/after. Verified output-identical (`vars/constraints/bus`) against the pre-change binary
on the entry-53 13-case list plus apc_036 — identical on every case. Nothing in the audited
surface changed; correctness axioms stay `{propext, Classical.choice, Quot.sound}`;
`lake build` green; `check-proof-integrity.sh` passes.

Remaining bottlenecks (documented for future work): `domainFold` is now apc_036's top pass
(3.4 s; plain per-node-instance `Expression.eval` in `constOnSurvs` — the entry-54 `evalFast`
treatment applies almost verbatim); `busPairCancel`'s residual ~3 s is spread across the
fixpoint wrapper (`sizeKey`/`varCount` per invocation), the per-invocation `decide p.Prime`,
and the per-accepted-drop `checkCancel`/split-decide — a batched multi-pair sweep (entry 53's
idea) would cut the invocation count itself but needs an output-equality argument across
reordered drops.

**Entry 55 addendum:** deferring the A/B/C materialization behind the region tests
(`Array.all` over the index ranges; lists built only for accepted candidates) recovers a
further ~0.8 s on apc_006 (`busPairCancel` 11.3 s → 10.5 s) and ~0.3 s on apc_036 (3.1 s →
2.8 s), output identical. The remaining apc_006 residual is the refutation scans over ~28k
matched same-payload candidates and the ~1.2k not-yet-justifiable candidates re-scanned per
drop — the batched multi-drop sweep above remains the real lever.

### 56. Optimizer runtime: single-invocation `busPairCancel` fixpoint (kill the per-drop rescan) + deep-path hoists (effectiveness unchanged)

Pure **performance** work in the entry-53/54/55 style — every change is output-preserving, so
effectiveness is untouched and only the optimizer's wall-clock cost drops. The CI *Runtime Bench*
job (per-pass timing) showed `busPairCancel` had become by far the dominant pass on the expensive
cases: on apc_037, **137 s of the 167 s optimizer call (82 %)**; also the top pass on apc_100
(16 s), apc_006 (15 s). This closes entry 55's "batched multi-drop sweep" note.

**Where the time went.** Instrumenting the pass (invocation/candidate counters) plus a `deep`-off
probe pinned it down: apc_037 ran **531** `busPairCancelPass` invocations (one per dropped pair,
under `iterateToFixpoint`), and **~87 % of the pass was the deep byte-justification**
(`deepBoundOk`/`pointByteOk`: enumerate a receive's selector-flag domains and linearize the
substituted defining constraint per point). Because the pass dropped **one** pair per invocation
and `iterateToFixpoint` restarts the scan from position 0 every time, the same region-passing but
not-yet-justifiable candidates before the accepted drop had their expensive deep justification
recomputed on every one of the 531 invocations (one candidate was re-examined **170×**).

1. **Single-invocation cancellation fixpoint (`cancelLoop`)** — run the whole cancellation
   fixpoint *inside one pass invocation*, resuming the scan after each drop instead of restarting
   from the top. `findCancelGoIdx`/`findCancelForBus`/`findCancel` now return the accepted send's
   bus-list index and position and whether a byte check was emitted; `cancelLoop` composes each
   drop with `PassCorrect.andThen` and, after a drop that emitted **no** check, resumes at that
   drop's own bus/position (`resumeIdx`/`resumePos`) — skipping the already-rejected prefix and
   any earlier, exhausted bus. This is output-identical to the old restart-from-top behaviour: a
   drop on one bus never re-enables a candidate on another (region tests refute cross-bus messages
   by `busId` outright) and removing interactions can only make byte-justification *harder*, so no
   skipped candidate can have become droppable; only a drop that **emits** a byte check (which
   joins the remaining interactions and could newly justify an earlier pair) restarts from the top.
   Every accepted drop is still certified by `checkCancel_sound` exactly as before, so the set and
   order of drops — hence the output — is unchanged; the loop only controls the search order.
   (`cancelLoop` is a `partial def`: each drop strictly shrinks the interaction count so it
   terminates, but that measure is not machine-checked. Correctness does not depend on it — the
   returned `PassResult` carries its `PassCorrect` proof by construction — and the correctness
   theorems' axioms stay `{propext, Classical.choice, Quot.sound}`.)
2. **Deep-path recomputation hoists** — bind `LinExpr.norm l` once per enumerated point in
   `pointByteOk` (was recomputed ~5×), `deepEnumDoms domCs x c` once per candidate in `deepBoundOk`
   (was 3×), and the single-variable-constraint filter `all.filter isSingleVar` once per
   `deepByteJustified` (was up to 4×, inside the `.any`). All are zeta-transparent `let`s; the
   soundness proofs are unchanged bar one `simp only [] at h` to reduce the introduced `let` before
   `split_ifs` in `deepBoundOk_sound`.

**Impact (solo runs, same machine, output identical; A/B against the pre-change binary):**
apc_037 whole optimizer **167.7 s → 36.0 s (4.7×)** — `busPairCancel` **137 s → 6.9 s (~20×)**,
no longer a top-3 pass; apc_100 total 41.4 s → 28.3 s (`busPairCancel` 16.3 → 3.7 s), apc_006
35.2 → 21.5 s (15.0 → 1.7 s), apc_005 19.0 → 16.8 s (4.3 → 1.3 s), apc_036 (4.3 → 1.3 s). Verified
output-identical (`vars/constraints/bus`) against the pre-change binary on every openvm-eth case.
Nothing in the audited surface or `Basic.lean`/`FactPass.lean` changed; `lake build` green;
`check-proof-integrity.sh` passes.

Remaining bottlenecks (documented for future work): `domainBatch` and `reencode` are now the top
passes on the expensive cases (apc_037: 11.9 s / 8.8 s); the deep byte-justification's per-point
`substF`/`fold`/`linearize` still pays the entry-54 per-node `ZMod` instance-projection tax (a
compiled/`evalFast`-style linearizer would cut it further), and `deepByteVars`'s `findVarBound`
scan over the remaining interactions is recomputed per candidate.

### 57. Carry-branch resolution (`CarryBranch.lean`): interval analysis collapses one-sided adder carry products — the main per-case variable win

**The idea** (from the apc_039 variable diff against powdr): add/move blocks keep whole
register data-word copies alive through unresolved **carry-branch constraints** — per limb, the
byte-decomposed adder leaves `(b₀ − a₀)·(b₀ − a₀ − 256) = 0` ("the difference is 0 or 256").
When both operands are provably bytes — `b₀` because it is a memory receive (the entry-50
receive-byte spec change), `a₀` because it is bitwise-checked — the second factor's value lies
in the integer interval `[p−511, p−1]`, so it can *never* vanish and the product is **equivalent**
to the linear `b₀ = a₀`. Gauss then substitutes the `b` word away entirely (its memory receive
carries the `a` limbs directly), and the higher limbs cascade: once `b₀ = a₀` is substituted and
normalized, the limb-1 constraint's cross terms cancel and it becomes the same one-sided shape.
No existing pass could do this: the roots are parameterized by another variable (`b₀ ∈
{a₀, a₀+256}`), outside the constant-domain passes, and the constraint is degree 2, outside
Gauss/affine.

**Implementation** (`ApcOptimizer/Implementation/OptimizerPasses/CarryBranch.lean`): a `VerifiedPassW`
that maps each algebraic constraint through `resolveExpr`: on a product `f·g`, if either factor
is certified never-zero, keep (recursively) the other. The certificate (`neverZeroB`) linearizes
the factor, normalizes, and computes a **two-sided interval** from the proven bus-fact bounds
(`BoundsMap`, built from `BusFacts.slotBound` exactly as in `hintCollapse`): each term picks the
representation — positive `a·v` or negative `−((−a)·v)` — with the smaller magnitude
(`splitSumMax`), and the form is refuted when `maxNeg < const.val ∧ const.val + maxPos < p`
(`linNeverZeroSplit`, the two-sided generalization of `MemoryUnify.linNeverZero`). Two
non-obvious points, both found by measurement:

1. **Candidate rescaling.** Mid-pipeline (before the coda's `monicScale`) the carry factors read
   `−1 + 256⁻¹·b₀ − 256⁻¹·a₀` — raw coefficient values overflow every interval. Since a factor's
   zero set is scaling-invariant, the certificate tries the field inverse of each coefficient and
   of the constant as a scalar and certifies any rescaling. Soundness needs nothing about the
   candidate (if `k·l` never vanishes, `l = 0` would force `k·l = 0`), so the candidate list is
   pure heuristic.
2. **Placement: first in the cycle, *before* Gauss.** `iterateToFixpoint` only keeps a cycle
   whose lexicographic `sizeKey` strictly drops. Resolution alone changes no count (the variables
   still sit in the memory interactions), so with the pass placed after Gauss its rewrite was
   *discarded* at the fixpoint — the linear constraint must be consumed by Gauss in the same
   cycle to shrink the key. One cycle resolves one limb per word; the cascade converges in a few
   extra cycles.

Correctness: the rewrite is an *equivalence* on satisfying assignments (`resolveExpr_eval_iff`;
`p` prime checked at runtime for `mul_eq_zero`, like the other field-dependent passes), so both
`PassCorrect` directions use the unchanged assignment; bus interactions, side effects, and
`admissible` are untouched, and no variable is introduced. With `BusFacts.trivial` no bound
exists, no certificate fires, and the pass is the identity.

**The regression it exposed, and the `domainBatch` fix.** The first full-set baseline
comparison showed 51 of 100 cases improved but **apc_051 regressed** (482 → 485 vars,
329 → 354 bus): the new pass changed Gauss's substitution orientation around a chained register
word, and the final state stranded XOR rows `[0, 0, a__i, 1]` (constant operands — the table
forces `a__i = 0`) plus an identical memory send/receive pair kept alive by those unpinned
limbs. No pass could make progress on that state: nothing consumes `BusFacts.slotFun`, and
`domainBatch` skipped the XOR rows as *uninformative* — its gate assumed any all-vars/constants
payload is the range check that defined the box domains. The gate was sharpened
(`biInformative`): an interaction is also informative when it has a raw-variable slot carrying
**no** `interactionBound` from that same interaction (the XOR result slot) — its domain came
from elsewhere, so the table can genuinely filter the box. Domain-defining range/byte/tuple
checks bound every variable slot they carry and stay excluded, so the gate keeps its performance
property; the change is heuristic-only (target selection — forced values still carry their own
certificates). This recovered apc_051's variables exactly (482) and its bitwise count; 7
identical send/receive pairs with compound (shift-gadget) payload slots remain uncancelled there
(+14 bus on that one case, invisible in the aggregate) — `busPairCancel`'s byte justification
does not cover compound slots, a known boundary-pair gap.

**Impact** (full 100-case `openvm-eth` benchmark, target vs baseline vs powdr): variables
**4.082× → 4.136× aggregate** (powdr 4.092× — apc-optimizer now wins the aggregate),
**3.605× → 3.706× geomean** (powdr 3.787× — over half the remaining geomean gap closed);
per-case variable losses to powdr **71 → 52** (wins 17, ties 31). Constraints improve to
9.073×/11.190× agg/geo (powdr 5.853×/10.311×); bus interactions unchanged (2.922×/2.440× vs
powdr 3.480×/2.822×). Per-case against baseline: **no case regressed in variables or
constraints**; the only bus regression is apc_051's +14 above. Spot checks: apc_039 38 → 30 vars
(= powdr), apc_011 59 → 51 (powdr 48), apc_090 50 → 46 (powdr 43). Runtime is *down* on the
affected cases (apc_039 ~700 → ~400 ms — the resolved constraints leave later passes less
work). `lake build` green; `check-proof-integrity.sh` passes; correctness axioms stay
`{propext, Classical.choice, Quot.sound}`.

Two negative findings recorded in `docs/ideas.md`: the apc_005-class `mem_ptr_limbs` carry
products are **not** one-sided (the 16-bit wrap genuinely occurs on some traces — both factors'
intervals contain 0), so that bus gap needs cross-access limb unification instead; and the
apc_018 compare-block gap is the sltu-style `diff_marker` gadget that `hintCollapse`'s matcher
does not cover yet (43 vs powdr 34 after this change).

### 58. Bitwise-lookup **result** byte bound (`openVmFacts.slotBound` slot 2): unblocks keccak memory-pair cancellation — the main bus win

**The idea** (from profiling the new keccak stress case against powdr). The headline keccak gap
was bus interactions: apc-optimizer 5206 vs powdr 1734, dominated by the **memory** bus — apc kept
2482 memory interactions (1241 send/receive pairs) where powdr keeps 258. `busPairCancel` cancels a
matched send→receive pair only when the dropped receive's data limbs are provably bytes from the
*remaining* system (the `recvByteSlots` spec obligation, entry 50); when ≥2 limbs are unjustified
it can't even emit the fallback self-check (that path covers a single slot), so the drop is
refused. On keccak the **first** send of each register access chain writes an *XOR result*
(`a__i` in a bitwise interaction `[x, y, a__i, 1]`), and the result slot carried **no** byte
guarantee — `openVmFacts.slotBound` bounded the bitwise **operands** (slots 0, 1) but not the
**result** (slot 2). So the first pair of every chain failed byte-justification, and — being the
earliest active send — blocked the whole chain from cancelling (later pairs, whose data *was*
justified, saw a same-address active send before them).

But the bitwise table already forces the result to be a byte: op 0 pins `z = 0`, op 1 pins
`z = x ⊕ y` with `x, y < 256` (and op ≥ 2 violates), so `z < 256` in every non-violating case.

**Implementation** (`ApcOptimizer/Implementation/OpenVmFacts.lean`, ~25 lines, zero audit surface):
one new `slotBoundImpl` arm `| some .bitwiseLookup, [_, _, _, some op], 2 => if op.val ≤ 1 then
some 256 else none`, mirroring the operand arms, plus its `slotBound_sound` bullet — op 0 gives
`z.val = 0`, op 1 gives `z.val = Nat.xor x.val y.val < 2^8` (`Nat.xor_lt_two_pow`). Purely
additive true information: every existing `slotBound` consumer (`busPairCancel` byte
justification, `domainProp`, `CarryBranch`, `hintCollapse`) can only fire *more*, never less, so
no pass's correctness or the audited surface is touched. With `BusFacts.trivial` the bound is
absent and behaviour is unchanged.

**Impact.** keccak stress case: **bus interactions 5206 → 3904** (2.55× → 3.40×; memory
2482 → cascaded down as the chains now fully cancel), variables 3626 → 3622 (slightly better, no
regression — the freed data limbs still live in the XOR interactions, so the *variable* gap to
powdr's 2021 is untouched; see the new ideas entry), constraints unchanged at 492. Full
100-case **openvm-eth** sweep: variables unchanged (4.136×/3.706× agg/geo), **bus interactions
2.922× → 2.951× agg / 2.440× → 2.447× geo** (a small win there too), constraints unchanged
(9.073×/11.190×); per-case variables still 17 wins / 52 losses / 31 ties — **no case regressed**.
Runtime unchanged (keccak ~320 s). `lake build` green; `check-proof-integrity.sh` passes;
correctness axioms stay `{propext, Classical.choice, Quot.sound}`.

The residual keccak gap is now **variables** (3622 vs 2021): the read-data limbs (`b`/`c` classes,
~1200 vars powdr has none of) survive because they still occur as operands/results of the XOR
(bitwise) interactions even after their memory pairs cancel. Closing it needs read-value
unification (substitute a read limb by the value written to that cell, or by the XOR functional
dependence `slotFun`) — recorded in `docs/ideas.md`.
### 57. Two-root decomposition unification (`RootPairUnify.lean`) — bounded-integer reasoning, aggregate variable lead over powdr

Memory-pointer decompositions pin each limb by a **two-root carry constraint**
`(A + k·x)(A + δ + k·x) = 0` (the two address-wraparound cases) plus a range check keeping the
limb inside a window smaller than the root gap. Two accesses at the *same* address produce two
such constraints with the same `A, k, δ` but distinct limb variables — each variable
independently picks a root, so no purely algebraic pass can equate them, and every
finite-*constant*-domain pass is blocked by the parameterized roots (the gap diagnosed in
`docs/ideas.md`'s mem-ptr item). apc-optimizer kept 258 `mem_ptr_limbs` on apc_005 vs powdr's 130.

**The bounded-integer argument** (`rootPair_eq`): both roots differ by `g = k⁻¹·δ`; if
`x.val < B` and `y.val < B` with `B ≤ g.val` and `B ≤ p − g.val`, the field difference
`x − y = ±g` is impossible over the integers, so `x = y`. The entailed equality feeds the same
proof-carrying `Solved` map as `Gauss.lean` (solutions are bare variables — no degree gate, no
resolution) and one `ConstraintSystem.substF`. Prime `p` only (root membership needs an integral
domain; re-checked at runtime as in `busPairCancelPass`).

**Bound sources** (`anyVarBound`, env-conditional on the system's own satisfaction):
1. raw range-check slots via `findVarBound` (`DomainProp`) — covers the high limbs (13-bit);
2. **scaled slots** (`scaledSlotBound`): the low limb's checked slot is `4⁻¹·(x − F)` with `F` a
   degree-2 flag polynomial, so `linearize` fails on it — a new constant-coefficient
   decomposition `Expression.splitAt` (`e = k·x + r`, `r` opaque and possibly nonlinear) handles
   it. The slot value is fact-bounded (`slotBound`), the offset part enumerates the flag
   variables' proven finite domains (`findDomainAlg` booleanity, ≤ 16 points), and
   `ZMod.val_add_of_lt`/`val_mul_of_lt` carry the no-wrap integer arithmetic:
   `x.val < m.val·(bound−1) + Wmax + 1`.

The scan groups two-root candidates by key `(k, A.terms, A.const, δ)` and re-checks a decidable
pair certificate (`rpCheckPair`) inside the adoption proof, so the scan itself is proof-free.
**Runtime trap**: booleanity `b(b−1) = 0` is itself two-root (gap 1), which made every boolean
variable an expensive-to-reject candidate pair — the first run of apc_005 exceeded 35 minutes.
A root-gap prefilter (`min(g.val, p − g.val) ≥ 256`, which the pair condition could never pass
anyway) restores it to seconds. Wired into `cleanupCycle` after `hintCollapse`; the fixpoint
chains the stages (high limbs key-match only after the low limbs unify, equal bases only form
after busUnify/pairCancel — each next cycle picks up what the previous one exposed).

`lake build` green; all three `maintainsCorrectness` theorems still
`{propext, Classical.choice, Quot.sound}`-only; `check-proof-integrity.sh` passes.

**Impact.** apc_005 / apc_044 / apc_067: **1683 → 1555 vars (−128 each**, the predicted 64 low
+ 64 high limb pairs; powdr keeps 1808); apc_005 wall-clock 14.2 s at this commit. A 10-case
sample across the other size classes is byte-identical. Full 100-case sweep (before → after,
baseline re-measured at this commit's parent):

- **variables: 4.082× → 4.222× aggregate (3.605× → 3.644× geomean)** vs powdr's 4.092×/3.787×
  — **apc-optimizer takes the aggregate variable lead for the first time**; per-case wins 15 → 17
- bus interactions 2.922× → 2.924× (downstream cascade), constraints 8.801×/9.918× unchanged

Left on the table (see `docs/ideas.md`): the unification leaves the duplicate's carry
constraints and range checks behind as *syntactically identical* copies — a duplicate-dropper
would convert the remaining redundancy into constraint/bus wins; and powdr's cross-offset
chaining (`ptr+4` sharing the high limb) needs page-crossing reasoning beyond equal-address
unification.

### 58. Syntactic duplicate removal (`Dedup.lean`) — collect what unification leaves behind

Entry 57's limb unification substitutes one variable for another, which turns the eliminated
decomposition's two carry constraints and its raw-slot range check into **literal copies** of
the survivor's. Nothing dropped them: `trivialConstraintDropPass` only removes identically-zero
constraints, and a `List.filter` cannot express "keep the first occurrence" — identical elements
get identical predicate values. (Before entry 57 the optimized outputs contained no syntactic
duplicates at all, so this pass would have been a no-op — measured as part of the entry-56-era
census on the old line.)

**The pass (`Implementation/OptimizerPasses/Dedup.lean`, fact-free `VerifiedPass`).** Constraints
dedup via `List.dedup` — `satisfies` only consults membership, so which occurrence survives is
irrelevant and correctness is `List.mem_dedup`. Stateless interactions dedup by an explicit
keep-first recursion carrying the kept-so-far list; three small lemmas discharge `PassCorrect`
via `ofEnvEq`: every kept interaction is original (`dedupStateless_subset`), every original is
kept or already seen (`dedupStateless_covers` — the dropped copy's obligation transfers from its
kept twin), and both the syntactic stateful sublist and the active∧stateful *evaluated* message
list are untouched (`_statefulFilter`/`_evalFilter` — so `sideEffects` stays *equal* and
`admissible` transfers). Stateful duplicates are deliberately kept: two sends of the same
message are two sends. Wired into `cleanupCycle` right after `rootPairUnifyPass`.

`lake build` green; all three `maintainsCorrectness` theorems still
`{propext, Classical.choice, Quot.sound}`-only; `check-proof-integrity.sh` passes.

**Impact.** apc_005-class: **841 → 713 constraints (−128) and 829 → 765 bus interactions (−64)**
per block at unchanged 1555 vars — the 64 unified pairs' two carry constraints and one raw-slot
range check each (the flag-dependent scaled check survives: its flag polynomial differs per
access, so the copies are not syntactic — see `docs/ideas.md`). 9-case sample across the other
size classes byte-identical. Full 100-case sweep (before → after):

- variables **4.222×/3.644× unchanged** (the pass is variable-neutral by construction)
- **bus interactions: 2.924× → 3.006× aggregate (2.442× → 2.466× geomean)**
- **constraints: 8.801× → 9.500× aggregate (9.918× → 10.144× geomean)**

### 59. Flag unification across duplicate scaled range checks (`FlagUnify.lean`)

Entry 58 left the unified decomposition's *scaled* low-limb check behind: its flag polynomial
uses the eliminated access's own flag variables, so the copy is not syntactic — and it is not
droppable either, since that check is exactly what pins those flags (the divisibility of the
scaled slot). But the flags are provably *equal* to the survivor's: both checks decompose the
**same** shared limb as `x = m·u + W` (`Expression.splitAt`, slot value `u` fact-bounded, `W`
the flag-polynomial value), so `W_X.val = W_Y.val` — both are the residue of `x.val` under
`m.val` (`residue_uniq`, `ZMod.val_add_of_lt`/`val_mul_of_lt` no-wrap arithmetic, per-point
`W < m` over the joint flag box) — and on every joint flag point with equal offset values the
certificate demands the target components agree (≤ 32 points, `findDomainAlg` booleanity
domains). Certified equalities feed the same `Solved`/`substF` machinery; the pass runs between
`rootPairUnifyPass` (which shares the carrier limb) and `dedupPass`.

The certificate is deliberately *componentwise*: it only accepts a flag pair whose equality
holds at every offset-equal point. Measured on apc_005-class blocks exactly **one of the two
flag components certifies** per pair — the two accesses' encodings relate the other component
non-componentwise — so the checks do not become fully syntactic duplicates and the bus count
stays; the remaining component would need a derived-variable substitution `b := f(a₀, a₁)`
(nonlinear solution, degree-guarded), noted in `docs/ideas.md`.

`lake build` green; all three `maintainsCorrectness` theorems still
`{propext, Classical.choice, Quot.sound}`-only; `check-proof-integrity.sh` passes.

**Impact.** apc_005-class blocks: **1555 → 1491 vars (−64) and 649 constraints (−64**, the
unified flags' booleanity copies collected by `dedupPass`); bus interactions unchanged. 9-case
sample byte-identical. Full 100-case sweep (before → after):

- **variables: 4.222× → 4.286× aggregate (3.644× → 3.655× geomean)** vs powdr's 4.092×/3.787×
- **constraints: 9.500× → 9.854× aggregate (10.144× → 10.214× geomean)**
- bus interactions 3.006×/2.466× unchanged

### 60. Optimizer runtime: share `flagUnify`'s pair-level certificate work (effectiveness unchanged)

Pure performance work in the entry-53 style. Profiling apc_005 put **`flagUnify` at 17.4 s of
the 30.8 s total (57%)**; stage instrumentation (temporary `fuprof` command, since reverted)
showed all of it inside `fuCheck` — 256 calls per cleanup iteration (64 matched pairs × 4 flag
combos) at ~10–28 ms each, and iterations 3–6 spending ~10 s re-rejecting certificates that can
never pass after the flags unify. Each call redid the *pair-level* work — the slot-bound
probes (`payload.map constValue?` folds), both `splitAt`s, `findDomainAlg` over every
constraint, the ≤32-point joint enumeration, and **dozens of runtime `ZMod` inversions** (every
`k⁻¹` occurrence re-runs the extended-gcd inverse; entry-54's gotcha in a new costume).

**Fix (value-identical by construction):** `fuCheck` is now *defined* as
`fuPairData?` (all pair-level work, inversion hoisted into a single `let m := k⁻¹`, the
enumerated point list bound once and reused for both the bound check and the `pts` table)
composed with `fuCheckWith` (memberships, disequality, and the pointwise agreement scan). The
scan calls `fuPairData?` once per matched pair and `fuCheckWith` per flag combo; the adoption
proof re-checks `fuCheck` through the same definition, so the accepted set is unchanged
definitionally. The `fuCheck_sound`/`fuCheck_vars` proofs re-thread through the split (same
case chain, inverted on `fuPairData?`).

A hash-prefilter for `rootPairUnify`'s seen-key scan was also tried and **measured zero**
(3.06 s → 3.02 s ≈ noise — the scan is not where its time goes); it was reverted rather than
landed. Written-in-advance cost models remain undefeated in their wrongness.

**Validation:** A/B binaries (stash-built reference at the parent commit) byte-identical on the
13-case entry-53 set (`apc_001/003/005/006/008/010/014/028/047/056/069/092/100` — vars,
constraints, bus all equal) plus a **full-render diff on apc_005** (identical). `lake build`
green; `check-proof-integrity.sh` passes; axioms unchanged.

**Impact (profiler, apc_005):** flagUnify **17.4 s → 5.3 s (3.3×)**; end-to-end run
**30.8 s → 18.0 s (1.7×)**. apc_006/apc_100 unaffected (flagUnify does not fire there).

Remaining bottlenecks (documented for the next agent): `flagUnify` 5.3 s — the per-pair
residual is `findDomainAlg` over the full constraint list (×4 vars) plus the plain
`Expression.eval` per enumeration point (the entry-54 `evalWith` treatment applies), and
iterations 3–6 still pay 64 pair-datas each for zero adoptions; `rootPairUnify` 3.0 s — *not*
the seen-scan (measured), so likely `rpCandidates`'s per-variable `splitAt`+`LinExpr.norm`
over every constraint every iteration; `domainFold` 3.4 s — the pre-existing
`ImprovingRuntime.md` lead #1 (`constOnSurvs` still on per-node-instance `eval`).

### 61. Measurement: free-variable removal and smarter disconnected-witnesses have no remaining targets

Measurement only, no code change (in the spirit of entry 42). Two long-standing candidates — the
`docs/ideas.md` "smarter witnesses for `disconnectedComponentPass`" item (entry 43's "dominant
unremoved pattern": orphaned register-read byte-decompositions needing a non-zero witness) and
powdr's `remove_free_variables` (drop a variable occurring in exactly one solvable
constraint/stateless interaction) — were sized against the current optimizer's outputs before
implementing. Both are **empty**:

- **Disconnected variables: 0** on every sampled case (apc_001/003/008/010/014/047/056/069) —
  the entry-43 orphan pattern has been consumed by the passes that landed since (the entry-50
  received-byte facts, entry-51 zero-register pinning, and the entry-57–59 unification/cleanup
  chain). The all-zero witness never fails on anything anymore because nothing disconnected
  survives at all.
- **Single-occurrence variables: 0–1 per case**, and the singleton is always the `hcinv#`
  reciprocal hint from `hintCollapse` — whose defining constraint `a·inv − cmp = 0` is *not*
  unconditionally solvable for it (`a` may be zero), so it is not removable under powdr's rule
  either, and it is load-bearing for the is-zero gadget.

The `docs/ideas.md` entry is updated accordingly. Together with entry 55 (degree-bounded
inlining structurally blocked), two of the three Tier-1 variable candidates from the Rust-vs-Lean
comparison are now measured dead on this benchmark; the live remainder of that tier is the
constraint/limb-splitting shape (entry 36 lineage).

### 62. Measurement: limb splitting is basis-neutral; the real residual gaps are the signed-comparison gadget and read-read data sharing

Measurement only (entry-42 style), via a **variable-set diff** between our optimized outputs and
powdr's exports on loss cases (apc_003: 133 vs 131; apc_047: 91 vs 87). Findings:

1. **Constraint/limb splitting (the entry-36 lineage) is variable-neutral here.** Our surviving
   `…timestamp_lt_aux__lower_decomp__1_*` high limbs pair **exactly 1:1** with powdr's surviving
   `…prev_timestamp_*` columns (16↔16 on apc_003, 12↔12 on apc_047). powdr does not eliminate
   the less-than witness; it solves the *high limb* away (`d1 = (now − prev − 1 − d0)·2⁻¹⁷`,
   degree-1, substituted into its range check) and keeps `prev_timestamp`, while we solve
   `prev_timestamp` away and keep both limbs. Different basis, same count. Do not build a
   splitter for variables' sake; at most it trades a 12-bit range check's operand shape.
2. **The whole apc_003-class gap (+2/case) is the signed-comparison gadget**: we keep
   `{a_msb_f, b_msb_f, cmp_lt}` where powdr keeps `{cmp_result}` — the msb-extraction booleans
   survive on our side. New, previously uncatalogued target (`docs/ideas.md`).
3. **The apc_047-class gap (~+3/case) is duplicated read data**: powdr keeps one copy of the
   same-address read words (`b__*`, `writes_aux__prev_data__*`) across consecutive accesses
   where we keep several. Hypothesis: our receive-equals-send chaining (`busUnify`) is blocked
   because the access addresses are still not *syntactically* equal — the entry-59 residual
   (one flag component per access pair relates non-componentwise). Finishing that flag story
   (the derived-variable interpolation in `docs/ideas.md`) would likely unlock this cascade.

With entries 55 and 61, all three Tier-1 variable candidates from the Rust-comparison survey
are now measured dead as scoped; the live variable work is items (2) and (3) above.

### 63. Diagnosis: the two entry-62 gaps, pinned down (XOR flag relation; sign-split comparison gadget)

Measurement/diagnosis only, completing entry 62 with the concrete shapes.

1. **The entry-59 flag residual is XOR.** Probing the persisting scaled-check pairs on apc_005
   (via `fuPairData?`'s own point tables): after entry 59 each pair's flag sets already share
   one variable, and the compatible joint points for the remainder read off as exactly
   `c1 = a0 ⊕ a1` — e.g. carrier `mem_ptr_limbs__0_3`, X flags `{567_0, 567_1}`, Y flags
   `{567_1, 575_1}`, compatible points `{(0,0,0),(1,1,0),(1,0,1),(0,1,1)}`. As a field
   polynomial `a0 + a1 − 2·a0·a1` (degree 2), so plain entailed substitution is
   **degree-blocked twice over**: `c1`'s booleanity becomes degree 4 (> identities 3) and the
   Y check's payload `F_Y(a1, c1 := ⊕)` becomes degree 3 (> bus 2). Eliminating the ~64
   remaining `c1`s per apc_005-class block therefore needs a *composite, singly-guarded* pass:
   entailed nonlinear substitution + a box-tautology constraint drop (the substituted booleanity
   vanishes on the boolean box) + a pointwise-equal bus-payload replacement (the substituted
   check's slot equals the survivor's on the box). All three pieces have precedents
   (`Solved`/`substF`, the `fuCheck` box machinery, `filterBusEntailed_correct`), but composing
   them under one `guardDegree` with intermediate over-bound states is its own project.
2. **apc_047 has zero scaled-check pairs** in its final output — entry 62's hypothesis that its
   duplicated read-data words are blocked on the flag residual is **wrong for that case**; its
   read-read duplication needs a separate diagnosis (the addresses there presumably differ in
   more than a flag component).
3. **The sign-split comparison gadget (apc_003 class, the +2/case).** `a_msb_f` is pinned by its
   own two-root constraint `(a__3 − f)(a__3 − f − 256) = 0` — a *definition* (limb minus sign
   bit), not a duplicate, so `rootPairUnify` does not apply — plus the byte pair-check
   `[a_msb_f, b_msb_f, 0, 0]` and a `diff_marker` chain deciding `cmp_lt`. powdr keeps one
   `cmp_result` for our three `{a_msb_f, b_msb_f, cmp_lt}`. The domains are *parameterized*
   (`f ∈ {a3, a3 − 256}`), so `reencode`/`domainBatch` (constant-domain machinery) cannot
   compress the group either; a folding pass would need parameterized-domain reasoning or
   derived-column substitution with the same composite-guard treatment as (1).

### 64. XOR flag fold: three of five pieces built and firing; blocked on stateful-payload and selection-constraint degrees

Implementation attempt on log 63's finding 1 (`FlagFold.lean`, committed **unwired**). The
composite `flagFoldPass = fxSubstPass ∘ boxTautoDropPass ∘ pointwiseDupDropPass` under a single
degree guard. Stage probe on apc_005's optimized output:

- `fxSubstPass` **fires: 1491 → 1427 vars (−64)** — the certified interpolation `c1 := a0 ⊕ a1`
  (built from `fuPairData?`'s own compatible-point tables, validated pointwise by `fxCheckWith`,
  entailed by the residue argument via `fxCheck_sound`) substitutes every remaining pair flag.
- `boxTautoDropPass` replaces the degree-4 substituted booleanities by `0` (multi-variable
  constraints vanishing on their proven domain box; single-variable constraints are never
  replaced, keeping the `findDomainAlg` sources — non-circular by construction).
- `pointwiseDupDropPass` **fires: 765 → 701 bus (−64)** — stateless interactions pointwise-equal
  on the box to an earlier *first-of-class* twin are dropped (`filterBusEntailed_correct`
  ported from the entry-56 line with `hok` generalized to be multiplicity-conditional; the
  depth-1 first-of-class rule avoids chain induction).
- **But `withinDegree = false` at every stage**: the substituted flag also sits in the
  **stateful memory address payloads** (`limbsum − F(a1, c1)`, degree 3 after substitution —
  no pass may drop or alter stateful interactions) and in the degree-3 **data-selection
  constraints** (degree 4 after). The guard rejects the composite, so the wired pipeline is a
  no-op at +74 s per apc_005 run — hence unwired at this commit.

**What completing it needs** (both specified, neither trivial):
(D) a *compatible-point-entailed payload rewrite* — replace the eliminated access's address
expression by the survivor's (already degree-legal; pointwise-equal under the pair certificate,
i.e. `slotEqCert` refined from box-equality to compatible-point equality with both checks
retained); sideEffects stay *equal* because the evaluated messages are. (E) a multilinear
reduction (`b² → b` on boolean-domained variables, box-certified) for the selection
constraints — the general contextual rewriter sketched in the design documents. (D) unlocks the
address-side; (E) the constraint side; with both, the probe numbers above (−64 vars, −64 bus
per apc_005-class block) become landable.

### 65. Box-certified multilinear rewriting completes the XOR flag fold (`BoxRewrite.lean`)

The missing piece from entry 64, and it subsumes both gaps at once: a pass that rewrites every
**over-bound** expression of the system to its multilinear reduction (`b² → b` on
small-domain variables), accepting each rewrite only under a decidable certificate — on every
point of the expression's small-domain box, both forms **partially evaluate to the same affine
form** in the remaining symbolic (e.g. data) variables (`linearize` + canonical normalized
comparison; soundness via `eval_substF`/`envF` restriction, `linearize_eval`, and permutation
sums). The reduction itself is heuristic monomial expansion (exponent capping on box variables,
64-monomial cap) and carries no proof; the certificate re-verifies pointwise. Single-variable
constraints are never rewritten (the `findDomainAlg` sources — same non-circularity as the
entry-64 parts), and rewrites that would introduce variables are rejected by a decidable guard.

The completed composite `flagFoldPass' = fxSubst ∘ boxRewrite ∘ boxTautoDrop ∘ pointwiseDupDrop`
under one degree guard: the XOR substitution fires, the rewriter legalizes the substituted
address payloads (degree 3 → 2) and selection constraints (degree 4 → 3), the tautology and
duplicate collectors clean up. Stage probe on apc_005: `wd=false` after substitution,
**`wd=true` after the rewrite**, and the guard now accepts.

`lake build` green; all three `maintainsCorrectness` theorems still
`{propext, Classical.choice, Quot.sound}`-only; `check-proof-integrity.sh` passes.

**Impact.** apc_005-class blocks: **1491 → 1427 vars (−64), 649 → 585 constraints (−64),
765 → 701 bus (−64)** each. 9-case sample across the other size classes byte-identical. Full
100-case sweep (before → after, baseline = the entry-60 line):

- **variables: 4.286× → 4.352× aggregate (3.655× → 3.667× geomean)** vs powdr's 4.092×/3.787×
- **bus interactions: 3.006× → 3.077× aggregate (2.466× → 2.482× geomean)**
- **constraints: 9.854× → 10.235× aggregate (10.214× → 10.292× geomean** — closing on powdr's
  10.311× geomean)

Runtime cost: apc_005 ~18 s → ~80 s (the composite's scans run every cycle) — a known
entry-53-style target for a follow-up perf pass; not intractable, and effectiveness lands
first. The `boxRewritePass` is general machinery: it is the "contextual polynomial reduction"
enabler the early design surveys called for, and the sign-split comparison gadget (entry 63
item 3) is its natural next customer.

### 66. Perf: the flagFold composite from 67 s to 1.7 s on apc_005 (entry-65 follow-up)

The `ImprovingRuntime.md` pass over the entry-64/65 additions. Baseline: `flagFoldPass'` cost
66.9 s of apc_005's ~81 s run. Staged sub-pass timings (temporary `ffprof` command) plus layered
scan decompositions localized four mechanisms, landed as three commits:

1. **`findDomainAlg` gates its scan on `Expression.mentions`** (`DomainProp.lean`). `rootsIn`
   runs `linearize` — allocation-heavy normalization — per (variable, constraint) probe, so
   every domain lookup scanned all ~650 single-variable constraints at full price. A constraint
   that does not mention the variable can only yield a root list through the
   unsatisfiable-constant case (`rootsOfTerms` on an empty term list), so skipping it never
   loses a live domain. This one gate took boxTauto from 15.4 s → 0.2 s (with the cache below)
   and sped up every caller: flagUnify, `slotEqCert`, `brCert`.
2. **Hoisted scan invariants** (`FlagFold.lean`, `BoxRewrite.lean`). `btCert`, `slotEqCert`/
   `msgEqCert`, `pdFirst`/`pdKeep`, and `brRw`/`brCert` all refiltered `singleVarCs all` per
   candidate (in `brRw`'s case per *variable* of every over-bound expression); they now take
   the precomputed list, bound once per pass invocation. boxRewrite's fold-iteration stage:
   4.4 s → 0.16 s. **Lean gotcha worth remembering**: precomputed values must be passed as
   *plain arguments* — a def-local `let` in front of a trailing `fun c => …` is re-evaluated on
   every application by arity expansion, and hoisting the partial application
   (`let keep := btKeepCond cs`) does **not** prevent it (first attempt hung: O(n) cache
   rebuilds per constraint).
3. **boxTauto memoized-domain prefilter** (`btPre`): a faithful mirror of `btCert` over a
   per-pass `HashMap` of `findDomainAlg` results gates the certificate; the certificate
   re-checks with the real scan, so the cache carries no proof obligation (the `BusFacts`
   philosophy applied to perf).
4. **`slotEqCert` requires a shared carrier** (`x ∈ e'` via a ZMod-free `mentions` walk) before
   any `splitAt`. The pointwiseDup prefix scans visit 2.5M interaction pairs on apc_005; layered
   timing showed the skeleton (findIdx?, busId, multiplicity, payload-BEq layers) costs 0.26 s
   and *everything else* was `splitAt`/`coeffAt` per-node ZMod ring ops — the runtime-`p`
   instance-reconstruction tax (entry 53). The dropped arm — carrier with a fully cancelled
   constant coefficient, absent from `e'` — cannot survive the constantFold/normalize passes
   that run ahead of the composite every cycle. pointwiseDup: 4.1 s → 0.43 s.

Dead ends, killed by measurement: a domain-`HashMap` for pointwiseDup (cache build alone cost
9.1 s over payload vars and saved nothing — domains were never the scan's cost); iterating var
*occurrences* instead of `eraseDups` (repeated flag variables re-ran certified arms per
occurrence: 4.1 s → 18.7 s).

Validation per the playbook: 13-case `run` outputs and the full apc_005 render **byte-identical**
against a 9e703ed reference binary (this also empirically confirms the two "cannot fire on real
inputs" arguments above — items 1 and 4 are conservative narrowings, sound by construction
either way). Effectiveness unchanged by construction. apc_005: **81 s → 12.7 s**; flagFold
**66.9 s → 1.7 s** (iter 0: 0.65 s; fold iteration: 0.44 s). The profile is now led by
pre-existing passes — domainFold 3.3 s, reencode 1.7 s, domainBatch 1.6 s — so the composite is
no longer the pipeline's bottleneck. `lake build` green at every commit; proof integrity clean.

### 68. Redundant byte-check removal (C2): drop entailed bitwise byte checks (`RedundantByteDrop.lean`)

Blocks keep stateless bitwise-lookup interactions whose only obligation is "this operand is a
byte": the self-check `[x, x, 0, 1]` (`BusFacts.byteCheck`), the XOR-with-zero `[x, 0, x, 1]`
(`BusFacts.xorZeroCheck`, added this entry), and the packed pair `[x, y, 0, 0]`
(`bytePairBus` + `byteCheck`). When an operand's byte-ness is already guaranteed by the *rest* of
the retained system — a raw slot of a retained memory receive (`slotBound`), a retained range check
(`findVarBound`), or a constraint that pins it on every selector-flag branch (`deepBoundOk`, prime
`p`) — the check is *entailed* and dropping it is sound, variable-neutral, and removes one bus
interaction. Checks on freshly *computed* values (byte-ness enforced only by the check itself) are
**kept** — `byteJustified` cannot justify them — matching powdr (drop on memory-read words, keep on
ALU results). `redundantByteDropPass` runs in the pipeline coda, after the cleanup fixpoint, so it
does not starve the mid-loop enumeration passes of the finite-domain knowledge a raw byte-check slot
carries.

Reuses existing machinery: `ConstraintSystem.filterBusEntailed_correct` (from `FlagFold.lean`; the
drop's acceptance is conditional on satisfaction of the *filtered* system — exactly "redundant"),
`byteJustified`/`deepBoundOk` (from `BusPairCancel.lean`), and a **non-circular justification base**
(operands justified only against interactions this pass can never drop, so two identical checks
can't justify each other). `byteCheckOperands?` recognises all three forms; soundness threads
through `byteCheck_sound`/`xorZeroCheck_sound`/`bytePairBus_sound`. Only new audit-free surface is
the `xorZeroCheck` `BusFacts` field + its OpenVM instance (`bitwiseLookup` accepts `[x,0,x,1]` iff
`x` is a byte).

Coverage checked against powdr per case: the pass drops all three forms whenever the operand is
byte-justified; the residual bitwise interactions it leaves are genuine XOR *operations* (not byte
checks) or checks on computed values whose byte-ness is not otherwise entailed — which powdr removes
only by eliminating the variable (C4) or deeper structural reasoning, outside C2's scope.

`lake build` green; all three `maintainsCorrectness` theorems still `{propext, Classical.choice,
Quot.sound}`-only; `check-proof-integrity.sh` passes.

**Impact.** Variable- and constraint-neutral by construction (a coda `filterBus`). Full 100-case
sweep vs the C1 (entry-67) line, per-case: **bus dropped on 57 cases, 0 regressions**; totals
variables 28645 (unchanged), constraints 11215 (unchanged), bus 18887 → 18341 (−546). Aggregate vs
powdr:

- **bus interactions: 3.081× → 3.173× aggregate (2.486× → 2.581× geomean)** vs powdr's 3.480×/2.822×
- variables 4.411×/3.768× and constraints 10.593×/11.585× unchanged

Largest drops on memory/shift-heavy blocks (apc_037 −110 bus, apc_071 −48, apc_100 −35, apc_006 −30).
Runtime smoke set vs C1: **+0% total** (one coda pass; worst case apc_100 +1.5%).

## Entry 69: width-0 range-check → equality (C3)

**Idea.** powdr-exported address-computation blocks keep, on the variable range checker, a family of
**width-0 range checks** `[expr, 0]` (multiplicity 1). A 0-bit range check asserts `expr < 2⁰ = 1`,
i.e. `expr = 0` — it is powdr/OpenVM's encoding of "this linear form is exactly zero", pinning an
intermediate address/data limb to a combination of others (e.g. `-a__2 + b__3 = 0`,
`7864320·(a__3 − b__0) = 0`). Because the optimizer's Gaussian elimination consumes only *algebraic*
constraints, these equalities — carried on the **bus** — are never used to eliminate a variable, so
the intermediate limbs (the `a`/`b`/`c` families) survive. powdr substitutes them away.

`zeroWidthRangePass` converts each such interaction into the algebraic constraint `expr = 0` and
drops the interaction — they have the *same* satisfying set (a stateless range check `[x, 0]` is
accepted iff `x = 0`, new fact `BusFacts.zeroRangeEq`). Placed first in the cleanup cycle, it feeds
the equalities to same-cycle Gauss, which eliminates the intermediate variables and cascades: a
variable win, plus a bus win (the dropped interaction and the range checks the eliminated variables
no longer need).

**How.** New audit-free `BusFacts` field `zeroRangeEq busId` — "on a stateless bus, `[x,0]` mult-1 is
accepted iff `x = 0`" — proven for the OpenVM `variableRangeChecker` (`violates [x,0] = false ↔ x.val
< 2⁰ = 1 ↔ x = 0`). The pass is two `PassCorrect` steps via `andThen`: (1) *add* the equality
constraints, keeping every interaction — `PassCorrect.ofEnvEq`, side effects/admissibility literally
unchanged (same interactions), completeness from "an accepted width-0 interaction forces its value to
zero"; (2) *drop* the now-entailed interactions via `ConstraintSystem.filterBusEntailed_correct`
(each dropped check is stateless and accepted under the filtered system, which retains the step-1
equality). Gated on `(1 : ZMod p) ≠ 0` (every prime field; identity on `ZMod 1`).

`lake build` green; all three `maintainsCorrectness` theorems still `{propext, Classical.choice,
Quot.sound}`-only; `check-proof-integrity.sh` passes.

**Impact.** A faithful census what-if (apply the sound transform to apc's own output, re-optimize)
predicted the exact realized numbers. The pattern occurs on 3 of the 100 cases (address-computation
loads/stores); the pass is a provable no-op on the other 97. Full 100-case sweep vs the C2 (entry-68)
line — **circuit sizes changed on exactly 3 cases, 0 regressions**:

- **apc_071: 453 → 413 vars (−40), 407 → 335 bus (−72)**, constraints unchanged (53)
- **apc_020: 800 → 789 vars (−11), 457 → 435 bus (−22)** — already ahead of powdr (800 < 850), lead extended
- **apc_037: 733 → 730 vars (−3), 793 → 789 bus (−4)**
- totals across the 3: **−54 variables, −98 bus interactions, 0 constraints**

Aggregate vs powdr: **variables 4.411× → 4.420× agg (3.768× → 3.772× geo)**, ahead of powdr's
4.092×/3.787×; **bus 3.173× → 3.190× agg (2.581× → 2.588× geo)** vs powdr 3.480×/2.822×; constraints
unchanged (10.593×/11.585×). Runtime smoke set (13 cases, none width-0-bearing) vs C2: **−0.9% total**
(within noise; the only cost is one filter/filterMap scan per cleanup iteration).

**Follow-up.** #EQ closes ~40 of apc_071's 123-variable gap to powdr; the residual `a`/`c` families
(~64 vars on apc_071) are the intermediate effective-address bytes powdr derives directly from
`base + offset` — a derived-column (reencode-class) elimination (see docs/ideas.md), higher proof
cost. The same faithful-what-if pass also confirmed three **washes** (do not build): the
genuine-two-root carry-witness follow-up (add a boolean carry ⇒ net 0 vars — the −249-on-apc_037
ceiling was unsound one-root collapse), the N2 signed-compare msb fold (basis rename; apc/powdr both
keep 2 gadget vars), and the C4c timestamp split (`2×lower_decomp` ↔ `lower_decomp + prev_timestamp`,
equal counts).

## Entry 70: bitwise-XOR equality extraction, 0-operand (C4a)

**Idea.** powdr-exported memory/shift blocks keep, on the bitwise-lookup bus, interactions
`[x, y, z, 1]` (op 1: `z = x ⊕ y`, `x`,`y` bytes) with **one operand the constant 0**. The XOR then
linearizes to an equality: `[0, y, z, 1] ⟹ z = y`, `[x, 0, z, 1] ⟹ z = x`. These pin an intermediate
loaded-data / effective-address byte (the `b`/`a`/`c` families — essentially the whole residual
variable gap to powdr) to another variable, but Gaussian elimination — consuming only *algebraic*
constraints — never uses them, so the intermediate limbs survive. powdr represents everything with
the canonical loaded value.

`xorEqExtractPass` recognizes each 0-operand XOR interaction and **adds the entailed equality**
`z − y` (resp. `z − x`) as an algebraic constraint, keeping the interaction (still imposes byte-ness).
Placed early in the cleanup cycle, the equalities feed same-cycle Gauss, which eliminates the
intermediate variables and cascades — a variable win plus a bus win (the range/bitwise checks the
eliminated variables no longer need).

**How.** New audit-free `BusFacts` field `xorZeroEq busId` — "an accepted mult-1 `[0,y,z,1]` forces
`z = y`, `[x,0,z,1]` forces `z = x`" — proven for OpenVM's `bitwiseLookup` from `Nat.zero_xor` /
`Nat.xor_zero`. The pass is a `ConstraintSystem.addConstraints_correct`: the equalities are entailed
by the interactions' acceptance (completeness), soundness drops the added constraints, and adding
constraints touches no interaction so side effects/admissibility are unchanged. Gated on
`(1 : ZMod p) ≠ 0` (identity on `ZMod 1`).

`lake build` green; all three `maintainsCorrectness` theorems still `{propext, Classical.choice,
Quot.sound}`-only; `check-proof-integrity.sh` passes.

**Impact.** Faithful census what-if (#XE0) predicted the realized numbers. Broad: **38 of 100 cases**
carry const-operand XOR interactions. Full 100-case sweep vs the C3 (entry-69) line: **16 cases
changed, 0 regressions**; totals **−449 variables, −554 bus interactions, 0 constraints**. Biggest:
apc_071 413→349 vars / 335→279 bus (now 349 vs powdr 330), apc_006 −64 vars, apc_019/012/049 −64 vars
each, apc_089 −40, apc_037 −16 vars / −148 bus, apc_100 −24. Aggregate vs powdr: **variables
4.420× → 4.490× agg (3.772× → 3.810× geo)** — well ahead of powdr's 4.092×/3.787×; **bus 3.190× →
3.290× agg (2.588× → 2.629× geo)** vs powdr 3.480×/2.822×; constraints unchanged. Runtime smoke set
vs C3: **−3.9% total** (the pass pays for itself — eliminating variables early shrinks the circuit
for later passes; apc_056/069/092 −80%, apc_008 −21%, apc_014 −19%).

**Follow-up (C4b).** The 255-operand XOR cases (`[x, 255, z, 1] ⟹ z = 255 − x`) stack on this pass —
they need the byte-complement identity `Nat.xor n 255 = 255 − n` (n < 256); +16 vars on apc_071.

### 69. Finite-domain byte justification generalises the keccak byte-source fix (`BusPairCancel.byteJustified`)

**Context / investigation.** Entry (#95) added a byte bound on the bitwise **result** slot so keccak's
memory pairs (whose data are XOR outputs) could be byte-justified and cancelled. This entry
investigates whether that memory-cancellation mechanism transfers to the openvm-eth set. Profiling
(a temporary `dbgcancel` harness running `busPairCancel` alone on each optimized circuit and
reporting, per blocked send, the `mid`/`pre`/`just` breakdown and the unjustified byte slots)
found:

- The blocked-memory-chain **trigger does occur** in openvm-eth — ~12 cases have a chain whose
  first send/receive pair fails byte justification (`just=false`), which — being the earliest
  active send — blocks the whole chain.
- The unjustified data are **not** XOR results. Two families dominate: (a) **sign-extension**
  high limbs `255·b` where `b` is a boolean most-significant-bit (`apc_010` etc.), and (b) an
  **AND gadget** `b = x AND y` encoded via the adder identity `x + y − 2b = x⊕y` (`apc_037`).
  Family (a) is a clean, general "single variable over a small finite domain" shape.

**The generalization (implemented).** `byteJustified` now also accepts a **single-variable
expression whose variable ranges over a small constraint-derived finite domain** and which
evaluates to a byte at every point of that domain (`domainByteJustified` / `exprPointByte`, gated
on prime `p`). For `255·b` with `b`'s boolean domain `{0,1}` (from `b·(b−1)=0`, found by
`findDomainAlg`), the two points evaluate to `{0, 255}`, both `< 256`. Soundness
(`domainByteJustified_sound`): `findDomainAlg_sound` puts `env x` in the enumerated domain, and
the checked point's substituted fold is a constant equal to `e.eval env` (`eval_substF` +
`envF_eq_self`), so the byte bound transports. Purely additive to `byteJustified`; no audited
surface, no new axioms; `BusFacts.trivial` unaffected. This subsumes the raw-byte-variable case
and the XOR-result-limb case as instances of "e is a byte at every point of its variable's
domain."

**Impact and the *real* binding constraint.** With this change the sign-extension limbs are
byte-justified (`just` flips to `true`), but the openvm-eth gain is only marginal — bus
interactions **3.324× → 3.333× agg** (2.638× → 2.644× geo) over the 100-case sweep, variables
unchanged (4.491×/3.810×, still ahead of powdr's 4.092×/3.787×), no case regressed; **keccak
unchanged** (3056 vars / 2862 bus / 120 constraints, identical — its cancellations were already
captured by the memory/dedup passes merged since #95). The reason: unblocking `just` exposes a
**second, conservative blocker** — `busPairCancel`'s completeness side condition requires the
dropped send to be the **earliest active same-address send** (`admissibleMemoryBus_dropPair`'s
`hearliest`). On the openvm-eth chains a boundary *store* of a computed value sits before the
read pairs as an earlier active same-address send with no syntactic match, so every later read
pair is refused (`pre=false`). Byte justification and the earliest-send condition must **both**
be relaxed for the chains to cascade; this entry lands the first half (general and correct on its
own), and records the earliest-send relaxation as the next step (see `docs/ideas.md`) — it is
sound (a trailing active same-address *receive* in the "before" region shields every earlier
send, so no removal exposes a mismatched consecutive pair) but touches the memory-discipline
completeness proof, so is left as a separate, carefully-scoped change. Runtime unaffected
(keccak within noise; the new path only fires where the shallow bound already failed).

### 70. Shielded pair cancellation: relax `busPairCancel`'s earliest-send completeness condition — the openvm-eth + keccak bus win

**Context.** Entry 69 landed finite-domain byte justification (sign-extension `255·b` limbs), but
the openvm-eth memory chains still didn't cascade: once byte justification passes, the *second*
blocker is `busPairCancel`'s completeness side condition, which required the dropped send `S` to be
the **earliest active same-address send** (`admissibleMemoryBus_dropPair`'s `hearliest`). Real
blocks lead an access chain with an unmatched **boundary store** (a computed value written once,
never read back identically) sitting before the read-modify-write pairs — an earlier active
same-address send — so every later pair was refused.

**The relaxation (sound).** Weaken the side condition from "no active same-address send in the
before-region `A`" to the **shield**: *every active same-address send in `A` is followed by an
active same-address receive in `A`* (equivalently, the last active same-address message in `A` is a
receive, or there is none). Soundness: dropping the pair can only expose a fresh consecutive
send→receive pair straddling the removed messages; if its send `Sx` were an active same-address
send in `A`, the shield's receive `Rp` (after `Sx` in `A`) lies strictly between `Sx` and the
exposed receive — inside the pair's middle — contradicting the "no active same-address message
between" obligation. So the trailing receive shields every earlier send and no mismatched pair
survives. This is the read-before-write discipline's actual invariant, and it admits the
boundary-store-led chains.

**Implementation.** All in the non-audited layer, no new axioms
(`{propext, Classical.choice, Quot.sound}` unchanged):
- `MemoryBusDrop.lean`: `admissibleMemoryBus_dropOne`/`_dropPair` re-proved with the shield
  precondition (the exposed-pair case now derives its contradiction from the shield receive +
  the split's clean-middle hypothesis, rather than "no send exists"); generic `filter_split` /
  `map_split` list lemmas added.
- `BusFacts.lean`: the `admissible_dropPair` field's `A`-precondition becomes the shield (a
  split-existential); `trivial` still discharges it vacuously.
- `OpenVmFacts.lean`: the field re-proved, lifting the abstract shield to
  `admissibleMemoryBus_dropPair`'s per-bus filtered form via `filter_split`.
- `BusPairCancel.lean`: `provRecv` (a provable active same-address receive), `shieldScan`/`shieldOk`
  (one O(n) right-to-left pass certifying the shield), `activeStatefulMsgs_split` (lift an
  evaluated-message split back to a syntactic split of `A`), and the rewired `checkCancel` /
  `dropPair_correct` / `findCancelGoIdx` region-`A` test.

**Impact** (combined with entry 69, this PR's total vs clean main 9844184):
- **openvm-eth** (100-case sweep): bus interactions **3.324× → 3.360× agg / 2.638× → 2.662× geo**
  (over the entry-69 3.333×/2.644×); variables unchanged (4.491×/3.810×, still ahead of powdr's
  4.092×/3.787×), constraints unchanged (10.595×/11.585×); per-case by variables still 25 W / 43
  L / 32 T — **no case regressed**. Spot: apc_010 bus 307 → 276 (powdr 239).
- **keccak** stress case: bus interactions **2862 → 2690** (4.63× → 4.93×), variables/constraints
  unchanged (3056 / 120). Runtime ~455 s (no regression; the shield pass is O(n), and more
  cancellation leaves later passes less work).

The remaining openvm-eth bus gap to powdr is now `−0.120×` agg (from `−0.156×` at clean main),
narrowed by the two entries together. Residual: the AND-gadget byte source (`apc_037`) and
range-check packing (see `docs/ideas.md`).

### 71. Tuple-range packing (`TupleRange.lean`) — bus-interaction effectiveness

powdr packs a byte check and an exact-width range check into a single `TupleRangeChecker (s1, s2)`
interaction `[x, y]` (accepted iff `x < s1 ∧ y < s2`); apc-optimizer kept them as two stateless
lookups. With `s1 = 256` and a range check `[y, bits]` of exactly `2^bits = s2`, the tuple check
imposes the **identical** obligation as the two originals together — a pure two-for-one bus win
(the byte + 13-bit `mem_ptr_limbs` pairing on memory blocks). `tupleRangePass` performs it.

Why it is sound (no audited-surface change):
- Two new proven `BusFacts` fields: `varRangeBus` (a variable-range-checker message `[x, b]` is
  accepted **iff** `b.val ≤ 25 ∧ x.val < 2^b.val`) and `tupleRangeBus` (`[x, y]` accepted **iff**
  `x < s1 ∧ y < s2`; multiplicity-1 messages break no invariant), both discharged for OpenVM
  against the concrete `violates`/`breaksInvariant`; `trivial` claims nothing, so the pass is a
  no-op without facts and stays VM-agnostic. Together with the existing `byteCheck` fact the
  packed check's obligation is exactly the conjunction of the replaced pair's (`tupleKey`).
- The correctness core is a **generic stateless two-for-one swap** (`mergeStateless2_correct`):
  replacing stateless multiplicity-1 interactions `D₁, D₂` by a stateless `C` whose obligation is
  their conjunction preserves the satisfying set, side effects, invariants and `admissible`
  verbatim — the entry-49 `mergeBytePair_correct` is the same shape, now available generically.
- The target tuple bus typically carries **no interaction in the input circuit** (powdr's
  optimizer introduces it too), so its id cannot be read off the system; the pass probes the
  `tupleRangeBus` fact over a bounded id range (max existing bus id + 65) instead.

Wired into `cleanupCycle` between `busPairCancelPass` and `bytePackPass`, so byte singles are
absorbed into tuple checks (saving 1 per single) before `bytePack` pairs the leftovers (saving 1
per two); one pair packs per invocation, drained by `iterateToFixpoint`.

`lake build` green; `optimizerWithBusFacts_maintainsCorrectness`, `simpleOptimizer_maintainsCorrectness`,
`openVmOptimizer_maintainsCorrectness` still `{propext, Classical.choice, Quot.sound}`-only; no
`sorry`/`admit`/`axiom`/`native_decide` (`check-proof-integrity.sh` passes); outputs within the
degree bound (the packed check's operands are the originals').

**Impact (bus interactions; variables and constraints unchanged on every sampled case; vs the
entry-70 `main` baseline).** apc_003 90 → **85** (parity with powdr's 85), apc_010 276 → **271**,
apc_014 156 → **151**, apc_008 63 → 62, apc_001 unchanged (its 17/12-bit checks fit no tuple
bus); apc_005 701 → 702 (+1 — a packed tuple survives where the interplay with the later
byte-check dropper would otherwise have removed a single; aggregate-invisible). The remaining
tuple gap is the byte+byte *widening* pack (second slot only needs `< s2`), which needs a
justification argument — see `docs/ideas.md`.

### 72. Runtime: inverted index for the domain-trio covered-set scans (`CoveredIndex.lean`)

**Context / profiling.** On the keccak stress case (~28.6k constraints, 13.3k bus interactions,
27.5k variables) the optimizer runs 7 cleanup-cycle iterations; `apc-optimizer profile` (accurate
since the shared pass list of #102) attributes the bulk of the time to the three finite-domain
passes, each doing an
**O(#targets × #system)** covered-set rescan — for every target variable set `xs` (one per
constraint and per bus interaction, ~42k on keccak) it `filter`s the *entire* system for the items
whose variables all lie in `xs`: baseline `domainBatch` 127.0 s, `reencode` 88.7 s,
`domainFold` 64.7 s (of a 494 s profiled total).

**Change.** New audit-free `ApcOptimizer/Implementation/OptimizerPasses/CoveredIndex.lean`: a
variable→positions inverted index (`CovIndex`, built once per pass invocation) plus
`coveredIdx idx arr Q xs`, which gathers only the items sharing a variable with `xs` (plus the
variable-less items), deduplicates the candidate positions through a `HashSet` (linear — a naive
`List.dedup` is quadratic and blows up on widely-shared variables), sorts them ascending to keep the
items' original order, and re-checks the exact predicate `Q`. Correctness needs only `coveredIdx_mem`
(every returned item is a genuine system item satisfying `Q`); index *completeness* is not required
for the proof, so the enumeration soundness lemmas are unchanged and completeness (hence
effectiveness) is verified empirically. Wired into `domainBatch` (`forcedOver`; `cs` is immutable
across the target loop, one build per invocation) and `reencode` (`buildReencode`, proof-free; the
index is threaded through `reencodeLoop` and rebuilt only on the rare accepted rewrite).

**Impact.** No audited surface touched; the three `*_maintainsCorrectness` theorems still
`{propext, Classical.choice, Quot.sound}`-only; `check-proof-integrity.sh` passes. **Effectiveness
unchanged** — full openvm-eth sweep bit-identical to `main` (variables 4.491× / 3.810× agg/geo,
constraints 10.595× / 11.585×, per-case 25 W / 43 L / 32 T), keccak output identical
(3056 vars / 120 constraints / 2690 bus). **Runtime (profile, per-pass):** `domainBatch`
127.0 → 85.2 s, `reencode` 88.7 → 53.8 s (−77 s combined; every other pass flat, confirming no
collateral change); profiled total 494 → 431 s. The `run` wall-clock timer is noisy on this machine
(baseline solo 529 s vs concurrent 449 s — ~18 % variance), so the per-pass profile deltas are the
reliable signal; a solo `run` A/B measured 529 → 378 s.

**Remaining (see `docs/ideas.md`).** `domainFold`'s covered scan feeds `foldOut_correct` (tied to
`coveredCsOf`), so indexing it needs a `coveredIdx = items.filter Q` equality lemma; the residual
per-pass time is the finite-domain enumeration itself (box scanning); the next tier is `flagFold`
and `busUnify` (per-target `cs.vars` / `List.contains` membership).

### 73. Runtime: index the domain-fold covered-set scan; hash the busUnify variable-membership check

**Context / profiling.** Building on the entry-72 inverted index (#104), the post-#104 keccak
profile (`apc-optimizer profile`, 7 cleanup iterations, ~383 s total) leaves these finite-domain / bus
hot spots: `domainBatch` 75.2 s, `domainFold` 54.6 s, `flagFold` 50.9 s, `reencode` 45.3 s,
`busPairCancel` 45.2 s, `busUnify` 40.8 s. This entry attacks two of them, with **no effectiveness
change**.

**(a) `domainFold` covered-set index (`CoveredIndex.coveredIdx_eq_filter`).** `foldStep` gated every
target on `groupDoms (coveredCsOf cs xs) xs`, whose `coveredCsOf` is a full
`cs.algebraicConstraints.filter (coveredBy xs)` scan **per target** — the same O(#targets × #system)
term #104 removed from `domainBatch` / `reencode`. Those passes consumed only the soundness-only
`coveredIdx_mem`, but `domainFold` threads the covered set into `foldOut_correct`, whose statement
pins it to `coveredCsOf cs xs` **exactly**, so soundness is not enough. New
`CoveredIndex.coveredIdx_eq_filter`: `coveredIdx (build varsOf items) items.toArray Q xs =
items.filter Q` whenever every `Q`-item shares a variable with `xs` (index *completeness* — the
`build` buckets, `HashSet` dedup and `mergeSort` all collapse back to the plain filter). The
hypothesis holds for `coveredBy` (`hasVar` yields a variable, `varsInF` puts every one in `xs`).
Wired into `foldStep` via a `FoldIdx` structure carrying the index plus the `= build …` /
`= …toArray` proofs, built once per pass and rebuilt only on an accepted fold; the step re-derives
`foldOut_correct`'s `hdoms` by rewriting the equality.

**(b) `busUnify` membership (`Std.HashSet`).** The pass's load-bearing "introduces no new variable"
filter tests `z ∈ cs.vars` for every variable of every collected slot-equality; `cs.vars` is the
whole ~27.5k-entry occurrence list, so each `z` paid a **linear** list scan. Replace it with a
`Std.HashSet.ofList cs.vars` membership test (O(1)); `Std.HashSet.contains_ofList` transports the
result back to genuine `z ∈ cs.vars` (all the correctness proof consumes). Output is bit-identical
(the kept set `new` is unchanged).

**Impact.** No audited surface touched; the three `*_maintainsCorrectness` theorems stay
`{propext, Classical.choice, Quot.sound}`-only; `check-proof-integrity.sh` passes. **Effectiveness
unchanged** — keccak output bit-identical (3056 vars / 120 constraints / 2690 bus interactions), and
the full openvm-eth sweep matches the entry-72 baseline exactly (variables 4.491× / 3.810× agg/geo,
bus 3.398× / 2.705×, constraints 10.595× / 11.585×; per-case 25 W / 43 L / 32 T). **Runtime (keccak
profile, per-pass):** `busUnify` 40.8 → 11.3 s (**−72 %**, −29.6 s) — the variable-membership scan was
the dominant term; `domainFold` 54.6 → ~46–48 s (−~13 %). Every other pass is flat within the ~3 %
cross-pass measurement noise; profiled total 383 → 356 s. As in #104 the `run` wall-clock is noisy on
this machine, so the per-pass profile deltas are the reliable signal.

**Remaining (see `docs/ideas.md`).** `busUnify`'s other per-equality scan,
`cs.algebraicConstraints.contains c`, needs a `Hashable (Expression p)` instance to index; the next
runtime tiers are `flagFold` (~51 s) and the finite-domain box enumeration inside
`domainBatch` / `domainFold`.

### 73a. Follow-up: size-gate the domain-fold index (avoid the small-circuit regression)

The entry-73 `domainFold` index amortizes the covered-set scan across targets but pays a fixed
per-invocation build (+ a rebuild per accepted fold) and a per-target `HashSet`/`mergeSort`. The #103
CI bench (openvm-eth 100 cases + keccak) showed this is **net-slower on small circuits**: per-pass
`domainFold` 5344 → 6639 ms (**1.24×**) on openvm-eth (largest block ~4.6k constraints), even though
it wins on keccak (~28.6k constraints, −13 %). End-to-end the openvm-eth total was still flat (busUnify
offsets it: 1870 → 644 ms, 0.34×), and keccak was −10 % overall — but the pass-level regression is
avoidable.

`domainFoldPass` now gates on `cs.algebraicConstraints.length`: ≥ `domainFoldIndexThreshold` (8192,
comfortably above openvm-eth's ~4.6k and below keccak's ~28.6k) uses the indexed `foldLoop`; smaller
systems use the new `foldLoopDirect` (recomputing `coveredCsOf` per target, as before the index).
Both call the shared `foldStepWith` core, so the fold — hence effectiveness — is **identical on every
case**; only the covered-set lookup differs. No audited surface; proof integrity unchanged
(`{propext, Classical.choice, Quot.sound}`-only). Expected effect: keccak keeps its −13 % `domainFold`
win; openvm-eth `domainFold` returns to baseline (no 1.24× regression); `busUnify`'s −66/−72 % win is
unaffected.

## Entry 71: symbolic-timestamp forwarding — two-root address disequality

**Idea.** `busUnifyPass` (`BusUnify.lean`) forwards read/`prev_data` limbs across a
symbolic-timestamp memory access by pairing an active send `S` with its consumer receive `R` (same
address, none active-same-address between) and adding the slot equalities `memEqConstraints`
(timestamp included) — Gauss then pins the timestamp `lower_decomp` and substitutes the read/
`prev_data` limbs by the written value. On keccak's heap this never fired: `findConsumer`'s scan
must step over interleaved *other-pointer* accesses, and `addrConstsNeq` only refutes a
different-address message when **both** address slots are literal constants — but a heap address is
the pointer *expression* `mem_ptr_limbs__0 + 2¹⁶·mem_ptr_limbs__1`, so no candidate ever formed
(AS2 stuck at 482, `lower_decomp`/`prev_data` families uncollapsed — the concrete blocker behind the
top ideas.md item "unify read-data limbs").

**Mechanism (bound-free, simpler than a bounded-interval approach).** Each pointer limb is
pinned by a two-root constraint `(A + k·x)(A + δ + k·x) = 0` (recognized by `twoRootOf?`,
`RootPairUnify.lean`). The high limb's constraint reads `(F − limb₁)(F − 2¹⁶ − limb₁) = 0` with
`F = C_hi + 30720·limb₀`. Over BabyBear `1 + 2¹⁶·30720 ≡ 0 (mod p)`, so substituting either root of
`limb₁` into `addr = limb₀ + 2¹⁶·limb₁` **cancels `limb₀` algebraically**, leaving an affine form in
the base register `rs1_data` only, in each of the two branches: `addr ∈ {2¹⁶·C_hi, 2¹⁶·C_hi − 2³²}`.
For two same-base pointers every one of the four branch-pair differences is a nonzero field constant
(the immediate diff, ±2³²) ⇒ the addresses provably differ — **no range bounds needed**, purely the
two-root disjunction and linear arithmetic.

**How.** New audit-free `AddrDiseq.lean`: `ptrBranchesOf` (substitute a two-root branch into a
`LinExpr`), `ptrReductions` (the ≤2 branch forms per limb of an address expression), `constDiffNZ`
(a nonzero-constant difference), `exprTwoRootNeq` (four branch-pair diffs all nonzero constants),
`addrTwoRootNeq` (some address slot provably differs). Wired into `BusUnify.lean`: the new disjunct
`addrTwoRootNeq` is OR-ed into `findConsumer`'s step-over test and `checkPair`'s `mid`-refutation;
`checkPair_sound` gained an `hsat` hypothesis (the two-root soundness needs the constraints to hold).
The same predicate is also usable by `busPairCancel`'s `midRefuted` (not wired yet). Zero audit
surface, no new `BusFacts`. Proof: `twoRootOf?_sound` gives the root disjunction, `LinExpr`
arithmetic gives the branch reduction, and the four nonzero-constant checks contradict any address
equality.

**Perf.** The naive per-pair certificate (re-scan every constraint per `(send, mid)`
pair, plus a per-call `decide (Nat.Prime p)`) made keccak **~5× slower** (30+ min vs ~6). Fixed with
a proof-carrying `TwoRootMap` (per-variable `(k, A, δ)` data, mirroring `BoundsMap`) built **once per
pass** — constant-time hash lookup per pair; each entry also carries `Nat.Prime p`, dropping the
per-call primality `decide`. Keccak runtime is **back to ~baseline (~6 min)**; output byte-identical
to the naive version on the quick case.

**Impact.** **keccak: 3056 → 2224 variables (−832, −27%), 2862 → 2411 bus interactions (−451),
120 → 118 constraints.** The variable gap to powdr shrank **+1035 → +203** (80% closed, now 2224 vs
2021). The cascade landed as predicted: `read_data_aux…lower_decomp` 534→164, `prev_data` 448→148,
width-12/17 range checks 267/267 → **129/129 (= powdr)**; register-chain (AS1) cancellation cascaded
free (230 → **58 = powdr**). AS2 count itself stays 482 (the ±1 identical-tuple residue rose 178→282 —
those need the item-1.2 affine `byteJustified` rule to cancel; future work). **openvm-eth 100-case
sweep: variables 4.490× → 4.507× agg (3.810 → 3.818 geo), bus 3.290× → 3.331× agg (2.629 → 2.641
geo), constraints ~flat, 0 regressions** — the pass also fires on the main benchmark's heap accesses.
Build + `check-proof-integrity.sh` green ({propext, Classical.choice, Quot.sound}-only).

**Follow-up.** (1) The 282 identical ±1 memory tuples my forwarding created are cancellable by
`busPairCancel` once `byteJustified` gets an affine no-wrap rule (ideas.md 1.2) — another ~−282 bus.
(2) Wiring `addrTwoRootNeq` into `busPairCancel.midRefuted` could telescope the AS2 middle pairs
(below powdr's 200 floor; ideas.md 2.2).

### 74. Generalize `xorEqExtract` to the 255-complement (C4b) — keccak variable effectiveness

**Idea.** `xorEqExtractPass` (entry 70, C4a) already recognizes the *zero*-operand bitwise-XOR
interactions `[0, y, z, 1] ⟹ z = y` / `[x, 0, z, 1] ⟹ z = x` and adds the entailed equality so
Gauss can eliminate the pinned intermediate byte. The other constant that makes `x ⊕ c` **affine**
in `x` is `255`: XOR-ing a byte with the all-ones byte is the byte complement,
`[x, 255, z, 1] ⟹ z = 255 − x` and `[255, y, z, 1] ⟹ z = 255 − y` (`n ⊕ 255 = 255 − n` for a byte
`n`). `{0, 255}` are the *only* two affine constants, so this **completes** the constant-operand
generalization rather than adding a new mechanism. Diagnosed on the keccak stress case: ~200 of its
bitwise interactions have the form `[x, 255, z, 1]` with `z` a fresh NOT-result variable (the `c__*`
family) that powdr does not materialize — apc kept the complement equality only on the bus, so Gauss
never used it (196 of them are eliminable on the post-#105 base; see below).

**Change (generalize the existing pass, no new pass, no pipeline edit).**
- New proven `BusFacts` field `xorComplEq` (sibling of `xorZeroEq`): on the bitwise bus an accepted
  `[x, 255, z, 1]` / `[255, y, z, 1]` gives `z = 255 − x` / `z = 255 − y`. Discharged for OpenVM
  from the concrete `violates` (byte bound on the free operand + `z.val = x.val ⊕ 255`) via the nat
  lemma `n ⊕ 255 = 255 − n` for `n < 256` (a one-shot 256-case `decide`, no runtime cost). Sound
  only when `255` is a genuine byte of the field, so the OpenVM instance **gates the fact on
  `256 ≤ p`** (true for BabyBear; a small field, and `trivial`, claim nothing — the pass stays a
  no-op and VM-agnostic). Counterexample without the gate: `(255 : ZMod 3) = 0`, where the identity
  is `z = x`, not `z = 255 − x`.
- `xorEq?` extended from 2 to 4 constant-operand cases; the pass proof adds the two 255 branches via
  `xorComplEq_sound`. Same shape as C4a — `addConstraints_correct` (soundness drops the added
  equality; adding a constraint touches no interaction, so side effects / admissibility are
  unchanged; the added equality's variables all come from the interaction's payload, so no new
  variable is introduced).

`lake build` green; the three `*_maintainsCorrectness` theorems still
`{propext, Classical.choice, Quot.sound}`-only; `check-proof-integrity.sh` passes (no
`sorry`/`admit`/`axiom`/`native_decide`); keccak output within the degree bound.

All numbers below are measured on the **post-#105 (entry-71 forwarding) base**, on which this pass
stacks — C4b is orthogonal to the memory forwarding, so the two compose (a baseline vs. C4b A/B on
one build; the two changes touch disjoint families).

**Impact — keccak (post-#105 baseline → C4b, same build).**
- **variables 2224 → 2028 (−196; 12.375× → 13.571×)** — the `[x, 255, z, 1]` NOT-results eliminated
  by same-cycle Gauss (substituted `z := 255 − x`). This puts keccak at **2028 vs powdr 2021 — a +7
  variable gap (near parity)**, closing the residual +203 gap that #105 left down to +7.
- bus interactions 2405 → 2418 (+13), constraints 118 → 120 (+2) — small, and dominated by the −196
  variables under the priority order (the 255-XOR interactions stay put, still byte-checking their
  free operand; a few send/receive cancellations shift under the changed variable structure).
- **Runtime not increased — FASTER: solo `run` 674.6 s → 633.5 s (−6 %)** — eliminating 196 variables
  in the prelude of the cleanup cycle shrinks the system every downstream pass rescans (wall-clock is
  noisy on this machine, but the direction is not increase).

**Impact — openvm-eth (full 100-case benchmark.py sweep; post-#105 baseline → C4b, same build).**
Variable-positive and per-case-neutral: variables 4.507× → **4.509×** agg (3.818× → 3.820× geo), bus
interactions 3.405× → 3.401× agg (2.707× → 2.705× geo), constraints 10.595× → 10.590× agg
(11.585× → 11.578× geo); the per-case standings vs powdr are **unchanged at 25 W / 42 L / 33 T**. The
variable gain lands on the register/shift blocks carrying `255`-complement (NOT) results (the
apc_071 / apc_037 cases `docs/ideas.md` flagged for C4b); the sub-0.01× bus/constraint movement is the
255-XOR interactions staying put as a few downstream cancellations shift (aggregate-invisible).

Together with #105 (entry 71), the keccak variable gap to powdr collapses from +1035 (pre-both) to
**+7** (post-both). The residual keccak variable families are the memory read/write-aux witnesses and
`bit_shift_carry` (rotation-gadget carries) — separate mechanisms, not constant-operand XOR; see
`docs/ideas.md`.

## Ideas-file regeneration (2026-07-13, fresh baselines — no optimizer change)

Rewrote `docs/ideas.md` from scratch into a ranked shortlist of 5 high-impact ideas after a
multi-agent brainstorm (keccak + openvm-eth first-principles, powdr-gap census, pass generalization,
prototype measurement). No code change; recording the baselines the ranking rests on. (This commit
was rebased on top of C4b/#109 — entry 74 — so the ideas file's keccak figures reflect the post-C4b
state: keccak **2028 v** / 118 c / ~2405 bus, variable gap to powdr now **+7 (near parity)**, leaving
**bus (+671)** as keccak's dominant remaining loss.)

**Baselines the brainstorm measured (on `c007db0`, pre-C4b).** keccak: 2224 v / 118 c / 2405 bus vs
powdr 2021 / 186 / 1734. openvm-eth 100-case: apc vars 4.507× / 3.818× agg/geo, bus 3.405× / 2.707×,
per-case **25 W / 42 L / 33 T**. apc_010: 466/251/**271** vs powdr 498/331/**239**.

**Gap decomposition.** eth vars ~+243/42c: `rd_data` write-result limbs ~93 (23c, powdr keeps 0) ·
comparison gadget markers/flags ~130 (43c) · `bit_shift_carry` +67 (13c) · `apc_071` intermediate
address bytes. eth bus net +368: bitwise **+440** (72c) · tupleRange +160 (22c) · memory +144 (15c) ·
varRange **−376** (apc *wins*). keccak bus +671: memory interior pairs +276 · bitwise +327 · width-1
range +68.

**Prototype measurement (memory interior-pair cancellation).** Simulated cancellation on the live apc
renders: keccak has **138 byte-identical ±1 memory pairs (276 interactions)** → memory 534 → 258 =
exact powdr parity; all 12 205 interleaved messages are other-address heap accesses (0 same-address),
so the cancellation is valid and the real blocker is `busPairCancel.midRefuted`'s inability to prove
symbolic heap addresses differ (fix = wire the proven `addrTwoRootNeq` in). Corrects the prior
ideas.md item-1.2 framing: an affine `byteJustified` rule is **not** the keccak blocker (0 cancellable
pairs contain rotation carries; data limbs already have a `slotBound` byte source). apc_010's −32 is a
*different* problem — register-chain pairs whose value equality `busUnify` already adds but Gauss
can't apply under the degree-3 bound (needs entailed-payload matching, not syntactic).

**New top idea surfaced:** folding byte/limb decompositions of compile-time constants (JAL/JALR return
addresses, jump targets) — the largest variable family (`rd_data`, ~93 vars/23 cases) — ranked #1.

**Dead-ends confirmed** (see ideas.md): timestamp re-encoding wash, carry-witness wash, PC-lookup drop
(no gap), disconnected-component (empty), keccak genuine-XOR bus gap (representation artifact),
`bit_shift_carry` (VM-specific), varRange packing (apc already wins), `b`/`c` naming artifact,
`apc_003` now a tie, constant-operand XOR exhausted (C4a/C4b landed).

## Idea #5 attempt — functional-dependence derived columns for read/write limbs — FAILED (measured dead-end, no optimizer change)

**Idea (ideas.md #5).** Make a functionally-determined limb (a bitwise-XOR result `z = x⊕y`, or a
write-result limb `rd_data = f(inputs)`) a *derived* column — register a `ComputationMethod` for it
and "drop it from the free-variable set" — to cut the variable count. Rated medium–low confidence,
high effort; flagged as the highest proof cost of the five.

**Result: infeasible.** It cannot reduce the primary (variable) metric, for a structural reason, so
there is nothing to prove and no pass was added. The chain, each link checked against the code and the
live benchmark renders:

1. **The variable count is purely syntactic.** `ConstraintSystem.variables` (`ApcOptimizer/Utils/Size.lean`)
   is the dedup of every name appearing in a constraint or bus interaction. `Derivations` are a
   *separate* output list (`Spec.lean`), not subtracted from `.variables`. So registering a
   `ComputationMethod` for `z` does **not** drop `z` from the count — a derived column that still
   appears in the system is still counted. The only levers that remove a name are **substitution**
   (`Subst`/`Gauss`, replace the name by an `Expression` everywhere) and **re-encoding** a group into
   fewer fresh vars (`Reencode`). "Drop `z` from the free-variable set (interaction retained for
   byteness)" as written is a contradiction: if the interaction is retained, `z` is still counted.

2. **XOR is not substitutable and not `ComputationMethod`-expressible.** `z = x ⊕ y` is not a
   low-degree `ZMod p` polynomial, so there is no `Expression` to substitute for `z`; and
   `ComputationMethod` offers only `const`/`quotientOrZero`/`ifEqZero`, none of which computes XOR
   (encoding it bit-wise would first require bit columns the byte-level circuits don't have, adding far
   more variables than it removes). `BusFacts.slotFun` provides only the *value-level* soundness
   function `List (ZMod p) → ZMod p`, not a substitutable expression. `Reencode` can't reach it either:
   it reads algebraic constraints (the XOR relation is a *bus*), and the group `{x,y,z}` has 65536
   joint values → 16 fresh bits to replace 3 vars (a regression).

3. **Every surviving functional-dependence limb is XOR-based; the affine ones are already gone.**
   Measured on the live renders. keccak apc output: **359 pure-XOR chain intermediates** (`a=b⊕c`, then
   `a` is an operand of another XOR), **458 XOR-results written to memory** (`rd_data`), **159 redundant
   range-checks on XOR results** — all XOR, none affine. The affine functional dependences (ADD/SUB
   carry limbs) are already eliminated by `Gauss` (degree-1 substitution, including into stateful memory
   payloads; `Gauss` only *declines* to substitute raw payload slots of **stateless** buses, to
   preserve range knowledge). eth apc-only variables (vs powdr) are dominated by idea #1 (constant
   PC/immediate/return-address limbs), idea #4 (comparison markers), and the documented timestamp /
   `b`,`c` naming artifacts — not a runtime-`rd_data` functional slice.

4. **powdr does not beat apc here.** powdr keeps the same XOR limbs — **1** derived column total on
   keccak, via `QuotientOrZero` — consistent with keccak's +7 variable near-parity. There is no
   competitive gap for idea #5 to close.

**Impact: none** (no code changed; `lake build` unaffected). Idea #5 removed from the active list and
recorded under "Rejected / measured dead-ends" in `docs/ideas.md`.

**Adjacent real wins surfaced while investigating** (already tracked in ideas.md, *not* idea #5): the
159 redundant range-checks on byte-guaranteed XOR results are a bus-only drop (width-1 range-check →
booleanity / redundant-byte follow-ups), and the `[x,y,0,0]` byte-check packing (idea #3) is a bus
win. These reduce bus interactions, not variables.

## 75. Generalized single-value byte-check recognizer: `[0,x,x,1]` mirror drop + form-agnostic pack (idea #3)

**Idea.** `docs/ideas.md` #3 ("bitwise-bus cleanup") had three parts: (i) result-zero equality
extraction `[x,y,0,1] ⟹ x=y`, and (ii)/(iii) recognizing the missing XOR-with-zero mirror
`[0,x,x,1]` so the byte-check dropper/packer reaches it. Measured on the current optimizer output:

- **(i) result-zero is a measured dead-end.** Rendering the optimized keccak circuit shows **zero**
  `[x,y,0,1]` interactions — every op-1 bitwise message carries a genuine XOR-result variable in the
  result slot (XOR chaining), which idea #3 itself flags as *not* to target. A prototype pass
  (`xorResultZeroEq` fact + a fifth `xorEq?` arm) built and proved clean but left both benchmarks
  byte-identical, so it was dropped. Recorded as a dead-end.
- **(ii)/(iii) is real.** Keccak's optimized bitwise bus has **68** `[0,x,x,1]` mirror byte-checks
  (`0 ⊕ x = x`, i.e. "x is a byte" with the zero in the *first* operand slot). Neither
  `RedundantByteDrop` (recognized `[x,x,0,1]`, `[x,0,x,1]`, `[x,y,0,0]`) nor `bytePackPass`
  (recognized only `[x,x,0,1]`) could reach them.

**Change.**
- `BusFacts.xorZeroCheck` extended from `[x,0,x,1]` to *both* mirrors `[x,0,x,1]` / `[0,x,x,1]`
  (discharged for OpenVM from `Nat.xor_zero` / `Nat.zero_xor`; the mirror is `256 ≤ p`-free, holding
  even in the degenerate `p=1` case).
- `RedundantByteDrop.byteCheckOperands?` gains the `[0,x,x,1]` arm (drop when the operand is
  byte-justified elsewhere).
- New `ByteCheckPack.lean`: one canonical single-value recognizer `svCheck?` for **all three**
  encodings (`[x,x,0,1]`, `[x,0,x,1]`, `[0,x,x,1]`) → the checked value, and a packer that merges
  any two into one pair check `[eA,eB,0,0]` via the *existing* general stateless two-for-one swap
  `mergeStateless2_correct` (no new correctness lemma). This **subsumes** `bytePackPass`, which was
  removed together with its helpers (`matchByteCheck` / `findSecond` / `findBytePackGo` /
  `mergeBytePair_correct`); `BytePack.lean` now only exports the canonical `byteCheck1` / `byteCheck2`
  message constructors reused by `ByteCheckPack` and `TupleRange`. The pipeline's `bytePack` slot now
  runs the generalized packer.

**Why sound.** A recognized single-value check is stateless, multiplicity-1, and accepted iff its
value is a byte (`svCheck?_sound`, from `byteCheck` / `xorZeroCheck`); a pair check `[x,y,0,0]` is
accepted iff both are bytes (`bytePairBus` + `byteCheck`). So the pair's obligation is exactly the
conjunction — the hypothesis `mergeStateless2_correct` needs. All are stateless, so stateful side
effects and `admissible` are untouched; variable-neutral (operands retained), degree-guarded.
VM-agnostic: with `BusFacts.trivial` every fact is `false`, so `svCheck?` returns `none` and the pass
is the identity.

**Impact (variable-neutral bus win on both benchmarks; no constraint change).**
- **keccak: bus 2418 → 2348 (−70)** — 15 mirror checks dropped (justified elsewhere), the rest packed
  two-per; variables 2028 and constraints 120 unchanged.
- **openvm-eth (100-case sweep): bus 3.401× → 3.439× agg (2.705× → 2.723× geo)** — closes ~half the
  bus gap to powdr (diff −0.079× → −0.040×); variables 4.509× → 4.511× agg (non-regressing),
  constraints ~flat, per-case standings vs powdr unchanged (25 W / 42 L / 33 T).

`lake build` green; `check-proof-integrity.sh` passes (no `sorry`/`admit`/`axiom`/`native_decide`);
the three `*_maintainsCorrectness` theorems still `{propext, Classical.choice, Quot.sound}`-only;
keccak output within the degree bound.

## Result-zero XOR equality extraction (2026-07-13) — refuted by measurement; ideas.md #3(i) retired

**Idea (ideas.md #3(i)).** Complete `xorEqExtract`'s constant-slot family with the *result-zero*
arm: an accepted bitwise `[x, y, 0, 1]` (op 1, multiplicity 1) asserts `x ⊕ y = 0`, hence `x = y` —
equivalence-grade (XOR-cancellation on `Nat`, no byte bound, no `256 ≤ p` gate, strictly simpler
than the landed C4b). Add the entailed `x − y = 0` (guarded on syntactic `x ≠ y` so the canonical
self-XOR byte checks `[e, e, 0, 1]` are skipped and the arm stops firing once Gauss renames), keep
the interaction for byteness, let Gauss remove one operand. ideas.md #3 predicted ~50 keccak
variables (2028 → ~1978, below powdr's 2021 for the first time).

**Built and proven, then discarded.** Third conjunct on `xorZeroEq_sound` (`[x, y, 0, 1]` accepted
→ `x = y`; OpenVM proof XORs `y.val` into both sides of `0 = x.val ^^^ y.val` and cancels), fifth
`xorEq?` arm + spec disjunct, both pass proof obligations extended. `lake build` +
`check-proof-integrity.sh` green ({propext, Classical.choice, Quot.sound}-only). ~40 lines over
`BusFacts.lean` / `OpenVmFacts.lean` / `XorEqExtract.lean`; trivially re-creatable from this entry.

**Measured: exact no-op on the entire corpus.**
- keccak: byte-identical **2028 v / 120 c / 2418 bus** (baseline re-measured in-session for a clean
  A/B).
- openvm-eth 100-case sweep: aggregates identical to baseline (vars 4.509×/3.820×, bus
  3.401×/2.705×, constraints 10.590×/11.578×; per-case 25 W / 42 L / 33 T).
- Render census of the current keccak *output*: **zero** `[x, y, 0, 1]` interactions. Bus 6 holds
  1183 op-1 XORs — every one with a *variable* result slot — plus 55 **op-0** pair checks
  `[x, y, 0, 0]`.
- Instrumented pass (`dbg_trace` counter on the arm's exact match condition): **0 matches in every
  cleanup cycle** — i.e. the shape is absent mid-pipeline too, not merely in final outputs — on
  keccak and the XOR-heavy eth cases (apc_037/051/071/010). Positive control: the same channel
  counting all-arm extractions prints the known C4a/C4b firings (112/96/72/24 per cycle on
  apc_071), so the zero is real, not an instrumentation artifact.

**Why the census was wrong.** ideas.md #3 claimed "50 result-zero XORs on keccak, all `aᵢ ^ aⱼ = 0`
with two bare vars". The only z-slot-zero bitwise messages in the current output are the **op-0**
byte-pair checks (55 ≈ the claimed 50): `[x, y, 0, 0]` range-checks both operands and carries **no
equality semantics**. The census evidently keyed on "slot 2 = 0" without requiring `op = 1` (or was
taken pre-C4b and never re-checked). OpenVM circuits do not emit `x ⊕ y = 0` as an equality
encoding — equality is the inverse-marker gadget family (the comparison-gadget idea, now ideas.md #3).

**Outcome: discarded; do not re-propose #3(i).** Worked: no — idea refuted for ~1 h of proof
effort; the correct order would have been the 5-minute output census *first* (the standing
what-if-before-build rule; the miss was trusting a recorded census instead of re-verifying it on
current `main`). The live remainder of ideas.md #3 — (ii) the canonical byte-check recognizer
(incl. the `[0, x, x, 1]` mirror arm) and (iii) redundant-byte drop + packing — targeted exactly
the op-0/self-check shapes that *do* exist, and landed independently as entry 75 (#113), which
also reconfirmed this entry's result-zero dead-end on its own render census.

**Impact: none (no code landed).**

### 76. Is-equal gadget collapse via sum-of-squares — landed

**Idea (the is-equal slice of the comparison-gadget idea, now ideas.md #3).** The is-equal/is-zero gadget keeps one
inverse-marker witness per limb (`−cmp + Σ (aᵢ − bᵢ)·diff_inv_markerᵢ = 0`, four markers per
comparison); powdr keeps a **single** witness. The linear collapse (`hintCollapse`) is unsound here
because signed differences can cancel; the sound form is powdr's **sum-of-squares**:
`inv · Σ (aᵢ − bᵢ)² = cmp` with one derived `inv = QuotientOrZero(...)` column — zero iff all limbs
match, because each `(aᵢ − bᵢ)²` has value < 256² (byte-bounded limbs) so the sum cannot wrap `p`
(`sumSq_zero_all_eq`; needs `65536 ≤ p` and `#limbs · 65536 < p`, both checked). Drops n−1 markers
per gadget. Reencode-class completeness handled by the derived-column bookkeeping; no new
`BusFacts`.

**Provenance.** Built and measured on branch `c6-tuple-range-pack` (commit 05fd3a0, on the #97
base): −48 vars / 16 cases / 0 regressions. This entry is the rebase onto current `main`
(finally onto #113): the 640-line `EqCollapse.lean` ported **unchanged** (two unused-simp-arg lint
fixes only), wiring translated to one `cleanupPasses` entry after `hintCollapse`. Premise
re-verified fresh: #110's census still lists `diff_inv_marker` +61 over 16 cases, and the per-case
win reproduced identically on the #110 and #113 bases.

**Measured on current `main` (per-case JSON diff, not aggregates):**
- openvm-eth: **16 cases improved, every one exactly −3 vars, 0 regressions on any axis, net −48
  vars**; bus and constraints byte-neutral corpus-wide. Aggregate variables **4.511× → 4.518×**
  (geo 3.822× → 3.837×); per-case vs powdr **25 W / 42 L / 33 T → 27 W / 29 L / 44 T** (13 losses
  flipped). `apc_072` 32 → 29 = exact powdr parity on all three axes.
- keccak: **2028 → 2025 vars** (keccak contains a single is-equal gadget), bus (2348) /
  constraints (120) unchanged — gap to powdr now **+4**.
- Runtime (solo A/B sweeps): total **+1.4%**, median case +0.3%; named outliers apc_044 +25%
  (24.6→30.8 s), apc_019 +19%, apc_080 +54% (1.1→1.7 s). Acceptable for a per-cycle pass; if a
  future profile flags it, gate the collector on the presence of multi-marker hint constraints.

Build + `check-proof-integrity.sh` green ({propext, Classical.choice, Quot.sound}-only), zero lint
warnings. **Worked: yes.**

**Remaining from the same family (ideas.md #3):** the signed-compare / sltu slice
(`diff_marker` +24, `c_msb_f` +27, `b_msb_f` +19) — needs the sign-split byte-bounded-difference
coefficients, a different matcher; the is-equal slice this entry lands covered the
`diff_inv_marker` +61 chunk minus what hintCollapse already caught.

### 77. Interior memory pair cancellation: two-root step-over + coda-phase entailed payload matching

**Idea (ideas.md #2).** A cell accessed N times emits 2N memory interactions; only the first
receive and last send are observable — the N−1 interior `+1`/`−1` pairs cancel, but
`busPairCancel` could not *recognize* them. Two independent recognizer gaps, both fixed in
`BusPairCancel.lean` with no new `BusFacts` and no audited-surface change:

**(a) Symbolic-address step-over.** `midRefuted` refuted an interleaved message as
different-address only via `addrConstsNeq` (both addresses literal constants) — heap pointers are
`mem_ptr_limbs` *expressions*, so keccak's 137 byte-identical interior pairs never cleared. Fix:
OR the proven `addrTwoRootNeq` (`AddrDiseq.lean`, upstream since #105) into
`midRefuted`/`preRefuted`/`shieldScan`; the `TwoRootMap` is a `Thunk` built **at most once per
pass invocation** — forced only when a candidate survives the constant-address tests, so
register-only systems never pay — and transported across `cancelLoop`'s drop recursion via a
constraint-preservation equality returned with each `PassResult` (drops leave
`algebraicConstraints` untouched). This is the §3.3-prototype design with its documented
per-drop-rebuild runtime bug fixed.

**(b) Constraint-entailed payload matching.** apc_010-class pairs share address, timestamp and
three data slots; slot 0 differs *syntactically* (send `(1−flag)·srd0 + flag·srd1`, receive
`read_data`) even though `busUnify` already added the slot equality — Gauss can never apply it
(degree 4 > 3), so the payloads never become identical. New `EqConstraintMap` indexes the
*normalized* constraints by structural hash; `payloadEntailedEq` decides each slot pair
syntactically first, then by one `normalize` + hash probe per orientation.
`dropPair_correct`'s syntactic payload hypothesis weakens to *evaluated* equality under the
constraints — sound in **both** refinement directions because a drop leaves the constraint list
untouched (`hSE`/`haddrEv` discharge from `hsat.1` on either side).

**The phase lesson (measured, not designed up front).** Running (b) inside the cleanup cycle is
a net **loss**: entailed drops fire before the justification machinery has caught up, taking the
byte-check-emission path on pairs the deferred syntactic cancellation would later drop for free
(apc_005 class: +66 emitted checks vs −32 varRange, **+34 bus each**; 31 cases regressed), and
the per-cycle map builds + coarse address-hash index buckets cost **keccak 2.4× runtime**
(687 s vs 291 s). Gating entailed matches to emission-free drops kills the wins instead —
apc_010's equality is degree-blocked *forever*, so its pairs need emission. Resolution: **phase
separation.** The cycle invocation stays purely syntactic (exact-payload-hash index, `M` empty);
a new **aggressive coda invocation** (`busPairCancelLate`, followed by `bytePackLate` to pack the
emitted survivors) runs entailed matching once, after the fixpoint, where the race is over and
each drop is locally net −1 bus at worst. Deliberately forgone: −6 keccak / −6 apc_100 bus that
only mid-cycle entailed matching reaches — recorded here so the trade is visible.

**Measured vs `main` = #114 (per-case JSON A/B; solo runtime runs):**
- keccak: bus **2348 → 2072 (−276)** — memory **534 → 258 = exact powdr parity**; vars 2025 /
  constraints 120 unchanged; bus effectiveness 5.648× → **6.400×**; runtime 291 → 295 s (+1.3%).
- openvm-eth: bus agg **3.439× → 3.455×** (geo 2.723× → 2.735×), powdr gap −0.041 → **−0.025**;
  **10 cases improved / −76 bus / 0 regressions** (apc_010 271 → 247 vs powdr 239, apc_042 −16,
  apc_014 −12, apc_051 −8, apc_031 −6, apc_097 −3, apc_008/019/100 −2, apc_091 −1); variables
  and constraints byte-neutral (4.518× / 10.595×, W/L/T 27/29/44 unchanged); runtime **−2.5%**
  total, median case −3.8% (earlier cancellation shrinks the systems downstream passes see).

Build + `check-proof-integrity.sh` green ({propext, Classical.choice, Quot.sound}-only).
**Worked: yes.**

**Remaining on this front:** keccak bus gap now **+338** (was +614): bitwise ≈ +257 (genuine-XOR
representation, no current lever) + width-1 range +68 (convertible to booleanity constraints —
ideas.md follow-up) + ~13 misc. The eth bus gap −0.025 is the last aggregate deficit on any axis.

### 78. Coda byte-pair splitting: operand-granular redundant-byte drop (−45 keccak / −115 eth bus)

**Idea.** `RedundantByteDrop` works pair-at-a-time on packed bitwise byte checks `[a, b, 0, 0]`:
a pair drops only when *both* operands are byte-justified elsewhere, so a justified operand
trapped in a pair with a fresh one keeps its redundant obligation; and the same value
byte-checked in two *different* pairs (`[0, b, 0, 0]` vs `[0, c, 0, 0]`) is not a syntactic
duplicate, so `dedup` keeps both. Fix: a coda pass `splitBytePairPass`
(`OptimizerPasses/SplitBytePair.lean`) explodes every packed pair into the two single-value
checks `[a, a, 0, 1]`, `[b, b, 0, 1]` — obligation-identical by the proven `bytePairBus` fact —
then a coda `dedupLate` collapses duplicated byte-values, `redundantByteDrop` drops justified
singles operand-granularly, and the existing `bytePackLate` re-packs the survivors two per
interaction. A pair with nothing to shed round-trips unchanged.

**Provenance.** Built and proven 2026-07-11 against a pre-`ByteCheckPack` pipeline, where it
measured −89 eth bus; shelved for re-measurement because the generalized byte-check recognizer
(entry 75) and the coda pair cancellation (entry 77) touch the same byte-check stock. Re-measured
now on current `main` (`6e91df2`): **not subsumed — the win grew** (the entry-77 coda emits byte
checks whose redundancy the split can now shed).

**Measured (this branch vs `main` `6e91df2`).**
- openvm-eth (100 cases): bus 16842 → 16727 (**−115 over 27 cases, 0 regressions**); aggregate
  bus effectiveness 3.455× → **3.479×** (geo 2.735× → 2.753×; powdr 3.480× — the aggregate bus
  deficit is now −0.001). Variables and constraints bit-identical (agg vars 4.518×, per-case
  W/L/T 27/29/44 unchanged). Biggest movers: apc_037 −30, apc_100 −28, apc_022/apc_027 −7.
- keccak: bus 2072 → **2027 (−45)**; vars 2025 / constraints 120 unchanged; runtime
  294.7s → 285.8s (−3%, i.e. flat).
- **Attribution ablation:** running the coda with `dedupLate` alone (split disabled) is
  bit-identical to `main` on all 100 cases and in aggregate — the entire win is the split;
  none of it comes from the extra coda dedup.

**Wiring.** Coda only (`busPairCancelLate → splitBytePair → dedupLate → redundantByteDrop →
bytePackLate → …`): the split transiently *increases* the bus count, so it must never run inside
the size-decreasing cleanup fixpoint. No new `BusFacts`; the pass reuses the `bytePairBus`/
`byteCheck` facts that `bytePackPass` was proven from. Build + proof integrity green
({propext, Classical.choice, Quot.sound}-only).

## Ideas-file regeneration from fresh first-principles measurement (2026-07-14, no optimizer change)

Rewrote `docs/ideas.md` from scratch on main `656a9d8` (post-#114) after re-measuring both
benchmarks from zero: fresh `opt-export` of all 100 openvm-eth cases + keccak, canonical-polynomial
diffs against the checked-in powdr exports (exact per-variable/per-interaction attribution, not
family heuristics). Headline corrections to the previous file's beliefs:

- **eth absolute totals**: apc leads powdr on variables by −2,918 and constraints by −9,086, and
  trails bus by only +196 absolute — but loses bus **per-case 7 W / 67 L / 26 T** (+588 over the
  losing cases), which is what the geo metric punishes. The bus work is per-case hygiene, not one
  big mechanism.
- **eth variable losses decompose exactly**: constant decompositions +135 (Gauss unit-pivots the
  affine digit seeds away before any digit solver sees them; the cascade needs carry-disjunction
  pruning) · comparison gadgets +105 (−48 landed as #114; residue is the `sltu x,1` seqz idiom) ·
  dead `bit_multiplier` one-hot family +14. Everything else nets in apc's favor.
- **eth bus losses decompose into 8 mechanisms** totaling ~515 recoverable of +588: width-1
  checks 90, stale byte/tuple coverage after unification ≥112, cancellable ±1 memory pairs 78 +
  long (≥3) same-address chains 64, constant-family checks ~126, subsumed range checks 22,
  NOT-form `[x,255,255−x,1]` byte checks 23.
- **keccak +614 bus decomposes exactly**: 284 (142 byte-identical ±1 memory pairs; two-root
  `midRefuted` is the only blocker; **zero** variable cascade) + 262 bitwise (200 NOT-form checks
  all droppable — operands byte-justified by XOR slots; op-0 slot waste) + 68 width-1 checks (the
  bus-3 width histograms are otherwise identical to powdr's). Fixes land exactly on powdr's
  1734/2021/186; **nothing below that floor exists**: the XOR dag is measured perfectly clean
  (0 duplicates / 0 dead / 0 collapsible chains; 862 genuine XORs ≡ powdr's).
- **#116's gate rationale disproven**: `byteJustified` already accepts constants <256; the ungated
  keccak regression must be a pair-matching artifact (constant-folded send vs unfolded receive) —
  the fold is recoverable and owns the top eth variable family.
- **New justification rule found**: AND/OR-result bytes (`z`-slot `±(x+y−2v)` in a genuine XOR ⟹
  `v` is a byte) — needed by both the memory-pair drops (eth) and op-0 repacking (keccak).
- Fresh dead ends recorded: keccak-below-powdr, timestamp/mem_ptr 2-var floors (1:1 washes in all
  100 cases), bit_shift_carry representation wash, sub-byte checks not packable as bytes.

New `docs/ideas.md`: 5 ranked ideas (constant-decomposition folding done right; memory-bus
completion in 4 sub-items; seqz comparison collapse; stateless-check hygiene ×4; one-hot
annihilation) with mechanisms, proof paths, worked examples, and per-benchmark expected impact,
plus in-flight PR markers and working rules (duplicate-PR check, runtime discipline, per-case
measurement).

*(Rebase note: entries 77 (#117, interior memory pair cancellation = the file's idea 2 items (a)+(b))
and 78 (#119, coda byte-pair splitting = the op-0 half of idea 4d) merged while this regeneration was
in flight; the ideas file's baselines and ideas 2/4 were refreshed accordingly on rebase.)*

### 79. Consolidate the is-equal collapse into a generalization of `hintCollapse` (supersedes the standalone `EqCollapse` pass)

**Context.** Entry 76 (#114) landed the is-equal / is-zero sum-of-squares collapse as a **separate**
640-line pass `EqCollapse.lean`, wired as its own `cleanupPasses` entry right after `hintCollapse`.
Independently (PR #112) the *same* collapse was built as a **generalization of `hintCollapse`**:
`collapse_correct` takes the soundness reassignment as a parameter, so one proven theorem backs both
the plain-sum collapse (single byte-bounded coefficients, `is-zero`/`seqz`, `tryOne`) and the
sum-of-squares collapse (byte-bounded *difference* coefficients `aᵢ − bᵢ`, `is-equal`, `tryOneSq`);
both shapes are offered in a **single** `hintCollapse` scan that computes the per-constraint witness
set once (`witnessesOf`) and shares it. This entry consolidates onto that generalization and
**removes** `EqCollapse.lean` and its pass-list entry.

**Why.** Two motivations, matching the two questions raised on #112:
- *More generic* (repo principle "prefer fewer, more general passes"): one collapse framework and one
  proven `collapse_correct` theorem for both the linear and the quadratic (sum-of-squares) witness
  shapes, versus a second standalone 640-line pass. Net −270 lines for identical behaviour.
- *Lower runtime*: on `main` the is-equal work runs as a separate `eqCollapse` pass **in addition to**
  `hintCollapse` every cleanup iteration — a second whole-system witness scan. Folding it into
  `hintCollapse`'s single shared scan makes the sum-of-squares case cost only a cheap coefficient
  re-check on the rare multi-marker candidates. Measured per-pass with `profile` (combined
  collapse-stage time, `main`'s `hintCollapse` + `eqCollapse` vs the consolidated `hintCollapse`):
  apc_044 401 → 187 ms, apc_037 1261 → 631 ms, apc_006 834 → 411 ms — roughly **halved**, and it
  removes entry 76's named runtime outliers (apc_044 +25%, apc_080 +54%) since there is no longer a
  second pass.

**Effectiveness — byte-neutral vs `main` (this is a consolidation, not a new win).** The −48 eth
vars / −3 keccak vars already landed via entry 76; the generalized `hintCollapse` reproduces them
exactly. Full 100-case sweep matches `main`: variables **4.518× / 3.837×**, bus **3.479× / 2.753×**,
constraints **10.595× / 11.585×**, per-case **27 W / 29 L / 44 T**; `apc_033` 121, `apc_072` 29
(powdr parity). `apc-optimizer run` output byte-identical to `main` on the spot-checked cases.

`lake build` green; `check-proof-integrity.sh` passes (the three `*_maintainsCorrectness` theorems
`{propext, Classical.choice, Quot.sound}`-only); audited surface untouched. **Worked: yes** (same
effectiveness as entry 76, fewer passes, ~half the collapse-stage runtime).

## Entry 80: Width-1 range check → booleanity + subsumed range-check drop (idea 4(b)+(c))

Bundled the two stateless-range-hygiene items from `docs/ideas.md` idea 4. Both are pure bus wins
(variable-neutral), proven with **no new `BusFacts` and no audited-surface change**; correctness
follows from each pass's own `PassCorrect`.

**4(b) — width-1 → booleanity** (`ZeroWidthRange.lean`, cleanup cycle). A range check `[e, 1]` on
the variable range checker is accepted iff `e < 2` — booleanity — so `zeroWidthRangePass` grew a
width-1 arm alongside its width-0 arm: ADD the degree-2 constraint `e·(e−1) = 0` via
`PassCorrect.ofEnvEq`, then DROP the interaction via `filterBusEntailed_correct`. The width-1 iff
comes straight from the **existing mult-generic `varRangeBus` fact** — the ideas file's proposed
new `oneRangeBool` field was redundant. The backward direction (`e·(e−1)=0 → e < 2`) needs an
integral domain, so the arm gates on `decide (Nat.Prime p)` (the `deep` pattern); a per-candidate
degree gate (`e.degree ≤ 1`) keeps every emitted constraint ≤ 2, so it can never trip the
whole-pass `guardDegree` revert. Trades bus −1 for constraint +1 — a strict lexicographic win
(bus ≻ constraints), compatible with the fixpoint `sizeKey`.

**4(c) — subsumed range checks** (`SubsumedRange.lean`, new pass, coda). Drops a var-range check
`[x, w]` when a **retained** interaction already bounds `x` by `b' ≤ 2^w`. Structure mirrors
`RedundantByteDrop` exactly: a **non-circular justification base** (interactions this pass never
drops = everything not recognized as a single-variable range check) plus the proven `findVarBound`,
whose `slotBound`-derived bounds cover tuple-range slots, byte-limb memory receives, and any
retained range check. The drop is `filterBusEntailed_correct` again (each base interaction survives
the filter, so a satisfying assignment of the output accepts it, forcing `x` into range). Two
corrections to the ideas-file write-up:
- the bound test is **`≤`, not strict `<`**: apc_038's `mem_ptr_limbs__1` sits in a `[256, 8192]`
  tuple slot bounding it by *exactly* `2^13`, which a strict test would miss. The non-circular
  base — not strictness — is what prevents two equal-width checks from dropping each other.
- the base subsumes byte/memory sources too, so it reaches **~43 eth interactions**, not the
  estimated 22 (the extra hits are wide range checks on byte-guaranteed / smaller-tuple-slot vars).

**Wiring.** 4(b) stays in the cleanup cycle (the booleanity feeds the finite-domain passes); 4(c)
runs once in the coda after `redundantByteDrop` (a run-once, variable-neutral drop, so it never
starves the mid-loop enumeration of a variable's range bound — the same discipline as
`RedundantByteDrop`).

**Measured (A/B: this branch vs `main` `5bcbb85`, full `benchmark.py` + keccak `run`).**
- **openvm-eth (100 cases):** bus 16727 → **16595 (−132, 18 cases improved, 0 regressions)**;
  aggregate bus effectiveness 3.479× → **3.506×** — the last trailing eth aggregate axis **flips
  to a lead over powdr** (16595 vs 16722, was +5 → −127). Variables **bit-identical** (27967,
  per-case W/L/T 27/29/44 unchanged — 0 regressions). Constraints 11213 → 11303 (+90, the
  width-1→booleanity trade; still 10.5× vs powdr's 5.85×). Split: ≈ −89 bus is width-1 (con
  +90), ≈ −43 bus is subsumed-range drops (constraint-neutral: apc_049 −9, apc_042 −6,
  apc_005/009/015/036/044/067/068 −3 each, apc_038 −2, …). Biggest movers apc_100 −40,
  apc_037 −25, apc_038 −14, apc_051 −12.
- **keccak:** bus 2027 → **1959 (−68)** — all 68 width-1 checks (4(c) finds 0 subsumed pairs, as
  predicted); vars **2025 unchanged**; constraints 120 → 188 (+68). Bus effectiveness 6.543× →
  6.770×; gap to powdr +293 → +225.

Build green; `Scripts/check-proof-integrity.sh` passes — the correctness theorems
(`optimizerWithBusFacts_maintainsCorrectness`, `simpleOptimizer_maintainsCorrectness`,
`openVmOptimizer_maintainsCorrectness`) depend only on `{propext, Classical.choice, Quot.sound}`.
Worked: yes.
### 81. Bounded-payload digit fold: byte-checked mixed-radix ladders force constant limbs (−165 eth vars, keccak variable parity)

**Idea (the bounded-payload slice of ideas.md idea 1, constant-decomposition folding).** A bitwise pair check asserts an
affine operand `E = K ± (g·v₀ + 256g·v₁ + 65536g·v₂ + …)` is a byte, and each ladder variable
carries its own range check `vᵢ < Bᵢ ≤ 256` — together these can force every `vᵢ` to a
compile-time constant (the digits of the byte-checked value). The census on current output
(renders, all 100 cases): **42 such checks over 35 cases**, two shapes — the `rd_data` return
address `K − 256·rd₀ − 65536·rd₁ − 16777216·rd₂`, and a scaled `K + 480·rd₀ + 122880·pc₀ +
31457280·pc₁` PC-limb form — 2–3 pinnable vars each, far above the recorded "~3 vars over ~20
cases" estimate.

**The wrap analysis is the crux.** BabyBear `p ≡ 1 (mod 256)`, so `S = tval(b) + m·p` admits a
phantom digit vector for every wrap count `m ≤ maxΣ/p` (≈ 2 for the rd_data shape): the digits
are *not* forced by byte bounds alone. What kills the phantoms is the **narrow top-limb range
check** (e.g. the 6-bit top PC limb: phantom tops 120/240 ≥ 64) — a first solver assuming
all-byte bounds found unique solutions on only 6/35 cases; with the true per-variable widths,
33/35. The what-if (solve digits offline, pin via a scratch `whatif-pin` subcommand, re-run the
full pipeline): **−165 vars / −141 bus / −36 constraints over 33 cases, 0 regressions** —
including a −14-var cascade on the apc_045/026/051/055/085/094 family where pinned digits enable
folds an earlier affine-seed what-if had measured as non-cascading (that experiment seeded only
the `imm_limbs` constraint slice; seeding the byte-check digits is what cascades).

**Pass (`DigitFold.lean`, cleanup cycle).** Recognize `[x, y, 0, 0]` pair checks (mult 1,
`bytePairBus` + `byteCheck` facts), `linearize` each operand, sort terms into a `g·256^i`
coefficient ladder (both sign interpretations), read per-variable bounds from the proof-carrying
`BoundsMap` (`varRangeBus`/bitwise slot facts), then **enumerate the whole (byte, wrap) grid**
(`solutions`, ≤ 256·(maxΣ/p+1) points) and decode each admissible value as a bounded ladder.
Fires only on a **singleton** solution set: `solutions_complete` proves any satisfying
assignment's digit vector is enumerated (mixed-radix uniqueness `unpack?_ladderVal` + the
ZMod→ℕ residue bridge), so the singleton forces `env v₀ = d₀`, discharged into
`ConstraintSystem.subst_correct`. One substitution per invocation; the cleanup fixpoint
re-solves the shrunken ladder. The enumeration is generic — no OpenVM constants, no
`native_decide`; it fires exactly when the facts force uniqueness.

**Perf lesson (measured, then fixed).** A first cut hit **+174% eth runtime**: a length-1
"ladder" is every plain byte-checked variable, and each paid the 256-point grid with
runtime-`p` ZMod ops (profile: digitFold 19.0s of 28s on apc_019). A `terms.length ≥ 2` guard
(the idiom is multi-digit by nature) dropped it to **36 ms** on the same case; full-corpus
runtime is now **−1% eth / −2% keccak** vs main.

**Measured (per-case JSON A/B, exactly matching the what-if; first measured vs `9c92008` = #119,
re-measured with identical deltas after rebasing onto `71330d5` = #122 — the fold is independent
of the width-1/subsumed-range and hintCollapse-consolidation landings):**
- openvm-eth (vs `71330d5`): vars agg **4.518× → 4.545×** (geo 3.837× → 3.878×), bus
  **3.506× → 3.536×** (geo 2.762× → 2.796×), constraints 10.511× → 10.544×; 33 cases improved,
  **−165 vars / −141 bus / −36 constraints / 0 regressions** (totals 27967 → 27802 vars,
  16595 → 16454 bus, 11303 → 11267 constraints). Per-case variable W/L/T vs powdr
  **27/29/44 → 30/11/59** — 18 losses flip (apc_045/055/094/026/085 −14 each to parity or win);
  the aggregate bus lead over powdr widens (16454 vs 16722).
- keccak (vs `71330d5`): vars **2025 → 2021 = exact powdr variable parity** (13.618× both), bus
  1959 → 1952 (gap +218), constraints 188 → 186 = **exact powdr constraint parity**, runtime flat
  (273.3s vs 275.8s solo) — the same fold fires on a keccak address ladder and cascades.
- Residual eth variable losses: **11 cases / +56 vars** (was 29 / ~150): apc_037 +14,
  apc_051/018 +9, apc_038 +7, apc_064/042 +4, apc_066/034 +3 (shifted `rd_data__{1,2,3}`
  ladders whose top limb is a full byte — genuinely not forced by the present facts), 3× +1.

**Also measured this iteration (what-if only, no pass): the signed-compare collapse re-scoped.**
The ideas.md #3 remaining slice assumed powdr keeps "a single comparison-result witness" —
render diffs show **powdr has no generic signed-compare collapse either** (it keeps the marker
gadgets on apc_037/100/027; the apparent msb-flag gap is a var-neutral naming difference, flag
vs top limb). Its real lever is **compare-against-constant → is-zero-of-limb-sum** (per-case
renders: `cmp·Σlimbs = 0` + inv witness replacing 4 markers + diff_val). Census on our output:
118 surviving marker-gadget instances, **11 unsigned-vs-constant → est −44 vars / −11 bus over
8 cases** (plus a few signed-vs-constant, e.g. apc_018's second gadget). Smaller than the digit
fold, so deferred — recorded in ideas.md #3 with the corrected mechanism.

Build + `check-proof-integrity.sh` green ({propext, Classical.choice, Quot.sound}-only).
**Worked: yes.**

### 82. NOT-form byte checks: recognize `[x, 255, 255 − x, 1]` as a byte check (idea 4a) — keccak −200 bus, eth −20 bus, 0 regressions

**Idea (ideas.md #4a).** `xorEqExtractPass` (C4b) linearizes a `255`-operand bitwise XOR
`[x, 255, z, 1]` into `z = 255 − x`; Gauss substitutes the NOT-result, leaving `[x, 255, 255 − x, 1]`
on the bitwise-lookup bus — semantically just "x is a byte", but no recognizer matched the shape, so
it was neither dropped nor packed (keccak keeps 200 of these; eth 23). It is the largest remaining
keccak bus family: after #117/#119/#122/#120, the keccak bus gap decomposes to "NOT-form byte checks
200 · ~18 misc".

**Mechanism.**
- New proven fact `BusFacts.xorComplCheck` (OpenVM instance: bitwise-lookup bus, gated `256 ≤ p`
  exactly like its sibling `xorComplEq`): `[x, 255, 255 − x, 1]` and mirror `[255, x, 255 − x, 1]`
  (any multiplicity) are accepted **iff** `x.val < 256`. `trivial` sets it `false`, so the pass is
  VM-agnostic; zero audit surface.
- Both single-value byte-check recognizers gain the two NOT arms. The third slot is decided to be
  `255 − x` by folding `e3 − (255 − e1)` and checking it is the constant `0` via
  `normalize`/`constValue?` (`isByteCompl`; sound by `normalize_eval`):
  - `RedundantByteDrop.byteCheckOperands?` returns `[x]`, so the existing `byteJustified` machinery
    **drops** the interaction (coda) when `x` is byte-justified from the rest of the system;
  - `ByteCheckPack.svCheck?` recognizes it as a single-value check, so `byteCheckPackPass` **packs**
    it (with any other single byte check) into a pair `[x, y, 0, 0]` in the cleanup cycle.

**The "reflection / AND-OR justification rule" ideas.md #4a demanded is NOT needed — stale
attribution.** The file claimed 84 of the 200 keccak operands would need a `255 − v` reflection rule
in `byteJustified`. Re-measured: every one of the 200 NOT-form operands `x` *also* occurs as a raw
variable in a genuine-XOR slot (0/1/2) of a *retained* interaction, and `slotBound` already bounds
those slots to 256, so `findVarBound`/`byteJustified` justify all 200 with the existing machinery —
the coda drop alone removes exactly 200 keccak bitwise interactions. The 84-via-reflection figure
was a stale attribution from base 656a9d8; **no reflection/AND-OR rule was added** (it would be dead
code).

**Why `svCheck?` (cycle packing) too, not just the coda drop.** Coda-drop-only regressed two eth
cases by +1 bus each: recognizing a NOT-form removes it from `RedundantByteDrop`'s non-circular
justification base, so a *second* byte-check on the same operand — previously dropped because the
NOT-form (then in the base) bounded the operand — no longer drops when the operand is not otherwise
justified. Recognizing the NOT-form in `svCheck?` fixes this: the cleanup-cycle packer folds the
operand's two checks into one pair, which the coda `splitBytePair`/`dedupLate` collapse to a single
retained check (net "drop one", not "drop none"). With it both cases become **improvements**.
(On the pre-#120 base the cycle packing also unlocked a −4-var keccak cascade; #120's digit fold now
owns those variables — keccak is already at 2021-var parity — so on this base the change is
variable-neutral and, unlike the pre-#120 measurement, adds **no** keccak runtime.)

**Measured (per-case JSON A/B vs main 851198d; effectiveness is deterministic):**
- keccak: vars 2021 (unchanged, = powdr parity), **bus 1952 → 1752 (−200)**, constraints 186
  (unchanged); bus effectiveness 6.794× → 7.569×. Runtime neutral (587 s vs 619 s back-to-back
  single-threaded — noise on a transiently-slow runner).
- openvm-eth (100 cases): vars agg **4.545× (identical)**, constraints **10.544× (identical)**, bus
  agg 3.536× → **3.541×** (geo 2.796× → 2.799×; powdr 3.480× — the eth bus aggregate leads powdr by
  +0.061×). **3 cases improved (apc_071 −16, apc_037 −2, apc_064 −2) = −20 bus, 0 regressions**;
  per-case W/L/T vs powdr 30/11/59 unchanged; runtime +3% (rough, parallel-contended).

Build + `check-proof-integrity.sh` green ({propext, Classical.choice, Quot.sound}-only); audited
surface untouched. **Worked: yes.**

---

### 83. Seqz comparison-gadget collapse: `sltu x, 1` → two-line is-zero gadget (`SeqzCollapse.lean`)

**Idea (ideas.md #3).** OpenVM lowers `sltu rd, x, 1` (i.e. `rd = (x == 0)`) through its generic
`LessThanCoreChip`: per instance, four `diff_marker` booleans + a `diff_val`, tied by a
14-constraint cluster plus a range-check bus interaction `[diff_val − 1, 0, 0, 0]`. powdr recognises
the constant comparand and replaces all of it with the two-line is-zero gadget
`cmp·S = 0 ∧ inv·S + cmp − 1 = 0` (`S = x₀+x₁+x₂+x₃`), keeping one derived `inv =
QuotientOrZero(1 − cmp, S)`. Because the limbs are byte-range-checked, `S = 0 ⇔ x == 0`, so both
gadgets compute exactly `cmp = [x == 0]`. This pass performs that collapse: it drops the five
private witnesses (`m0..m3`, `diff_val`) and the range bus, and introduces the single `inv`.

**Why the earlier "reuse #114" plan was wrong.** ideas.md #3 proposed reusing
`HintCollapse.collapse_correct`'s parameterized reassignment. That does not apply: `collapse_correct`
collapses **one** bilinear reciprocal-witness constraint whose witnesses are **bus-free**, and
`reencode_correct` keeps **every** bus. Here the cluster is **14** constraints and one witness
(`diff_val`) lives **inside** the range-check bus, so both framings are structurally inapplicable.
The transformation is nonetheless a genuine refinement (powdr does it) and provable directly — it
just needs a bespoke ~500-line `PassCorrect`, not a one-liner. It is **not impossible** under the
current spec; the whole file is machine-checked with no new axioms.

**Proof shape.** The semantic core is two value-level lemmas over the 14 constraint-values (needing
byte bounds on the limbs, `1024 ≤ p`, and the monic constant `2K = −1`): `seqz_forward` derives
`cmp = [S == 0]` (completeness engine) and `seqz_reconstruct` rebuilds the markers/`diff_val` by a
per-limb case analysis (soundness engine; the range check pins the reconstruction to the byte
range). `clusterEval_iff` bridges the serialised constraint templates to those clean value forms.
The framing (`seqzCollapse_correct`) discharges `PassCorrect`: soundness reconstructs a `cs`-model
via `setFive` + `seqz_reconstruct`, re-deriving the dropped range bus from the reconstructed byte
(the absolute "accepted ⇔ byte" law is `bytePairBus` chained with `byteCheck`); completeness supplies
`inv` by `QuotientOrZero` and uses `seqz_forward`; side effects / admissibility are preserved because
the dropped range bus is **stateless** (`bytePairBus ⇒ isStateful = false`, via `admissible_filterBus`
and a stateless-drop list lemma). Field-independent (constants matched structurally, so not tied to
BabyBear); identity under `BusFacts.trivial`.

**Recognizer.** `extractRoles` matches the range bus (`[−1 + dv, 0, 0, 0]`, multiplicity the marker
sum) and the constraint cluster by shape; `rolesValid` gates the collapse on: `Nat.Prime p ∧ 1024 ≤
p`, the monic constant `2K = −1`, `bytePairBus`/`byteCheck` on the bus id, the 14 templates + result
booleanity all present, the range bus present, the five witnesses occurring **only** in the cluster,
byte bounds on the four limbs (via the *output* bounds map), distinctness, `inv` fresh, and the
result/limbs carrying powdr IDs (so witgen can compute `inv`). Wired coda-only, after `monicScale`
(where the cluster has stabilised into the `−1 + x` serialisation the recognizer expects).

**Measured (this branch vs the same pipeline with the coda entry disabled, both vs powdr, over the
100 openvm-eth cases).** A clean win on every axis with **zero regressions**:
- variables (priority axis): agg **4.518× → 4.522×** (geo 3.837× → 3.842×); per-case
  **27 W / 29 L / 44 T → 28 W / 28 L / 44 T** — apc_037 flips from a loss to a win
  (**706 → 690 vars, now below powdr's 692**); lead over powdr +0.427× → **+0.430×**.
- bus interactions: agg **3.479× → 3.480×** — the dropped range check **closes the aggregate bus
  deficit vs powdr from −0.001× to 0.000×**.
- constraints: agg **10.595× → 10.652×** (14 cluster constraints → 2 per instance).
- keccak: unchanged (its lone comparison gadget landed with #114; the seqz idiom is eth-only here).

**Wiring / integrity.** One `codaPasses` entry
(`iterateToFixpoint SeqzCollapse.seqzCollapsePass |>.guardDegree`) plus the import; no audited
surface touched, no new `BusFacts` (reuses the OpenVM `bytePairBus`/`byteCheck` instances). `lake
build` green; proof integrity green (no `sorry`/`admit`/`axiom`/`native_decide`; the top-level
theorems still depend only on `{propext, Classical.choice, Quot.sound}`).

### 84. One-hot annihilation: eliminate dead shift-multiplier variables (idea 5) — −14 eth vars / −252 constraints, 0 regressions

**Idea.** A shift chip with a runtime shift amount but a fixed direction keeps *both*
`bit_multiplier_left` and `bit_multiplier_right`; one is dead. It is forced to `0` by the existing
constraints, but only through a linear combination *across the one-hot marker family* that Gauss
cannot see (the constraints are the nonlinear products `markerᵢ · x`). For a marker set `{mᵢ}` the
block keeps `mᵢ · x = 0` for every `i` plus the closer `±(Σ mᵢ − 1) · x = 0`; writing `s = Σ mᵢ`,
the products give `s·x = 0` and the closer `(s−1)·x = 0` (or `(1−s)·x = 0`), which together force
`x = 0`.

**Pass (`OneHotAnnihilate.lean`, cleanup cycle).** Recognize a closer constraint `A · x` whose
affine cofactor `A` linearizes to `±(Σ mᵢ − 1)` (all coefficients a common unit `k ∈ {1, −1}`,
constant `−k`), and check that every marker's product `mᵢ · x = 0` is present; then **add the
entailed constraint `x = 0`** (`ConstraintSystem.addConstraints_correct`) and let the existing
Gaussian elimination substitute the dead variable away and cascade (each eliminated multiplier
collapses ~18 product constraints). Purely equational — no `BusFacts`, no field/primality
assumption; the added constraint is degree 1. Soundness does not depend on the recognizer being
precise (the added `x = 0` is a linear combination of constraints already present).

*Sign subtlety, found by measurement:* the recognizer initially matched only `(Σmᵢ − 1)·x`
(`const −1`, `coeff 1`), but mid-cycle the optimizer holds the **negated** form `(1 − Σmᵢ)·x`
(`const 1`, `coeff −1 = p−1`) — a later pass flips the sign, so the final render's `(−1 + Σmᵢ)` was
misleading. The recognizer now accepts both signs; both entail the same `x = 0`.

**Measured (per-case JSON A/B vs `main` = #125 `bd367dd`; delta identical when first measured vs
#124 — fully independent of the seqz collapse, which touches different cases).**
- openvm-eth (100 cases): **2 cases improved (apc_038, apc_051), 0 regressions**; each −7 vars /
  −126 constraints, bus-neutral. Corpus totals: vars 27782 → **27768 (−14)**, constraints
  11207 → **10955 (−252)**, bus 16429 unchanged. Aggregate variable effectiveness 4.548× →
  **4.551×**; per-case variables W/L/T vs powdr 31/10/59 → **31/9/60** (one loss flips to a tie).
- keccak: **unchanged** (2021 v / 186 c / 1752 bus) — the pass finds no dead shift-multiplier there
  (the ρ-rotations are encoded differently); it is a no-op, `profile` shows `oneHotAnnihilate` at
  726 ms of ~420 s (0.17%, machine-noise territory). Runtime neutral on both benchmarks.

Build + `Scripts/check-proof-integrity.sh` green — the correctness theorems depend only on
`{propext, Classical.choice, Quot.sound}`. **Worked: yes.**
### 85. Probed slot bounds: reading the XOR-mask range facts (idea 1's residual `JAL` ladders) — −6 eth vars, 2 losses flip to powdr parity, 0 regressions

**The gap.** After entry 81 the residual eth variable losses attributed to constant
decompositions were the `JAL` link ladders (apc_034/066 +3 vars each): the digit fold saw the
byte-checked ladder `[K − 256·rd₁ − 65536·rd₂ − 16777216·rd₃, rd₁, 0, 0]`, but with all-byte
limb bounds the (byte, wrap) grid admits a mod-p phantom digit vector per wrap count and never
collapses to a singleton. Entry 81 recorded "needs a tighter top-limb bound from another
constraint, if one exists". **Rendering the residue shows it exists in every instance** — as
the genuine-XOR check `[rd₃, 192, 192 + rd₃, 1]`: an accepted message forces
`rd₃ ⊕ 192 = rd₃ + 192`, i.e. `rd₃ ∧ 0b11000000 = 0`, i.e. `rd₃ < 64` — OpenVM's 6-bit
top-limb bound for `pc < 2³⁰`, shipped as bit-disjointness rather than a range check. No bound
recognizer read that encoding.

**Mechanism (`probedSlotBoundAt`, DomainProp.lean — generic: no XOR, mask, or OpenVM
specifics).** For an interaction with constant nonzero multiplicity, a variable `x` raw in slot
`i` with a `slotBound` fact `x < B₀ ≤ 256`, a slot `j ≠ i` whose content linearizes to
`l.const + c·x`, a `slotFun` fact computing slot `j` from the rest of the payload, and every
other slot constant: probe all `v < B₀` for `f(payload[x := v, j := 0]) = l.const + c·v` and
bound `x` by one plus the largest survivor (`probeMax`), kept only when it strictly improves on
`B₀`. For the mask check the survivors are exactly `[0, 64)`; for the NOT-form checks
`[x, 255, 255 − x, 1]` every byte survives and nothing is inserted. `BoundsMap.addAll` feeds the
probed bound through the existing `insertEntry` (keeping the smaller); `digitFold`'s grid then
collapses to a singleton and the existing cascade folds the ladder — **no new pass, no
`digitFold` change**. A once-per-interaction pre-scan (`probeCandidatesOf`: a slot affine in a
single variable `y` can only ever bound `y`) keeps the recognizer off the hot path; the first
cut without it re-linearized per (variable, slot) pair and looked like +37% keccak runtime —
which turned out to be measurement error against entry 81's runtime from a different machine
(see below), but the pre-scan is the right shape regardless.

**Why sound.** `slotFun_sound` pins the evaluated slot `j` to `f` of the zeroed payload; with
slots `≠ i, j` constant and slot `i` a raw variable, that zeroed payload *is* the probe payload
at `v = x.val` (`probeBase_eq_set`, a `getElem?`-extensionality argument); `linearize` pins slot
`j`'s value to `l.const + c·x`; so `x.val` survives the probe and `probeMax_lt` bounds it.
Needs `p ≠ 0` only (val/cast round-trip); no primality.

**Measured (per-case JSON A/B vs main `2b1e5c1`, all 100 eth cases + keccak):**
- openvm-eth: vars **27,768 → 27,762 (−6)**, bus 16,429 → 16,424 (−5), constraints unchanged;
  exactly two cases move — apc_034 −3 vars/−3 bus → **105/22/80 = exact powdr parity**, apc_066
  −3 vars/−2 bus → **49/10/37 = exact powdr parity** — and nothing else changes. Variable
  W/L/T vs powdr **31/9/60 → 31/7/62**; agg vars 4.551× → 4.552× (geo 3.884× → 3.887×), bus
  3.542× → 3.543× (geo 2.800× → 2.803×).
- keccak: bit-identical (2021 / 1752 / 186); runtime 369 s vs main 383 s **solo on the same
  container** (parity). Note for future entries: entry 81's ~275 s keccak runtime was measured
  on different hardware — always re-measure the baseline on the machine at hand before calling
  a runtime regression (this iteration chased a phantom +37% for one round because of it).
- The remaining "parts of apc_038/042/064" residue did not move — their ladders lack a mask
  check on the top limb; they stay with the joint-refutation slice in ideas.md.

Build + `check-proof-integrity.sh` green ({propext, Classical.choice, Quot.sound}-only).
**Worked: yes.**

### 86. Optimizer runtime: hoist `domainFold`'s constant-on-survivors evaluation (effectiveness unchanged)

Pure **performance** work in the entry-45/54 style — output-preserving, so effectiveness is
untouched and only wall-clock cost drops. Closes entry 54's documented `domainFold` leftover
("`domainFold` evaluates through the plain per-node-instance `Expression.eval` — the `evalFast`
treatment applies almost verbatim"). Entry 54 had upgraded `domainFold`'s survivor *filter*
(`groupSurvivorsE`) to `evalFast`, but the fold-decision core `constOnSurvs` was still on the slow
path.

**The two fixes (both extensionally equal to the old form, so the fold decision and the folded
constant are unchanged):**
1. Evaluate through `Expression.evalFast` (field operations derived once per call instead of
   re-projecting the `ZMod p` `CommRing` instance chain at every expression node — the entry-54
   tax), via the existing `Expression.evalFast_eq`.
2. Compute the reference value `e.evalFast (envOf s₀)` **once** with a `let` rather than
   re-evaluating it against every survivor inside the `.all` (the old
   `fun s => e.eval (envOf s) = e.eval (envOf s₀)` recomputed the `s₀` value once per survivor).

Only `constOnSurvs` and its soundness lemma `constOnSurvs_sound` change; `foldRewrite` /
`foldRewrite_agree` consume `constOnSurvs` abstractly (via the soundness lemma and a `cases` on its
`Option` result), so they are untouched. The folded constant is numerically identical
(`evalFast_eq`), so the circuit the pass emits is unchanged.

**Measured (clean A/B, both binaries built from the current source; the session's pre-built binary
turned out to be stale — an older commit with a slower `domainBatch` — so it is not a valid
baseline and was discarded).** Output byte-for-byte identical (`vars/constraints/bus`) on
apc_001/005/006/009/012. `domainFold` per-pass time (profiler, same-process, so binary-load is
amortised):
- apc_005 / apc_009 (same load/store block, the heaviest fold case): **6221 → 4691 ms (−25 %)**.
- apc_006: 2416 → 2274 ms (−6 %); apc_012: 1767 → 1732 ms (−2 %).

The win is concentrated on the constant-fold-heavy load/store cases (where `constOnSurvs` runs over
many survivors × many fold candidates) and is within noise on the rest; whole-optimizer totals move
only within run-to-run noise. keccak is unaffected in practice (186 constraints — `domainFold` does
little there). The change never does *more* work in `domainFold`.

`lake build` green; `Scripts/check-proof-integrity.sh` green — the correctness theorems still depend
only on `{propext, Classical.choice, Quot.sound}`; no `sorry`/`admit`/`axiom`/`native_decide`; no
audited surface, `Basic.lean`/`FactPass.lean`, or pass-pipeline change. **Worked: yes (modest).**

**Runtime picture / bigger levers (measured this session; documented for future work).** Per-pass
share over the top-12 eth cases: `busPairCancel` 31 %, `domainBatch` 24 %, `domainFold` 14 %,
`reencode` 13 % (top-4 = 82 %; the finite-domain family alone = 51 %); the cleanup cycle iterates
4–7× on the expensive cases. The two largest remaining levers both need real proof effort, not just
a hoist: (a) the **pinned-variable box reduction** in the finite-domain enumeration (entries 45 &
54) — substitute the domain-1 (pinned) variables as constants and enumerate/compile only the free
vars, shrinking every enumerated point; attacks the dominant 51 % directly, self-contained in
`DomainBatch.lean`, needs `forcedOver`'s soundness re-proven against the reduced box. (b)
`busPairCancel` (top on eth, and dominant on memory-heavy keccak) — already heavily tuned
(entries 55/56); the residual is the deep byte-justification's per-candidate `findVarBound` rescan
and per-point `substF`/`linearize`. A cheaper extension of *this* entry: index-compile
`constOnSurvs` (à la `domainBatch`'s `IExpr`) to also drop the `envOf` linear scan, which would help
the cases where the `evalFast` hoist alone barely moved.

### 87. Affine same-base address disequality (`addrAffineNeq`): closes the wasm-eth variable gap — apc reaches powdr parity or better on every case (wasm-eth root cause 1)

**The gap** (`../leanr-wasm/fable-wasm-1.md`, root cause 1). On the `wasm-eth` corpus (merged
#131), memory forwarding never fired for the frame-pointer-relative shadow stack (address space
1). A wasm stack pointer is `c + fp` — a symbolic base `fp` plus a constant offset — which
neither existing disequality certificate can refute: `addrConstsNeq` needs both slots literal,
and `addrTwoRootNeq` needs a two-root limb-wraparound decomposition + primality (`fp` has
neither). So `busUnifyPass`'s consumer scan (`findConsumer`) and `busPairCancel`'s mid-region
check (`midRefuted`) both aborted at the *first* interleaved other-stack-slot access
(`140+fp` vs `108+fp` could not be refuted as a different address), and **no AS-1 access was ever
forwarded** on the big blocks. The excess scaled with reuse count — the three worst offenders
(apc_037/012/006, k256 square/mul + tiny_keccak `keccakf`) sat at **4.85× / 4.81× / 4.20×** the
powdr variable count.

**The fix.** A third disequality certificate `addrAffineNeq` (`AddrDiseq.lean`): for some address
slot, `linearize` both expressions, subtract, `.norm`; if the difference has no variable terms
and a nonzero constant, the slots provably differ — `(c₁+fp) − (c₂+fp) = c₁−c₂ ≠ 0`. No bounds,
no primality, no `TwoRootMap`, no constraints consulted — a total `Bool` predicate. Soundness is
three lines: `linearize_eval` on each slot + the existing `constDiffNZ_sound`. Wired as a third
disjunct at the refutation sites — `findConsumer`/`checkPair` (`BusUnify.lean`) and `midRefuted`
(`BusPairCancel.lean`, through which `preRefuted`/`shieldOk` and the aggressive-path array scan all
funnel). The consumer *equality* side already worked (`addrConstsEq`'s syntactic `e = e'` branch
matches two identical `fp+c` expressions), so only the mid-region disequality was missing. It
**strictly generalizes** `addrConstsNeq` (const−const is a constant difference), so it can only
enable *more* cancellation, never less; and it needs no primality/two-root, so it composes as a
separate disjunct with `addrTwoRootNeq` (kept for the keccak heap, whose distinct-limb pointers
have a variable-bearing difference that `addrAffineNeq` correctly declines).

**Impact — wasm-eth (`apc-optimizer compare` vs powdr, variables the top-priority metric):**

| case | apc vars (main) | apc vars (now) | powdr vars | ratio now | ratio main |
|------|----:|----:|----:|----:|----:|
| apc_037 k256 square | 9201 | 1929 | 1896 | 1.02× | 4.85× |
| apc_012 k256 mul     | 12885 | 2705 | 2678 | 1.01× | 4.81× |
| apc_006 keccakf      | 8021 | 1606 | 1908 | **0.84×** | 4.20× |
| apc_028              | — | 1478 | 1478 | 1.00× | — |
| apc_004              | — | 238 | 238 | 1.00× | — |
| apc_005              | — | 184 | 200 | **0.92×** | — |
| apc_022              | — | 21 | 21 | 1.00× | — |

Variable effectiveness reaches **powdr parity or better on every case measured** (apc_006 and
apc_005 beat powdr outright); constraints likewise at/near parity (apc_006 88 vs powdr 548;
apc_012 1034 = 1034; apc_004 118 = 118). The residual is entirely **bus interactions** (apc_037
2317 vs 1430, apc_006 1934 vs 1479, apc_022 19 vs 15): the byte-identical AS-5 fp-cell pairs and
the fp-read chains — the target of the stacked step 2 (`recvByteSlots`).

**openvm-eth (the merge-gating benchmark): no regression — a slight win.** 100-case sweep,
aggregate / geo effectiveness: variables **4.552× / 3.887×** (powdr 4.092× / 3.787×; main was
4.551× agg), bus **3.543× / 2.803×** (powdr 3.480×), constraints **10.845× / 12.026×** (powdr
5.853×). Per-case variables W/L/T vs powdr **31 / 7 / 62** — vs the pre-change **31 / 9 / 60**,
**two powdr-losses flip to ties** (affine addressing enabled an additional forward), zero
regressions. Exactly what monotonicity predicts: the new disjunct only ever refutes *more*.
keccak two-root heap path unchanged.

Build + `Scripts/check-proof-integrity.sh` green (`{propext, Classical.choice, Quot.sound}` only);
no `sorry`/`admit`/`axiom`/`native_decide`; no audited-surface / `Basic.lean` / `FactPass.lean` /
pass-pipeline change (correctness rides on the pass's own `PassCorrect`, extended by one `rcases`
branch per soundness theorem). **Worked: yes (major — the dominant wasm-eth variable lever).**

### 88. Pattern-aware `recvByteSlots`: cancel non-{1,2} address-space memory pairs (wasm-eth root cause 2)

**The gap** (`../leanr-wasm/fable-wasm-1.md`, root cause 2). After entry 87's forwarding,
`busPairCancel` still refused to drop the byte-identical AS-5 pairs — the wasm frame-pointer cell
`send(5,0,fp,0,0,0,k+ts)` immediately followed by its `receive` — because dropping a memory
*receive* re-imposes its byte obligation, and the `recvByteSlots` fact declared the byte slots
`[2,3,4,5]` **per bus, unconditionally**. The fp payload has `fp` at slot 2, which is not a byte,
so justification failed and no cancellation ever fired. But the obligation is **vacuous**:
`violates` (`OpenVmSemantics.lean`) only rejects a non-byte memory receive when its address-space
slot is 1 or 2; an AS-5 receive never violates, whatever its data.

**The fix.** Make the `recvByteSlots` `BusFacts` field pattern-aware, mirroring `slotBound`'s
signature — `recvByteSlots busId pattern`. The OpenVM instance (`recvByteSlotsImpl`) returns `[]`
(no obligation) for a memory receive whose AS slot is a known constant ∉ {1,2}, and `[2,3,4,5]`
otherwise (AS ∈ {1,2}, or a symbolic AS — conservative). The new soundness lemma
`memory_recv_nonByte_ok`: a memory message with a constant AS ∉ {1,2} never violates, whatever its
data (that arm of `violates` is `false`). `recvByteSlots_sound`'s **send** clause stays
pattern-free (sends never violate); the **receive** clause gains a `Matches m.payload pattern`
hypothesis, discharged by the existing `matches_evalPattern`. Threaded through `BusPairCancel`:
`slots` moves from per-bus to **per-candidate**, resolved from `R.payload.map constValue?` at each
candidate receive (`findCancel`/`findCancelForBus`/`findCancelGoIdx` shed the per-bus `slots`
argument); `dropPair_correct`/`checkCancel_sound` gain the pattern and its `Matches` witness. All
of this is `Implementation/` — `BusFacts.lean` is zero audit surface (a wrong fact would not
compile); the trivial instance adapts mechanically.

**Impact — wasm-eth (bus interactions; variables unchanged from entry 87):**

| case | apc bus (entry 87) | apc bus (now) | powdr bus |
|------|----:|----:|----:|
| apc_006 keccakf | 1934 | 1498 | 1479 |
| apc_022         | 19 | **15** | 15 |
| apc_004         | 246 | 176 | 146 |
| apc_005         | 140 | 106 | 92 |

apc_022 reaches **exact bus parity** (15 = 15, plus var/constraint parity); apc_006 drops −436
(1934 → 1498, near powdr's 1479) and is now **at or better than powdr on all three axes**
(vars 1606 < 1908, bus 1498 ≈ 1479, constraints 88 ≪ 548). Exactly the plan's predicted −436 on
apc_006 — the AS-5 identical-payload fp cells now telescope. The residual bus gap on the mid cases
(apc_004/005) is the shift-carry / range-rebuild residue (step 4).

**openvm-eth (merge-gating): byte-for-byte identical to entry 87** — 100-case `--compare` reports
Δ **+0.000×** on every axis, "per-case circuit sizes identical". eth has no non-{1,2} address
spaces, so `recvByteSlots` returns `[2,3,4,5]` for every receive exactly as the old unconditional
form did. keccak unchanged (2021v/186c/1752bus; its heap is AS 2 ∈ {1,2}). No regression anywhere.

Build + `Scripts/check-proof-integrity.sh` green ({propext, Classical.choice, Quot.sound} only);
no `sorry`/`admit`/`axiom`/`native_decide`; no audited-surface / `Basic.lean` / `FactPass.lean` /
pass-pipeline change. **Worked: yes (bus-effectiveness lever; prerequisite for full AS-5
telescoping).**

### 89. wasm-eth corpus measurement + re-ranking (entries 87 + 88 combined): apc goes from far behind to ahead of powdr on variables

Full-corpus A/B of the two wasm-eth fixes (entries 87 + 88 together) against pre-fix `main`
(`c6a167b`), plus the openvm-eth merge gate. Both binaries built from source; `benchmark.py`
`--jobs` default (parallel, so per-case runtimes are rough).

**wasm-eth, 100 cases — apc-optimizer effectiveness (size before / after; agg / geomean), main → stack:**

| measure | main | stack | Δ (agg) | powdr |
|---|---|---|---|---|
| variables | 1.979× / 2.756× | **7.228× / 3.588×** | **+5.248×** | 6.273× / 3.542× |
| bus interactions | 1.547× / 1.840× | **5.254× / 2.714×** | +3.707× | 5.666× / 2.868× |
| constraints | 14.664× / 10.279× | **15.165× / 10.438×** | +0.501× | 9.671× / 11.949× |

Circuit sizes changed on **100 of 100** cases. On the **top-priority variable** axis apc now
**leads powdr** (7.228× vs 6.273×): total surviving variables **apc 17035 vs powdr 19628** — apc
uses **13% fewer** than powdr corpus-wide. Per-case variables W/L/T vs powdr: **1/56/43 → 16/11/73**
(main lost 56 cases to powdr; the stack loses 11, all by a handful of vars on tiny blocks). The
worst variable-ratio offender went from **4.85×** (apc_037 on main) to **1.15×** (apc_060, a
23-vs-20-var block); the three headline cases: apc_037 4.85→1.02, apc_012 4.81→1.01, apc_006
4.20→**0.84** (beats powdr). Constraints already crushed powdr and improved further. Bus
interactions closed most of the gap (1.547×→5.254×, near powdr's 5.666×); the residual (apc 13535
vs powdr 12552 total, +8%) is concentrated in apc_037/012 — the shift-carry / functional-XOR /
range-rebuild residue (entry-90 / ideas.md follow-ups). Re-ranking saved to
`../leanr-wasm/worst_vars_wasm.txt`.

**Runtime:** essentially **flat** — main 1924 s vs stack 1965 s (+2 %, within parallel-contention
noise), *not* the 5–8× collapse the investigation hoped for. Forwarding now succeeds (far fewer
surviving interactions), but the enabling scans (`findConsumer`/`midRefuted` crossing refutable
slots, plus the extra cancellations that now land) cost about what the shrink saves. So the win is
entirely output size at flat cost; the fixpoint is still doing real per-cycle work on the big k256
cases — a profiling target noted for step 4, not a regression.

**openvm-eth (merge gate): no regression.** vs pre-fix main, aggregate variables 4.551× → **4.552×**
(bus 3.543×, constraints 10.845×; all ≥ main), per-case vars W/L/T vs powdr 31/9/60 → **31/7/62**
(two powdr-losses flip to ties, entry 87). Entry 88 is byte-identical to entry 87 on eth. **keccak
unchanged** (2021 v / 186 c / 1752 bus). Build + `Scripts/check-proof-integrity.sh` green
throughout ({propext, Classical.choice, Quot.sound} only). **Worked: yes — the wasm-eth variable
gap that motivated the investigation (`../leanr-wasm/fable-wasm-1.md`) is closed; apc now leads
powdr on variables and constraints, trails only slightly on bus.**
