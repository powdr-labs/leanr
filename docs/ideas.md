# Ideas for future optimization passes

Ranked by estimated benchmark impact under the effectiveness priority (**variables > bus
interactions > constraints**), certainty-weighted. Ideas **1** and **4** require a *slight,
completeness-only extension of the audited spec* and are **flagged for Georg's review** — do not
implement them without sign-off; the next autoopt iteration should start at idea **2**.

Empirical basis (2026-07-09 brainstorm; renders/reports of apc_002/003/004/008/010/014/020/023/
025/028/030/069 vs powdr): leanr now *beats* powdr on variables and constraints on nearly every
sampled case (e.g. apc_010: 480 vars/258 constraints vs powdr 498/331; apc_020: 818/317 vs
850/501) and the pc-lookup (bus 2) gap is already closed (0 bus-2 interactions in every sampled
output — domainFold pins the payloads, tautoBusDrop removes them). The residual leanr-vs-powdr
variable gaps decompose *exactly* into the patterns behind ideas 1–3 and 5–7 (e.g. apc_069's gap
of 10 = 4 x0-read vars + 3 XOR-forced vars + 3 cascaded diff_inv_markers; apc_023's gap of 9 = 4
XOR-forced + 3 dead-decomposition + 2 duplicate-address limbs); the residual bus gap is memory
chains blocked on syntactic payload mismatch (idea 8) and unpacked byte checks (idea 9).

---

## 1. Zero-register (x0) data zeroing — **[SPEC CHANGE — review before implementing]**

**Impact estimate: ~200–260 variables over the 100-case benchmark** (largest single residual
class), plus cascaded constraint/bus drops. **Axis: variables. Proof difficulty: medium.**

OpenVM stores RISC-V registers in address space 1; cell (1,0) is x0 — never written (the
transpiler forces `needs_write` off for rd = x0) and zero-initialized. Blocks that read x0 leave
a receive/send pair `[1, 0, d0..d3, ts]` whose 4 data variables leanr keeps forever: they are
chain endpoints (busUnify cannot cancel them, disconnectedComponent cannot drop them — stateful
bus). powdr bakes the invariant in: **47 of 100** powdr_opt outputs contain `[1,0,0,0,0,0]`
memory messages (94 messages total, ~188 endpoint vars), and the zeros cascade: on apc_069 the
x0 cluster explains 7 of the 10-var gap (4 data vars + 3 `diff_inv_marker`s that die once
`0 * marker` terms fold); apc_008's gap of 24 is dominated by x0 feeding two comparison gadgets.

**Spec change (audited surface, completeness-only):** add one conjunct to the OpenVM `admissible`
predicate (`Leanr/OpenVmSemantics.lean`), documented in the README assumptions: every *active*
memory-bus message whose address fields are (1,0) carries all-zero data slots. Same tier as the
existing last-write-wins/timestamp-order assumption: true of every real trace, used only in the
completeness direction (`impliesAdmissible`), so a malicious prover is unaffected — soundness
never invokes `admissible`. Bridged to passes by a new *proven* `BusFacts` field (zero audit
surface), like `admissible_dropPair`.

```
-- audited (OpenVmSemantics.lean): add one conjunct to the OpenVM admissible predicate:
--   ∀ m ∈ activeMessages, memShapeOf m.busId = memory → m.payload prefix = [1, 0] →
--     data slots of m.payload are all 0
-- BusFacts (Implementation/, proven): zeroCellData : busId → Option (List (ZMod p)) -- [1,0]
--   zeroCellData_sound : bs.admissible msgs → m ∈ msgs → m.multiplicity ≠ 0 →
--     zeroCellData m.busId = some pfx → payload prefix = pfx → data slots of m = 0

def zeroRegPass (facts) (cs) :=
  let eqs := cs.busInteractions.filterMap fun bi =>
    match facts.zeroCellData bi.busId with
    | some pfx =>
        if bi.multiplicity.isNonzeroConst &&
           (pfx.zip bi.payload).all (fun (c, e) => e.constValue? = some c)
        then some (dataSlots bi.payload)     -- each slot e becomes the constraint e = 0
        else none
    | none => none
  cs.withConstraints (cs.algebraicConstraints ++ eqs.flatten)
-- PassCorrect: soundness = drop the added constraints (trivial); completeness = zeroCellData_sound
-- (the busUnify pattern: admissibility-entailed equations). env' = env, no derivations.
-- gauss/constantFold then substitute the zeros; comparison gadgets collapse downstream.
```

Evidence: powdr apc_069 reads x0 as `[1, 0, 0, 0, 0, 0, ts]` vs leanr's `[1, 0, b__0_1..b__3_1,
ts]`; confirmed one x0 pair each in apc_008/014/023/025/028/069 renders.

## 2. Bitwise forced-slot equations (`slotEq`: XOR with a constant-zero operand)

**Impact estimate: ~100–160 variables** (19 harvestable instances counted across 12 sampled
cases: apc_008: 6, apc_010: 3, apc_014: 3, apc_023: 4, apc_069: 3 — each kills exactly 1 var via
gauss), plus ~40 bus interactions whose messages become fully constant and hit tautoBusDrop.
**Axis: variables. Proof difficulty: easy. No spec change.** *Best effort/impact ratio — start
here.*

The bitwise bus (op = 1) accepts exactly `(x, y, x XOR y, 1)` for bytes x, y. When one input slot
is the literal 0, the interaction *forces* a linear identity between the other two slots:
`[0, e1, e2, 1]` ⇒ `e2 = e1`; `[e1, 0, e2, 1]` ⇒ `e2 = e1`. leanr's final outputs contain many
such interactions whose forced equation is never harvested — the andi-mask / sign-extension
idiom, e.g. apc_023's `[0, c__0_14, 2*read_data__0_15 - c__0_14, 1]` (forces `read_data__0_15 =
c__0_14`) and apc_069's `[b__1_0, 0, -2*a__1_1 + b__1_0, 1]` (forces `a__1_1 = 0`). domainBatch
cannot see them: the forced vars have no constraint-derived domain to enumerate.

New proven `BusFacts` field (Implementation/, zero audit): `slotEq : busId → pattern →
Option (Nat × Nat)` — "accepted messages matching the pattern have `payload[i] = payload[j]`".
OpenVM instance: bus 6 with pattern `[some 0, none, none, some 1] ↦ (1,2)` and
`[none, some 0, none, some 1] ↦ (0,2)` (0 XOR v = v). Patterns are built from constant payload
slots exactly as DomainProp already builds slotBound patterns.

```
def slotEqPass (facts) (cs) :=
  let eqs := cs.busInteractions.filterMap fun bi =>
    if !bi.multiplicity.isNonzeroConst then none else
    match facts.slotEq bi.busId (bi.payload.map Expression.constValue?) with
    | some (i, j) => some (monicNormalize (bi.payload[i] - bi.payload[j]))
    | none => none
  cs.withConstraints (cs.algebraicConstraints ++ eqs.dedup)
-- PassCorrect: adds entailed constraints only. Soundness: drop them. Completeness: satisfies
-- demands violatesConstraint = false for every message with mult ≠ 0 (Spec.lean:198), then
-- slotEq_sound gives the equation — the same plumbing DomainProp uses for slotBound.
-- monicNormalize so gauss's unit-coefficient pivot fires (2*rd - 2*c = 0 → rd - c = 0).
```

Generalization (agent-0 variant, optional second step): probe `slotFun` over a slotBound-bounded
input slot to also cover "all determining slots constant ⇒ out slot = f(consts)" and non-XOR
identities; the two-pattern `slotEq` above already captures every instance observed.

## 3. Range-excluded-root linearization (`rangeSolvePass`)

**Impact estimate: ~100–250 variables** (mv/addi-0 result limbs and ALU-based imm=0 address
decompositions; measured: apc_008 −8 vars + ~6 bus + −8 constraints, apc_004 −2 vars — exactly
the vars powdr kills there), plus unlocked busPairCancel cancellations. **Axis: variables.
Proof difficulty: hard. No spec change.**

powdr's workhorse that leanr lacks. After normalization many constraints have the two-root form
`F * (F − d) = 0` with F affine and d a syntactic constant (carry/borrow elimination from
ADD/SUB/mv and mem_ptr decomposition). When every variable of F carries an in-circuit range bound
(byte checks `[v,v,0,1]` on the bitwise bus, `[v,bits]` on the range checker — all already exposed
by proven `BusFacts.slotBound`), lift F to a signed-integer interval; if the interval excludes the
root d (e.g. F = a_old − a_new with both byte-checked ⇒ F ∈ [−255,255], excluding 256), **replace
the quadratic with the linear `F = 0`** — gauss then eliminates one variable per constraint.
Mid-pipeline coefficients are scaled (e.g. 7864320 = (p−1)/256), so search a small scalar s
(powers of 256, or the inverse of a pivot coefficient) making s·F's signed coefficients small
before bounding.

```
for each constraint C = F * (F - d), F affine, d constant:
  bounds: for v ∈ F.vars find bound(v) from stateless lookups present in cs (slotBound):
    [v,v,0,1] / [v,y,0,1] / [x,v,0,1] on bitwise bus → 256; [v, bits] on range checker → 2^bits
  for s in {1, 256, 65536, 2^24} ∪ {c⁻¹ : c coeff of F}:
    F' := s*F, d' := s*d
    if all coeffs of F' signed-small (min(c, p−c) < 2^26):
      [lo, hi] := interval of F' from bounds;  if hi − lo < p:
        if signed(d') ∉ [lo,hi] and 0 ∈ [lo,hi]: replace C with F = 0
        if 0 ∉ [lo,hi] and signed(d') ∈ [lo,hi]: replace C with F − d = 0
-- PassCorrect (ofEnvEq): soundness trivial (F=0 ⇒ F*(F−d)=0). Completeness: the bounding lookups
-- have const mult 1 ⇒ accepted ⇒ slotBound_sound bounds each var ⇒ a decide-checked
-- integer-interval lemma shows (s*F).eval env ≠ s*d, hence F.eval env = 0. Degree only drops.
```

Evidence: apc_008 keeps `(a__0_1 − a__0_10)*(a__0_1 − a__0_10 − 256) = 0` (×8) with both families
byte-checked in-circuit; powdr's output has neither the constraints nor the vars. Two-root
candidates counted: apc_002 4, apc_003 7, apc_004 3, apc_008 18.

## 4. Received-memory-data byte bounds — **[SPEC CHANGE — review before implementing]**

**Impact estimate: ~150–300 variables combined with idea 3** — unlocks the excluded-root cases
whose base limbs are plain register reads with *no in-circuit byte check* (apc_002 −4, apc_003
−4, apc_004 −2, apc_008 −4 beyond idea 3). powdr *misses* these (its range info doesn't cover
read data either), so this puts leanr **strictly ahead** on cases it currently loses (apc_003
129 vs powdr 131). **Axis: variables. Proof difficulty: hard.**

**Spec change (audited, completeness-only):** extend the OpenVM `admissible` predicate with:
active memory-bus messages carry byte-valued data slots. Already anticipated by the TODO in
`OpenVmSemantics.lean` (~line 105): "under the invariant that all *sent* memory values are
range-checked, *received* memory values can be assumed to be range-checked". Every value entering
OpenVM memory is a range-checked u8 cell (chips range-check writes; boundary/merkle chips enforce
byte-ness of initial memory), so every real trace satisfies it. Consumed only in the completeness
branch: the two-root rewrite `F*(F−d)=0 → F=0` is *always sound* (F=0 implies the product), and
only completeness needs the bound — an admissible-only fact suffices, no soundness hole.
Bridge: new proven `BusFacts` field `dataBytes : busId → Option (List Nat)` (data-slot indices)
with soundness vs `admissible`; `rangeSolvePass` consults it for bounds on bare-variable data
slots of memory receives, and runs the excluded-root argument inside `impliesAdmissible` where
`cs.admissible` provides the bounds.

## 5. Solve-by-carry witness finder for `disconnectedComponentPass`

**Impact estimate: ~90–100 variables + ~120 bus interactions** (~29 cases × ~3 vars of orphaned
register reads, plus dead register *writes* of link values — apc_023: 3 vars, 4 bus). **Axis:
variables. Proof difficulty: easy — zero proof change.** No spec change.

The pass currently certifies a dropped component satisfiable only with the **all-zero** witness.
The common residue is a dead affine byte-decomposition cluster, e.g. apc_023 keeps
`rd_data__{0,1,2}_20` occurring *only* in `[3317668 − 256·rd0 − 65536·rd1 − 16777216·rd2, rd0,
0, 0]` (bus 6) + `[rd1, 8]`, `[rd2, 6]` (bus 3) — a disconnected component where zero fails but
the base-256 decomposition of the constant (164, 159, 50) satisfies every lookup. Only the
witness *finder* changes; the correctness machinery already accepts any witness (it re-checks
`violatesConstraint`/`eval` at run time). Keep it general (probe-driven, no base-256 hardcoding):

```
def findWitness (component) : Option (Var → ZMod p) :=
  env := {};  repeat until fixpoint:
    for lookup in component.lookups, for slot in lookup.payload:
      if slot.evalPartial env is affine with a single unresolved var x:
        try values v from x's own lookup-admitted domain (≤ 2^8, probe violatesConstraint);
        pick v such that probing the lookup with slot value (K − c·v) accepts; env[x] := v
  final check: all component constraints eval 0, all stateless lookups accepted (existing check)
```

## 6. Duplicate address-limb unification (two-root disambiguation) + stateless dedup

**Impact estimate: ~80 variables + ~80 constraints + ~80 bus interactions** (5 duplicate address
pairs in 12 sampled cases, ~2 vars each; apc_004/020/023/025). **Axis: variables. Proof
difficulty: medium.** No spec change.

When a block accesses the same (base register, immediate) address twice, leanr keeps two copies
of the mem_ptr limb vars, each defined by an *identical-up-to-renaming* two-root constraint
`(E + a − x)(E + a − 65536 − x) = 0` plus identical scaled range checks `[4⁻¹·x, 14]`. Equality
`x = y` is entailed: both lie in `{E+a, E+a−65536}` so `x − y ∈ {0, ±65536}`, and the range
checks bound `val(4⁻¹·x), val(4⁻¹·y) < 2^14` while `4⁻¹·(±65536) = ±2^14` cannot be a difference
of two values below 2^14 (decidable check: `delta.val ≥ 2^b ∧ (p − delta.val) ≥ 2^b`).
Substituting `y := x` is a pure rewrite in the domainFold style (`ofEnvEq`, agreement on all
satisfying assignments). Limb-0 unification makes the limb-1 constraints identical, cascading.
Afterwards the pair's constraints/lookups are *exact duplicates* — add a trivial duplicate-drop
sub-pass (identical constraint; identical stateless interaction: violation is per-message,
stateless messages are outside the side-effect relation) to harvest the bus/constraint half.

## 7. Bound-1 range-check slots become equations (`bits = 0` forces `e = 0`)

**Impact estimate: ~50–250 variables** (apc_020: −11 vars/−11 bus measured; frequency uncertain —
1 of 12 sampled cases, but the register-equality idiom suggests 10–25 cases at 3–12 vars).
**Axis: variables. Proof difficulty: easy.** No spec change.

apc_020 keeps 11 range checks `[x − y, 0]`: bits = 0 means `(x−y).val < 2^0 = 1`, i.e. `x = y`.
domainBatch's slotBound reasoning fires only on *bare-variable* slots; here the slot is affine, so
both var and interaction survive. Pass: for every stateless interaction with constant nonzero
multiplicity and `facts.slotBound busId pattern slot = some 1`, add the entailed constraint
`payload[slot] = 0` (three lines from `slotBound_sound`; the busUnify `addConstraints` shape).
gauss then eliminates a variable, the slot folds to 0, tautoBusDrop removes the interaction.

## 8. `busPairCancel`: payload equality modulo kept constraints

**Impact estimate: ~1000–1500 bus interactions** — the single largest residual bus gap
(apc_010: bus 1 goes 144 → 78, exact powdr parity; apc_014: −34; the loadb/loadh class is
~25–40 of 100 cases at −30 to −60 each). **Axis: bus (variable-neutral). Proof difficulty:
medium.** No spec change.

The dominant load/store bus gap: every loadb/loadh *write* pair has send slot = a degree-2
sign/shift mux M while the matching receive slot is the single variable `read_data__0_k` —
syntactically unequal, though the witness equation `read_data__0_k − M = 0` is *already a kept
constraint* (busUnify added it; gauss can't substitute a non-affine pivot). And each
uncancellable pair blocks all later payload-identical pairs on that address via the
earliest-active-send precondition. Extend `checkCancel`: slots (Sᵢ, Rᵢ) match if syntactically
equal **or** the normalized difference `(Rᵢ − Sᵢ).normalize.fold` equals ±(a kept constraint's
normal form). Both `out` and `cs` keep the same algebraicConstraints, so evaluated payload
equality holds on every satisfying env of either system — which is all `dropPair_correct`
consumes (`hpay` is only used at out-satisfying envs for soundness and cs-satisfying envs for
completeness). Rework `hpay : S.payload = R.payload` into
`∀ env, (∀ c ∈ cs.algebraicConstraints, c.eval env = 0) → (S.eval env).payload = (R.eval env).payload`.
Once the first write pair cancels, the fixpoint drains the whole chain to powdr's
2-endpoints-per-register state.

Note (measured, saves a dead end): symbolic heap addresses are *not* worth chaining — all 32 of
apc_010's symbolic addresses carry exactly 2 messages in both leanr and powdr.

## 9. Stateless byte-check packing (`[x,x,0,1]` pairs → `[x,y,0,0]`; tuple-bus pairing)

**Impact estimate: ~700–1200 bus interactions** (apc_003: −11 = its *entire* residual gap,
reaching exact powdr parity; apc_008: −12; apc_020: −40 to −60; 70+ cases with ≥8 packable
checks). **Axis: bus (variable-neutral). Proof difficulty: easy–medium.** No spec change.

leanr emits one bitwise lookup per byte check (`[x, x, 0, 1]` self-XORs — 12–24 per ALU-heavy
case); powdr packs two byte checks into one op-0 lookup `[x, y, 0, 0]` (exact table equivalence:
`[x,y,0,0]` accepted ⟺ x,y bytes ⟺ `[x,x,0,1] ∧ [y,y,0,1]` accepted) and further pairs a byte
with a ≤11-bit check on the declared-but-unused-by-leanr `TupleRangeChecker(256,2048)` bus.
Expose the equivalence through a new proven `BusFacts` field (`boundCheck_iff`: non-violation ⟺
declared value bounds; plus `sendInvariantOk` for the emitted message's `breaksInvariant`
obligation), then greedily pair single-bound messages with constant mult 1. Subsumption dedup
falls out free (a message whose bounds are implied by kept messages packs into nothing).
Stateless ⇒ no side effects; both refines directions are pure `violatesConstraint` reasoning.

## 10. `busPairCancel`: relax earliest-send to nearest-predecessor-is-a-receive

**Impact estimate: ~400–700 bus interactions standalone; mostly subsumed by idea 8 but adds
robustness** (chains whose first write genuinely cannot match still drain behind it). **Axis:
bus. Proof difficulty: medium.** No spec change.

`checkCancel` requires S to be the earliest active same-address send in the whole list, so one
uncancellable pair blocks every later identical pair on that address. Safe relaxation: if the
nearest active same-address message *before* S is a **receive** (mult −1), any earlier send is
blocked by that receive, so dropping (S,R) creates no new consecutive send→receive pair and
`admissibleMemoryBus` is preserved. Needs a generalized `admissible_dropPair` hypothesis
(`Implementation/BusFacts.lean` + `MemoryBusDrop.lean` + OpenVM instance — all zero-audit).
Under OpenVM's alternating receive/send discipline this holds at every interior pair.

---

## Housekeeping / standing decisions

### Consider dropping `reencode` in favour of `domainFoldPass` alone (entry-47 option B)

Unchanged from before — left for Georg to decide. Measured trade-off on the apc_005 load/store
class: fold-only reaches **1939** vars (keeping all flags, close to powdr's 1808) vs **1683**
with `reencode`; option B is more principled/powdr-aligned but gives up the ~13% flag
binary-compression that currently makes leanr *beat* powdr there. If taken, the fold pass would
want a `bits ≥ vars` / large-group path to claw some back.

### Batch pair cancellation in one traversal (performance only)

`busPairCancelPass` drops one pair per invocation, drained via `iterateToFixpoint`. On the
largest blocks this is a dominant per-pass cost; a single-traversal multi-drop needs a multi-drop
discipline lemma. Only worth it if it becomes a benchmark bottleneck — and ideas 8/10 make the
per-pair machinery fire far more often, so revisit after landing them.

### Removed ideas

- *Drop never-violating stateless lookups (pc lookups)*: **already achieved** — current outputs
  contain zero bus-2 interactions (domainFold constant-pins the payloads and multiplicities,
  tautoBusDrop removes the constant messages). A generic arity-based drop
  (`BusFacts.neverViolatesArity`, reusing `filterBusStateless_correct`) remains a 30-line
  fallback if some future case keeps a symbolic pc lookup, but it currently buys nothing.
- *Symbolic heap-address chaining*: measured dead end (single-access addresses in both leanr and
  powdr; see idea 8's note).
- *Nonlinear definition inlining* (write-data muxes): killed by the OpenVM degree bound
  (payload degree cap 2; the muxes are degree 3). powdr keeps these vars too.
- *Exact-duplicate interaction dedup as a standalone pass*: zero instances in current outputs;
  it only pays as the harvest step of idea 6.
