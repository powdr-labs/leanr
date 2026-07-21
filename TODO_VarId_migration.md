# TODO — completing the VarId migration

The optimizer is being migrated from its original `Variable`-keyed representation to a dense
`VarId` (registry-indexed) internal representation: the constraint system is encoded once into
dense form, the passes run ID-native with **native** correctness proofs (`DensePassCorrect` over
`VarId → ZMod p` environments, lifted to the audited `Variable`-based spec at the edges via
`OptimizerPasses/Bridge.lean`), and the result is decoded once. This file is the worklist for
finishing that migration, up to and including the deletion of the legacy
`ApcOptimizer/Implementation/OptimizerPasses/OldVariableBased/` tree. Tasks are ordered; each is
independently landable.

## Current state

- **The whole pipeline is dense** (Task 1 complete): `preludePasses`, `cleanupPasses`, and
  `codaPasses` (`Implementation/Optimizer.lean`) are all `DenseVerifiedPassW`-typed schedules —
  42 labels (1 prelude, 29 cleanup, 12 coda), every one a native dense implementation with a
  native `DensePassCorrect` proof (no decode-commutation proofs, no per-pass decode/re-encode
  adapters anywhere). The pipeline encodes ONCE at optimizer entry and decodes ONCE at output
  (`densePipeline` inside `pipeline`); the Bridge lift to the audited `Variable`-based spec sits
  at exactly those edges. The `profile` CLI command steps the same three lists densely, with
  encode and decode timed as their own lines, never charged to a pass.
- `DenseVerifiedPassW.ofSpec` has zero schedule call sites; it remains the documented on-ramp
  for contributing a `Variable`-based pass (Task 4 decides its fate).
- The dense-cleanup milestone was verified byte-identical to the pre-migration optimizer on
  every benchmark corpus (identical per-case circuit sizes, effectiveness delta exactly 0), with
  whole-corpus runtime improvements of 16% (openvm-eth), 30% (wasm-eth), 17% (keccak), 11%
  (sp1-rsp) and 19% (sp1-keccak). The Task 1 commits are each verified byte-identical on the
  local reference cases below; the corpus-wide CI confirmation of the completed Task 1 state is
  pending the next draft-PR run (watch `bytePackLate` — its dense pass drains internally,
  subsuming the old `iterateToFixpoint` wrapper — and `subsumedCheck`, which is a no-op on
  OpenVM, so only the SP1 corpus exercises it).
- Byte-identity reference counts (vars / constraints / bus interactions) for local checks:
  `Benchmarks/OpenVM/openvm-eth/apc_037_pc0x361604` → 689/525/445;
  `…/openvm-eth/apc_001_pc0x4ecc54` → 35/18/24;
  `…/wasm-eth/apc_005_pc0x2E9C48` → 184/94/92;
  `…/keccak/apc_001_pckeccak` → 2021/186/1748;
  `Benchmarks/SP1/keccak/apc_001_pc0x78007bbc` → 2665/313/2067;
  `Benchmarks/SP1/rsp/apc_055_pc0x781ae3f8` → 18/0/16.

## Standing rules (apply to every task below)

- **The schedule is frozen**: pass sequence, labels, and optimization decisions never change.
  Element types and wiring may — that is the migration. Byte-identical output is the expectation
  for every step; it is verified by `cmp` on `opt-export` output locally and by the CI
  effectiveness benchmark corpus-wide, never as a Lean obligation.
- **Audit first, exact shape**: every pass conversion STARTS with a token-parallel audit of the
  dense runtime definitions against the original pass; fix deviations before proof work.
  Output-identical divergence from the reference implementation's micro-shape (data structures,
  hoisted lets, early-outs, fold shapes) is not acceptable debt. This discipline has caught real
  bugs: a missing `@[csimp]` fast-path twin, and a full-system scan recomputed inside a
  per-candidate lambda where the reference hoists it once.
- **Output-divergence policy**: ports are line-parallel transliterations; output may
  legitimately differ only where the representation forces order changes (hash-map iteration
  order, `VarId` sort keys replacing `Variable` name sorts, the value-only enumeration engine).
  Any divergence must be attributed to its cause; effectiveness-count regressions are escalated
  for human review rather than committed.
- **Forbidden**: `sorry`/`admit`/`native_decide` (never write these tokens anywhere, including
  comments — `Scripts/check-proof-integrity.sh` greps sources), new axioms, new `partial`
  definitions, arbitrary fuel. Every commit builds warning-free with all modules reachable.
- **Verification per commit**: `lake build` (no warnings), `bash
  Scripts/check-proof-integrity.sh` (exactly the three standard axioms `propext`,
  `Classical.choice`, `Quot.sound`), run the benchmark cases above and check counts, `cmp` the
  `opt-export` output against a pre-change baseline when behavior should be unchanged. Do not
  run the full corpus locally — open/update a draft PR and let CI run the full effectiveness
  and runtime benchmarks.
- **Audited surface untouchable**: `Spec.lean`, `OpenVmSemantics.lean`, `Sp1Semantics.lean`,
  `MemoryBus.lean`, `ApcOptimizer/Optimizer.lean`, `OptimizerPasses/Basic.lean`.
- **Known trap** (cost hours twice): a definition returning a bare function type is
  eta-expanded to maximum arity by the compiler, so `let`s written before a trailing lambda
  re-run on every call. Never strip a reference implementation's `Subtype` or one-field
  structure return — it is often load-bearing for exactly this reason. When in doubt, compare
  the generated C under `.lake/build/ir/` against the reference's actual shape.
- **Worked examples to imitate** (all in `ApcOptimizer/Implementation/OptimizerPasses/`):
  `GaussProof.lean` (loop-invariant threading through a solver loop), `DigitFoldProof.lean`
  (value-level fact soundness — `denseBuild_sound` — with no registry or decode in the
  statement), `CarryBranchProof.lean` and `RangeBoolProof.lean` (single-shot
  `DenseVerifiedPassW.ofNative`, prime-witness-gated), `DropPassesProof.lean` (drop/filter
  passes via `DensePassCorrect.ofEnvEq` and the entailed-filter helpers), `ReencodeProof.lean`
  with `ofNativeExtending` in `Bridge.lean` (passes that mint fresh variables and extend the
  registry), `BridgeSteps.lean` (drain/foldList combinators for internally-iterating passes).

## Task 1 — Extend the dense region to the pipeline edges — DONE

Landed as twelve commits (`f45736a` … `818ee09`): structural flip first (dense-typed
prelude/coda with every entry `ofSpec`-wrapped, pipeline restructured to edge encode/decode,
`denseCleanupAdapter` deleted, profiler moved to the same edges), then per-label swaps to native
dense passes, each commit verified byte-identical on the local reference cases. Notes for later
tasks:

- The anticipated `busPairCancelLate` mode-extension work was unnecessary: `denseBusPairCancelPass`
  takes `aggressive : Bool` and its bundled proof always covered both modes; the rewire was
  audit-only.
- `bytePackLate` uses `denseByteCheckPackPass`, whose internal drain subsumes the old
  `iterateToFixpoint ByteCheckPack.byteCheckPackPass` wrapper; `seqzCollapse` keeps its
  reference fixpoint as `denseIterateToFixpoint` around the `ofNativeExtending`-built step.
- Pass/VM coverage of the local byte-identity cases: `subsumedCheck` is a no-op on OpenVM
  (`rangeCheckAt` empty there) and `subsumedRange` is a no-op on SP1 (no `varRangeBus`), so the
  corpus-wide CI run is the real check for the respective other side.

## Task 2 — Exact ID-set key in domainBatch (intentional behavior repair)

`varSetKey` (the dedup key for candidate variable sets in domainBatch's finite-domain
enumeration) concatenates variable NAME strings, so two distinct variables with equal names and
different powdr IDs collide, and two different variable sets can be treated as the same
candidate set. Not a soundness issue (every pass carries its correctness proof) — an
optimization-behavior wart on adversarial inputs; real circuits never hit it. The dense side
currently inherits the bug faithfully (`denseVarSetKey` resolves IDs back to `Variable`s and
calls the string key) to preserve byte-identity.

Fix: registry injectivity makes a `VarId` full variable identity, so replace the key with a
sorted, duplicate-free `VarId` sequence (or an order-independent hash followed by exact
comparison of the canonical sequence — hash collisions must never be trusted). This also
removes the resolve + string-building cost from the key path.

Requirements: **separate commit**; a regression test involving equal names with different powdr
IDs; verify normal benchmark outputs are unchanged. This is the ONLY place the migration may
intentionally change optimization behavior, and only on such adversarial inputs.

**Done.** `denseVarSetKey` (`DomainBatch.lean`) now returns the exact set identity of a target as a
sorted, duplicate-free `List VarId` (`xs.dedup.mergeSort` on the underlying index) — no `reg`
lookup, no name string, no reference to the legacy `varSetKey`. `denseDedupTargetsV` /
`denseCollectForcedV` (and the σ/transform above them) dropped their now-unused `reg` params, and
`seen` became `Std.HashSet (List VarId)`. `#guard` regression guards (distinctness of equal-name
singletons, order-independence, duplicate-collapse, and `denseDedupTargetsV` keeping both equal-name
targets) sit next to the definitions. All six benchmark exports stayed byte-identical; behavior
differs only on adversarial equal-name inputs. The proof plumbing was type-only (the entailment
proofs never inspect the key).

## Task 3 — Remove the remaining references into OldVariableBased/

Task 3 proceeds in labelled steps A–F. Steps A–E are done (representation-independent re-homes,
the sparse LinExpr spec core, the two decode transports, and the finite-domain enumeration engine);
Step F is all that remains — native twins / re-homes for the residual `Variable`-typed memory-bus
theorems, plus the two Step-B residual legacy couplings.

**Step A — re-home representation-independent legacy content — DONE.** Content that quantifies over
`Nat`/`ZMod`/`List`/bus-spec values only, previously owned by `OldVariableBased/` files that the
dense tree consumed, moved to neutral non-legacy homes (fully-qualified names preserved; each legacy
file imports its home back):
- list machinery `argmin_map_key` / `map_filterMap` and the linear-time `dedupHash` →
  `OptimizerPasses/ListSplit.lean`;
- the search / enumeration budget constants `maxDeepPoints` / `maxDeepDomain` / `maxDeepConstraints`
  / `maxDeepVars` / `basisFuel` / `maxEnumWork` / `domainFoldIndexThreshold` →
  `OptimizerPasses/SearchBudgets.lean` (new neutral file, `Nat`-only);
- the `seqzCollapse` gadget's `ZMod p`-value-level lemmas and range-check bus facts (`seqz_forward`,
  `seqz_reconstruct`, `zbool`, `bus_accepts_byte_zero`, `bus_byte_of_accepts`, and the support
  closure `neg_byte_val_big` / `small_natCast_ne_zero` / `val_one_eq` / `val_add_one` /
  `byte_sub_one_val` / `byte_sub_two_val` / `oneHot`; `sum_zero_all_zero` was already in
  `HintCollapse.lean`) → `OptimizerPasses/SeqzCollapseCore.lean` (new neutral file, kept under the
  `SeqzCollapse` namespace);
- `ComputationMethod.eval_congr` (`ComputationMethod` is the audited spec type) →
  `OptimizerPasses/DomainProp.lean`, next to its `Expression.eval_congr` / `BusInteraction.eval_congr`
  companions; consumed by the master-theorem completeness proof (`Implementation/Optimizer.lean`).

**Step B — sparse LinExpr spec core re-home — DONE.** The representation-independent
(`Variable`-keyed) sparse linear-expression spec core moved to the new neutral
`OptimizerPasses/LinExprCore.lean` (imports `Spec` only, nothing legacy; each reference file imports
it back; fully-qualified names preserved). Re-homed:
- the sparse `LinExpr` with its algebra `eval` / `add` / `scale` / `coeff` / `others` / `eval_split`
  / `toExpr` (and `add_eval` / `scale_eval` / `toExpr_eval`), plus `linearize` / `linearize_eval`
  (from `OldVariableBased/Affine.lean`);
- the normalization chain `addCoeff` / `mergeTerms` (with `addCoeff_eval` / `foldl_addCoeff_eval` /
  `mergeTerms_eval` / `dropZero_eval`) and `LinExpr.norm` / `LinExpr.norm_eval` (from
  `OldVariableBased/Normalize.lean`; the fast `@[csimp] mergeTerms_eq_fast` and the variable-bound
  lemmas stay in the reference file, still targeting the moved `addCoeff`/`mergeTerms`);
- `Expression.constValue?` / `constValue?_sound`, and — as their dependency closure — the
  constant-fold *value* core `Expression.foldAdd` / `foldMul` / `fold` with their eval lemmas (from
  `OldVariableBased/TautoBus.lean` and `OldVariableBased/ConstantFold.lean`; the variable-bound
  lemmas and the folding pass stay in the reference file);
- the syntactic `Expression` helpers `Expression.mentions` / `Expression.varCount` /
  `Expression.isVar` (from `OldVariableBased/Gauss.lean`; `mentions` is consumed by `DomainProp.lean`,
  `isVar`/`varCount` by the dense `Gauss.lean` — the Step-A scan finding, handled here).

This frees `OldVariableBased/Affine.lean` / `Normalize.lean` / `Gauss.lean` / `ConstantFold.lean` /
`TautoBus.lean` of being consumed for the spec core, and kills `DomainProp.lean`'s and
`MemoryUnify.lean`'s legacy couplings *for this content* (they now reach it via `LinExprCore.lean`).
Two independent legacy couplings remain, out of Step B's scope: `DomainProp.lean` still uses
`ConstraintSystem.subst` / `subst_correct` from `OldVariableBased/Subst.lean` (substitution
machinery, not the LinExpr core), and `MemoryUnify.lean` still imports `TrivialConstraint.lean`
(→ `OldVariableBased/TrivialConstraint.lean`).

**Step C — nativize `RootPairUnifyProof` — DONE.** The decode transport is gone: `RootPairUnifyProof.lean`
no longer imports `OldVariableBased/RootPairUnify.lean` and references no `decodeLin`/`decodeExpr`
evaluation bridge, `eval_decode*`, or `denseTwoRootOf?_decode`/`_A_valid`. The three legacy lemma uses
were dispatched as follows:
- **Keystone (nativized):** the value-level two-root soundness `ApcOptimizer.Dense.denseTwoRootOf?_sound`
  (`Dense/AddrDiseqProof.lean`, in the section "Two-root decomposition soundness (native, value-level)")
  is proved directly over `DenseExpr`/`DenseLinExpr` evaluation via the field core `twoRoot_mem` — no
  registry, no decode in statement or proof. **Step D reuses this lemma directly** (it lives in
  `AddrDiseqProof.lean`, which `RootPairUnifyProof.lean` already imports); the helper
  `DenseLinExpr.eval_of_terms_eq` moved there alongside it. Because the native soundness needs no
  coverage/validity, the `reg`/`hcov`/`CoveredBy`/`Valid` hypotheses dropped out of the whole
  `denseRpCheckPair_sound` → `denseRpLoop_sound` → `denseRootPairUnify_loop_invariant` chain.
- **Re-homed (representation-independent):** the field lemmas `twoRoot_mem` and `rootPair_eq` →
  new neutral file `OptimizerPasses/RootPairCore.lean` (`ZMod p`-value only); the `Nat`/`List` lemmas
  `init_le_foldl_max`/`le_foldl_max` → `OptimizerPasses/ListSplit.lean`. The legacy
  `OldVariableBased/RootPairUnify.lean` imports both back (still consumed by its own
  `twoRootOf?_sound` and by `OldVariableBased/AddrDiseq.lean`), and stays reachable via
  `Implementation/Optimizer.lean`'s legacy import block. The still-live decode transport is now only in
  `AddrDiseqProof.lean` (`denseTwoRootOf?_decode`/`_A_valid` and the certificate stack) — Step D's target.

**Step D — nativize `AddrDiseqProof`'s certificate stack — DONE.** Every decode transport is gone from
`AddrDiseqProof.lean`: it no longer imports `OldVariableBased/AddrDiseq.lean` and references no
`decodeLin`/`decodeExpr`/`decodeBI` bridge, `eval_decode*`, or `denseTwoRootOf?_decode`/`_A_valid`.
Each certificate is now proved sound **natively at the value level** over `VarId → ZMod p`, mirroring
the reference `Variable`-level argument with the dense eval algebra (`DenseLinExpr.norm_eval`/
`add_eval`/`scale_eval`/`eval_split`, `denseLinearize_eval`) and the representation-independent field
core (`twoRoot_mem`):
- `denseConstDiffNZ_sound`, `denseIsZeroLin_sound`, `denseDiffSumOver_eval_zero`,
  `densePtrBranchesOf_eval`, `denseReciprocalWitsProd_sound`/`denseReciprocalWits?_sound`,
  `denseAddr_slot_neq`/`denseAddr_eq_slot`, `densePtrReductions_sound`, `denseExprTwoRootNeq_sound`
  — new/rewritten native lemmas in `AddrDiseqProof.lean`;
- the public certificate soundness lemmas `denseAddrAffineNeq_sound`, `denseAddrTwoRootNeq_sound`,
  `denseAddrNonzeroNeq_sound` keep their signatures (so `BusUnifyProof`/`BusPairCancelCheckProof`
  callers are untouched) but their proofs are now native; the residual `reg`/`CoveredBy`/`denseBICovered`
  hypotheses are unused by the native proofs (underscored);
- the `DenseTwoRootMap.Sound` invariant and `denseTwoRootOf?_sound` were already native (Step C).

The orphaned decode skeleton was deleted in the same commit (grep-verified consumer-less): the
`decodeLin` family + `denseLinearize_decode`/`map_resolve_filter_eq`/`map_resolve_filter_ne` +
`flatMap_congr_mem`/`denseLinearize_covered_terms` in `Affine.lean`, and the `decodeLin_norm` chain
(`map_resolve_filter`/`denseAddCoeff_map`/`denseFoldAddCoeff_map`/`denseMergeTerms_map`) in
`Normalize.lean`. `OldVariableBased/AddrDiseq.lean` stays reachable via
`OldVariableBased/BusUnify.lean` in `Implementation/Optimizer.lean`'s legacy block.

**The "Decode transports" group of Task 3 is now dead** — both transports (`RootPairUnifyProof`,
Step C; `AddrDiseqProof`, Step D) are nativized and their bridging machinery deleted. What remains of
Task 3 is Step F (native twins / re-homes for the residual `Variable`-typed memory-bus theorems, plus
the two Step-B residual couplings).

**Step E — re-home the enumeration engine — DONE.** The value-only, `Variable`- and `VarId`-free core
of the finite-domain enumeration moved to two neutral non-legacy homes (fully-qualified names
preserved; each legacy file imports its home back):
- the generic early-exit list fold `foldlStop` with its family (`foldlStop_stopped` / `_append` /
  `_map` / `_flatMap` / `_congr` / `_all`), and the generic list lemmas `zipIdx_map_sparse` (from
  `OldVariableBased/DomainFold.lean`) and `zip_map_self_mem` (from `OldVariableBased/Reencode.lean`) →
  `OptimizerPasses/ListSplit.lean`;
- the symbolic `FiniteDomain` (`explicit`/`range`) with `toList` / `size` / `size_eq` and its
  `Nat`-loop element fold `rangeFoldFrom` (+`rangeFoldFrom_eq`) / `FiniteDomain.foldElts`
  (+`foldElts_eq`), and the interned, index-compiled item types `IExpr` / `CBi` (from
  `OldVariableBased/DomainBatch.lean`) → new `OptimizerPasses/EnumEngine.lean` (imports only
  `ListSplit.lean`; mentions no `Variable`, no `VarId`, no reference pass, so it survives the legacy
  deletion).

The dense `DomainBatch.lean` / `Reencode.lean` / `DomainFold.lean` **dropped** their
`OldVariableBased.*` imports (they consumed the engine only for these value-only items; `DomainBatch`
now imports `EnumEngine` plus the `CoveredIndex` / `HashedDedup` / `SearchBudgets` its downstream
`Runtime`/`Proof` used to reach transitively through the legacy import). The reference
`OldVariableBased/DomainBatch.lean` / `DomainFold.lean` / `Reencode.lean` stay reachable via
`Implementation/Optimizer.lean`'s legacy import block (`DomainBatch` and `DomainFold` directly;
`Reencode` via the legacy `DomainFold`).

What stayed in the reference tree (not consumed by any dense code — the dense side has native
`dense…` twins, so these appear only in "mirrors X" docstrings and die with the folder in Task 4):
the compiled evaluators/compilers and the eager box engine `IExpr.eval` / `evalWith` / `CBi.eval` /
`evalWith` / `lookupIx` / `varIx(_lookup)` / `compileE(s)(_eval/_all/_map)` / `compileBi(s)` /
`boxFold(_eq)` / `allBox(_eq)` / `survivesAll*` / `compiledSurv` / `envOfFast`, and the spec
`DomainTable` (with `doms` / `doms_fst` / `doms_sound` / `matList`+lemmas). The Step-inventory's
`doms_fst:542` flag was `Dense/DomainBatch.lean`'s own `DenseDomainTable.doms_fst` definition (whose
docstring names the spec lemma), not a use of the spec `DomainTable.doms_fst`.

**Step F — native twins or re-homes for the residual memory-bus theorems.** The `Variable`-typed
facts the dense `BusPairCancel` cluster still consumes through `OldVariableBased/BusPairCancel.lean`
(and its neighbours): `multiplicitySum_append`, `mem_core_of_ne`, `MemoryBusShape.setNewMult_ne_zero`,
plus the extra legacy pulls surfaced by the Step-A scan — `IntervalForce.srep` and `MemoryBusDrop`.
Also fold in the two Step-B residual couplings: `DomainProp.lean` still uses
`ConstraintSystem.subst` / `subst_correct` from `OldVariableBased/Subst.lean`, and `MemoryUnify.lean`
still imports `OldVariableBased/TrivialConstraint.lean`.

**Scan findings (current):** `DomainFold.lean` is already keeper-only (no non-legacy consumer);
dense `Gauss.lean`'s consumption of spec `Expression.isVar` / `varCount` is resolved by Step B (moved
to `LinExprCore.lean`); `MemoryUnify.lean` was a newly-identified `LinExpr` consumer (handled by
Step B); the `BusPairCancel` cluster's extra legacy pulls (`IntervalForce.srep`, `MemoryBusDrop`)
join Step F's scope; `Implementation/Optimizer.lean`'s `ComputationMethod.eval_congr` use is handled
by Step A.

**Dies with the folder (Task 4) — reachability keepers:** after Task 1, no schedule or pipeline
code references a legacy pass; what remains are imports kept only so the legacy modules stay in
the build graph until deletion (several — `Identity`, `ZeroRegister`, `CarryBranch`,
`BoxRewrite`, `OneHotAnnihilate`, `DigitFold` — are reachable ONLY this way):
- `Implementation/Optimizer.lean`'s `OldVariableBased.*` import block;
- the `import …OldVariableBased.X` line inside each of the eight Task 1 port files
  (`SubsumedCheck`, `SubsumedRange`, `MonicScale`, `SplitBytePair`, `RedundantByteDrop`,
  `IdentitySubst`, `TupleRange`, `SeqzCollapse` — these files now host the dense
  implementations, so only the import line dies, not the file);
- the four import-only keeper files `ConstantFold.lean`, `TautoBus.lean`,
  `TrivialConstraint.lean`, `ZeroMultBus.lean` (their dense twins live in `ExprOps.lean` /
  `DropPassesProof.lean`);
- the four content-vestigial keepers `ByteCheckPack.lean`, `DisconnectedComponent.lean`,
  `RangeBool.lean`, `RangeForceZero.lean`.

## Task 4 — Delete the legacy tree

When Tasks 1–3 are done: delete `OldVariableBased/` (42 files) and every reachability keeper
listed at the end of Task 3 (the four import-only keeper files, the four content-vestigial
keepers, the legacy import lines inside the eight Task 1 port files, and
`Implementation/Optimizer.lean`'s legacy import block); re-attempt the
two deferred lemma moves (the Gauss `argmin_map_key`/`map_filterMap` pair and the
`BusPairCancelJustify` constants — their blockers are gone by now); decide the fate of
`DenseVerifiedPassW.ofSpec` (currently zero call sites; it is the documented on-ramp in
"Adding an optimization" for spec-side passes — either keep it for contributor ergonomics or
delete it and make new passes native-only; `AGENTS.md` must match the decision).

Permanent, by design — do NOT delete: `Encoding.lean`'s encode/decode round-trip,
`Bridge.lean`/`Measure.lean` (the lift to the audited `Variable`-based spec at the pipeline
edges), `Registry.lean`, and the dense pass tree. The audited specification remains
`Variable`-based; encode-at-entry/decode-at-output are the permanent boundary.

## Task 5 — Comment and terminology hygiene

Guiding principle: a comment or docstring must describe the code **as it stands**. Anything
that narrates the migration process, contrasts with a discarded strategy, or only makes sense
relative to the temporary in-migration state gets deleted or recast as a statement about the
current code. Sweep the whole non-legacy tree; the categories below are known instances, NOT an
exhaustive list — apply the principle, not just the list.

- Migration-project jargon: "Task 3", work-package codenames ("WP-A" … "WP-H"), and
  chunk/dispatch labels ("chunk C0"–"C7", "D1"–"D4", "F1/F2", "BP-I1/BP-P1", batch numbers).
- Strategy-relative terminology: "native proof", "proved natively", "`VarId`-native" — the
  contrast was with a decode-commutation proof strategy that no longer exists; it is just a
  proof. Same for "commutation-era", "landing tactic", "decode-commutation" and similar
  references, except where a comment genuinely documents the still-existing spec-lemma decode
  transports (Task 3's first group) — those describe current code and stay until the transports
  die.
- Provenance/review-talk: comments that justify a change against a previous implementation
  state ("byte-identical to …", "matches the spec shape", "the shape audit found …") rather
  than stating what the code does.
- Stale references to deleted machinery: six files still mention the removed label-dispatch
  selector (`denseImpl`): `IntervalForce.lean`, `RangeForceZero.lean`, `RangeBool.lean`,
  `XorEqExtract.lean`, `ByteCheckPack.lean`, `FlagFold.lean`.
- Citations of untracked design notes (`VarId.md`/`VarIdAddendum.md`) in five files:
  `DomainBatchRuntime.lean:43`, `BoxRewrite.lean:66`, `Reencode.lean:84`,
  `DomainFoldRuntime.lean:38`, `Bridge.lean:7`. Replace each with a self-contained statement of
  the relevant policy (all policies are in this file's Standing rules).
- Identifier names are OUT of scope for the sweep (no API churn), with one noted exception to
  decide at Task 4: `DenseVerifiedPassW.ofNative` keeps its meaning only as the counterpart of
  `ofSpec` — revisit the name when `ofSpec`'s fate is decided.
