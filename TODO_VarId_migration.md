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
- The pass-entry API is native-only: `DenseVerifiedPassW.of` (registry unchanged) and
  `DenseVerifiedPassW.ofExtending` (fresh-variable passes) are the two builders. The old
  `ofSpec` decode → run → re-encode on-ramp for a `Variable`-based pass was deleted in Task 4.
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
  `DenseVerifiedPassW.of`, prime-witness-gated), `DropPassesProof.lean` (drop/filter
  passes via `DensePassCorrect.ofEnvEq` and the entailed-filter helpers), `ReencodeProof.lean`
  with `ofExtending` in `Bridge.lean` (passes that mint fresh variables and extend the
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
  reference fixpoint as `denseIterateToFixpoint` around the `ofExtending`-built step.
- Pass/VM coverage of the local byte-identity cases: `subsumedCheck` is a no-op on OpenVM
  (`rangeCheckAt` empty there) and `subsumedRange` is a no-op on SP1 (no `varRangeBus`), so the
  corpus-wide CI run is the real check for the respective other side.

## Task 2 — Exact ID-set key in domainBatch (intentional behavior repair) — DONE

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

## Task 3 — Remove the remaining references into OldVariableBased/ — DONE

Task 3 proceeded in labelled steps A–F, all now done (representation-independent re-homes, the
sparse LinExpr spec core, the two decode transports, the finite-domain enumeration engine, and the
residual memory-bus / substitution couplings). An identifier-level sweep of the whole non-legacy
tree (comments excluded) shows **zero** non-legacy code consuming any `OldVariableBased/`
definition. The only arrows that remain into the legacy tree are the documented reachability-keeper
imports (see "Dies with the folder" below): `Implementation/Optimizer.lean`'s legacy import block,
the keeper `import` line inside each of the eight Task 1 port files, the four import-only keeper
wrappers, and the four content-vestigial keepers — sixteen files in all, each verified to reference
no legacy identifier in code. Task 4 deletes them.

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

**Step F — re-home the residual memory-bus / substitution couplings — DONE.** The last genuine
arrows from non-legacy code into `OldVariableBased/` are gone:

- **busPairCancel cluster.** The two representation-independent facts the dense cluster consumed
  through `BusPairCancelJustify.lean`'s import of `OldVariableBased/BusPairCancel.lean` were
  re-homed to the neutral `OptimizerPasses/ListSplit.lean` (fully-qualified names preserved; legacy
  `BusPairCancel.lean` already imports `ListSplit`, so it picks them up back): the generic list
  lemma `mem_core_of_ne` (a two-point-split lemma — ListSplit's own topic) and the spec-side
  net-multiplicity additivity `multiplicitySum_append` (over `Spec`'s `BusState p`). The two facts
  the TODO also flagged were already non-legacy and needed no work: `IntervalForce.srep` lives in
  the neutral `OptimizerPasses/IntervalForce.lean` (Step A) and `MemoryBusShape.setNewMult_ne_zero`
  / `filter_split` live in `ApcOptimizer/Implementation/MemoryBusDrop.lean`; `MemoryBusDrop` is a
  module name, not a legacy pull. `BusPairCancelJustify.lean` dropped its
  `OldVariableBased.BusPairCancel` import and now imports the neutral homes it actually uses
  (`IntervalForce`, `ListSplit`, `SearchBudgets`); `BusPairCancelCore.lean` imports
  `MemoryBusDrop` directly for `filter_split` / `setNewMult_ne_zero`.
- **`Subst` re-home.** The substitution equivalence machinery (`Expression.subst` /
  `BusInteraction.subst` / `ConstraintSystem.subst` with the `eval`/`satisfies`/`sideEffects`/
  `admissible`/`vars` transfer lemmas and the payoff `ConstraintSystem.subst_correct`) moved to the
  new neutral `OptimizerPasses/SubstCore.lean` (imports `Basic` only; fully-qualified names
  preserved). `DomainProp.lean` (permanent `Variable`-side shared-facts file) imports `SubstCore`
  directly; legacy `OldVariableBased/Subst.lean` imports it back and keeps only the
  `substFromConstraint` pass builder on top of it.
- **`MemoryUnify` → `TrivialConstraint`.** Vestigial for `MemoryUnify` itself (it references
  nothing from `TrivialConstraint`), so the import was dropped. It had been an accidental conduit
  by which legacy `OldVariableBased/BusUnify.lean` reached legacy `Expression.isConstZero`; that
  legacy consumer now imports `OldVariableBased/TrivialConstraint.lean` directly (legacy→legacy).
- **dense `Affine` / `Normalize` / `Gauss` vestigial imports.** These three dense files still
  imported their legacy namesakes, consuming no legacy definition — only using them as a transitive
  conduit for the `ring` tactic and for the Step-A/Step-B re-homes (`argmin_map_key` /
  `map_filterMap`, now in `ListSplit.lean`). The legacy imports were dropped: `Affine.lean` imports
  `Mathlib.Tactic.Ring` directly (inherited by `Normalize`/`Gauss`), and `Gauss.lean` imports
  `ListSplit` directly.

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

## Task 4 — Delete the legacy tree — DONE

The `OldVariableBased/` tree (42 files) and every reachability keeper are gone: the four
import-only wrapper files (`ConstantFold`/`TautoBus`/`TrivialConstraint`/`ZeroMultBus`),
`Implementation/Optimizer.lean`'s legacy import block, and the keeper `import` line inside each of
the twelve files that host dense content (they stay — only the import line died). Every textual
reference to the legacy tree is gone from the non-legacy code, comments, and docs. The two lemma
moves an earlier plan deferred (`argmin_map_key`/`map_filterMap`, the `BusPairCancelJustify`
constants) had already been completed in Task 3 (Steps A/F, into `ListSplit.lean`), so nothing
remained to re-attempt.

Two design decisions (made by the repo owner) were carried out:
- **Native-only pass API.** `DenseVerifiedPassW.ofSpec` (the decode → run → re-encode on-ramp for a
  `Variable`-based pass, zero call sites) was deleted, together with the derivation-encoding chain
  (`encodeCM`/`encodeDerivs` and their extension/coverage/round-trip lemmas, plus `encodeCS_extends`)
  that only it consumed. `Adapter.lean` keeps only the still-consumed coverage lemmas
  (`DenseConstraintSystem.CoveredBy.mono`, `encodeCS_covered` and their dependencies).
- **Rename.** `DenseVerifiedPassW.ofNative` → `DenseVerifiedPassW.of` and `ofNativeExtending` →
  `ofExtending`; these two builders are now the whole pass-entry API. `AGENTS.md`, the
  `Implementation/Optimizer.lean` docstrings, `Bridge.lean`, and `docs/design/architecture.md` match.

Permanent, by design — do NOT delete: `Encoding.lean`'s encode/decode round-trip,
`Bridge.lean`/`Measure.lean` (the lift to the audited `Variable`-based spec at the pipeline
edges), `Registry.lean`, and the dense pass tree. The audited specification remains
`Variable`-based; encode-at-entry/decode-at-output are the permanent boundary. `Adapter.lean` is no
longer an adapter (its `ofSpec` is gone); it now hosts the constraint-system coverage lemmas.

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
- Identifier names are OUT of scope for the sweep (no API churn). The one exception flagged for
  Task 4 is resolved: `ofSpec` is deleted and `ofNative`/`ofNativeExtending` are renamed to
  `DenseVerifiedPassW.of`/`ofExtending`.

Ordering note: run Task 6 (below) first — its deletions remove whole files of stale comments,
shrinking this sweep.

## Task 6 — Delete the orphaned Variable-side layer (unused-declaration sweep findings)

Found by an untracked local reachability script (`Scripts/FindUnusedDecls.lean`, not committed;
recreate as: a `lake env lean`-run meta-script computing environment reachability from `main`,
every constant of the audited modules, and the `CheckAxioms` theorems, closed over each
constant's type/value references — including `._unsafe_rec` bodies, without which every
`partial def`'s dependencies vanish from the closure — with auto-generated names filtered). At HEAD `52ec606`: 7,467 project constants, 4,429
reachable, 279 reported, triaged to **219 genuine orphan candidates**. Roughly 180 of them are
one event: Task 4's native-only decision (legacy tree + `ofSpec` deleted) orphaned the whole
`Variable`-side spec-support layer — including two files Task 3's own re-homes had just
created (`SubstCore.lean`, `LinExprCore.lean`), whose only would-be consumers died with it.

**Keep-lists established by the triage (do NOT delete; the sweep tool over-reports these by
design):**
- the `@[csimp]` fast-merge cluster in `Normalize.lean` (14 decls around
  `denseMergeTermsFast`/`denseMergeTerms_eq_fast`) — compiler-consumed;
- the `@[export]` FFI cluster (6 decls: `apcOptimizerOptimizeJson` in `Ffi.lean`, `KnownVm` +
  helpers, `Serialize.serializeResult`) — rooted by the C shim, not `main`;
- the 6 `#guard`-anchored DSL decls in `Utils/Dsl.lean`;
- 32 deliberate-API decls (Bridge/BridgeSteps builder lemmas and the `DenseNativeStep`
  toolkit, `Measure`/`Registry`/`Encoding` helpers, `denseIterateToFixpoint_monotone`,
  `Utils/Size.lean`'s documented effectiveness metrics, `matchesSnapshot`).
- Borderline, decide at execution: `instDecidableEqKnownVm`/`instReprKnownVm` (deriving
  artifacts unused even by the FFI path).

**Deletion worklist (verify each against the build — reachability is the tool's judgment, the
compiler's is final; re-point or drop imports as files empty out):**
1. Whole files dead: `SubstCore.lean` (12 decls), `LinExprCore.lean` (37), `BytePack.lean`
   (16 — dense twins live in `BusPairCancelCheck.lean`), `MemoryUnify.lean` (27).
2. Nearly whole files: `CoveredIndex.lean` (28 of 31 — re-home the 3 surviving generic list
   lemmas `filterMap_congr'`/`filterMap_if_some`/`mem_foldl_insert` first);
   `DomainProp.lean` (56 of 65 — the complete `Variable`-based `domainPropPass` and its
   soundness chain; keep/re-home the 9 shared survivors: the `eval_congr` family, `capBound`,
   `maxDomainBound`, `maxEnumSize`, `probeMax`); `FactPass.lean` (17 of 21 — the spec-side
   pass driver `iterateToFixpoint`/`andThen`/`guardDegree`/`withFacts`/`sizeKey` family and
   two `DecidableEq` instances, orphaned with `ofSpec`; the `VerifiedPassW` type itself stays).
3. Clusters: the 13 dense↔spec decode-correspondence lemmas in `DomainBatch.lean`
   (`denseCovBuild_corr` etc. — the last decode transports, and `CoveredIndex`'s only
   would-be consumer); `ListSplit.lean`'s 4 split-equation lemmas (`list_split_two*`,
   `split_of_extracts`, `foldlStop_all`); the superseded bytePack prototype in
   `ByteCheckPack.lean` (`denseDrainBytePacks`, `denseByteCheckPackF` — the shipped pass is
   `denseByteCheckPackPass` in `ByteCheckPackProof.lean`).
4. Singletons (medium confidence): `denseInteractionBoundPat_eq` (`BusPairCancelWits.lean`),
   `get_spawn` (`DomainBatchProof.lean`), `denseCoveredIdx_eq_filter` (`DomainFold.lean`),
   `denseFoldOutInPlaceV_covered` (`DomainFoldProof.lean`), `FiniteDomain.size_eq`
   (`EnumEngine.lean`), `VarRegistry.decodeExpr_isVar` (`Gauss.lean`),
   `denseTwoRootVarsOk` (`RootPairUnify.lean`).
5. Unused imports (corroborated by `lake exe shake`; apply only the clearly-dead ones, NOT
   wholesale `--fix`, and never touch the audited `Basic.lean`): `Implementation/Optimizer.lean`
   → `BytePack`, `CoveredIndex.lean` → `DomainProp`, `Encoding.lean` → `Utils.Size`,
   `OpenVmFacts.lean`/`Sp1Facts.lean` → `MemoryBusDrop`, `LinExprCore` → `Mathlib.Tactic.Ring`
   (moot if the file dies), `Utils/Size.lean` → `Mathlib.Data.Rat.Defs`.
6. Stale-doc repairs surfaced by the sweep: `LinExprCore.lean`/`DomainProp.lean` headers call
   themselves permanently-consumed `Variable`-side files (false since Task 4 — moot where the
   file dies); Task 4's note above that `Adapter.lean`'s `CoveredBy.mono` is still consumed
   (re-verify — `Bridge.lean:878` carries its own private copy); `Main.lean:90` duplicates
   `Utils/Size.lean`'s metric computation (`distinctVarCount`) instead of consuming it —
   unify or note deliberately.

Verification per commit: the standard gates (build warning-free, proof integrity, six-case
`cmp` byte-identity — everything here is never-executed code, so byte-identity is expected
throughout), then re-run `Scripts/FindUnusedDecls.lean` and confirm only the keep-lists
remain, and let the draft-PR CI confirm corpus-wide.
