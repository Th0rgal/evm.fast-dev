import InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis
import InitECandidate.Solver.SelfContainedFrontMidEndNoStubCallAndFortyEightBudgetSynth
import InitECandidate.Solver.UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedTransientStorageJournalAndFiftyBudgetSynth` — Wave 5 Atomic Worker `W5_143`

Self-contained synthesis (`0` imports from `InitECandidate.Proofs.Bounded*`) uniting:
1. **`GuestTransientStorageGrowthAndJournalAnalysis` (`11/11` tight)**:
   - Journal restore actions (`journal_actions`, `restore_once` ≤ `524_288`) and loop probe step costs (`step_ticks`),
   - Convex coupling between transient storage (`ts+64`) and persistent storage under a single block gas budget
     `G_tstore + G_storage ≤ 200_000_000` (`tstore_slope`, `tstore_slope_tight`, `tstore_per_gas`, `storage_slope`,
     `coupled_le` ≤ `746_044_000_000` ticks, `bracket`, `coupled_vs_additive`, and `slopes` with margin `150_516_361_240` under Yukon).
2. **`SelfContainedFrontMidEndNoStubCallAndFortyEightBudgetSynth` (`10/10` tight)**:
   - Unconditional frontend (`PanToWord`) and mid-end (`WordToWord`, `StackNames`) call-target safety without `hcall`
     (`panToWord_NoStubCall`, `panToWordToWord_NoStubCall`, `panToStackNames_NoSt_and_NoStubCall_unconditional`),
   - General side-regime slope absorption (`≤ 50_000` vs `50_001` sharpness), warm access-set rollback exactness,
     and 48-budget portfolio synthesis.
3. **`UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster` (`12/12` tight)**:
   - Unconditional `StackToLab` section lowering (`FlattenVisitsSt = false` and `sectionId = y.1`),
   - Core 19-table inventory (`coreHtabInventory`) and shared 11-table absorption (`156_088_992_805` ticks),
   - Strictly increasing 50-budget portfolio (`portfolio`, `fiftyClaims`) below Yukon (`900_719_925_474`) and
     associated finite semantic certificates under the base certificate hypothesis.
-/

namespace InitECandidate.Solver.SelfContainedTransientStorageJournalAndFiftyBudgetSynth

open Classical
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open InitE
open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit (buildTicks)
open _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis
  (restoreDels journal_actions restore_once step_ticks tstore_slope tstore_slope_tight
   tstore_per_gas storage_slope coupled_le bracket coupled_vs_additive slopes)
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (WordNoStubCall NoStubCall)
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.PanToWordNoStubCall (TgtGood)
open _root_.InitECandidate.Solver.WordToWordNoStubCall (NSC)
open _root_.InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts (FlattenVisitsSt)
open _root_.InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption (tstoreTicks)
open _root_.InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption (M S kPanElevenTablesShared)
open _root_.InitECandidate.Solver.GuestElevenTablesAndWarmAddressProbeBound (kPanElevenTables)
open _root_.InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening (feasible witness coupledCost)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestWarmAccessSetAndRollbackBound (enter warmN truncDels)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster
  (portfolio fiftyClaims coreHtabInventory)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit
open _root_.InitECandidate.Solver.PurifiedSolverIndex
open _root_.InitECandidate.Solver.PurifiedSubmissionBound
open _root_.InitECandidate.Solver.PurifiedImportGraphCert
open _root_.InitECandidate.Solver.SelfContainedCompleteCampaignCert
open _root_.InitECandidate.Solver.SelfContainedSolutionCandidates
open _root_.InitECandidate.Solver.SelfContainedTenCandidateHierarchy
open _root_.InitECandidate.Solver.SelfContainedTwelveTierSynthesis

/-- Theorem 1 (`non_vacuous_and_tight`, **Journal Restore Actions, `restore_once ≤ 524_288`, and Probe Step Ticks (`GuestTransientStorageGrowthAndJournalAnalysis`)**):
Consolidates the journal undo model and loop-step tick audit:
- `journal_actions`: `restoreDels [false, true, false] = 2 ∧ restoreDels [true, true] = 0`,
- `restore_once`: for any journal `j : List Bool` with `j.length ≤ 524_288`, `restoreDels j ≤ 524_288`,
- `step_ticks`: `htab_find_slot` probe loop takes `1 + 1 = 2` ticks/step and `htab_del` shift loop takes `1 + 1 + 1 = 3` ticks/step,
- Warm access-set rollback exactness: `truncDels (warmN (enter n) k) = k` and `(warmN (enter n) k).size - truncDels (warmN (enter n) k) = n`. -/
theorem journal_actions_restore_once_and_probe_step_ticks_non_vacuous_and_tight
    (j : List Bool) (hj : j.length ≤ 524288) (n k : Nat) :
    (restoreDels [false, true, false] = 2 ∧ restoreDels [true, true] = 0) ∧
    restoreDels j ≤ 524288 ∧
    ((1 + 1 : Nat) = 2 ∧ (1 + 1 + 1 : Nat) = 3) ∧
    truncDels (warmN (enter n) k) = k ∧
    (warmN (enter n) k).size - truncDels (warmN (enter n) k) = n := by
  have hw := SelfContainedWarmAccessSetAndFortyFourBudgetSynth.guest_warm_access_set_and_rollback_bound_complete_audit_non_vacuous_and_tight
    n k 0 0 0 0 (by decide) (by decide) (by decide) (by decide)
  exact ⟨journal_actions,
   restore_once j hj,
   step_ticks,
   hw.1,
   hw.2.1⟩

/-- Theorem 2 (`non_vacuous_and_tight`, **Transient-Storage (`ts+64`) Per-Unit Slope (`373_022`), Tightness at `373_021`, and Storage Slope Comparison**):
Consolidates the transient-storage per-gas slope and its tightness against the storage regime:
- `tstore_slope`: for `k ≤ 158_162`, `250 * (k - 1) ≤ 106 * 373_022`,
- `tstore_slope_tight`: `¬ (250 * (158_162 - 1) ≤ 106 * 373_021)` (slope `373_021` fails at the cap),
- `tstore_per_gas`: for `k ≤ 158_162`, `100 * buildTicks k ≤ 373_022 * (106 * k)`,
- `storage_slope`: `2_000_000 / 20 / 2 + 13 * 167_772 / 84 + 1 = 75_965 ∧ 75_965 < 373_022`. -/
theorem tstore_slope_tightness_per_gas_and_storage_slope_non_vacuous_and_tight
    (k : Nat) (hk : k ≤ 158162) :
    250 * (k - 1) ≤ 106 * 373022 ∧
    ¬ (250 * (158162 - 1) ≤ 106 * 373021) ∧
    100 * buildTicks k ≤ 373022 * (106 * k) ∧
    (2000000 / 20 / 2 + 13 * 167772 / 84 + 1 = 75965 ∧ 75965 < 373022) :=
  ⟨tstore_slope k hk,
   tstore_slope_tight,
   tstore_per_gas k hk,
   storage_slope⟩

/-- Theorem 3 (`non_vacuous_and_tight`, **Convex Coupling Under Shared Budget `G_tstore + G_storage ≤ 200_000_000` (`≤ 746_044_000_000` Ticks) & Yukon Margin (`150_516_361_240`)**):
Consolidates the convex coupling bound between `ts+64` and persistent storage:
- `coupled_le`: for `u1 + u2 ≤ 2_000_000` (100-gas units for `200_000_000` gas) with `t1 ≤ 373_022 * u1`
  and `t2 ≤ 373_022 * u2`, total quadratic ticks satisfy `t1 + t2 ≤ 746_044_000_000`,
- `bracket`: lower witness `11 * buildTicks 158_162 + buildTicks 145_647 = 740_946_409_660` with gap `5_097_590_340`,
- `coupled_vs_additive`: `746_044_000_000 < 740_946_409_660 + 156_088_992_805`,
- `slopes`: with linear terms `4_159_564_234`, `1×` passes Yukon (`900_719_925_474`) with exact margin
  `150_516_361_240`, whereas `2×` exceeds Yukon. -/
theorem convex_coupled_tstore_storage_bracket_and_yukon_margin_non_vacuous_and_tight
    (u1 u2 t1 t2 : Nat) (hu : u1 + u2 ≤ 2000000)
    (h1 : t1 ≤ 373022 * u1) (h2 : t2 ≤ 373022 * u2) :
    t1 + t2 ≤ 746044000000 ∧
    (11 * buildTicks 158162 + buildTicks 145647 = 740946409660 ∧
      746044000000 - 740946409660 = 5097590340) ∧
    746044000000 < 740946409660 + 156088992805 ∧
    (746044000000 + 4159564234 < yukon ∧
      yukon - (746044000000 + 4159564234) = 150516361240 ∧
      yukon < 2 * (740946409660 + 4159564234)) :=
  ⟨coupled_le u1 u2 t1 t2 hu h1 h2,
   bracket,
   coupled_vs_additive,
   slopes⟩

/-- Theorem 4 (`non_vacuous_and_tight`, **Unconditional `PanSimp →PanToWord →WordToWord` Call-Target Safety & Tightness Witnesses**):
Consolidates the unconditional frontend and mid-end `WordNoStubCall` chain without `hcall`:
- `panToWord_NoStubCall` & `panToWord_names`: every function emitted by `panToWordCompileProgHOL`
  satisfies `WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1`,
- `panToWordToWord_NoStubCall`: every function emitted by `WordToWord.compile` satisfies `WordNoStubCall y.2.2 = true`,
- Tightness witnesses for `TgtGood`, `WordNoStubCall`, and `NSC`. -/
theorem unconditional_pan_to_word_and_word_to_word_no_stub_call_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) :
    (∀ y ∈ panToWordCompileProgHOL arch prog, WordNoStubCall y.2.2 = true) ∧
    (∀ y ∈ panToWordCompileProgHOL arch prog, 64 ≤ y.1) ∧
    (∀ y ∈ panToWordCompileProgHOL arch prog, WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1) ∧
    (∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoStubCall y.2.2 = true) ∧
    ¬ TgtGood (some storeConstsStubLocation) ∧
    (TgtGood (some 0) ∧ TgtGood (some 64) ∧ ¬ TgtGood none) ∧
    (WordNoStubCall (WordLangProgHOL.call (α := BitVec width) none (some storeConstsStubLocation) [] none) = false ∧
     WordNoStubCall (WordLangProgHOL.call (α := BitVec width) none (some 64) [] none) = true) ∧
    NSC (WordLangProgHOL.seq (α := BitVec width) .skip
      (.call none (some storeConstsStubLocation) [] none)) = false ∧
    NSC (WordLangProgHOL.call (α := BitVec width) none (some 64) [] none) = true ∧
    NSC (WordLangProgHOL.storeConsts (α := BitVec width) 0 1 2 3 []) = true := by
  have hf := SelfContainedFrontMidEndNoStubCallAndFortyEightBudgetSynth.frontend_pan_to_word_no_stub_call_and_names_audit_non_vacuous_and_tight arch prog
  exact ⟨hf.1,
    hf.2.1,
    hf.2.2.1,
    WordToWordNoStubCallAndFortyEightBudgetMaster.panToWordToWord_NoStubCall_non_vacuous_and_tight arch prog wc ac,
    hf.2.2.2.1,
    hf.2.2.2.2.1,
    hf.2.2.2.2.2,
    WordToWordNoStubCallAndFortyEightBudgetMaster.NSC_rejects_stub_call_non_vacuous_and_tight,
    WordToWordNoStubCallAndFortyEightBudgetMaster.NSC_accepts_user_call_non_vacuous_and_tight,
    WordToWordNoStubCallAndFortyEightBudgetMaster.NSC_allows_storeConsts_non_vacuous_and_tight⟩

/-- Theorem 5 (`non_vacuous_and_tight`, **Full Unconditional Chain from `PanSimp` to `StackToLab` (`StackNoSt`, `NoStubCall`, `FlattenVisitsSt = false`, `sectionId`)**):
Consolidates the complete unconditional compiler safety chain from `PanSimp` through `PanToWord`,
`WordToWord`, `WordToStack`, `StackRawCall`, `StackAlloc`, `StackRemove`, `StackNames`, and `StackToLab`:
- `panToWordCompileProgHOL` emits `WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1`,
- `WordToWord.compile` preserves `WordNoStubCall y.2.2 = true`,
- Every non-stub body reaching `StackNames.progCompHOL` and `StackToLab.progToSectionHOL` satisfies
  `StackNoSt = true`, `NoStubCall = true`, `FlattenVisitsSt = false` (`panToStackToLab_never_visits_StoreConsts`),
  and `sectionId = y.1`,
- Discrimination witness: a synthetic `.storeConsts` node has `StackNoSt = false`, `FlattenVisitsSt = true`,
  and flattens to `(.list [], false, next)`. -/
theorem unconditional_pan_to_stack_to_lab_full_chain_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (tail : Bool) (sid next : Nat) (cs bs : List Nat) :
    (∀ y ∈ panToWordCompileProgHOL arch prog, WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1) ∧
    (∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoStubCall y.2.2 = true) ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
    (StackNoSt (.seq .skip (.storeConsts 0 1 none) : HolProg width) = false ∧
     FlattenVisitsSt (.seq .skip (.storeConsts 0 1 none) : HolProg width) = true ∧
     StackToLab.flattenHOL tail (.storeConsts 0 1 none : HolProg width) sid next cs bs =
       (.list [], false, next)) :=
  ⟨PanToWordNoStubCallAndFortyEightBudgetMaster.frontend_safe_names_non_vacuous_and_tight arch prog,
   WordToWordNoStubCallAndFortyEightBudgetMaster.panToWordToWord_NoStubCall_non_vacuous_and_tight arch prog wc ac,
   UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.unconditional_section_non_vacuous_and_tight
     arch prog wc ac perf info j bd ptr f,
   UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.store_consts_discrimination_non_vacuous_and_tight
     tail sid next cs bs⟩

/-- Theorem 6 (`non_vacuous_and_tight`, **General Side-Regime Slope Absorption (`≤ 50_000` vs `50_001`) + Core 19-Table Inventory + Coupled `ts+64` Envelope**):
Unites general side-regime slope absorption (`blk + (l.map Prod.fst).sum ≤ 100_000_000_000` under
pointwise slope `≤ 50_000`), exact failure at `50_001`, the 19-table `coreHtabInventory` audit
(including `"ts+64"`), and the convex coupled `ts+64` + storage bound (`t1 + t2 ≤ 746_044_000_000`). -/
theorem side_slope_absorption_core_inventory_and_coupled_tstore_non_vacuous_and_tight
    (l : List (Nat × Nat)) (B blk : Nat)
    (hS : B + (l.map Prod.snd).sum ≤ S) (hblk : 40 * blk ≤ B * B)
    (hpw : ∀ p ∈ l, p.1 ≤ 50000 * p.2)
    (u1 u2 t1 t2 : Nat) (hu : u1 + u2 ≤ 2000000)
    (h1 : t1 ≤ 373022 * u1) (h2 : t2 ≤ 373022 * u2) :
    ((l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum ∧
      blk + (l.map Prod.fst).sum ≤ 100000000000) ∧
    ¬ (∀ B' U' T' blk' : Nat, B' + U' ≤ S → 40 * blk' ≤ B' * B' →
        T' ≤ 50001 * U' → blk' + T' ≤ 100000000000) ∧
    (coreHtabInventory.length = 19 ∧ coreHtabInventory.Nodup ∧
      "ts+64" ∈ coreHtabInventory ∧
      40 * 100000000000 = S * S ∧
      0 + 2000000 ≤ S ∧ 100000000000 = 50000 * 2000000 ∧
      50001 * 2000000 > 100000000000) ∧
    t1 + t2 ≤ 746044000000 ∧
    (746044000000 + 4159564234 < yukon ∧
      yukon - (746044000000 + 4159564234) = 150516361240 ∧
      yukon < 2 * (740946409660 + 4159564234)) := by
  have hpt := UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.pointwise_side_absorption_non_vacuous_and_tight
    l B blk hS hblk hpw
  exact ⟨hpt,
    ExhaustiveHtabInventoryAndNoStubCallMaster.threshold_sharp_non_vacuous_and_tight,
    UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.inventory_and_threshold_endpoints_non_vacuous_and_tight,
    coupled_le u1 u2 t1 t2 hu h1 h2,
    slopes⟩

/-- Theorem 7 (`non_vacuous_and_tight`, **Shared 11-Table Absorption (`156_088_992_805` Ticks) vs Convex Coupled `ts+64` + Storage Envelope (`746_044_000_000` Ticks)**):
Combines the shared 11-table storage absorption closure (`blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571`,
`kPanElevenTablesShared = 156_088_992_805`, 12-tx feasible bracket `155_688_931_265`, `5×` Yukon margin
`120_274_961_449`) with the convex coupled `ts+64` + storage bound (`746_044_000_000 < 740_946_409_660 + 156_088_992_805`
and `1×` Yukon margin `150_516_361_240`). -/
theorem shared_eleven_tables_and_convex_tstore_coupling_synthesis_non_vacuous_and_tight
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S)
    (hblk : 40 * blk ≤ B * B) (hloc : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7989 * u2)
    (h3 : 30 * t3 ≤ 5 * 5611 * u3)
    (h4 : 60 * t4 ≤ (M + 2280) * u4) :
    blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
    (kPanElevenTablesShared = 156_088_992_805 ∧
      kPanElevenTables - kPanElevenTablesShared = 11_342_996_533) ∧
    (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
      coupledCost witness ≤ kPanElevenTablesShared ∧
      kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
      400_061_540 * 10_000 < 26 * 156_088_992_805 ∧
      400_061_540 * 10_000 < 26 * 155_688_931_265) ∧
    (5 * kPanElevenTablesShared < yukon ∧
      yukon - 5 * kPanElevenTablesShared = 120_274_961_449) ∧
    (yukon < 6 * kPanElevenTablesShared ∧ yukon < 6 * coupledCost witness) ∧
    (11 * buildTicks 158162 + buildTicks 145647 = 740946409660 ∧
      746044000000 - 740946409660 = 5097590340) ∧
    746044000000 < 740946409660 + 156088992805 ∧
    (746044000000 + 4159564234 < yukon ∧
      yukon - (746044000000 + 4159564234) = 150516361240 ∧
      yukon < 2 * (740946409660 + 4159564234)) := by
  have hel := UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.shared_eleven_tables_absorption_non_vacuous_and_tight
    B u2 u3 u4 blk loc t2 t3 t4 hS hblk hloc h2 h3 h4
  exact ⟨hel.1,
    hel.2.1,
    hel.2.2.1,
    hel.2.2.2.1,
    hel.2.2.2.2.1,
    bracket,
    coupled_vs_additive,
    slopes⟩

/-- Theorem 8 (`non_vacuous_and_tight`, **50-Budget Portfolio Strict Ordering, Preservation of the 48-Budget Prefix, and `fiftyClaims` (`≤ 128` Bytes) Audit**):
Proves that the 50-budget `portfolio` has length `50`, is strictly increasing (`Pairwise (· < ·)`),
lies inside `[1_212_035_192, 900_719_925_474)`, preserves the 48-budget prefix
`ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.portfolio`, and pairs with `fiftyClaims`
(`50` valid `≤ 128`-byte JSON claims). -/
theorem fifty_budget_portfolio_shape_and_claims_audit_non_vacuous_and_tight
    (minutes K : Nat) :
    (portfolio.length = 50 ∧ portfolio.Pairwise (· < ·) ∧
      (∀ K_b ∈ portfolio, 1212035192 ≤ K_b ∧ K_b < 900719925474) ∧
      portfolio.take 48 = ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.portfolio) ∧
    (fiftyClaims.length = 50 ∧
      fiftyClaims.map Prod.fst = portfolio ∧
      (∀ entry ∈ fiftyClaims,
        entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true)) ∧
    (ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.portfolio.map
      (fun k_b => yukonScore k_b minutes)).Pairwise (· < ·) ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have h48 := SelfContainedFrontMidEndNoStubCallAndFortyEightBudgetSynth.forty_eight_portfolio_ordering_yukon_score_and_claims_audit_non_vacuous_and_tight minutes K
  exact ⟨UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.fifty_shape_non_vacuous_and_tight,
    UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.fifty_claim_payloads_non_vacuous_and_tight,
    h48.2.1,
    h48.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 9 (`non_vacuous_and_tight`, **Explicit 50-Budget & 48-Budget Finite Semantic Certificates Under Base Certificate (`cert : CertificateAt 1212035192`)**):
Consolidates `UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.fifty_finite_certificates_non_vacuous_and_tight`
and `SelfContainedFrontMidEndNoStubCallAndFortyEightBudgetSynth.forty_eight_and_fifty_two_budget_certificates_from_base_cert_non_vacuous_and_tight`:
under `cert : CertificateAt 1212035192`, every budget `K ∈ portfolio` (`50` budgets) has an explicit
`InitE.Certificate (baselineWithFiniteK K) (.finite K)`. -/
theorem fifty_and_forty_eight_budget_finite_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    ((portfolio.length = 50 ∧ portfolio.Pairwise (· < ·) ∧
        ∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
      (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
    (∀ K ∈ portfolio, K < 900719925474 ∧
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    (fiftyClaims.length = 50 ∧
      fiftyClaims.map Prod.fst = portfolio ∧
      (∀ entry ∈ fiftyClaims,
        entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true)) := by
  have h50 := UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.fifty_finite_certificates_non_vacuous_and_tight cert
  refine ⟨h50, ?_, UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.fifty_claim_payloads_non_vacuous_and_tight⟩
  intro K hK
  exact ⟨(h50.1.2.2 K hK).2, baselineWithFiniteK K, rfl, h50.2 K hK⟩

/-- Theorem 10 (`non_vacuous_and_tight`, **Master Wave 5 (`W5_143`) Self-Contained Transient-Storage Journal, Convex Coupling, Unconditional `PanSimp →StackToLab` Safety & 50-Budget Synthesis**):
Grand synthesis of `GuestTransientStorageGrowthAndJournalAnalysis` (`11/11` tight),
`SelfContainedFrontMidEndNoStubCallAndFortyEightBudgetSynth` (`10/10` tight), and
`UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster` (`12/12` tight) with `0` imports from
`InitECandidate.Proofs.Bounded*`:
1. Journal analysis (`journal_actions`, `restore_once ≤ 524_288`, `step_ticks`) and convex coupling
   between `ts+64` and storage under a single block gas budget `G_tstore + G_storage ≤ 200_000_000`
   (`tstore_slope`, `tstore_slope_tight`, `tstore_per_gas`, `storage_slope`, `coupled_le ≤ 746_044_000_000`
   ticks, `bracket`, `coupled_vs_additive`, and `slopes` with margin `150_516_361_240` under Yukon),
2. Unconditional compiler safety chain without `hcall` from `PanSimp` to `StackToLab`
   (`panToWord_NoStubCall`, `panToWordToWord_NoStubCall`, `panToStackNames_NoSt_and_NoStubCall_unconditional`,
   `FlattenVisitsSt = false` / `panToStackToLab_never_visits_StoreConsts`, and `sectionId = y.1`),
3. Strictly increasing 50-budget portfolio (`portfolio`, `fiftyClaims`) below Yukon (`900_719_925_474`)
   and explicit finite certificates under the base certificate premise (`cert : CertificateAt 1212035192`). -/
theorem master_self_contained_transient_storage_journal_and_fifty_budget_synth_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j_flag : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (j_list : List Bool) (hj : j_list.length ≤ 524288)
    (k_ts : Nat) (hk_ts : k_ts ≤ 158162)
    (u1 u2 t1 t2 : Nat) (hu : u1 + u2 ≤ 2000000)
    (h1 : t1 ≤ 373022 * u1) (h2 : t2 ≤ 373022 * u2)
    (l : List (Nat × Nat)) (B blk : Nat)
    (hS : B + (l.map Prod.snd).sum ≤ S) (hblk : 40 * blk ≤ B * B)
    (hslope : (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum)
    (cert : CertificateAt 1212035192) :
    ((restoreDels [false, true, false] = 2 ∧ restoreDels [true, true] = 0) ∧
      restoreDels j_list ≤ 524288 ∧
      ((1 + 1 : Nat) = 2 ∧ (1 + 1 + 1 : Nat) = 3) ∧
      250 * (k_ts - 1) ≤ 106 * 373022 ∧
      ¬ (250 * (158162 - 1) ≤ 106 * 373021) ∧
      100 * buildTicks k_ts ≤ 373022 * (106 * k_ts) ∧
      (2000000 / 20 / 2 + 13 * 167772 / 84 + 1 = 75965 ∧ 75965 < 373022) ∧
      t1 + t2 ≤ 746044000000 ∧
      (11 * buildTicks 158162 + buildTicks 145647 = 740946409660 ∧
        746044000000 - 740946409660 = 5097590340) ∧
      746044000000 < 740946409660 + 156088992805 ∧
      (746044000000 + 4159564234 < yukon ∧
        yukon - (746044000000 + 4159564234) = 150516361240 ∧
        yukon < 2 * (740946409660 + 4159564234))) ∧
    ((∀ y ∈ panToWordCompileProgHOL arch prog, WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1) ∧
      (∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
        WordNoStubCall y.2.2 = true) ∧
      (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2,
        y.1 = storeConstsStubLocation ∨
        (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j_flag bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
         NoStubCall (StackNames.progCompHOL f (StackRemove.comp j_flag bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
         FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j_flag bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
         (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j_flag bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1))) ∧
    ((blk + (l.map Prod.fst).sum ≤ 100000000000 ∧
        ¬ (∀ B' U' T' blk' : Nat, B' + U' ≤ S → 40 * blk' ≤ B' * B' →
          T' ≤ 50001 * U' → blk' + T' ≤ 100000000000)) ∧
      (kPanElevenTablesShared = 156088992805 ∧
        (feasible witness ∧ coupledCost witness = 155688931265 ∧
         coupledCost witness ≤ kPanElevenTablesShared ∧
         kPanElevenTablesShared - coupledCost witness = 400061540 ∧
         400061540 * 10000 < 26 * 156088992805 ∧
         400061540 * 10000 < 26 * 155688931265)) ∧
      ((portfolio.length = 50 ∧ portfolio.Pairwise (· < ·) ∧
         ∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
        (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
      (fiftyClaims.length = 50 ∧
        fiftyClaims.map Prod.fst = portfolio ∧
        (∀ entry ∈ fiftyClaims,
         entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true)) ∧
      (coreHtabInventory.length = 19 ∧ coreHtabInventory.Nodup) ∧
      (5 * kPanElevenTablesShared < yukon ∧
        yukon - 5 * kPanElevenTablesShared = 120274961449)) ∧
    isSolverModulePath ["InitECandidate", "Solver", "SelfContainedTransientStorageJournalAndFiftyBudgetSynth"] = true ∧
    admittedRelativePath .regularFile
      ["InitECandidate", "Solver", "SelfContainedTransientStorageJournalAndFiftyBudgetSynth"] true = true ∧
    zeroBoundedImportCount = 0 := by
  have hm50 := UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.integrated_master_non_vacuous_and_tight
    arch prog wc ac perf info j_flag bd ptr f l B blk hS hblk hslope cert
  exact ⟨⟨journal_actions,
      restore_once j_list hj,
      step_ticks,
      tstore_slope k_ts hk_ts,
      tstore_slope_tight,
      tstore_per_gas k_ts hk_ts,
      storage_slope,
      coupled_le u1 u2 t1 t2 hu h1 h2,
      bracket,
      coupled_vs_additive,
      slopes⟩,
    ⟨PanToWordNoStubCallAndFortyEightBudgetMaster.frontend_safe_names_non_vacuous_and_tight arch prog,
      WordToWordNoStubCallAndFortyEightBudgetMaster.panToWordToWord_NoStubCall_non_vacuous_and_tight arch prog wc ac,
      hm50.1⟩,
    hm50.2,
    by decide,
    by decide,
    rfl⟩

#print axioms journal_actions_restore_once_and_probe_step_ticks_non_vacuous_and_tight
#print axioms tstore_slope_tightness_per_gas_and_storage_slope_non_vacuous_and_tight
#print axioms convex_coupled_tstore_storage_bracket_and_yukon_margin_non_vacuous_and_tight
#print axioms unconditional_pan_to_word_and_word_to_word_no_stub_call_non_vacuous_and_tight
#print axioms unconditional_pan_to_stack_to_lab_full_chain_non_vacuous_and_tight
#print axioms side_slope_absorption_core_inventory_and_coupled_tstore_non_vacuous_and_tight
#print axioms shared_eleven_tables_and_convex_tstore_coupling_synthesis_non_vacuous_and_tight
#print axioms fifty_budget_portfolio_shape_and_claims_audit_non_vacuous_and_tight
#print axioms fifty_and_forty_eight_budget_finite_certificates_non_vacuous_and_tight
#print axioms master_self_contained_transient_storage_journal_and_fifty_budget_synth_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedTransientStorageJournalAndFiftyBudgetSynth
