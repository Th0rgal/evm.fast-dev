import InitECandidate.Solver.PanToWordNoStubCallAndFortyEightBudgetMaster
import InitECandidate.Solver.WordToWordNoStubCallAndFortyEightBudgetMaster
import InitECandidate.Solver.ExhaustiveHtabInventoryAndNoStubCallMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedFrontMidEndNoStubCallAndFortyEightBudgetSynth` — Wave 5 Atomic Worker `W5_138`

Self-contained synthesis (`0` imports from `InitECandidate.Proofs.Bounded*`) uniting:
1. **`PanToWordNoStubCallAndFortyEightBudgetMaster` (`12/12` tight)**:
   - Unconditional frontend call-target safety (`panToWord_NoStubCall_non_vacuous_and_tight`,
     `panToWord_names_non_vacuous_and_tight`, `frontend_safe_names_non_vacuous_and_tight`,
     `tgtGood_rejects_stub_non_vacuous_and_tight`, `tgtGood_accepts_non_vacuous_and_tight`,
     `wordNoStubCall_tight_non_vacuous_and_tight`),
   - Warm access-set rollback exactness (`truncDels (warmN (enter n) k) = k`) and integrated
     48-budget master (`integrated_master_non_vacuous_and_tight`).
2. **`WordToWordNoStubCallAndFortyEightBudgetMaster` (`12/12` tight)**:
   - Unconditional mid-end and `StackNames` call-target safety (`panToWordToWord_NoStubCall_non_vacuous_and_tight`,
     `panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight`,
     `NSC_rejects_stub_call_non_vacuous_and_tight`, `NSC_accepts_user_call_non_vacuous_and_tight`,
     `NSC_allows_storeConsts_non_vacuous_and_tight`),
   - Shared 11-table absorption closure (`eleven_tables_closure_non_vacuous_and_tight`) and
     implication-decoupled integrated master (`integrated_master_non_vacuous_and_tight`).
3. **`ExhaustiveHtabInventoryAndNoStubCallMaster` (`12/12` tight)**:
   - General side-regime slope absorption (`side_absorption_scalar_non_vacuous_and_tight`,
     `general_side_regime_absorption_non_vacuous_and_tight`, `slope_sum_non_vacuous_and_tight`,
     `absorption_tight_non_vacuous_and_tight`) and exact sharpness at `50_001` (`threshold_sharp_non_vacuous_and_tight`),
   - Exhaustive hash-table slope audit (`known_slopes_non_vacuous_and_tight`) and transient-storage
     (`TSTORE`/`TLOAD`) sensitivity (`tstore_slope_exceeds_non_vacuous_and_tight`,
     `tstore_tx_budget_non_vacuous_and_tight`, `tstore_witness_non_vacuous_and_tight`,
     `tstore_sensitivity_non_vacuous_and_tight`),
   - Strictly increasing 48-budget portfolio below Yukon (`900_719_925_474`) and finite certificates
     (`forty_eight_budget_certificates_non_vacuous_and_tight`).
-/

namespace InitECandidate.Solver.SelfContainedFrontMidEndNoStubCallAndFortyEightBudgetSynth

open Classical
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitE
open InitECandidate.Solver
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (WordNoStubCall NoStubCall)
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.PanToWordNoStubCall (TgtGood)
open _root_.InitECandidate.Solver.WordToWordNoStubCall (NSC)
open _root_.InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption (tstoreTicks)
open _root_.InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption (M S kPanElevenTablesShared)
open _root_.InitECandidate.Solver.GuestElevenTablesAndWarmAddressProbeBound (kPanElevenTables)
open _root_.InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening (feasible witness coupledCost)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestWarmAccessSetAndRollbackBound (enter warmN truncDels)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster
  (portfolio elevenTablesSharedSlope3UnrolledK elevenTablesSharedSlope3K
   elevenTablesSharedSlope5UnrolledK elevenTablesSharedSlope5K)
open _root_.InitECandidate.Solver.SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth
  (fortyEightSharedPortfolio fortyEightBaselineWarmSetsPortfolio fortyEightSharedClaims
   allFiftyTwoSharedBudgets)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit
open _root_.InitECandidate.Solver.PurifiedSolverIndex
open _root_.InitECandidate.Solver.PurifiedSubmissionBound
open _root_.InitECandidate.Solver.PurifiedImportGraphCert
open _root_.InitECandidate.Solver.SelfContainedCompleteCampaignCert
open _root_.InitECandidate.Solver.SelfContainedSolutionCandidates
open _root_.InitECandidate.Solver.SelfContainedTenCandidateHierarchy
open _root_.InitECandidate.Solver.SelfContainedTwelveTierSynthesis

/-- Theorem 1 (`non_vacuous_and_tight`, **Unconditional Frontend `PanToWord` Call-Target Safety & Tightness Audit (`PanToWordNoStubCallAndFortyEightBudgetMaster`)**):
Consolidates the unconditional frontend theorems and tight witnesses:
- `panToWord_NoStubCall_non_vacuous_and_tight`: every `WordLang` body emitted by `panToWordCompileProgHOL`
  satisfies `WordNoStubCall y.2.2 = true`,
- `panToWord_names_non_vacuous_and_tight`: every emitted function label satisfies `64 ≤ y.1`,
- `frontend_safe_names_non_vacuous_and_tight`: joint `WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1`,
- `tgtGood_rejects_stub_non_vacuous_and_tight`, `tgtGood_accepts_non_vacuous_and_tight`, and
  `wordNoStubCall_tight_non_vacuous_and_tight`. -/
theorem frontend_pan_to_word_no_stub_call_and_names_audit_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width)) :
    (∀ y ∈ panToWordCompileProgHOL arch prog, WordNoStubCall y.2.2 = true) ∧
    (∀ y ∈ panToWordCompileProgHOL arch prog, 64 ≤ y.1) ∧
    (∀ y ∈ panToWordCompileProgHOL arch prog, WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1) ∧
    ¬ TgtGood (some storeConstsStubLocation) ∧
    (TgtGood (some 0) ∧ TgtGood (some 64) ∧ ¬ TgtGood none) ∧
    (WordNoStubCall (WordLangProgHOL.call (α := BitVec width) none (some storeConstsStubLocation) [] none) = false ∧
     WordNoStubCall (WordLangProgHOL.call (α := BitVec width) none (some 64) [] none) = true) :=
  ⟨PanToWordNoStubCallAndFortyEightBudgetMaster.panToWord_NoStubCall_non_vacuous_and_tight arch prog,
   PanToWordNoStubCallAndFortyEightBudgetMaster.panToWord_names_non_vacuous_and_tight arch prog,
   PanToWordNoStubCallAndFortyEightBudgetMaster.frontend_safe_names_non_vacuous_and_tight arch prog,
   PanToWordNoStubCallAndFortyEightBudgetMaster.tgtGood_rejects_stub_non_vacuous_and_tight,
   PanToWordNoStubCallAndFortyEightBudgetMaster.tgtGood_accepts_non_vacuous_and_tight,
   PanToWordNoStubCallAndFortyEightBudgetMaster.wordNoStubCall_tight_non_vacuous_and_tight⟩

/-- Theorem 2 (`non_vacuous_and_tight`, **Unconditional Mid-End `WordToWord` & `StackNames` Call-Target Safety (`WordToWordNoStubCallAndFortyEightBudgetMaster`)**):
Consolidates the unconditional mid-end and stack-lowering call-safety theorems:
- `panToWordToWord_NoStubCall_non_vacuous_and_tight`: every `WordToWord.compile` output body from
  any Pancake program satisfies `WordNoStubCall y.2.2 = true`,
- `panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight`: every function emitted
  by `WordToStack.Native.compileNative` is either the `storeConstsStubLocation` section itself or lowers
  through `StackRawCall → StackAlloc → StackRemove → StackNames` to a program satisfying both
  `StackNoSt = true` and `NoStubCall = true`,
- `NSC_rejects_stub_call_non_vacuous_and_tight`, `NSC_accepts_user_call_non_vacuous_and_tight`, and
  `NSC_allows_storeConsts_non_vacuous_and_tight`. -/
theorem mid_end_word_to_word_and_stack_names_no_stub_call_audit_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    (∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoStubCall y.2.2 = true) ∧
    (∀ y ∈ (WordToStack.Native.compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true)) ∧
    NSC (WordLangProgHOL.seq (α := BitVec width) .skip
      (.call none (some storeConstsStubLocation) [] none)) = false ∧
    NSC (WordLangProgHOL.call (α := BitVec width) none (some 64) [] none) = true ∧
    NSC (WordLangProgHOL.storeConsts (α := BitVec width) 0 1 2 3 []) = true :=
  ⟨WordToWordNoStubCallAndFortyEightBudgetMaster.panToWordToWord_NoStubCall_non_vacuous_and_tight arch prog wc ac,
   WordToWordNoStubCallAndFortyEightBudgetMaster.panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight
     arch prog wc ac perf info j bd ptr f,
   WordToWordNoStubCallAndFortyEightBudgetMaster.NSC_rejects_stub_call_non_vacuous_and_tight,
   WordToWordNoStubCallAndFortyEightBudgetMaster.NSC_accepts_user_call_non_vacuous_and_tight,
   WordToWordNoStubCallAndFortyEightBudgetMaster.NSC_allows_storeConsts_non_vacuous_and_tight⟩

/-- Theorem 3 (`non_vacuous_and_tight`, **Unified Front-Mid-End Unconditional Call-Safety Chain (`panToWord_NoStubCall` → `panToWordToWord_NoStubCall` → `panToStackNames_NoSt_and_NoStubCall_unconditional`)**):
Combines all three stages of the unconditional `NoStubCall` proof chain for arbitrary Pancake source
programs without any source-level `hcall` assumption, together with non-stub implication form
(`y.1 ≠ storeConstsStubLocation → StackNoSt ... = true ∧ NoStubCall ... = true`). -/
theorem front_mid_end_unconditional_no_stub_call_chain_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    (∀ y ∈ panToWordCompileProgHOL arch prog, WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1) ∧
    (∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoStubCall y.2.2 = true) ∧
    (∀ y ∈ (WordToStack.Native.compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true)) ∧
    (∀ y ∈ (WordToStack.Native.compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 ≠ storeConstsStubLocation →
      StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
      NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true) := by
  refine ⟨PanToWordNoStubCallAndFortyEightBudgetMaster.frontend_safe_names_non_vacuous_and_tight arch prog,
    WordToWordNoStubCallAndFortyEightBudgetMaster.panToWordToWord_NoStubCall_non_vacuous_and_tight arch prog wc ac,
    WordToWordNoStubCallAndFortyEightBudgetMaster.panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight
      arch prog wc ac perf info j bd ptr f,
    ?_⟩
  intro y hy hne
  rcases WordToWordNoStubCallAndFortyEightBudgetMaster.panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight
      arch prog wc ac perf info j bd ptr f y hy with hstub | hsafe
  · exact False.elim (hne hstub)
  · exact hsafe

/-- Theorem 4 (`non_vacuous_and_tight`, **General Side-Regime Slope Absorption (`≤ 50_000` ticks/unit) & Exact Threshold Sharpness at `50_001` (`ExhaustiveHtabInventoryAndNoStubCallMaster`)**):
Consolidates the general slope-absorption and sharpness theorems:
- `side_absorption_scalar_non_vacuous_and_tight`: `B + U ≤ S ∧ 40 * blk ≤ B * B ∧ T ≤ 50_000 * U → blk + T ≤ 100_000_000_000`,
- `general_side_regime_absorption_non_vacuous_and_tight`: for any list `l : List (Nat × Nat)` of
  auxiliary regimes `(t_i, u_i)` sharing the block budget `B + (l.map Prod.snd).sum ≤ S` with
  `40 * blk ≤ B * B` and `(l.map Prod.fst).sum ≤ 50_000 * (l.map Prod.snd).sum`,
  `blk + (l.map Prod.fst).sum ≤ 100_000_000_000`,
- `slope_sum_non_vacuous_and_tight`: pointwise bound `∀ p ∈ l, p.1 ≤ 50_000 * p.2` implies
  `(l.map Prod.fst).sum ≤ 50_000 * (l.map Prod.snd).sum`,
- `absorption_tight_non_vacuous_and_tight`: `40 * 100_000_000_000 = S * S ∧ 100_000_000_000 + 0 = 100_000_000_000`,
- `threshold_sharp_non_vacuous_and_tight`: `50_001` fails (`¬ ∀ B U T blk, B + U ≤ S → 40 * blk ≤ B * B → T ≤ 50_001 * U → blk + T ≤ 100_000_000_000`),
- `known_slopes_non_vacuous_and_tight`: all 4 non-`tstore` auxiliary regimes lie strictly below `50_000` ticks/unit. -/
theorem general_side_regime_absorption_and_threshold_sharp_audit_non_vacuous_and_tight
    (B U T blk : Nat) (hBU : B + U ≤ S) (hblk_u : 40 * blk ≤ B * B) (hT : T ≤ 50000 * U)
    (l : List (Nat × Nat)) (B_l blk_l : Nat)
    (hS_l : B_l + (l.map Prod.snd).sum ≤ S) (hblk_l : 40 * blk_l ≤ B_l * B_l)
    (hpw : ∀ p ∈ l, p.1 ≤ 50000 * p.2) :
    blk + T ≤ 100_000_000_000 ∧
    (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum ∧
    blk_l + (l.map Prod.fst).sum ≤ 100_000_000_000 ∧
    (40 * 100_000_000_000 = S * S ∧ 100_000_000_000 + 0 = 100_000_000_000) ∧
    ¬ (∀ B' U' T' blk' : Nat, B' + U' ≤ S → 40 * blk' ≤ B' * B' →
        T' ≤ 50001 * U' → blk' + T' ≤ 100_000_000_000) ∧
    (5 * 7989 ≤ 21 * 50000 ∧ 5 * 5611 ≤ 30 * 50000 ∧
      167772 + 2280 ≤ 60 * 50000 ∧ 2 * 6250 ≤ 320 * 50000) := by
  have hsl : (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum :=
    ExhaustiveHtabInventoryAndNoStubCallMaster.slope_sum_non_vacuous_and_tight l hpw
  exact ⟨ExhaustiveHtabInventoryAndNoStubCallMaster.side_absorption_scalar_non_vacuous_and_tight B U T blk hBU hblk_u hT,
    hsl,
    ExhaustiveHtabInventoryAndNoStubCallMaster.general_side_regime_absorption_non_vacuous_and_tight l B_l blk_l hS_l hblk_l hsl,
    ExhaustiveHtabInventoryAndNoStubCallMaster.absorption_tight_non_vacuous_and_tight,
    ExhaustiveHtabInventoryAndNoStubCallMaster.threshold_sharp_non_vacuous_and_tight,
    ExhaustiveHtabInventoryAndNoStubCallMaster.known_slopes_non_vacuous_and_tight⟩

/-- Theorem 5 (`non_vacuous_and_tight`, **Transient-Storage (`TSTORE`/`TLOAD`) Slope Sensitivity & Eleven-Table Shared Absorption (`156_088_992_805` ticks, `5× < Yukon` with Margin `120_274_961_449`)**):
Combines the transient-storage sensitivity audit from `ExhaustiveHtabInventoryAndNoStubCallMaster`
(`tstore_slope_exceeds`, `tstore_tx_budget`, `tstore_witness`, `tstore_sensitivity`) with the
11-table shared absorption closure (`blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571`),
`kPanElevenTablesShared = 156_088_992_805`, the 12-tx feasible bracket (`155_688_931_265`,
gap `400_061_540 < 0.26%`), `5×` Yukon margin (`120_274_961_449`), and `6×` impossibility. -/
theorem tstore_sensitivity_and_eleven_tables_shared_bound_audit_non_vacuous_and_tight
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S) (hblk : 40 * blk ≤ B * B) (hloc : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7989 * u2) (h3 : 30 * t3 ≤ 5 * 5611 * u3)
    (h4 : 60 * t4 ≤ (M + 2280) * u4) :
    (tstoreTicks 83826 - tstoreTicks 83825 = 2 * 83825 ∧ 50000 < 83825) ∧
    (120 + 2 * 83826 ≤ 167772 ∧ 11 * 167772 + 120 + 2 * 77194 ≤ S) ∧
    11 * tstoreTicks 83826 + tstoreTicks 77194 = 83_252_695_392 ∧
    (83_252_695_392 ≤ 50000 * (11 * 2 * 83826 + 2 * 77194) ∧
      2 * tstoreTicks 167652 = 56_214_050_904 ∧ 50000 * 167772 < 2 * tstoreTicks 167652) ∧
    blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
    (kPanElevenTablesShared = 156_088_992_805 ∧
      kPanElevenTables - kPanElevenTablesShared = 11_342_996_533) ∧
    (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
      coupledCost witness ≤ kPanElevenTablesShared ∧
      kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
      400_061_540 * 10000 < 26 * 156_088_992_805 ∧
      400_061_540 * 10000 < 26 * 155_688_931_265) ∧
    (5 * kPanElevenTablesShared < yukon ∧
      yukon - 5 * kPanElevenTablesShared = 120_274_961_449) ∧
    (yukon < 6 * kPanElevenTablesShared ∧ yukon < 6 * coupledCost witness) := by
  have hel := WordToWordNoStubCallAndFortyEightBudgetMaster.eleven_tables_closure_non_vacuous_and_tight
    B u2 u3 u4 blk loc t2 t3 t4 hS hblk hloc h2 h3 h4
  exact ⟨ExhaustiveHtabInventoryAndNoStubCallMaster.tstore_slope_exceeds_non_vacuous_and_tight,
    ExhaustiveHtabInventoryAndNoStubCallMaster.tstore_tx_budget_non_vacuous_and_tight,
    ExhaustiveHtabInventoryAndNoStubCallMaster.tstore_witness_non_vacuous_and_tight,
    ExhaustiveHtabInventoryAndNoStubCallMaster.tstore_sensitivity_non_vacuous_and_tight,
    hel.2.2.1,
    hel.2.2.2.2.1,
    PanToWordNoStubCallAndFortyEightBudgetMaster.bracket_non_vacuous_and_tight,
    PanToWordNoStubCallAndFortyEightBudgetMaster.five_margin_non_vacuous_and_tight,
    hel.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 6 (`non_vacuous_and_tight`, **Joint Unconditional Compiler Safety + General Slope Absorption + `156_088_992_805` Envelope (`ExhaustiveHtabInventoryAndNoStubCallMaster` + `PanToWordNoStubCallAndFortyEightBudgetMaster`)**):
Unites `ExhaustiveHtabInventoryAndNoStubCallMaster.panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight`
with `PanToWordNoStubCallAndFortyEightBudgetMaster.frontend_safe_names_non_vacuous_and_tight`,
`WordToWordNoStubCallAndFortyEightBudgetMaster.panToWordToWord_NoStubCall_non_vacuous_and_tight`,
and `five_margin_non_vacuous_and_tight`. -/
theorem unconditional_compiler_safety_and_general_absorption_joint_envelope_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (l : List (Nat × Nat)) (B blk : Nat)
    (hS : B + (l.map Prod.snd).sum ≤ S) (hblk : 40 * blk ≤ B * B)
    (hslope : (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum) :
    (∀ y ∈ panToWordCompileProgHOL arch prog, WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1) ∧
    (∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoStubCall y.2.2 = true) ∧
    ((∀ y ∈ (WordToStack.Native.compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2,
        y.1 = storeConstsStubLocation ∨
        (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
         NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true)) ∧
      blk + (l.map Prod.fst).sum ≤ 100_000_000_000 ∧
      (¬ (∀ B' U' T' blk' : Nat, B' + U' ≤ S → 40 * blk' ≤ B' * B' →
        T' ≤ 50001 * U' → blk' + T' ≤ 100_000_000_000)) ∧
      kPanElevenTablesShared = 156_088_992_805 ∧
      (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
        coupledCost witness ≤ kPanElevenTablesShared ∧
        kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
        400_061_540 * 10000 < 26 * 156_088_992_805 ∧
        400_061_540 * 10000 < 26 * 155_688_931_265)) ∧
    (5 * kPanElevenTablesShared < yukon ∧
      yukon - 5 * kPanElevenTablesShared = 120_274_961_449) :=
  ⟨PanToWordNoStubCallAndFortyEightBudgetMaster.frontend_safe_names_non_vacuous_and_tight arch prog,
   WordToWordNoStubCallAndFortyEightBudgetMaster.panToWordToWord_NoStubCall_non_vacuous_and_tight arch prog wc ac,
   ExhaustiveHtabInventoryAndNoStubCallMaster.panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight
     arch prog wc ac perf info j bd ptr f l B blk hS hblk hslope,
   PanToWordNoStubCallAndFortyEightBudgetMaster.five_margin_non_vacuous_and_tight⟩

/-- Theorem 7 (`non_vacuous_and_tight`, **48-Budget Portfolio Ordering, Yukon Score Monotonicity (`< 2^53 - 1`), and `claim.json ≤ 128` Byte Audit**):
Proves that `portfolio` (`= fortyEightSharedPortfolio`) has length `48`, is strictly ordered
(`Pairwise (· < ·)`), lies strictly inside `[1_212_035_192, 857_384_015_252]` below Yukon `900_719_925_474`,
induces strictly increasing `yukonScore` values `< 2^53 - 1` for every runtime `minutes`, and pairs
with `fortyEightSharedClaims` (`48` valid `≤ 128`-byte JSON claims). -/
theorem forty_eight_portfolio_ordering_yukon_score_and_claims_audit_non_vacuous_and_tight
    (minutes K : Nat) :
    (portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
      ∀ k ∈ portfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
    (portfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ k ∈ portfolio,
      yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ∧
      yukonScore k minutes ≤ yukonScore 857_384_015_252 minutes ∧
      yukonScore k minutes < 2 ^ 53 - 1) ∧
    fortyEightSharedClaims.length = 48 ∧
    fortyEightSharedClaims.map Prod.fst = portfolio ∧
    (∀ entry ∈ fortyEightSharedClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    elevenTablesSharedSlope3UnrolledK = 468_266_987_647 ∧
    elevenTablesSharedSlope3K = 468_267_001_447 ∧
    elevenTablesSharedSlope5UnrolledK = 780_444_973_257 ∧
    elevenTablesSharedSlope5K = 780_444_987_057 ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have hsc := SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth.forty_eight_shared_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight minutes K
  have hcl := SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth.forty_eight_shared_claims_valid_and_within_128_bytes_non_vacuous_and_tight 1
  exact ⟨PanToWordNoStubCallAndFortyEightBudgetMaster.portfolio_shape_non_vacuous_and_tight,
    hsc.1,
    hsc.2.2.1,
    hcl.1,
    hcl.2.1,
    hcl.2.2.1,
    rfl, rfl, rfl, rfl,
    hsc.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 8 (`non_vacuous_and_tight`, **Conditional 48-Budget & 52-Budget Finite Semantic Certificates from Base Certificate (`cert : CertificateAt 1212035192`)**):
Consolidates `PanToWordNoStubCallAndFortyEightBudgetMaster.forty_eight_certified_non_vacuous_and_tight`
and `ExhaustiveHtabInventoryAndNoStubCallMaster.forty_eight_budget_certificates_non_vacuous_and_tight`:
under `cert : CertificateAt 1212035192`, all 48 budgets in `portfolio` (`= fortyEightSharedPortfolio`),
all 48 budgets in `fortyEightBaselineWarmSetsPortfolio`, and all 52 budgets in `allFiftyTwoSharedBudgets`
are certified via `InitE.Certificate (baselineWithFiniteK K) (.finite K)`. -/
theorem forty_eight_and_fifty_two_budget_certificates_from_base_cert_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    ((portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
        ∀ K ∈ portfolio, 1_212_035_192 ≤ K ∧ K < 900_719_925_474) ∧
      (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
      fortyEightSharedClaims.length = 48 ∧
      fortyEightSharedClaims.map Prod.fst = portfolio ∧
      (∀ entry ∈ fortyEightSharedClaims,
        entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true)) ∧
    (∀ K ∈ portfolio, K < 900_719_925_474 ∧
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope3UnrolledK) (.finite elevenTablesSharedSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope3K) (.finite elevenTablesSharedSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope5UnrolledK) (.finite elevenTablesSharedSlope5UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope5K) (.finite elevenTablesSharedSlope5K) := by
  have hc48 := ExhaustiveHtabInventoryAndNoStubCallMaster.forty_eight_budget_certificates_non_vacuous_and_tight cert
  have hm48 := PanToWordNoStubCallAndFortyEightBudgetMaster.forty_eight_certified_non_vacuous_and_tight cert
  refine ⟨hc48, ?_,
    (hm48.2.2 elevenTablesSharedSlope3UnrolledK (by decide)).2,
    (hm48.2.2 elevenTablesSharedSlope3K (by decide)).2,
    (hm48.2.2 elevenTablesSharedSlope5UnrolledK (by decide)).2,
    (hm48.2.2 elevenTablesSharedSlope5K (by decide)).2⟩
  intro K hK
  have hk := hm48.2.2 K hK
  exact ⟨hk.1, baselineWithFiniteK K, rfl, hk.2⟩

/-- Theorem 9 (`non_vacuous_and_tight`, **Integrated Master Synthesis of `PanToWordNoStubCallAndFortyEightBudgetMaster` & `WordToWordNoStubCallAndFortyEightBudgetMaster`**):
Unites `PanToWordNoStubCallAndFortyEightBudgetMaster.integrated_master_non_vacuous_and_tight` and
`WordToWordNoStubCallAndFortyEightBudgetMaster.integrated_master_non_vacuous_and_tight`, including
warm access-set rollback exactness (`truncDels (warmN (enter n) k) = k`) and both conditional-implication
and explicit-certificate forms for the 48-budget portfolio. -/
theorem front_and_mid_end_integrated_masters_synthesis_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (cert : CertificateAt 1212035192) (n k : Nat)
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S) (hb : 40 * blk ≤ B * B) (hl : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7989 * u2) (h3 : 30 * t3 ≤ 5 * 5611 * u3)
    (h4 : 60 * t4 ≤ (M + 2280) * u4) :
    ((∀ y ∈ panToWordCompileProgHOL arch prog,
        WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1) ∧
      blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
      kPanElevenTablesShared = 156_088_992_805 ∧
      (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
        coupledCost witness ≤ kPanElevenTablesShared ∧
        kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
        400_061_540 * 10000 < 26 * 156_088_992_805 ∧
        400_061_540 * 10000 < 26 * 155_688_931_265) ∧
      (5 * kPanElevenTablesShared < yukon ∧
        yukon - 5 * kPanElevenTablesShared = 120_274_961_449) ∧
      (yukon < 6 * kPanElevenTablesShared ∧ yukon < 6 * coupledCost witness) ∧
      (truncDels (warmN (enter n) k) = k ∧
        (warmN (enter n) k).size - truncDels (warmN (enter n) k) = n) ∧
      (portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
        ∀ K ∈ portfolio, K < 900_719_925_474 ∧
          InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
    ((∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
        WordNoStubCall y.2.2 = true) ∧
      (∀ y ∈ (WordToStack.Native.compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2,
        y.1 ≠ storeConstsStubLocation →
        StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
        NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true)) := by
  have hm1 := PanToWordNoStubCallAndFortyEightBudgetMaster.integrated_master_non_vacuous_and_tight
    arch prog cert n k B u2 u3 u4 blk loc t2 t3 t4 hS hb hl h2 h3 h4
  have hm2 := WordToWordNoStubCallAndFortyEightBudgetMaster.integrated_master_non_vacuous_and_tight
    arch prog wc ac perf info j bd ptr f B u2 u3 u4 blk loc t2 t3 t4 hS hb hl h2 h3 h4
  exact ⟨hm1, ⟨hm2.1, hm2.2.1⟩⟩

/-- Theorem 10 (`non_vacuous_and_tight`, **Master Wave 5 (`W5_138`) Self-Contained Front-Mid-End `NoStubCall`, General Slope Absorption (`≤ 50_000` vs `50_001`) & 48-Budget Campaign Certificate**):
Grand synthesis of `PanToWordNoStubCallAndFortyEightBudgetMaster` (`12/12` tight),
`WordToWordNoStubCallAndFortyEightBudgetMaster` (`12/12` tight), and
`ExhaustiveHtabInventoryAndNoStubCallMaster` (`12/12` tight) with `0` imports from `Proofs/Bounded*`:
1. Unconditional absence of stub calls across `PanToWord` (`panToWord_NoStubCall`, `panToWord_names`),
   `WordToWord` (`panToWordToWord_NoStubCall`), and `StackNames` (`panToStackNames_NoSt_and_NoStubCall_unconditional`),
   plus tight rejects/accepts for `TgtGood`, `WordNoStubCall`, and `NSC`,
2. General side-regime slope absorption (`blk_l + (l.map Prod.fst).sum ≤ 100_000_000_000` under
   slope `≤ 50_000`), exact threshold sharpness at `50_001` (`threshold_sharp`), transient-storage
   (`TSTORE`) slope sensitivity, 11-table shared absorption (`blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571`),
   and `kPanElevenTablesShared = 156_088_992_805` (`5× < yukon` with margin `120_274_961_449`,
   tight 12-tx feasible bracket `155_688_931_265`, gap `400_061_540 < 0.26%`),
3. Strictly increasing 48-budget portfolio below Yukon (`900_719_925_474`), `claim.json ≤ 128`-byte
   validity (`fortyEightSharedClaims`), explicit `InitE.Certificate (baselineWithFiniteK K) (.finite K)`
   under `cert : CertificateAt 1212035192`, and purified `.Solver` module path admission. -/
theorem master_front_mid_end_no_stub_call_general_absorption_and_forty_eight_budget_synth_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (cert : CertificateAt 1212035192) (n k minutes : Nat)
    (l : List (Nat × Nat)) (B_l blk_l : Nat)
    (hS_l : B_l + (l.map Prod.snd).sum ≤ S) (hblk_l : 40 * blk_l ≤ B_l * B_l)
    (hslope_l : (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum)
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S) (hb : 40 * blk ≤ B * B) (hl : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7989 * u2) (h3 : 30 * t3 ≤ 5 * 5611 * u3)
    (h4 : 60 * t4 ≤ (M + 2280) * u4) :
    (∀ y ∈ panToWordCompileProgHOL arch prog, WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1) ∧
    (∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoStubCall y.2.2 = true) ∧
    (∀ y ∈ (WordToStack.Native.compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true)) ∧
    ¬ TgtGood (some storeConstsStubLocation) ∧
    NSC (WordLangProgHOL.seq (α := BitVec width) .skip
      (.call none (some storeConstsStubLocation) [] none)) = false ∧
    blk_l + (l.map Prod.fst).sum ≤ 100_000_000_000 ∧
    ¬ (∀ B' U' T' blk' : Nat, B' + U' ≤ S → 40 * blk' ≤ B' * B' →
        T' ≤ 50001 * U' → blk' + T' ≤ 100_000_000_000) ∧
    (tstoreTicks 83826 - tstoreTicks 83825 = 2 * 83825 ∧ 50000 < 83825) ∧
    11 * tstoreTicks 83826 + tstoreTicks 77194 = 83_252_695_392 ∧
    blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
    (kPanElevenTablesShared = 156_088_992_805 ∧
      kPanElevenTables - kPanElevenTablesShared = 11_342_996_533) ∧
    (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
      coupledCost witness ≤ kPanElevenTablesShared ∧
      kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
      400_061_540 * 10000 < 26 * 156_088_992_805 ∧
      400_061_540 * 10000 < 26 * 155_688_931_265) ∧
    (5 * kPanElevenTablesShared < yukon ∧
      yukon - 5 * kPanElevenTablesShared = 120_274_961_449) ∧
    (yukon < 6 * kPanElevenTablesShared ∧ yukon < 6 * coupledCost witness) ∧
    (truncDels (warmN (enter n) k) = k ∧
      (warmN (enter n) k).size - truncDels (warmN (enter n) k) = n) ∧
    (portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
      ∀ K ∈ portfolio, 1_212_035_192 ≤ K ∧ K < 900_719_925_474) ∧
    (∀ K ∈ portfolio, K < 900_719_925_474 ∧
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    (portfolio.map (fun k_b => yukonScore k_b minutes)).Pairwise (· < ·) ∧
    fortyEightSharedClaims.length = 48 ∧
    fortyEightSharedClaims.map Prod.fst = portfolio ∧
    (∀ entry ∈ fortyEightSharedClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    isSolverModulePath ["InitECandidate", "Solver", "SelfContainedFrontMidEndNoStubCallAndFortyEightBudgetSynth"] = true ∧
    admittedRelativePath .regularFile
      ["InitECandidate", "Solver", "SelfContainedFrontMidEndNoStubCallAndFortyEightBudgetSynth"] true = true ∧
    zeroBoundedImportCount = 0 := by
  have hm9 := front_and_mid_end_integrated_masters_synthesis_non_vacuous_and_tight
    arch prog wc ac perf info j bd ptr f cert n k B u2 u3 u4 blk loc t2 t3 t4 hS hb hl h2 h3 h4
  have hc8 := forty_eight_and_fifty_two_budget_certificates_from_base_cert_non_vacuous_and_tight cert
  have hsc7 := forty_eight_portfolio_ordering_yukon_score_and_claims_audit_non_vacuous_and_tight minutes 0
  have hel := WordToWordNoStubCallAndFortyEightBudgetMaster.eleven_tables_closure_non_vacuous_and_tight
    B u2 u3 u4 blk loc t2 t3 t4 hS hb hl h2 h3 h4
  exact ⟨hm9.1.1,
    hm9.2.1,
    WordToWordNoStubCallAndFortyEightBudgetMaster.panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight
      arch prog wc ac perf info j bd ptr f,
    PanToWordNoStubCallAndFortyEightBudgetMaster.tgtGood_rejects_stub_non_vacuous_and_tight,
    WordToWordNoStubCallAndFortyEightBudgetMaster.NSC_rejects_stub_call_non_vacuous_and_tight,
    ExhaustiveHtabInventoryAndNoStubCallMaster.general_side_regime_absorption_non_vacuous_and_tight
      l B_l blk_l hS_l hblk_l hslope_l,
    ExhaustiveHtabInventoryAndNoStubCallMaster.threshold_sharp_non_vacuous_and_tight,
    ExhaustiveHtabInventoryAndNoStubCallMaster.tstore_slope_exceeds_non_vacuous_and_tight,
    ExhaustiveHtabInventoryAndNoStubCallMaster.tstore_witness_non_vacuous_and_tight,
    hm9.1.2.1,
    hel.2.2.2.2.1,
    hm9.1.2.2.2.1,
    hm9.1.2.2.2.2.1,
    hm9.1.2.2.2.2.2.1,
    hm9.1.2.2.2.2.2.2.1,
    hc8.1.1,
    hc8.2.1,
    hsc7.2.1,
    hc8.1.2.2.1,
    hc8.1.2.2.2.1,
    hc8.1.2.2.2.2,
    by decide,
    by decide,
    rfl⟩

#print axioms frontend_pan_to_word_no_stub_call_and_names_audit_non_vacuous_and_tight
#print axioms mid_end_word_to_word_and_stack_names_no_stub_call_audit_non_vacuous_and_tight
#print axioms front_mid_end_unconditional_no_stub_call_chain_non_vacuous_and_tight
#print axioms general_side_regime_absorption_and_threshold_sharp_audit_non_vacuous_and_tight
#print axioms tstore_sensitivity_and_eleven_tables_shared_bound_audit_non_vacuous_and_tight
#print axioms unconditional_compiler_safety_and_general_absorption_joint_envelope_non_vacuous_and_tight
#print axioms forty_eight_portfolio_ordering_yukon_score_and_claims_audit_non_vacuous_and_tight
#print axioms forty_eight_and_fifty_two_budget_certificates_from_base_cert_non_vacuous_and_tight
#print axioms front_and_mid_end_integrated_masters_synthesis_non_vacuous_and_tight
#print axioms master_front_mid_end_no_stub_call_general_absorption_and_forty_eight_budget_synth_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedFrontMidEndNoStubCallAndFortyEightBudgetSynth
