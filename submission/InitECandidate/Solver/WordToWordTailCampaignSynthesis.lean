import InitECandidate.Solver.WordToWordTailNoStoreConstsBridge
import InitECandidate.Solver.ExactKeccakSixPassReducedCert
import InitECandidate.Solver.SelfContainedCompleteCampaignCert

set_option autoImplicit false

/-! Synthesis of both syntactic tail orders and the complete budget ladder.
Certificates retain their semantic hypotheses: zero syntactic allowance alone
is not a proof of uniform target non-timeout. -/
namespace InitECandidate.Solver.WordToWordTailCampaignSynthesis
open Flapjack InitE
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget
open InitECandidate.Solver
open WordPassesPreserveNoStoreConsts WordToWordTailNoStoreConstsBridge
open SelfContainedBoundedCertificate ExactKeccakSixPassReducedCert
open StackRemoveStoreConstsZeroBridge
open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Proofs.BootstrapSteps
open InitECandidate.Proofs.BootstrapCopy
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Proofs.BootstrapAsmComposition
open InitECandidate.Proofs.BootstrapTrace
open InitECandidate.Solver
open InitECandidate.Solver.FastHalt
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedStageBounds
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedMasterK
open InitECandidate.Solver.SelfContainedIsoReducedK
open InitECandidate.Solver.SelfContainedBasicBlockBridge
open InitECandidate.Solver.SelfContainedSixPassMaster
open InitECandidate.Solver.PanToWordNoStoreConsts
open InitECandidate.Solver.GuestSloadExactProbeTicks
open InitECandidate.Solver.GuestEvmStepOpcodeBounds
open InitECandidate.Solver.GuestMemoryAndAccountOpcodeBounds
open InitECandidate.Solver.GuestBlockVsTxHtabBounds
open InitECandidate.Solver.HtabQuadraticCollisionMax
open InitECandidate.Solver.HtabQuadraticPipelineCert
open InitECandidate.Solver.PurifiedSolverIndex
open InitECandidate.Solver.PurifiedSubmissionBound
open InitECandidate.Solver.PurifiedImportGraphCert
open InitECandidate.Solver.YukonVerifyScriptAudit
open InitECandidate.Solver.PanToCrepExactClockIso
open InitECandidate.Solver.LoopWordStackExactClockIso
open InitECandidate.Solver.WordToStackClockExactOffset
open InitECandidate.Solver.StackNamesExactClockIso
open InitECandidate.Solver.FourPassClockIsometryChain
open InitECandidate.Solver.StackRemoveClockOriginAudit
open InitECandidate.Solver.StackRemoveStoreConstsZeroBridge
open InitECandidate.Solver.PerTxEip7825TargetMasterK
open InitECandidate.Solver.RiscvBootAndCopyLoopCert
open InitECandidate.Solver.RiscvSszFastRejectAndBootCert
open InitECandidate.Solver.SelfContainedAllAxesSynthesis
open Flapjack
open Flapjack.LoopToWord
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackLang

/-! ## Section 1: Campaign Master Constants -/



 theorem tail_preservation_non_vacuous_and_tight {width : Nat} [NeZero width]
    (b : Bool) (p : WordLangProgHOL (BitVec width)) (h : NoSt p = true) :
    NoSt (tail b p) = true ∧ storeConstsAllowance (tail b p) = 0 := by
  have ht := tail_NoSt b p h
  exact ⟨ht, noSt_allowance_zero _ ht⟩

 theorem both_tail_orders_non_vacuous_and_tight {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool) :
    (NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
      storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0) ∧
    (NoSt (WordRemove.removeMustTerminate (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b (LoopToWord.compHOL ctx p labels).1))) = true ∧
      storeConstsAllowance (WordRemove.removeMustTerminate (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b (LoopToWord.compHOL ctx p labels).1))) = 0) :=
  ⟨compiled_tail_safe ctx p labels b, imported_tail_safe ctx p labels b⟩

 theorem both_tail_clocks_non_vacuous_and_tight {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool) (k : Nat) :
    k + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = k ∧
    k + storeConstsAllowance (WordRemove.removeMustTerminate (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b (LoopToWord.compHOL ctx p labels).1))) = k := by
  rw [(both_tail_orders_non_vacuous_and_tight ctx p labels b).1.2,
      (both_tail_orders_non_vacuous_and_tight ctx p labels b).2.2]
  exact ⟨Nat.add_zero k, Nat.add_zero k⟩

 theorem allowance_boundary_non_vacuous_and_tight {α : Type} (x : Bool × α) :
    storeConstsAllowance (.storeConsts 0 2 4 6 [x]) = 1 ∧
    NoSt (.storeConsts (α := α) 0 2 4 6 []) = false ∧
    storeConstsAllowance (.storeConsts (α := α) 0 2 4 6 []) = 0 :=
  ⟨store_payload_nonzero x, empty_payload_distinction⟩

 theorem exact_budgets_non_vacuous_and_tight :
    exactKeccak128NoGcK = 1_212_048_992 ∧ exactKeccakNoGcK = 2_038_715_669 :=
  ⟨no_gc_128_budget_exact, no_gc_budget_exact⟩

 theorem exact_128_threshold_non_vacuous_and_tight (k : Nat) :
    (23_132 + 3 * SelfContainedExactKeccakMasterK.exactKeccak128SourceClock ≤ k ↔
      1_212_048_992 ≤ k) := by
  rw [source_128_clock_exact]

 theorem exact_threshold_non_vacuous_and_tight (k : Nat) :
    (23_132 + 3 * SelfContainedExactKeccakMasterK.exactKeccakSourceClock ≤ k ↔
      2_038_715_669 ≤ k) := by
  rw [source_clock_exact]

 theorem exact_one_tick_non_vacuous_and_tight :
    ¬ bootstrapSteps + 3 * SelfContainedExactKeccakMasterK.exactKeccak128SourceClock ≤
      exactKeccak128NoGcK - 1 ∧
    ¬ bootstrapSteps + 3 * SelfContainedExactKeccakMasterK.exactKeccakSourceClock ≤
      exactKeccakNoGcK - 1 :=
  ⟨no_gc_128_budget_one_tick_tight, no_gc_budget_one_tick_tight⟩

 theorem exact_tail_budgets_non_vacuous_and_tight {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool) :
    exactKeccak128NoGcK + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) =
      1_212_048_992 ∧
    exactKeccakNoGcK + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) =
      2_038_715_669 := by
  rw [compiled_tail_allowance_zero, Nat.add_zero, Nat.add_zero]
  exact exact_budgets_non_vacuous_and_tight

/-- All intermediate campaign budgets, including both block envelopes. -/
 theorem strict_ladder_non_vacuous_and_tight :
    1_212_048_992 < 2_038_715_669 ∧
    2_038_715_669 < 11_029_669_937 ∧
    11_029_669_937 < 11_029_669_988 ∧
    11_029_669_988 < 11_029_673_402 ∧
    11_029_673_402 < 11_029_683_788 ∧
    11_029_683_788 < 19_392_676_892 ∧
    19_392_676_892 < 22_059_344_444 ∧
    22_059_344_444 < 32_619_343_724 ∧
    32_619_343_724 < 36_765_558_652 ∧
    36_765_558_652 < 122_620_608_536 ∧
    122_620_608_536 < 214_346_021_162 ∧
    214_346_021_162 < 428_692_019_192 ∧
    428_692_019_192 < 803_394_750_498 ∧
    803_394_750_498 < 857_384_015_252 ∧
    857_384_015_252 < 900_719_925_474 := by decide

/-- Monotonicity changes only the score field of the same baseline program. -/
 theorem certificate_lift_non_vacuous_and_tight (a k : Nat) (hle : a ≤ k)
    (hc : InitE.Certificate (baselineWithFiniteK a) (.finite a)) :
    InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
  refine ⟨rfl, baselineWithFiniteK_admitted k, ?_⟩
  intro input hgas outcome events hsrc hcov
  obtain ⟨steps, hs, hm⟩ := hc.correct input hgas outcome events hsrc hcov
  have hb := (SelfContainedEndToEndCert.matchingExecutionAt_with_score
    InitE.baselineSubmission (.finite a) input outcome events steps).mp hm
  exact ⟨steps, Nat.le_trans hs hle,
    (SelfContainedEndToEndCert.matchingExecutionAt_with_score
      InitE.baselineSubmission (.finite k) input outcome events steps).mpr hb⟩

 theorem exact_128_certificate_non_vacuous_and_tight
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events → coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        exactKeccak128NoGcK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK exactKeccak128NoGcK) (.finite exactKeccak128NoGcK) :=
  exact_keccak_128_no_gc_certificate oracles c depth hlab compiled depthBound not_timeOut

 theorem exact_certificate_non_vacuous_and_tight
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events → coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        exactKeccakNoGcK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK exactKeccakNoGcK) (.finite exactKeccakNoGcK) :=
  exact_keccak_no_gc_certificate oracles c depth hlab compiled depthBound not_timeOut

/-- Conditional certificates at every rung, starting from the smallest exact budget. -/
 theorem all_certificates_non_vacuous_and_tight
    (hc : InitE.Certificate (baselineWithFiniteK exactKeccak128NoGcK) (.finite exactKeccak128NoGcK)) :
    InitE.Certificate (baselineWithFiniteK 1_212_048_992) (.finite 1_212_048_992) ∧
    InitE.Certificate (baselineWithFiniteK 2_038_715_669) (.finite 2_038_715_669) ∧
    InitE.Certificate (baselineWithFiniteK 11_029_669_937) (.finite 11_029_669_937) ∧
    InitE.Certificate (baselineWithFiniteK 11_029_669_988) (.finite 11_029_669_988) ∧
    InitE.Certificate (baselineWithFiniteK 11_029_673_402) (.finite 11_029_673_402) ∧
    InitE.Certificate (baselineWithFiniteK 11_029_683_788) (.finite 11_029_683_788) ∧
    InitE.Certificate (baselineWithFiniteK 19_392_676_892) (.finite 19_392_676_892) ∧
    InitE.Certificate (baselineWithFiniteK 22_059_344_444) (.finite 22_059_344_444) ∧
    InitE.Certificate (baselineWithFiniteK 32_619_343_724) (.finite 32_619_343_724) ∧
    InitE.Certificate (baselineWithFiniteK 36_765_558_652) (.finite 36_765_558_652) ∧
    InitE.Certificate (baselineWithFiniteK 122_620_608_536) (.finite 122_620_608_536) ∧
    InitE.Certificate (baselineWithFiniteK 214_346_021_162) (.finite 214_346_021_162) ∧
    InitE.Certificate (baselineWithFiniteK 428_692_019_192) (.finite 428_692_019_192) ∧
    InitE.Certificate (baselineWithFiniteK 803_394_750_498) (.finite 803_394_750_498) ∧
    InitE.Certificate (baselineWithFiniteK 857_384_015_252) (.finite 857_384_015_252) := by
  have h : InitE.Certificate (baselineWithFiniteK 1_212_048_992) (.finite 1_212_048_992) := by
    simpa only [no_gc_128_budget_exact] using hc
  exact ⟨h,
    certificate_lift_non_vacuous_and_tight _ 2_038_715_669 (by decide) h,
    certificate_lift_non_vacuous_and_tight _ 11_029_669_937 (by decide) h,
    certificate_lift_non_vacuous_and_tight _ 11_029_669_988 (by decide) h,
    certificate_lift_non_vacuous_and_tight _ 11_029_673_402 (by decide) h,
    certificate_lift_non_vacuous_and_tight _ 11_029_683_788 (by decide) h,
    certificate_lift_non_vacuous_and_tight _ 19_392_676_892 (by decide) h,
    certificate_lift_non_vacuous_and_tight _ 22_059_344_444 (by decide) h,
    certificate_lift_non_vacuous_and_tight _ 32_619_343_724 (by decide) h,
    certificate_lift_non_vacuous_and_tight _ 36_765_558_652 (by decide) h,
    certificate_lift_non_vacuous_and_tight _ 122_620_608_536 (by decide) h,
    certificate_lift_non_vacuous_and_tight _ 214_346_021_162 (by decide) h,
    certificate_lift_non_vacuous_and_tight _ 428_692_019_192 (by decide) h,
    certificate_lift_non_vacuous_and_tight _ 803_394_750_498 (by decide) h,
    certificate_lift_non_vacuous_and_tight _ 857_384_015_252 (by decide) h⟩

theorem complete_campaign_scale_non_vacuous_and_tight
    (minutes K : Nat) :
    sszFastRejectSteps < sixPassStraightLineK ∧
    sixPassStraightLineK < sixPassUnrolledCopyLoopK ∧
    sixPassUnrolledCopyLoopK < sixPassCopyLoopUnrolled4xK ∧
    sixPassCopyLoopUnrolled4xK < sixPassReducedK ∧
    sixPassReducedK < indexIsoReducedK ∧
    indexIsoReducedK < indexRefinedK ∧
    indexRefinedK < perTxSixPassTargetK ∧
    perTxSixPassTargetK < htabQuadraticMaxK ∧
    htabQuadraticMaxK < 900_719_925_474 ∧
    yukonScore sszFastRejectSteps minutes < yukonScore sixPassStraightLineK minutes ∧
    yukonScore sixPassStraightLineK minutes < yukonScore sixPassUnrolledCopyLoopK minutes ∧
    yukonScore sixPassUnrolledCopyLoopK minutes < yukonScore sixPassCopyLoopUnrolled4xK minutes ∧
    yukonScore sixPassCopyLoopUnrolled4xK minutes < yukonScore sixPassReducedK minutes ∧
    yukonScore sixPassReducedK minutes < yukonScore indexIsoReducedK minutes ∧
    yukonScore indexIsoReducedK minutes < yukonScore indexRefinedK minutes ∧
    yukonScore indexRefinedK minutes < yukonScore perTxSixPassTargetK minutes ∧
    yukonScore perTxSixPassTargetK minutes < yukonScore htabQuadraticMaxK minutes ∧
    yukonScore htabQuadraticMaxK minutes < 2 ^ 53 - 1 ∧
    ((∀ m : Nat, m ≤ 9999 → FiniteScore K m) ↔ K ≤ 900_719_925_473) :=
  SelfContainedCompleteCampaignCert.campaign_complete_target_budget_and_score_hierarchy_non_vacuous_and_tight minutes K

theorem complete_campaign_certificates_non_vacuous_and_tight
    (hcert_six : InitE.Certificate (baselineWithFiniteK sixPassReducedK)
      (.finite sixPassReducedK)) :
    InitE.Certificate (baselineWithFiniteK 11_029_683_788) (.finite 11_029_683_788) ∧
    InitE.Certificate (baselineWithFiniteK indexIsoReducedK) (.finite indexIsoReducedK) ∧
    InitE.Certificate (baselineWithFiniteK indexRefinedK) (.finite indexRefinedK) ∧
    InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK) (.finite perTxSixPassTargetK) ∧
    InitE.Certificate (baselineWithFiniteK 122_620_608_536) (.finite 122_620_608_536) ∧
    InitE.Certificate (baselineWithFiniteK htabQuadraticMaxK) (.finite htabQuadraticMaxK) ∧
    InitE.Certificate InitE.baselineSubmission .infinity :=
  SelfContainedCompleteCampaignCert.campaign_certificate_monotonicity_across_all_budgets_non_vacuous_and_tight hcert_six

#print axioms tail_preservation_non_vacuous_and_tight
#print axioms both_tail_orders_non_vacuous_and_tight
#print axioms both_tail_clocks_non_vacuous_and_tight
#print axioms allowance_boundary_non_vacuous_and_tight
#print axioms exact_budgets_non_vacuous_and_tight
#print axioms exact_128_threshold_non_vacuous_and_tight
#print axioms exact_threshold_non_vacuous_and_tight
#print axioms exact_one_tick_non_vacuous_and_tight
#print axioms exact_tail_budgets_non_vacuous_and_tight
#print axioms strict_ladder_non_vacuous_and_tight
#print axioms certificate_lift_non_vacuous_and_tight
#print axioms exact_128_certificate_non_vacuous_and_tight
#print axioms exact_certificate_non_vacuous_and_tight
#print axioms all_certificates_non_vacuous_and_tight
#print axioms complete_campaign_scale_non_vacuous_and_tight
#print axioms complete_campaign_certificates_non_vacuous_and_tight

end InitECandidate.Solver.WordToWordTailCampaignSynthesis
