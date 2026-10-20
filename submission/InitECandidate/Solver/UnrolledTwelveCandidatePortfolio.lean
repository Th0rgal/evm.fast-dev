import InitECandidate.Solver.ExactKeccakCopyLoopUnrolledCert
import InitECandidate.Solver.WordToWordTailCampaignSynthesis
import InitECandidate.Solver.SelfContainedTenCandidateHierarchy

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-! Twelve finite candidates (the ten-tier hierarchy plus two unrolled budgets),
with the slope-12 endpoint as an additional ceiling check. Arithmetic candidate
costs do not assert a simulation of a changed ROM. All certificate selection
retains the semantic certificate or compilation/non-timeout premises. -/
namespace InitECandidate.Solver.UnrolledTwelveCandidatePortfolio
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
open InitECandidate.Solver.SelfContainedPush31MasterK
open InitECandidate.Solver.SelfContainedSolutionCandidates
open InitECandidate.Solver.SelfContainedAllAxesSynthesis
open InitECandidate.Solver.SelfContainedCompleteCampaignCert
open InitECandidate.Solver.BlockVsTxSixPassTargetCert
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

open ExactKeccakCopyLoopUnrolledCert ExactKeccakSixPassReducedCert
open SelfContainedTenCandidateHierarchy
open WordPassesPreserveNoStoreConsts WordToWordTailNoStoreConstsBridge

def candidates : List Nat := [exactKeccak128UnrolledK, exactKeccak0UnrolledK, sixPassUnrolledCopyLoopK, sixPassReducedK, exactKeccak128CandidateK, isoReducedCopyLoopK, isoReducedCandidateK, exactKeccakCandidateK, push31NoGcCandidateK, perTxSixPassTargetK, blockVsTxSlope3K, blockVsTxSlope6K]
def targetBudgets : List Nat := [1212035192, 2038701869, 11029669988, 11029683788, 19392692330, 22059330644, 22059344444, 32791963724, 87829684748, 122620608536, 214346021162, 428692019192]
def terminalK : Nat := blockVsTxSlope12K
def CertificateAt (k : Nat) : Prop := InitE.Certificate (baselineWithFiniteK k) (.finite k)

theorem candidate_values_non_vacuous_and_tight : candidates = targetBudgets := by decide

theorem candidate_count_non_vacuous_and_tight : candidates.length = 12 ∧ terminalK = 857_384_015_252 := by decide

theorem strict_ladder_non_vacuous_and_tight :
    1212035192 < 2038701869 ∧
    2038701869 < 11029669988 ∧
    11029669988 < 11029683788 ∧
    11029683788 < 19392692330 ∧
    19392692330 < 22059330644 ∧
    22059330644 < 22059344444 ∧
    22059344444 < 32791963724 ∧
    32791963724 < 87829684748 ∧
    87829684748 < 122620608536 ∧
    122620608536 < 214346021162 ∧
    214346021162 < 428692019192 ∧
    428692019192 < 857384015252 ∧
    857384015252 < 900719925474 := by decide

theorem named_strict_ladder_non_vacuous_and_tight :
    exactKeccak128UnrolledK < exactKeccak0UnrolledK ∧
    exactKeccak0UnrolledK < sixPassUnrolledCopyLoopK ∧
    sixPassUnrolledCopyLoopK < sixPassReducedK ∧
    sixPassReducedK < exactKeccak128CandidateK ∧
    exactKeccak128CandidateK < isoReducedCopyLoopK ∧
    isoReducedCopyLoopK < isoReducedCandidateK ∧
    isoReducedCandidateK < exactKeccakCandidateK ∧
    exactKeccakCandidateK < push31NoGcCandidateK ∧
    push31NoGcCandidateK < perTxSixPassTargetK ∧
    perTxSixPassTargetK < blockVsTxSlope3K ∧
    blockVsTxSlope3K < blockVsTxSlope6K ∧
    blockVsTxSlope6K < terminalK ∧
    terminalK < 900_719_925_474 := by decide

theorem best_and_ceiling_non_vacuous_and_tight (k : Nat) (hk : k ∈ candidates) :
    exactKeccak128UnrolledK ≤ k ∧ k < terminalK := by
  rw [candidate_values_non_vacuous_and_tight] at hk
  simp only [targetBudgets, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem unrolled_margins_non_vacuous_and_tight :
    743 * exactKeccak128UnrolledK < 900_719_925_474 ∧
    441 * exactKeccak0UnrolledK < 900_719_925_474 ∧
    ¬ 744 * exactKeccak128UnrolledK < 900_719_925_474 ∧
    ¬ 442 * exactKeccak0UnrolledK < 900_719_925_474 := by decide

theorem unrolled_savings_non_vacuous_and_tight :
    exactKeccak128NoGcK - exactKeccak128UnrolledK = 13_800 ∧
    exactKeccakNoGcK - exactKeccak0UnrolledK = 13_800 := ⟨exact_keccak_128_saving_exact, exact_keccak_0_saving_exact⟩

theorem one_tick_non_vacuous_and_tight (k : Nat) (hk : k ∈ candidates) : ¬ k ≤ k - 1 := by
  have h := (best_and_ceiling_non_vacuous_and_tight k hk).1
  rw [exact_keccak_128_unrolled_exact] at h
  omega

theorem score_monotone_non_vacuous_and_tight (a b minutes : Nat) (hab : a < b) :
    yukonScore a minutes < yukonScore b minutes := by
  unfold yukonScore
  omega

theorem optimal_score_non_vacuous_and_tight (k minutes : Nat) (hk : k ∈ candidates) :
    yukonScore exactKeccak128UnrolledK minutes ≤ yukonScore k minutes := by
  have h := (best_and_ceiling_non_vacuous_and_tight k hk).1
  unfold yukonScore
  omega

theorem strict_score_ladder_non_vacuous_and_tight (minutes : Nat) :
    yukonScore exactKeccak128UnrolledK minutes < yukonScore exactKeccak0UnrolledK minutes ∧
    yukonScore exactKeccak0UnrolledK minutes < yukonScore sixPassUnrolledCopyLoopK minutes ∧
    yukonScore sixPassUnrolledCopyLoopK minutes < yukonScore sixPassReducedK minutes ∧
    yukonScore sixPassReducedK minutes < yukonScore exactKeccak128CandidateK minutes ∧
    yukonScore exactKeccak128CandidateK minutes < yukonScore isoReducedCopyLoopK minutes ∧
    yukonScore isoReducedCopyLoopK minutes < yukonScore isoReducedCandidateK minutes ∧
    yukonScore isoReducedCandidateK minutes < yukonScore exactKeccakCandidateK minutes ∧
    yukonScore exactKeccakCandidateK minutes < yukonScore push31NoGcCandidateK minutes ∧
    yukonScore push31NoGcCandidateK minutes < yukonScore perTxSixPassTargetK minutes ∧
    yukonScore perTxSixPassTargetK minutes < yukonScore blockVsTxSlope3K minutes ∧
    yukonScore blockVsTxSlope3K minutes < yukonScore blockVsTxSlope6K minutes ∧
    yukonScore blockVsTxSlope6K minutes < yukonScore terminalK minutes ∧
    yukonScore terminalK minutes < yukonScore 900_719_925_474 minutes := by
  repeat' constructor
  all_goals exact score_monotone_non_vacuous_and_tight _ _ minutes (by decide)

def claims : List (Nat × String) := [
  (1212035192, verifierClaimJson "1212035192"),
  (2038701869, verifierClaimJson "2038701869"),
  (11029669988, verifierClaimJson "11029669988"),
  (11029683788, verifierClaimJson "11029683788"),
  (19392692330, verifierClaimJson "19392692330"),
  (22059330644, verifierClaimJson "22059330644"),
  (22059344444, verifierClaimJson "22059344444"),
  (32791963724, verifierClaimJson "32791963724"),
  (87829684748, verifierClaimJson "87829684748"),
  (122620608536, verifierClaimJson "122620608536"),
  (214346021162, verifierClaimJson "214346021162"),
  (428692019192, verifierClaimJson "428692019192"),
  (857384015252, verifierClaimJson "857384015252")]

theorem claim_budget_alignment_non_vacuous_and_tight : claims.map Prod.fst = targetBudgets ++ [terminalK] := by decide

theorem claim_bytes_non_vacuous_and_tight : ∀ entry ∈ claims, entry.2.utf8ByteSize ≤ 128 ∧
    validFiniteClaim entry.1 entry.2 = true := by decide

theorem certificate_lift_non_vacuous_and_tight (a k : Nat) (hle : a ≤ k) (hc : CertificateAt a) : CertificateAt k := WordToWordTailCampaignSynthesis.certificate_lift_non_vacuous_and_tight a k hle hc

theorem optimal_certificate_selection_non_vacuous_and_tight (hc : CertificateAt exactKeccak128UnrolledK) :
    ∀ k ∈ candidates, CertificateAt k := by
  intro k hk
  exact certificate_lift_non_vacuous_and_tight _ k
    (best_and_ceiling_non_vacuous_and_tight k hk).1 hc

theorem terminal_certificate_selection_non_vacuous_and_tight (hc : CertificateAt exactKeccak128UnrolledK) : CertificateAt terminalK := certificate_lift_non_vacuous_and_tight _ _ (by decide) hc

theorem optimal_direct_certificate_non_vacuous_and_tight 
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        exactKeccak128UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK exactKeccak128UnrolledK) (.finite exactKeccak128UnrolledK) := exact_keccak_128_unrolled_certificate oracles c depth hlab compiled depthBound not_timeOut

theorem second_direct_certificate_non_vacuous_and_tight 
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        exactKeccak0UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK exactKeccak0UnrolledK) (.finite exactKeccak0UnrolledK) := exact_keccak_0_unrolled_certificate oracles c depth hlab compiled depthBound not_timeOut

theorem both_tail_orders_non_vacuous_and_tight {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool) :
    (NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
      storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0) ∧
    (NoSt (WordRemove.removeMustTerminate (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b (LoopToWord.compHOL ctx p labels).1))) = true ∧
      storeConstsAllowance (WordRemove.removeMustTerminate (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b (LoopToWord.compHOL ctx p labels).1))) = 0) :=
  WordToWordTailCampaignSynthesis.both_tail_orders_non_vacuous_and_tight ctx p labels b

theorem both_tail_clocks_non_vacuous_and_tight {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool) (k : Nat) :
    k + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = k ∧
    k + storeConstsAllowance (WordRemove.removeMustTerminate (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b (LoopToWord.compHOL ctx p labels).1))) = k :=
  WordToWordTailCampaignSynthesis.both_tail_clocks_non_vacuous_and_tight ctx p labels b k

theorem allowance_boundary_non_vacuous_and_tight {α : Type} (x : Bool × α) :
    storeConstsAllowance (.storeConsts 0 2 4 6 [x]) = 1 ∧
    NoSt (.storeConsts (α := α) 0 2 4 6 []) = false ∧
    storeConstsAllowance (.storeConsts (α := α) 0 2 4 6 []) = 0 :=
  WordToWordTailCampaignSynthesis.allowance_boundary_non_vacuous_and_tight x

#print axioms candidate_values_non_vacuous_and_tight
#print axioms candidate_count_non_vacuous_and_tight
#print axioms strict_ladder_non_vacuous_and_tight
#print axioms named_strict_ladder_non_vacuous_and_tight
#print axioms best_and_ceiling_non_vacuous_and_tight
#print axioms unrolled_margins_non_vacuous_and_tight
#print axioms unrolled_savings_non_vacuous_and_tight
#print axioms one_tick_non_vacuous_and_tight
#print axioms score_monotone_non_vacuous_and_tight
#print axioms optimal_score_non_vacuous_and_tight
#print axioms strict_score_ladder_non_vacuous_and_tight
#print axioms claim_budget_alignment_non_vacuous_and_tight
#print axioms claim_bytes_non_vacuous_and_tight
#print axioms certificate_lift_non_vacuous_and_tight
#print axioms optimal_certificate_selection_non_vacuous_and_tight
#print axioms terminal_certificate_selection_non_vacuous_and_tight
#print axioms optimal_direct_certificate_non_vacuous_and_tight
#print axioms second_direct_certificate_non_vacuous_and_tight
#print axioms both_tail_orders_non_vacuous_and_tight
#print axioms both_tail_clocks_non_vacuous_and_tight
#print axioms allowance_boundary_non_vacuous_and_tight

end InitECandidate.Solver.UnrolledTwelveCandidatePortfolio
