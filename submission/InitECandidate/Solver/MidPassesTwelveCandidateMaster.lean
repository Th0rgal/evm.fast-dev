import InitECandidate.Solver.WordMidPassesPreserveNoStoreConsts
import InitECandidate.Solver.UnrolledTwelveCandidatePortfolio
import InitECandidate.Solver.JointBlockGasSixPassMasterCert

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-! Six Word passes preserve the structural no-store invariant. The 15-tier
portfolio is arithmetic; certificate transport retains the semantic certificate
premise. Trace allowance requires explicit provenance and is not inferred from
syntax alone. No claim is made about the still-open earlier Word passes. -/
namespace InitECandidate.Solver.MidPassesTwelveCandidateMaster
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

open StackRemoveStoreConstsZeroBridge StackRemoveClockOriginAudit
open JointBlockGasSixPassMasterCert WordMidPassesPreserveNoStoreConsts

noncomputable def mid_tail {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (temp : Nat) (b : Bool) (p : WordLangProgHOL (BitVec width)) :=
  WordRemove.removeMustTerminate (WordUnreach.removeUnreach
    (WordInst.threeToTwoRegProg b (WordCopy.copyProp (WordAlloc.removeDeadProg
      (WordInst.instSelect c temp p)))))

def unifiedCandidates : List Nat := [exactKeccak128UnrolledK, exactKeccak0UnrolledK, sixPassUnrolledCopyLoopK, sixPassReducedK, exactKeccak128CandidateK, isoReducedCopyLoopK, isoReducedCandidateK, exactKeccakCandidateK, push31NoGcCandidateK, jointBlockGasSlope3K, perTxSixPassTargetK, blockVsTxSlope3K, jointBlockGasSlope6K, blockVsTxSlope6K, jointBlockGasSlope12K]
def unifiedBudgets : List Nat := [1212035192, 2038701869, 11029669988, 11029683788, 19392692330, 22059330644, 22059344444, 32791963724, 87829684748, 121459456007, 122620608536, 214346021162, 242918888882, 428692019192, 485837754632]

 theorem unified_values_non_vacuous_and_tight : unifiedCandidates = unifiedBudgets := by decide
 theorem unified_count_non_vacuous_and_tight : unifiedCandidates.length = 15 := by decide
 theorem unified_members_non_vacuous_and_tight (k : Nat) :
    k ∈ unifiedCandidates ↔ k ∈ UnrolledTwelveCandidatePortfolio.candidates ∨
      k = jointBlockGasSlope3K ∨ k = jointBlockGasSlope6K ∨ k = jointBlockGasSlope12K := by
  simp only [unifiedCandidates, UnrolledTwelveCandidatePortfolio.candidates,
    List.mem_cons, List.not_mem_nil, or_false]
  tauto
 theorem unified_strict_ladder_non_vacuous_and_tight :
    exactKeccak128UnrolledK < exactKeccak0UnrolledK ∧
    exactKeccak0UnrolledK < sixPassUnrolledCopyLoopK ∧
    sixPassUnrolledCopyLoopK < sixPassReducedK ∧
    sixPassReducedK < exactKeccak128CandidateK ∧
    exactKeccak128CandidateK < isoReducedCopyLoopK ∧
    isoReducedCopyLoopK < isoReducedCandidateK ∧
    isoReducedCandidateK < exactKeccakCandidateK ∧
    exactKeccakCandidateK < push31NoGcCandidateK ∧
    push31NoGcCandidateK < jointBlockGasSlope3K ∧
    jointBlockGasSlope3K < perTxSixPassTargetK ∧
    perTxSixPassTargetK < blockVsTxSlope3K ∧
    blockVsTxSlope3K < jointBlockGasSlope6K ∧
    jointBlockGasSlope6K < blockVsTxSlope6K ∧
    blockVsTxSlope6K < jointBlockGasSlope12K := by decide
 theorem unified_pairwise_non_vacuous_and_tight : unifiedCandidates.Pairwise (· < ·) := by decide
 theorem unified_bounds_non_vacuous_and_tight (k : Nat) (hk : k ∈ unifiedCandidates) :
    exactKeccak128UnrolledK ≤ k ∧ k ≤ jointBlockGasSlope12K := by
  rw [unified_values_non_vacuous_and_tight] at hk
  simp only [unifiedBudgets, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
 theorem unified_one_tick_non_vacuous_and_tight (k : Nat) (hk : k ∈ unifiedCandidates) :
    ¬ k ≤ k - 1 := by
  have h := (unified_bounds_non_vacuous_and_tight k hk).1
  have he : exactKeccak128UnrolledK = 1212035192 := by decide
  rw [he] at h
  omega

section Mid
variable {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat)
  (b : Bool) (p : WordLangProgHOL (BitVec width)) (h : NoSt p = true)
include h

 theorem mid_preservation_non_vacuous_and_tight : NoSt (mid_tail c temp b p) = true :=
  t_mid_tail_chain c temp b p h
 theorem mid_zero_allowance_non_vacuous_and_tight :
    storeConstsAllowance (mid_tail c temp b p) = 0 :=
  noSt_allowance_zero _ (mid_preservation_non_vacuous_and_tight c temp b p h)
 theorem mid_clock_non_vacuous_and_tight (clock : Nat) :
    clock + storeConstsAllowance (mid_tail c temp b p) = clock := by
  rw [mid_zero_allowance_non_vacuous_and_tight c temp b p h, Nat.add_zero]

/-- The structural allowance model with the one entry tick, not a target
simulation theorem. Actual run allowances additionally need trace provenance. -/
 theorem mid_stackRemove_entry_budget_non_vacuous_and_tight (clock : Nat) :
    clock + storeConstsAllowance (mid_tail c temp b p) + 1 = clock + 1 ∧
    clock + storeConstsAllowance (mid_tail c temp b p) + 1 ≤ clock + 1 := by
  rw [mid_zero_allowance_non_vacuous_and_tight c temp b p h]
  omega

/-- Explicit per-event provenance is retained across the syntax/trace boundary. -/
 theorem mid_trace_zero_non_vacuous_and_tight (xs : List (Bool × Nat))
    (origin : ∀ e ∈ xs, e.1 = true → NoSt (mid_tail c temp b p) = false) :
    runAllowance xs = 0 := by
  apply runAllowance_zero_of_no_storeConsts
  intro e he
  have hn := mid_preservation_non_vacuous_and_tight c temp b p h
  cases hb : e.1 with
  | false => rfl
  | true => have hf := origin e he hb; simp_all

 theorem mid_trace_entry_tick_non_vacuous_and_tight (xs : List (Bool × Nat))
    (origin : ∀ e ∈ xs, e.1 = true → NoSt (mid_tail c temp b p) = false)
    (clock : Nat) : clock + runAllowance xs + 1 = clock + 1 := by
  rw [mid_trace_zero_non_vacuous_and_tight c temp b p h xs origin, Nat.add_zero]

 theorem unified_mid_certificates_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt exactKeccak128UnrolledK) :
    NoSt (mid_tail c temp b p) = true ∧
    storeConstsAllowance (mid_tail c temp b p) = 0 ∧
    ∀ k ∈ unifiedCandidates, InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
  refine ⟨mid_preservation_non_vacuous_and_tight c temp b p h,
    mid_zero_allowance_non_vacuous_and_tight c temp b p h, ?_⟩
  intro k hk
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight _ k
    (unified_bounds_non_vacuous_and_tight k hk).1 hc

 theorem tier01_mid_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt exactKeccak128UnrolledK) :
    NoSt (mid_tail c temp b p) = true ∧
    storeConstsAllowance (mid_tail c temp b p) = 0 ∧
    InitE.Certificate (baselineWithFiniteK exactKeccak128UnrolledK) (.finite exactKeccak128UnrolledK) ∧
    exactKeccak128UnrolledK = 1212035192 ∧ ¬ exactKeccak128UnrolledK ≤ exactKeccak128UnrolledK - 1 := by
  have hm : exactKeccak128UnrolledK ∈ unifiedCandidates := by decide
  have hmst := unified_mid_certificates_non_vacuous_and_tight c temp b p h hc
  exact ⟨hmst.1, hmst.2.1, hmst.2.2 _ hm, by decide,
    unified_one_tick_non_vacuous_and_tight _ hm⟩

 theorem tier02_mid_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt exactKeccak128UnrolledK) :
    NoSt (mid_tail c temp b p) = true ∧
    storeConstsAllowance (mid_tail c temp b p) = 0 ∧
    InitE.Certificate (baselineWithFiniteK exactKeccak0UnrolledK) (.finite exactKeccak0UnrolledK) ∧
    exactKeccak0UnrolledK = 2038701869 ∧ ¬ exactKeccak0UnrolledK ≤ exactKeccak0UnrolledK - 1 := by
  have hm : exactKeccak0UnrolledK ∈ unifiedCandidates := by decide
  have hmst := unified_mid_certificates_non_vacuous_and_tight c temp b p h hc
  exact ⟨hmst.1, hmst.2.1, hmst.2.2 _ hm, by decide,
    unified_one_tick_non_vacuous_and_tight _ hm⟩

 theorem tier03_mid_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt exactKeccak128UnrolledK) :
    NoSt (mid_tail c temp b p) = true ∧
    storeConstsAllowance (mid_tail c temp b p) = 0 ∧
    InitE.Certificate (baselineWithFiniteK sixPassUnrolledCopyLoopK) (.finite sixPassUnrolledCopyLoopK) ∧
    sixPassUnrolledCopyLoopK = 11029669988 ∧ ¬ sixPassUnrolledCopyLoopK ≤ sixPassUnrolledCopyLoopK - 1 := by
  have hm : sixPassUnrolledCopyLoopK ∈ unifiedCandidates := by decide
  have hmst := unified_mid_certificates_non_vacuous_and_tight c temp b p h hc
  exact ⟨hmst.1, hmst.2.1, hmst.2.2 _ hm, by decide,
    unified_one_tick_non_vacuous_and_tight _ hm⟩

 theorem tier04_mid_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt exactKeccak128UnrolledK) :
    NoSt (mid_tail c temp b p) = true ∧
    storeConstsAllowance (mid_tail c temp b p) = 0 ∧
    InitE.Certificate (baselineWithFiniteK sixPassReducedK) (.finite sixPassReducedK) ∧
    sixPassReducedK = 11029683788 ∧ ¬ sixPassReducedK ≤ sixPassReducedK - 1 := by
  have hm : sixPassReducedK ∈ unifiedCandidates := by decide
  have hmst := unified_mid_certificates_non_vacuous_and_tight c temp b p h hc
  exact ⟨hmst.1, hmst.2.1, hmst.2.2 _ hm, by decide,
    unified_one_tick_non_vacuous_and_tight _ hm⟩

 theorem tier05_mid_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt exactKeccak128UnrolledK) :
    NoSt (mid_tail c temp b p) = true ∧
    storeConstsAllowance (mid_tail c temp b p) = 0 ∧
    InitE.Certificate (baselineWithFiniteK exactKeccak128CandidateK) (.finite exactKeccak128CandidateK) ∧
    exactKeccak128CandidateK = 19392692330 ∧ ¬ exactKeccak128CandidateK ≤ exactKeccak128CandidateK - 1 := by
  have hm : exactKeccak128CandidateK ∈ unifiedCandidates := by decide
  have hmst := unified_mid_certificates_non_vacuous_and_tight c temp b p h hc
  exact ⟨hmst.1, hmst.2.1, hmst.2.2 _ hm, by decide,
    unified_one_tick_non_vacuous_and_tight _ hm⟩

 theorem tier06_mid_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt exactKeccak128UnrolledK) :
    NoSt (mid_tail c temp b p) = true ∧
    storeConstsAllowance (mid_tail c temp b p) = 0 ∧
    InitE.Certificate (baselineWithFiniteK isoReducedCopyLoopK) (.finite isoReducedCopyLoopK) ∧
    isoReducedCopyLoopK = 22059330644 ∧ ¬ isoReducedCopyLoopK ≤ isoReducedCopyLoopK - 1 := by
  have hm : isoReducedCopyLoopK ∈ unifiedCandidates := by decide
  have hmst := unified_mid_certificates_non_vacuous_and_tight c temp b p h hc
  exact ⟨hmst.1, hmst.2.1, hmst.2.2 _ hm, by decide,
    unified_one_tick_non_vacuous_and_tight _ hm⟩

 theorem tier07_mid_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt exactKeccak128UnrolledK) :
    NoSt (mid_tail c temp b p) = true ∧
    storeConstsAllowance (mid_tail c temp b p) = 0 ∧
    InitE.Certificate (baselineWithFiniteK isoReducedCandidateK) (.finite isoReducedCandidateK) ∧
    isoReducedCandidateK = 22059344444 ∧ ¬ isoReducedCandidateK ≤ isoReducedCandidateK - 1 := by
  have hm : isoReducedCandidateK ∈ unifiedCandidates := by decide
  have hmst := unified_mid_certificates_non_vacuous_and_tight c temp b p h hc
  exact ⟨hmst.1, hmst.2.1, hmst.2.2 _ hm, by decide,
    unified_one_tick_non_vacuous_and_tight _ hm⟩

 theorem tier08_mid_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt exactKeccak128UnrolledK) :
    NoSt (mid_tail c temp b p) = true ∧
    storeConstsAllowance (mid_tail c temp b p) = 0 ∧
    InitE.Certificate (baselineWithFiniteK exactKeccakCandidateK) (.finite exactKeccakCandidateK) ∧
    exactKeccakCandidateK = 32791963724 ∧ ¬ exactKeccakCandidateK ≤ exactKeccakCandidateK - 1 := by
  have hm : exactKeccakCandidateK ∈ unifiedCandidates := by decide
  have hmst := unified_mid_certificates_non_vacuous_and_tight c temp b p h hc
  exact ⟨hmst.1, hmst.2.1, hmst.2.2 _ hm, by decide,
    unified_one_tick_non_vacuous_and_tight _ hm⟩

 theorem tier09_mid_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt exactKeccak128UnrolledK) :
    NoSt (mid_tail c temp b p) = true ∧
    storeConstsAllowance (mid_tail c temp b p) = 0 ∧
    InitE.Certificate (baselineWithFiniteK push31NoGcCandidateK) (.finite push31NoGcCandidateK) ∧
    push31NoGcCandidateK = 87829684748 ∧ ¬ push31NoGcCandidateK ≤ push31NoGcCandidateK - 1 := by
  have hm : push31NoGcCandidateK ∈ unifiedCandidates := by decide
  have hmst := unified_mid_certificates_non_vacuous_and_tight c temp b p h hc
  exact ⟨hmst.1, hmst.2.1, hmst.2.2 _ hm, by decide,
    unified_one_tick_non_vacuous_and_tight _ hm⟩

 theorem tier10_mid_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt exactKeccak128UnrolledK) :
    NoSt (mid_tail c temp b p) = true ∧
    storeConstsAllowance (mid_tail c temp b p) = 0 ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope3K) (.finite jointBlockGasSlope3K) ∧
    jointBlockGasSlope3K = 121459456007 ∧ ¬ jointBlockGasSlope3K ≤ jointBlockGasSlope3K - 1 := by
  have hm : jointBlockGasSlope3K ∈ unifiedCandidates := by decide
  have hmst := unified_mid_certificates_non_vacuous_and_tight c temp b p h hc
  exact ⟨hmst.1, hmst.2.1, hmst.2.2 _ hm, by decide,
    unified_one_tick_non_vacuous_and_tight _ hm⟩

 theorem tier11_mid_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt exactKeccak128UnrolledK) :
    NoSt (mid_tail c temp b p) = true ∧
    storeConstsAllowance (mid_tail c temp b p) = 0 ∧
    InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK) (.finite perTxSixPassTargetK) ∧
    perTxSixPassTargetK = 122620608536 ∧ ¬ perTxSixPassTargetK ≤ perTxSixPassTargetK - 1 := by
  have hm : perTxSixPassTargetK ∈ unifiedCandidates := by decide
  have hmst := unified_mid_certificates_non_vacuous_and_tight c temp b p h hc
  exact ⟨hmst.1, hmst.2.1, hmst.2.2 _ hm, by decide,
    unified_one_tick_non_vacuous_and_tight _ hm⟩

 theorem tier12_mid_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt exactKeccak128UnrolledK) :
    NoSt (mid_tail c temp b p) = true ∧
    storeConstsAllowance (mid_tail c temp b p) = 0 ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope3K) (.finite blockVsTxSlope3K) ∧
    blockVsTxSlope3K = 214346021162 ∧ ¬ blockVsTxSlope3K ≤ blockVsTxSlope3K - 1 := by
  have hm : blockVsTxSlope3K ∈ unifiedCandidates := by decide
  have hmst := unified_mid_certificates_non_vacuous_and_tight c temp b p h hc
  exact ⟨hmst.1, hmst.2.1, hmst.2.2 _ hm, by decide,
    unified_one_tick_non_vacuous_and_tight _ hm⟩

 theorem tier13_mid_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt exactKeccak128UnrolledK) :
    NoSt (mid_tail c temp b p) = true ∧
    storeConstsAllowance (mid_tail c temp b p) = 0 ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope6K) (.finite jointBlockGasSlope6K) ∧
    jointBlockGasSlope6K = 242918888882 ∧ ¬ jointBlockGasSlope6K ≤ jointBlockGasSlope6K - 1 := by
  have hm : jointBlockGasSlope6K ∈ unifiedCandidates := by decide
  have hmst := unified_mid_certificates_non_vacuous_and_tight c temp b p h hc
  exact ⟨hmst.1, hmst.2.1, hmst.2.2 _ hm, by decide,
    unified_one_tick_non_vacuous_and_tight _ hm⟩

 theorem tier14_mid_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt exactKeccak128UnrolledK) :
    NoSt (mid_tail c temp b p) = true ∧
    storeConstsAllowance (mid_tail c temp b p) = 0 ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope6K) (.finite blockVsTxSlope6K) ∧
    blockVsTxSlope6K = 428692019192 ∧ ¬ blockVsTxSlope6K ≤ blockVsTxSlope6K - 1 := by
  have hm : blockVsTxSlope6K ∈ unifiedCandidates := by decide
  have hmst := unified_mid_certificates_non_vacuous_and_tight c temp b p h hc
  exact ⟨hmst.1, hmst.2.1, hmst.2.2 _ hm, by decide,
    unified_one_tick_non_vacuous_and_tight _ hm⟩

 theorem tier15_mid_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt exactKeccak128UnrolledK) :
    NoSt (mid_tail c temp b p) = true ∧
    storeConstsAllowance (mid_tail c temp b p) = 0 ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope12K) (.finite jointBlockGasSlope12K) ∧
    jointBlockGasSlope12K = 485837754632 ∧ ¬ jointBlockGasSlope12K ≤ jointBlockGasSlope12K - 1 := by
  have hm : jointBlockGasSlope12K ∈ unifiedCandidates := by decide
  have hmst := unified_mid_certificates_non_vacuous_and_tight c temp b p h hc
  exact ⟨hmst.1, hmst.2.1, hmst.2.2 _ hm, by decide,
    unified_one_tick_non_vacuous_and_tight _ hm⟩

end Mid
theorem direct_master_non_vacuous_and_tight 
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
    ∀ k ∈ unifiedCandidates, InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
  have hc := UnrolledTwelveCandidatePortfolio.optimal_direct_certificate_non_vacuous_and_tight
    oracles c depth hlab compiled depthBound not_timeOut
  intro k hk
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight _ k
    (unified_bounds_non_vacuous_and_tight k hk).1 hc

#print axioms unified_values_non_vacuous_and_tight
#print axioms unified_count_non_vacuous_and_tight
#print axioms unified_members_non_vacuous_and_tight
#print axioms unified_strict_ladder_non_vacuous_and_tight
#print axioms unified_pairwise_non_vacuous_and_tight
#print axioms unified_bounds_non_vacuous_and_tight
#print axioms unified_one_tick_non_vacuous_and_tight
#print axioms mid_preservation_non_vacuous_and_tight
#print axioms mid_zero_allowance_non_vacuous_and_tight
#print axioms mid_clock_non_vacuous_and_tight
#print axioms mid_stackRemove_entry_budget_non_vacuous_and_tight
#print axioms mid_trace_zero_non_vacuous_and_tight
#print axioms mid_trace_entry_tick_non_vacuous_and_tight
#print axioms unified_mid_certificates_non_vacuous_and_tight
#print axioms tier01_mid_certificate_non_vacuous_and_tight
#print axioms tier02_mid_certificate_non_vacuous_and_tight
#print axioms tier03_mid_certificate_non_vacuous_and_tight
#print axioms tier04_mid_certificate_non_vacuous_and_tight
#print axioms tier05_mid_certificate_non_vacuous_and_tight
#print axioms tier06_mid_certificate_non_vacuous_and_tight
#print axioms tier07_mid_certificate_non_vacuous_and_tight
#print axioms tier08_mid_certificate_non_vacuous_and_tight
#print axioms tier09_mid_certificate_non_vacuous_and_tight
#print axioms tier10_mid_certificate_non_vacuous_and_tight
#print axioms tier11_mid_certificate_non_vacuous_and_tight
#print axioms tier12_mid_certificate_non_vacuous_and_tight
#print axioms tier13_mid_certificate_non_vacuous_and_tight
#print axioms tier14_mid_certificate_non_vacuous_and_tight
#print axioms tier15_mid_certificate_non_vacuous_and_tight
#print axioms direct_master_non_vacuous_and_tight

end InitECandidate.Solver.MidPassesTwelveCandidateMaster
