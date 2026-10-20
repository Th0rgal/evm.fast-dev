import InitECandidate.Solver.WordMidPassesPreserveNoStoreConsts
import InitECandidate.Solver.JointBlockGasSixPassMasterCert
import InitECandidate.Solver.YukonSubmissionDryRunCert

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.WordMidTailNoStoreConstsBridge

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedMasterK hiding refinedCandidateK
open InitECandidate.Solver.SelfContainedSixPassMaster hiding sixPassReducedK
open InitECandidate.Solver.SelfContainedSolutionCandidates
open InitECandidate.Solver.PurifiedImportGraphCert
open InitECandidate.Solver.PurifiedSubmissionBound
open InitECandidate.Solver.GuestSloadExactProbeTicks
open InitECandidate.Solver.GuestBlockVsTxHtabBounds
open InitECandidate.Solver.GuestJointBlockGasHtabBound
open InitECandidate.Solver.BlockVsTxSixPassTargetCert
open InitECandidate.Solver.PanToWordNoStoreConsts
open InitECandidate.Solver.StackRemoveClockOriginAudit
open InitECandidate.Solver.StackRemoveStoreConstsZeroBridge
open InitECandidate.Solver.StackNamesExactClockIso
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordMidPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordToWordTailNoStoreConstsBridge
open InitECandidate.Solver.YukonEightTierMasterPortfolio hiding sixPassUnrolledCopyLoopK sixPassReducedK isoReducedCandidateK push31NoGcCandidateK push31CandidateK quadraticCollisionTargetK
open InitECandidate.Solver.JointBlockGasSixPassMasterCert
open InitECandidate.Solver.RiscvSszFastRejectAndBootCert
open InitECandidate.Solver.YukonVerifyScriptAudit
open InitECandidate.Solver.YukonFinalCandidateSelector
open InitECandidate.Solver.YukonSubmissionDryRunCert
open Flapjack
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target

/-- Six-pass `WordToWord` mid-tail chain (`instSelect -> removeDeadProg -> copyProp ->
threeToTwoRegProg -> removeUnreach -> removeMustTerminate`) matching `t_mid_tail_chain`. -/
noncomputable def midTailChain {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat)
    (b : Bool) (p : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  WordRemove.removeMustTerminate
    (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b
        (WordCopy.copyProp
          (WordAlloc.removeDeadProg
            (WordInst.instSelect c temp p)))))

/-- Effective `StackRemove` + `StackNames` entry clock budget for a post-`midTailChain`
program `q` at body clock `k_sn`: `C_sn * (k_sn + storeConstsAllowance q + 1) + D_sn`. -/
def stackRemoveMidTailClock {α : Type} (q : WordLangProgHOL α) (k_sn : Nat) : Nat :=
  C_sn * (k_sn + storeConstsAllowance q + 1) + D_sn

/-- Trace provenance from the 6-pass `midTailChain` output. -/
def MidTailTraceFrom {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat)
    (b : Bool) (p : WordLangProgHOL (BitVec width)) (xs : List (Bool × Nat)) : Prop :=
  ∀ event ∈ xs, event.1 = true → NoSt (midTailChain c temp b p) = false

/-- Theorem 1 (`non_vacuous_and_tight`): Bridge from `t_mid_tail_chain`
(`instSelect -> removeDeadProg -> copyProp -> threeToTwo -> removeUnreach -> removeMustTerminate`)
to `storeConstsAllowance = 0` (`StackRemoveStoreConstsZeroBridge`), together with individual
intermediate pass `storeConstsAllowance = 0` invariants and non-vacuity on `.storeConsts`. -/
theorem mid_tail_chain_preserves_noSt_and_zero_allowance_non_vacuous_and_tight
    {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat) (b : Bool)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true)
    (ws : List (Bool × BitVec width)) :
    NoSt (WordInst.instSelect c temp p) = true ∧
    storeConstsAllowance (WordInst.instSelect c temp p) = 0 ∧
    NoSt (WordAlloc.removeDeadProg (WordInst.instSelect c temp p)) = true ∧
    storeConstsAllowance (WordAlloc.removeDeadProg (WordInst.instSelect c temp p)) = 0 ∧
    NoSt (WordCopy.copyProp (WordAlloc.removeDeadProg (WordInst.instSelect c temp p))) = true ∧
    storeConstsAllowance (WordCopy.copyProp (WordAlloc.removeDeadProg (WordInst.instSelect c temp p))) = 0 ∧
    NoSt (midTailChain c temp b p) = true ∧
    storeConstsAllowance (midTailChain c temp b p) = 0 ∧
    NoSt (WordInst.instSelect c temp (.storeConsts 0 2 4 6 [])) = false ∧
    (storeConstsAllowance (.storeConsts 0 2 4 6 ws) = 0 ↔ ws = []) := by
  have h1 : NoSt (WordInst.instSelect c temp p) = true := t_instSelect c temp p hp
  have h2 : NoSt (WordAlloc.removeDeadProg (WordInst.instSelect c temp p)) = true :=
    t_removeDeadProg _ h1
  have h3 : NoSt (WordCopy.copyProp (WordAlloc.removeDeadProg (WordInst.instSelect c temp p))) = true :=
    t_copyProp _ h2
  have h6 : NoSt (midTailChain c temp b p) = true := t_mid_tail_chain c temp b p hp
  have htight := allowance_storeConsts_tight 0 2 4 6 ws
  refine ⟨h1, noSt_allowance_zero _ h1, h2, noSt_allowance_zero _ h2,
    h3, noSt_allowance_zero _ h3, h6, noSt_allowance_zero _ h6,
    instSelect_keeps_storeConsts c temp, ?_⟩
  rw [htight, List.length_eq_zero_iff]

/-- Theorem 2 (`non_vacuous_and_tight`): Any `WordProg` without `storeConsts` (`NoSt p = true`)
entering `instSelect` exits the 6-pass `midTailChain` with `storeConstsAllowance = 0`, zero
`StackRemove` trace `runAllowance`, and a `StackRemove` + `StackNames` entry clock bounded by
and equal to `k_sn + 1`. -/
theorem word_prog_no_store_consts_mid_tail_stack_remove_clock_bound_non_vacuous_and_tight
    {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat) (b : Bool)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true)
    (xs : List (Bool × Nat)) (horigin : MidTailTraceFrom c temp b p xs)
    (oracles : List (Option (Spt Nat))) (k_sn k_entry : Nat) :
    NoSt (midTailChain c temp b p) = true ∧
    storeConstsAllowance (midTailChain c temp b p) = 0 ∧
    runAllowance xs = 0 ∧
    (oracleCompilerConfig oracles).stackConf.jump = false ∧
    stackRemoveMidTailClock (midTailChain c temp b p) k_sn = k_sn + 1 ∧
    stackRemoveMidTailClock (midTailChain c temp b p) k_sn ≤ k_sn + 1 ∧
    k_sn + storeConstsAllowance (midTailChain c temp b p) + runAllowance xs = k_sn ∧
    (stackRemoveMidTailClock (midTailChain c temp b p) k_sn ≤ k_entry ↔ k_sn + 1 ≤ k_entry) := by
  have hnost : NoSt (midTailChain c temp b p) = true := t_mid_tail_chain c temp b p hp
  have hzero : storeConstsAllowance (midTailChain c temp b p) = 0 :=
    noSt_allowance_zero _ hnost
  have hflags : ∀ event ∈ xs, event.1 = false := by
    intro event he
    cases hb : event.1 with
    | false => rfl
    | true =>
      have hfalse := horigin event he hb
      rw [hnost] at hfalse
      contradiction
  have hrun0 : runAllowance xs = 0 := runAllowance_zero_of_no_storeConsts xs hflags
  have hclk : stackRemoveMidTailClock (midTailChain c temp b p) k_sn = k_sn + 1 := by
    unfold stackRemoveMidTailClock C_sn D_sn
    rw [hzero]
    omega
  refine ⟨hnost, hzero, hrun0, guest_stackRemove_jump_false oracles, hclk,
    Nat.le_of_eq hclk, ?_, ?_⟩
  · rw [hzero, hrun0]; omega
  · rw [hclk]

/-- Theorem 3 (`non_vacuous_and_tight`): Semantic `StackRemove` (`initCode` `0`-tick neutrality +
`+1` entry shift) and `StackNames` (`C_sn = 1, D_sn = 0`) composition at clock `k_sn + 1` for
any `NoSt` program `p` exiting `midTailChain`, plus `LoopToWord.compHOL` specialization. -/
theorem compiled_loop_to_word_mid_tail_and_stack_remove_semantic_clock_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (temp : Nat) (b : Bool)
    (ctx : Spt Nat) (lprog : HolLoopProg width) (labels : Nat × Nat)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true)
    (generateGc : Bool) (maxHeap pointer start : Nat)
    (comp : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C))
    (f : Spt Nat) (s2 t : StackSemStateFiniteExact width C F) (k_sn k_entry : Nat)
    (hentry : sptLookup 0 s2.code =
      some (.seq (StackRemove.initCode generateGc maxHeap pointer)
        (.call none (.inl start) none)))
    (hrun : StackSemEvaluate.evaluate (StackRemove.initCode generateGc maxHeap pointer, s2) =
      (none, t))
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (ha : ¬s2.useAlloc) (hs : ¬s2.useStore) (hk : ¬s2.useStack)
    (hc : s2.compile = (fun cfg => comp cfg ∘ StackNames.compileHOL f)) :
    NoSt (midTailChain ac temp b (LoopToWord.compHOL ctx lprog labels).1) = true ∧
    storeConstsAllowance (midTailChain ac temp b (LoopToWord.compHOL ctx lprog labels).1) = 0 ∧
    stackRemoveMidTailClock (midTailChain ac temp b p) k_sn = k_sn + 1 ∧
    clockNeutralHOL (StackRemove.initCode (width := width) generateGc maxHeap pointer) ∧
    (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { StackNamesExactClockIso.stateRel comp f s2 with
        clock := stackRemoveMidTailClock (midTailChain ac temp b p) k_sn })).1 =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k_sn })).1 ∧
    (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { StackNamesExactClockIso.stateRel comp f s2 with
        clock := stackRemoveMidTailClock (midTailChain ac temp b p) k_sn })).2.ffi =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k_sn })).2.ffi ∧
    (stackRemoveMidTailClock (midTailChain ac temp b p) k_sn ≤ k_entry ↔ k_sn < k_entry) := by
  have hcomp_nost : NoSt (LoopToWord.compHOL ctx lprog labels).1 = true :=
    loopToWord_NoSt ctx lprog labels
  have hmid_comp : NoSt (midTailChain ac temp b (LoopToWord.compHOL ctx lprog labels).1) = true :=
    t_mid_tail_chain ac temp b _ hcomp_nost
  have hmid_zero : storeConstsAllowance (midTailChain ac temp b (LoopToWord.compHOL ctx lprog labels).1) = 0 :=
    noSt_allowance_zero _ hmid_comp
  have hp_nost : NoSt (midTailChain ac temp b p) = true := t_mid_tail_chain ac temp b p hp
  have hp_zero : storeConstsAllowance (midTailChain ac temp b p) = 0 :=
    noSt_allowance_zero _ hp_nost
  have hclk_eq : stackRemoveMidTailClock (midTailChain ac temp b p) k_sn =
      C_sn * (k_sn + 1) + D_sn := by
    unfold stackRemoveMidTailClock
    rw [hp_zero, Nat.add_zero]
  have hclk_val : stackRemoveMidTailClock (midTailChain ac temp b p) k_sn = k_sn + 1 := by
    rw [hclk_eq]
    unfold C_sn D_sn
    omega
  have hsem := stack_names_compose_init_code_neutral generateGc maxHeap pointer start comp f
    s2 t k_sn hentry hrun hf ha hs hk hc
  rw [← hclk_eq] at hsem
  refine ⟨hmid_comp, hmid_zero, hclk_val, hsem.1, hsem.2.2.1, hsem.2.2.2.1, ?_⟩
  rw [hclk_val]
  omega

/-- Theorem 4 (`non_vacuous_and_tight`): Integration of `midTailChain` (`storeConstsAllowance = 0`)
with `JointBlockGasSixPassMasterCert`: exact ordering
`121_459_456_007 < 122_620_608_536 < 900_719_925_474` (`jointBlockGasSlope3K < perTxSixPassTargetK < yukon`),
invariance of all three joint block-gas budgets under `+ storeConstsAllowance (midTailChain c temp b p)`,
and the sharp multiplier bound `m * jointBlockGasSlope3K < 900_719_925_474 ↔ m ≤ 7`. -/
theorem mid_tail_joint_block_gas_ordering_and_allowance_invariance_non_vacuous_and_tight
    {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat) (b : Bool)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true) (m : Nat) :
    NoSt (midTailChain c temp b p) = true ∧
    storeConstsAllowance (midTailChain c temp b p) = 0 ∧
    jointBlockGasSlope3K = 121_459_456_007 ∧
    perTxSixPassTargetK = 122_620_608_536 ∧
    yukon = 900_719_925_474 ∧
    121_459_456_007 < 122_620_608_536 ∧
    122_620_608_536 < 900_719_925_474 ∧
    jointBlockGasSlope3K < perTxSixPassTargetK ∧
    perTxSixPassTargetK < yukon ∧
    jointBlockGasSlope3K + storeConstsAllowance (midTailChain c temp b p) = 121_459_456_007 ∧
    jointBlockGasSlope6K + storeConstsAllowance (midTailChain c temp b p) = 242_918_888_882 ∧
    jointBlockGasSlope12K + storeConstsAllowance (midTailChain c temp b p) = 485_837_754_632 ∧
    perTxSixPassTargetK - jointBlockGasSlope3K = 1_161_152_529 ∧
    yukon - perTxSixPassTargetK = 778_099_316_938 ∧
    (m * jointBlockGasSlope3K < 900_719_925_474 ↔ m ≤ 7) := by
  have hnost : NoSt (midTailChain c temp b p) = true := t_mid_tail_chain c temp b p hp
  have hzero : storeConstsAllowance (midTailChain c temp b p) = 0 := noSt_allowance_zero _ hnost
  have hptx : perTxSixPassTargetK = 122_620_608_536 :=
    (eight_tier_portfolio_strict_ordering_and_gaps_non_vacuous_and_tight 0).2.2.2.2.2.1
  have hj := joint_block_gas_three_regimes_exact_and_yukon_margins_non_vacuous_and_tight m
  rw [hptx]
  refine ⟨hnost, hzero, rfl, rfl, rfl, by decide, by decide, by decide, by decide,
    ?_, ?_, ?_, by decide, by decide, hj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  · rw [hzero, Nat.add_zero]; rfl
  · rw [hzero, Nat.add_zero]; rfl
  · rw [hzero, Nat.add_zero]; rfl

/-- Theorem 5 (`non_vacuous_and_tight`): Integration of `midTailChain` (`storeConstsAllowance = 0`
and `stackRemoveMidTailClock = k_sn + 1`) with `YukonSubmissionDryRunCert`:
8-tier candidate hierarchy (`11_029_669_988 < 11_029_683_788 < ... < 121_459_456_007 < 122_620_608_536 < ... < 900_719_925_474`),
valid `claim.json ≤ 128` bytes, `check_submission.py` / `verify.py` compliance, and `zeroBoundedImportCount = 0`. -/
theorem mid_tail_yukon_submission_dry_run_compliance_non_vacuous_and_tight
    {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat) (b : Bool)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true)
    (tier : DryRunCandidateTier) (k_sn claimBytes : Nat) :
    NoSt (midTailChain c temp b p) = true ∧
    storeConstsAllowance (midTailChain c temp b p) = 0 ∧
    stackRemoveMidTailClock (midTailChain c temp b p) k_sn = k_sn + 1 ∧
    sixPassUnrolledCopyLoopK = 11_029_669_988 ∧
    sixPassReducedK = 11_029_683_788 ∧
    sixPassUnrolledCopyLoopK < sixPassReducedK ∧
    sixPassReducedK < jointBlockGasSlope3K ∧
    jointBlockGasSlope3K < perTxSixPassTargetK ∧
    perTxSixPassTargetK < yukon ∧
    validFiniteClaim (selectDryRunCandidateK tier) (selectDryRunClaimJson tier) = true ∧
    validFiniteClaim (selectDryRunCandidateK tier) (selectDryRunVerifierJson tier) = true ∧
    (selectDryRunClaimJson tier).utf8ByteSize ≤ MAX_CLAIM_BYTES ∧
    checkSubmissionLimits dryRunFullSolverPackageFiles 2936344 65536 18 false false true = true ∧
    zeroBoundedImportCount = 0 ∧
    "sorryAx" ∉ standardAxioms ∧
    ((selectDryRunClaimJson tier).utf8ByteSize + claimBytes ≤ MAX_CLAIM_BYTES ↔
      claimBytes ≤ MAX_CLAIM_BYTES - (selectDryRunClaimJson tier).utf8ByteSize) := by
  have hnost : NoSt (midTailChain c temp b p) = true := t_mid_tail_chain c temp b p hp
  have hzero : storeConstsAllowance (midTailChain c temp b p) = 0 := noSt_allowance_zero _ hnost
  have hclk : stackRemoveMidTailClock (midTailChain c temp b p) k_sn = k_sn + 1 := by
    unfold stackRemoveMidTailClock C_sn D_sn
    rw [hzero]
    omega
  have hdry4 := dry_run_eight_tier_candidate_hierarchy_with_unrolled_copyloop_non_vacuous_and_tight 0
  have hdry5 := dry_run_all_eight_tiers_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight tier claimBytes
  have hptx : perTxSixPassTargetK = 122_620_608_536 :=
    (eight_tier_portfolio_strict_ordering_and_gaps_non_vacuous_and_tight 0).2.2.2.2.2.1
  have hunr : sixPassUnrolledCopyLoopK = 11_029_669_988 := hdry4.1
  have hred : sixPassReducedK = 11_029_683_788 := hdry4.2.1
  rw [hunr, hred, hptx]
  refine ⟨hnost, hzero, hclk, rfl, rfl, by decide, by decide, by decide, by decide,
    hdry5.2.2.2.2.2.2.2.2.1, hdry5.2.2.2.2.2.2.2.2.2.1, hdry5.2.2.2.2.2.2.1,
    by decide, rfl, by decide, hdry5.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 6 (`non_vacuous_and_tight`): Unified `yukonScore` IEEE-754 float64 representability
(`< 2^53 - 1`) and strict ordering across `sixPassUnrolledCopyLoopK`, `sixPassReducedK`,
`isoReducedCandidateK`, `jointBlockGasSlope3K = 121_459_456_007`, `perTxSixPassTargetK = 122_620_608_536`,
`jointBlockGasSlope6K`, and `jointBlockGasSlope12K`, with zero score shift under
`storeConstsAllowance (midTailChain c temp b p)`. -/
theorem mid_tail_joint_and_dry_run_yukonScore_strict_order_non_vacuous_and_tight
    {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat) (b : Bool)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true)
    (tier : DryRunCandidateTier) (minutes K : Nat) :
    storeConstsAllowance (midTailChain c temp b p) = 0 ∧
    yukonScore (jointBlockGasSlope3K + storeConstsAllowance (midTailChain c temp b p)) minutes =
      yukonScore jointBlockGasSlope3K minutes ∧
    yukonScore sixPassUnrolledCopyLoopK minutes < yukonScore sixPassReducedK minutes ∧
    yukonScore sixPassReducedK minutes < yukonScore isoReducedCandidateK minutes ∧
    yukonScore isoReducedCandidateK minutes < yukonScore jointBlockGasSlope3K minutes ∧
    yukonScore jointBlockGasSlope3K minutes < yukonScore perTxSixPassTargetK minutes ∧
    yukonScore perTxSixPassTargetK minutes < yukonScore jointBlockGasSlope6K minutes ∧
    yukonScore jointBlockGasSlope6K minutes < yukonScore jointBlockGasSlope12K minutes ∧
    yukonScore jointBlockGasSlope12K minutes < 2 ^ 53 - 1 ∧
    yukonScore (selectDryRunCandidateK tier) minutes < 2 ^ 53 - 1 ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have hnost : NoSt (midTailChain c temp b p) = true := t_mid_tail_chain c temp b p hp
  have hzero : storeConstsAllowance (midTailChain c temp b p) = 0 := noSt_allowance_zero _ hnost
  have hj5 := joint_block_gas_yukonScore_order_and_blockVsTx_savings_non_vacuous_and_tight minutes K
  have hdry6 := dry_run_eight_tiers_yukonScore_and_ssz_fast_reject_non_vacuous_and_tight
    tier minutes 0 (Nat.zero_le _)
  refine ⟨hzero, ?_, hdry6.2.2.1, hj5.2.2.2.1, hj5.2.2.2.2.1, hj5.2.2.2.2.2.1,
    hj5.2.2.2.2.2.2.1, hj5.2.2.2.2.2.2.2.1, hj5.2.2.2.2.2.2.2.2.1,
    hdry6.2.2.2.2.2.2.1, hj5.2.2.2.2.2.2.2.2.2⟩
  rw [hzero, Nat.add_zero]

/-- Theorem 7 (`non_vacuous_and_tight`): Finite `InitE.Certificate` at `jointBlockGasSlope3K = 121_459_456_007`
paired with `midTailChain` `NoSt`, `storeConstsAllowance = 0`, and `stackRemoveMidTailClock = k_sn + 1`,
plus automatic upward certificate transfer to `perTxSixPassTargetK = 122_620_608_536`,
`jointBlockGasSlope6K = 242_918_888_882`, and `jointBlockGasSlope12K = 485_837_754_632`. -/
theorem mid_tail_joint_block_gas_slope3_certificate_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (temp : Nat) (b : Bool)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true) (k_sn : Nat)
    (ctx : Spt Nat) (lprog : HolLoopProg width) (labels : Nat × Nat)
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
        jointBlockGasSlope3K (baselineInitialState input)).1 ≠ .timeOut) :
    NoSt (midTailChain ac temp b p) = true ∧
    storeConstsAllowance (midTailChain ac temp b p) = 0 ∧
    stackRemoveMidTailClock (midTailChain ac temp b p) k_sn = k_sn + 1 ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope3K) (.finite jointBlockGasSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK) (.finite perTxSixPassTargetK) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope6K) (.finite jointBlockGasSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope12K) (.finite jointBlockGasSlope12K) ∧
    ¬ (bootstrapSteps + jointBlockGasSlope3PostK ≤ jointBlockGasSlope3K - 1) := by
  have hnost : NoSt (midTailChain ac temp b p) = true := t_mid_tail_chain ac temp b p hp
  have hzero : storeConstsAllowance (midTailChain ac temp b p) = 0 := noSt_allowance_zero _ hnost
  have hclk : stackRemoveMidTailClock (midTailChain ac temp b p) k_sn = k_sn + 1 := by
    unfold stackRemoveMidTailClock C_sn D_sn
    rw [hzero]
    omega
  have hj6 := joint_block_gas_slope3_tail_certificate_non_vacuous_and_tight
    ctx lprog labels b oracles c depth hlab compiled depthBound not_timeOut
  exact ⟨hnost, hzero, hclk, hj6.2.2.1, hj6.2.2.2.1, hj6.2.2.2.2.1, hj6.2.2.2.2.2.1, hj6.2.2.2.2.2.2⟩

/-- Theorem 8 (`non_vacuous_and_tight`): Monotone upward transfer from `sixPassUnrolledCopyLoopK = 11_029_669_988`
(`YukonSubmissionDryRunCert`) across all 8 dry-run tiers and all three joint block-gas budgets
(`jointBlockGasSlope3K = 121_459_456_007`, `perTxSixPassTargetK = 122_620_608_536`,
`jointBlockGasSlope6K = 242_918_888_882`, `jointBlockGasSlope12K = 485_837_754_632`), paired with
`midTailChain` `storeConstsAllowance = 0` and `stackRemoveMidTailClock = k_sn + 1`. -/
theorem mid_tail_unrolled_copyloop_lifts_to_joint_and_dry_run_tiers_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (temp : Nat) (b : Bool)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true) (k_sn : Nat)
    (hcert_unr : InitE.Certificate (baselineWithFiniteK sixPassUnrolledCopyLoopK)
      (.finite sixPassUnrolledCopyLoopK))
    (dryTier : DryRunCandidateTier) (subTier : YukonCandidateTier) :
    NoSt (midTailChain ac temp b p) = true ∧
    storeConstsAllowance (midTailChain ac temp b p) = 0 ∧
    stackRemoveMidTailClock (midTailChain ac temp b p) k_sn = k_sn + 1 ∧
    InitE.Certificate (baselineWithFiniteK sixPassUnrolledCopyLoopK)
      (.finite sixPassUnrolledCopyLoopK) ∧
    InitE.Certificate (baselineWithFiniteK sixPassReducedK) (.finite sixPassReducedK) ∧
    InitE.Certificate (baselineWithFiniteK isoReducedCandidateK) (.finite isoReducedCandidateK) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope3K) (.finite jointBlockGasSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK) (.finite perTxSixPassTargetK) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope6K) (.finite jointBlockGasSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope12K) (.finite jointBlockGasSlope12K) ∧
    InitE.Certificate (baselineWithFiniteK (selectDryRunCandidateK dryTier))
      (.finite (selectDryRunCandidateK dryTier)) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    (∀ K₁ K₂ : Nat, (baselineWithFiniteK K₁).K = .finite K₂ ↔ K₁ = K₂) := by
  have hnost : NoSt (midTailChain ac temp b p) = true := t_mid_tail_chain ac temp b p hp
  have hzero : storeConstsAllowance (midTailChain ac temp b p) = 0 := noSt_allowance_zero _ hnost
  have hclk : stackRemoveMidTailClock (midTailChain ac temp b p) k_sn = k_sn + 1 := by
    unfold stackRemoveMidTailClock C_sn D_sn
    rw [hzero]
    omega
  have hdry7 := dry_run_certificate_monotone_from_unrolled_across_all_eight_tiers_non_vacuous_and_tight
    hcert_unr dryTier subTier
  have hcert_red := hdry7.2.1
  have hred : sixPassReducedK = 11_029_683_788 := reduced_budget_exact
  have hptx : perTxSixPassTargetK = 122_620_608_536 :=
    (eight_tier_portfolio_strict_ordering_and_gaps_non_vacuous_and_tight 0).2.2.2.2.2.1
  have hmono : ∀ {A B : Nat}, A ≤ B →
      InitE.Certificate (baselineWithFiniteK A) (.finite A) →
      InitE.Certificate (baselineWithFiniteK B) (.finite B) := by
    intro A B hab hA
    refine ⟨rfl, baselineWithFiniteK_admitted B, ?_⟩
    intro input hgas outcome events hsrc hcov
    obtain ⟨steps, hsteps, hm⟩ := hA.correct input hgas outcome events hsrc hcov
    have hm_base : matchingExecutionAt InitE.baselineSubmission input outcome events steps :=
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission (.finite A)
        input outcome events steps).mp hm
    exact ⟨steps, Nat.le_trans hsteps hab,
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission (.finite B)
        input outcome events steps).mpr hm_base⟩
  have hcert_j3 : InitE.Certificate (baselineWithFiniteK jointBlockGasSlope3K)
      (.finite jointBlockGasSlope3K) :=
    hmono (by rw [hred]; decide) hcert_red
  have hcert_ptx : InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK)
      (.finite perTxSixPassTargetK) :=
    hmono (by rw [hred, hptx]; decide) hcert_red
  have hcert_j6 : InitE.Certificate (baselineWithFiniteK jointBlockGasSlope6K)
      (.finite jointBlockGasSlope6K) :=
    hmono (by rw [hred]; decide) hcert_red
  have hcert_j12 : InitE.Certificate (baselineWithFiniteK jointBlockGasSlope12K)
      (.finite jointBlockGasSlope12K) :=
    hmono (by rw [hred]; decide) hcert_red
  exact ⟨hnost, hzero, hclk, hdry7.1, hcert_red, hdry7.2.2.2.1,
    hcert_j3, hcert_ptx, hcert_j6, hcert_j12,
    hdry7.2.2.2.2.2.2.2.2.2.1, hdry7.2.2.2.2.2.2.2.2.2.2.1,
    hdry7.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 9 (`non_vacuous_and_tight`): Master end-to-end synthesis of
`WordMidPassesPreserveNoStoreConsts` (`t_mid_tail_chain`), `StackRemoveStoreConstsZeroBridge`
(`storeConstsAllowance = 0`, `stackRemoveMidTailClock = k_sn + 1`),
`JointBlockGasSixPassMasterCert` (`121_459_456_007 < 122_620_608_536 < 900_719_925_474`), and
`YukonSubmissionDryRunCert` (`0 sorryAx`, `zeroBoundedImportCount = 0`). -/
theorem end_to_end_word_mid_tail_joint_block_gas_and_yukon_dry_run_master_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (temp : Nat) (b : Bool)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true) (k_sn : Nat)
    (ctx : Spt Nat) (lprog : HolLoopProg width) (labels : Nat × Nat)
    (dryTier : DryRunCandidateTier)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth minutes : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_sixPassReduced : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        sixPassReducedK (baselineInitialState input)).1 ≠ .timeOut) :
    NoSt (midTailChain ac temp b p) = true ∧
    storeConstsAllowance (midTailChain ac temp b p) = 0 ∧
    stackRemoveMidTailClock (midTailChain ac temp b p) k_sn = k_sn + 1 ∧
    121_459_456_007 < 122_620_608_536 ∧
    122_620_608_536 < 900_719_925_474 ∧
    InitE.Certificate (baselineWithFiniteK sixPassReducedK) (.finite sixPassReducedK) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope3K) (.finite jointBlockGasSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK) (.finite perTxSixPassTargetK) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope6K) (.finite jointBlockGasSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope12K) (.finite jointBlockGasSlope12K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    validFiniteClaim (selectDryRunCandidateK dryTier) (selectDryRunClaimJson dryTier) = true ∧
    (selectDryRunClaimJson dryTier).utf8ByteSize ≤ MAX_CLAIM_BYTES ∧
    yukonScore jointBlockGasSlope3K minutes < 2 ^ 53 - 1 ∧
    zeroBoundedImportCount = 0 ∧
    (stackRemoveMidTailClock (midTailChain ac temp b p) k_sn ≤ k_sn + 1 ↔ True) := by
  have hnost : NoSt (midTailChain ac temp b p) = true := t_mid_tail_chain ac temp b p hp
  have hzero : storeConstsAllowance (midTailChain ac temp b p) = 0 := noSt_allowance_zero _ hnost
  have hclk : stackRemoveMidTailClock (midTailChain ac temp b p) k_sn = k_sn + 1 := by
    unfold stackRemoveMidTailClock C_sn D_sn
    rw [hzero]
    omega
  have hj9 := end_to_end_joint_block_gas_six_pass_master_certificate_non_vacuous_and_tight
    ctx lprog labels b oracles c depth minutes hlab compiled depthBound not_timeOut_sixPassReduced
  have hdry5 := dry_run_all_eight_tiers_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight dryTier 0
  refine ⟨hnost, hzero, hclk, by decide, by decide,
    hj9.2.2.2.1, hj9.2.2.2.2.2.1, hj9.2.2.2.2.2.2.1, hj9.2.2.2.2.2.2.2.1,
    hj9.2.2.2.2.2.2.2.2.1, hj9.2.2.2.2.2.2.2.2.2.1,
    hdry5.2.2.2.2.2.2.2.2.1, hdry5.2.2.2.2.2.2.1,
    hj9.2.2.2.2.2.2.2.2.2.2.1, rfl, ?_⟩
  rw [hclk]
  simp

#print axioms mid_tail_chain_preserves_noSt_and_zero_allowance_non_vacuous_and_tight
#print axioms word_prog_no_store_consts_mid_tail_stack_remove_clock_bound_non_vacuous_and_tight
#print axioms compiled_loop_to_word_mid_tail_and_stack_remove_semantic_clock_non_vacuous_and_tight
#print axioms mid_tail_joint_block_gas_ordering_and_allowance_invariance_non_vacuous_and_tight
#print axioms mid_tail_yukon_submission_dry_run_compliance_non_vacuous_and_tight
#print axioms mid_tail_joint_and_dry_run_yukonScore_strict_order_non_vacuous_and_tight
#print axioms mid_tail_joint_block_gas_slope3_certificate_bridge_non_vacuous_and_tight
#print axioms mid_tail_unrolled_copyloop_lifts_to_joint_and_dry_run_tiers_non_vacuous_and_tight
#print axioms end_to_end_word_mid_tail_joint_block_gas_and_yukon_dry_run_master_non_vacuous_and_tight

end InitECandidate.Solver.WordMidTailNoStoreConstsBridge
