import InitECandidate.Solver.WordSsaCsePreserveNoStoreConsts
import InitECandidate.Solver.WordMidTailNoStoreConstsBridge
import InitECandidate.Solver.GuestBs32BlockStorageEnvelope

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.WordSsaCseSixPassBridge

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
open InitECandidate.Solver.WordSsaCsePreserveNoStoreConsts hiding storeConstsAllowance
open InitECandidate.Solver.WordToWordTailNoStoreConstsBridge
open InitECandidate.Solver.YukonEightTierMasterPortfolio hiding sixPassUnrolledCopyLoopK sixPassReducedK isoReducedCandidateK push31NoGcCandidateK push31CandidateK quadraticCollisionTargetK
open InitECandidate.Solver.JointBlockGasSixPassMasterCert
open InitECandidate.Solver.RiscvSszFastRejectAndBootCert
open InitECandidate.Solver.YukonVerifyScriptAudit
open InitECandidate.Solver.YukonFinalCandidateSelector
open InitECandidate.Solver.YukonSubmissionDryRunCert
open InitECandidate.Solver.WordMidTailNoStoreConstsBridge
open InitECandidate.Solver.GuestBs32BlockStorageEnvelope
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

/-- Eight-pass `WordToWord` chain matching `t_ssa_cse_mid_tail_chain`:
`instSelect -> fullSsaCcTrans -> removeDeadProg -> wordCommonSubexpElim -> copyProp ->
threeToTwoRegProg -> removeUnreach -> removeDeadProg`. -/
noncomputable def ssaCseMidTailChain {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (temp argc : Nat) (b : Bool) (p : WordLangProgHOL (BitVec width)) :
    WordLangProgHOL (BitVec width) :=
  WordAlloc.removeDeadProg
    (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b
        (WordCopy.copyProp
          (WordCse.wordCommonSubexpElim
            (WordAlloc.removeDeadProg
              (WordAlloc.fullSsaCcTrans argc
                (WordInst.instSelect c temp p)))))))

/-- Eight-pass `WordToWord` chain ending with `removeMustTerminate`:
`instSelect -> fullSsaCcTrans -> removeDeadProg -> wordCommonSubexpElim -> copyProp ->
threeToTwoRegProg -> removeUnreach -> removeMustTerminate`. -/
noncomputable def ssaCseMustTerminateChain {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (temp argc : Nat) (b : Bool) (p : WordLangProgHOL (BitVec width)) :
    WordLangProgHOL (BitVec width) :=
  WordRemove.removeMustTerminate
    (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b
        (WordCopy.copyProp
          (WordCse.wordCommonSubexpElim
            (WordAlloc.removeDeadProg
              (WordAlloc.fullSsaCcTrans argc
                (WordInst.instSelect c temp p)))))))

/-- Three-pass slope `threePassSlope = sixPassSlope 1 3 = 3` (`C_sr = 1, C_cl = 3`). -/
def threePassSlope : Nat := sixPassSlope 1 3

/-- Target RISC-V step budget for `kPanBs32Joint = 153,081,489,139` at slope `3x`
(`23,132 + 3 * 153,081,489,139 = 459,244,490,549`). -/
def bs32JointSlope3K : Nat := 23_132 + threePassSlope * kPanBs32Joint

/-- Target RISC-V step budget for `kPanBs32Sum = 166,686,761,248` at slope `3x`
(`23,132 + 3 * 166,686,761,248 = 500,060,306,876`). -/
def bs32SumSlope3K : Nat := 23_132 + threePassSlope * kPanBs32Sum

/-- Trace provenance from the 8-pass `ssaCseMidTailChain` output. -/
def SsaCseTraceFrom {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp argc : Nat)
    (b : Bool) (p : WordLangProgHOL (BitVec width)) (xs : List (Bool × Nat)) : Prop :=
  ∀ event ∈ xs, event.1 = true → NoSt (ssaCseMidTailChain c temp argc b p) = false

/-- Theorem 1 (`non_vacuous_and_tight`): Bridge from `t_ssa_cse_mid_tail_chain` and
`storeConstsAllowance_chain_zero` (`WordSsaCsePreserveNoStoreConsts`) to
`StackRemoveStoreConstsZeroBridge.storeConstsAllowance = 0` and `WordMidTailNoStoreConstsBridge`
across both 8-pass chains (`ssaCseMidTailChain` and `ssaCseMustTerminateChain`). -/
theorem ssa_cse_eight_pass_chain_preserves_noSt_and_zero_allowance_non_vacuous_and_tight
    {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp argc : Nat) (b : Bool)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true)
    (ws : List (Bool × BitVec width)) :
    NoSt (WordAlloc.fullSsaCcTrans argc (WordInst.instSelect c temp p)) = true ∧
    NoSt (WordCse.wordCommonSubexpElim (WordAlloc.removeDeadProg
      (WordAlloc.fullSsaCcTrans argc (WordInst.instSelect c temp p)))) = true ∧
    NoSt (ssaCseMidTailChain c temp argc b p) = true ∧
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance (ssaCseMidTailChain c temp argc b p) = 0 ∧
    storeConstsAllowance (ssaCseMidTailChain c temp argc b p) = 0 ∧
    NoSt (ssaCseMustTerminateChain c temp argc b p) = true ∧
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance (ssaCseMustTerminateChain c temp argc b p) = 0 ∧
    storeConstsAllowance (ssaCseMustTerminateChain c temp argc b p) = 0 ∧
    NoSt (midTailChain c temp b p) = true ∧
    storeConstsAllowance (midTailChain c temp b p) = 0 ∧
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance
      (WordLangProgHOL.storeConsts (α := BitVec width) 0 2 4 6 []) = 1 ∧
    (storeConstsAllowance (.storeConsts 0 2 4 6 ws) = 0 ↔ ws = []) := by
  have h1 : NoSt (WordInst.instSelect c temp p) = true := t_instSelect c temp p hp
  have h2 : NoSt (WordAlloc.fullSsaCcTrans argc (WordInst.instSelect c temp p)) = true :=
    t_fullSsaCcTrans argc _ h1
  have h3 : NoSt (WordAlloc.removeDeadProg
      (WordAlloc.fullSsaCcTrans argc (WordInst.instSelect c temp p))) = true :=
    t_removeDeadProg _ h2
  have h4 : NoSt (WordCse.wordCommonSubexpElim (WordAlloc.removeDeadProg
      (WordAlloc.fullSsaCcTrans argc (WordInst.instSelect c temp p)))) = true :=
    t_wordCommonSubexpElim _ h3
  have h5 : NoSt (WordCopy.copyProp (WordCse.wordCommonSubexpElim (WordAlloc.removeDeadProg
      (WordAlloc.fullSsaCcTrans argc (WordInst.instSelect c temp p))))) = true :=
    t_copyProp _ h4
  have h6 : NoSt (WordInst.threeToTwoRegProg b (WordCopy.copyProp (WordCse.wordCommonSubexpElim
      (WordAlloc.removeDeadProg (WordAlloc.fullSsaCcTrans argc (WordInst.instSelect c temp p)))))) = true :=
    t_threeToTwo b _ h5
  have h7 : NoSt (WordUnreach.removeUnreach (WordInst.threeToTwoRegProg b (WordCopy.copyProp
      (WordCse.wordCommonSubexpElim (WordAlloc.removeDeadProg
        (WordAlloc.fullSsaCcTrans argc (WordInst.instSelect c temp p))))))) = true :=
    t_removeUnreach _ h6
  have h8 : NoSt (ssaCseMidTailChain c temp argc b p) = true :=
    t_ssa_cse_mid_tail_chain c temp argc b p hp
  have h8_mt : NoSt (ssaCseMustTerminateChain c temp argc b p) = true :=
    t_removeMustTerminate _ h7
  have h8_zero_ssa :
      WordSsaCsePreserveNoStoreConsts.storeConstsAllowance (ssaCseMidTailChain c temp argc b p) = 0 :=
    storeConstsAllowance_chain_zero c temp argc b p hp
  have h8_mt_zero_ssa :
      WordSsaCsePreserveNoStoreConsts.storeConstsAllowance (ssaCseMustTerminateChain c temp argc b p) = 0 := by
    simp [WordSsaCsePreserveNoStoreConsts.storeConstsAllowance, h8_mt]
  have hmid : NoSt (midTailChain c temp b p) = true := t_mid_tail_chain c temp b p hp
  have htight := allowance_storeConsts_tight 0 2 4 6 ws
  refine ⟨h2, h4, h8, h8_zero_ssa, noSt_allowance_zero _ h8,
    h8_mt, h8_mt_zero_ssa, noSt_allowance_zero _ h8_mt,
    hmid, noSt_allowance_zero _ hmid, storeConstsAllowance_tight, ?_⟩
  rw [htight, List.length_eq_zero_iff]

/-- Theorem 2 (`non_vacuous_and_tight`): Every `WordProg` without `storeConsts` (`NoSt p = true`)
traversing the 8 passes of `t_ssa_cse_mid_tail_chain` guarantees `storeConstsAllowance = 0`,
`runAllowance xs = 0`, `C_sr = 1` (`threePassSlope = 3`), and `k_sr = k_sn + 1`
(`stackRemoveMidTailClock = k_sn + 1`). -/
theorem word_prog_ssa_cse_chain_stack_remove_clock_and_slope_three_non_vacuous_and_tight
    {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp argc : Nat) (b : Bool)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true)
    (xs : List (Bool × Nat)) (horigin : SsaCseTraceFrom c temp argc b p xs)
    (oracles : List (Option (Spt Nat))) (d_cl d_ws k_sn k_entry : Nat) :
    NoSt (ssaCseMidTailChain c temp argc b p) = true ∧
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance (ssaCseMidTailChain c temp argc b p) = 0 ∧
    storeConstsAllowance (ssaCseMidTailChain c temp argc b p) = 0 ∧
    storeConstsAllowance (ssaCseMustTerminateChain c temp argc b p) = 0 ∧
    runAllowance xs = 0 ∧
    (oracleCompilerConfig oracles).stackConf.jump = false ∧
    threePassSlope = 3 ∧
    sixPassSlope 1 3 = 3 ∧
    sixPassAffine d_cl d_ws (storeConstsAllowance (ssaCseMidTailChain c temp argc b p)) k_sn =
      3 * k_sn + (d_cl + d_ws) ∧
    stackRemoveMidTailClock (ssaCseMidTailChain c temp argc b p) k_sn = k_sn + 1 ∧
    stackRemoveMidTailClock (ssaCseMustTerminateChain c temp argc b p) k_sn = k_sn + 1 ∧
    (stackRemoveMidTailClock (ssaCseMidTailChain c temp argc b p) k_sn ≤ k_entry ↔
      k_sn + 1 ≤ k_entry) := by
  have h8 : NoSt (ssaCseMidTailChain c temp argc b p) = true :=
    t_ssa_cse_mid_tail_chain c temp argc b p hp
  have h8_zero_ssa :
      WordSsaCsePreserveNoStoreConsts.storeConstsAllowance (ssaCseMidTailChain c temp argc b p) = 0 :=
    storeConstsAllowance_chain_zero c temp argc b p hp
  have h8_zero : storeConstsAllowance (ssaCseMidTailChain c temp argc b p) = 0 :=
    noSt_allowance_zero _ h8
  have h8_mt : NoSt (ssaCseMustTerminateChain c temp argc b p) = true :=
    t_removeMustTerminate _ (t_removeUnreach _ (t_threeToTwo b _ (t_copyProp _
      (t_wordCommonSubexpElim _ (t_removeDeadProg _ (t_fullSsaCcTrans argc _
        (t_instSelect c temp p hp)))))))
  have h8_mt_zero : storeConstsAllowance (ssaCseMustTerminateChain c temp argc b p) = 0 :=
    noSt_allowance_zero _ h8_mt
  have hflags : ∀ event ∈ xs, event.1 = false := by
    intro event he
    cases hb : event.1 with
    | false => rfl
    | true =>
      have hfalse := horigin event he hb
      rw [h8] at hfalse
      contradiction
  have hrun0 : runAllowance xs = 0 := runAllowance_zero_of_no_storeConsts xs hflags
  have hclk1 : stackRemoveMidTailClock (ssaCseMidTailChain c temp argc b p) k_sn = k_sn + 1 := by
    unfold stackRemoveMidTailClock C_sn D_sn
    rw [h8_zero]
    omega
  have hclk2 : stackRemoveMidTailClock (ssaCseMustTerminateChain c temp argc b p) k_sn = k_sn + 1 := by
    unfold stackRemoveMidTailClock C_sn D_sn
    rw [h8_mt_zero]
    omega
  have haff : sixPassAffine d_cl d_ws (storeConstsAllowance (ssaCseMidTailChain c temp argc b p)) k_sn =
      3 * k_sn + (d_cl + d_ws) := by
    rw [h8_zero]
    exact neutral_six_pass_affine d_cl d_ws k_sn
  refine ⟨h8, h8_zero_ssa, h8_zero, h8_mt_zero, hrun0, guest_stackRemove_jump_false oracles,
    rfl, neutral_six_pass_slope, haff, hclk1, hclk2, ?_⟩
  rw [hclk1]

/-- Theorem 3 (`non_vacuous_and_tight`): Semantic `StackRemove` (`initCode` `0`-tick neutrality +
`k_sr = k_sn + 1`) and `StackNames` (`C_sn = 1, D_sn = 0`) composition at clock `k_sn + 1` for
any `NoSt` program `p` exiting the 8-pass `ssaCseMidTailChain`, plus `LoopToWord.compHOL` specialization. -/
theorem compiled_loop_to_word_ssa_cse_chain_and_stack_remove_semantic_clock_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (temp argc : Nat) (b : Bool)
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
    NoSt (ssaCseMidTailChain ac temp argc b (LoopToWord.compHOL ctx lprog labels).1) = true ∧
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance
      (ssaCseMidTailChain ac temp argc b (LoopToWord.compHOL ctx lprog labels).1) = 0 ∧
    storeConstsAllowance
      (ssaCseMidTailChain ac temp argc b (LoopToWord.compHOL ctx lprog labels).1) = 0 ∧
    stackRemoveMidTailClock (ssaCseMidTailChain ac temp argc b p) k_sn = k_sn + 1 ∧
    clockNeutralHOL (StackRemove.initCode (width := width) generateGc maxHeap pointer) ∧
    (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { StackNamesExactClockIso.stateRel comp f s2 with
        clock := stackRemoveMidTailClock (ssaCseMidTailChain ac temp argc b p) k_sn })).1 =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k_sn })).1 ∧
    (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { StackNamesExactClockIso.stateRel comp f s2 with
        clock := stackRemoveMidTailClock (ssaCseMidTailChain ac temp argc b p) k_sn })).2.ffi =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k_sn })).2.ffi ∧
    (stackRemoveMidTailClock (ssaCseMidTailChain ac temp argc b p) k_sn ≤ k_entry ↔
      k_sn < k_entry) := by
  have hcomp_nost : NoSt (LoopToWord.compHOL ctx lprog labels).1 = true :=
    loopToWord_NoSt ctx lprog labels
  have hcomp_8 : NoSt (ssaCseMidTailChain ac temp argc b (LoopToWord.compHOL ctx lprog labels).1) = true :=
    t_ssa_cse_mid_tail_chain ac temp argc b _ hcomp_nost
  have hcomp_zero_ssa :
      WordSsaCsePreserveNoStoreConsts.storeConstsAllowance
        (ssaCseMidTailChain ac temp argc b (LoopToWord.compHOL ctx lprog labels).1) = 0 :=
    storeConstsAllowance_chain_zero ac temp argc b _ hcomp_nost
  have hcomp_zero :
      storeConstsAllowance
        (ssaCseMidTailChain ac temp argc b (LoopToWord.compHOL ctx lprog labels).1) = 0 :=
    noSt_allowance_zero _ hcomp_8
  have hp_8 : NoSt (ssaCseMidTailChain ac temp argc b p) = true :=
    t_ssa_cse_mid_tail_chain ac temp argc b p hp
  have hp_zero : storeConstsAllowance (ssaCseMidTailChain ac temp argc b p) = 0 :=
    noSt_allowance_zero _ hp_8
  have hclk_eq : stackRemoveMidTailClock (ssaCseMidTailChain ac temp argc b p) k_sn =
      C_sn * (k_sn + 1) + D_sn := by
    unfold stackRemoveMidTailClock
    rw [hp_zero, Nat.add_zero]
  have hclk_val : stackRemoveMidTailClock (ssaCseMidTailChain ac temp argc b p) k_sn = k_sn + 1 := by
    rw [hclk_eq]
    unfold C_sn D_sn
    omega
  have hsem := stack_names_compose_init_code_neutral generateGc maxHeap pointer start comp f
    s2 t k_sn hentry hrun hf ha hs hk hc
  rw [← hclk_eq] at hsem
  refine ⟨hcomp_8, hcomp_zero_ssa, hcomp_zero, hclk_val, hsem.1, hsem.2.2.1, hsem.2.2.2.1, ?_⟩
  rw [hclk_val]
  omega

/-- Theorem 4 (`non_vacuous_and_tight`): Integration of the 8-pass `t_ssa_cse_mid_tail_chain`
(`storeConstsAllowance = 0`, `threePassSlope = 3`) with `GuestBs32BlockStorageEnvelope`:
`kPanBs32Joint = 153,081,489,139` and `kPanBs32Sum = 166,686,761,248` both pass under Yukon at
slope `3x` (`slope3_ok` and post-bootstrap `bs32JointSlope3K = 459,244,490,549 <
bs32SumSlope3K = 500,060,306,876 < 900,719,925,474`), whereas slopes `6x`, `9x`, `12x` fail,
with exact integer slope threshold `k * kPanBs32Joint < yukon ↔ k ≤ 5`. -/
theorem ssa_cse_bs32_block_storage_envelope_slope3_under_yukon_non_vacuous_and_tight
    {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp argc : Nat) (b : Bool)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true)
    (D W C T2 : Nat) (hbudget : 21 * D + W + 21 * C ≤ S) (hT2 : T2 ≤ perTx)
    (k : Nat) :
    NoSt (ssaCseMidTailChain c temp argc b p) = true ∧
    storeConstsAllowance (ssaCseMidTailChain c temp argc b p) = 0 ∧
    threePassSlope = 3 ∧
    kPanBs32Joint = 153_081_489_139 ∧
    kPanBs32Sum = 166_686_761_248 ∧
    linear + T2 + (2 * (D * W) + blkRead C) ≤ kPanBs32Joint ∧
    3 * kPanBs32Joint = 459_244_467_417 ∧
    3 * kPanBs32Sum = 500_060_283_744 ∧
    3 * kPanBs32Joint < yukon ∧
    3 * kPanBs32Sum < yukon ∧
    bs32JointSlope3K = 459_244_490_549 ∧
    bs32SumSlope3K = 500_060_306_876 ∧
    459_244_490_549 < 500_060_306_876 ∧
    500_060_306_876 < 900_719_925_474 ∧
    bs32JointSlope3K + storeConstsAllowance (ssaCseMidTailChain c temp argc b p) = 459_244_490_549 ∧
    bs32SumSlope3K + storeConstsAllowance (ssaCseMidTailChain c temp argc b p) = 500_060_306_876 ∧
    yukon < 6 * kPanBs32Joint ∧
    (k * kPanBs32Joint < yukon ↔ k ≤ 5) ∧
    (k * kPanBs32Sum < yukon ↔ k ≤ 5) := by
  have h8 : NoSt (ssaCseMidTailChain c temp argc b p) = true :=
    t_ssa_cse_mid_tail_chain c temp argc b p hp
  have hzero : storeConstsAllowance (ssaCseMidTailChain c temp argc b p) = 0 :=
    noSt_allowance_zero _ h8
  have hmaster := kPan_master D W C T2 hbudget hT2
  have hs3 := slope3_ok
  have hfail := slope_6_9_12_fail
  refine ⟨h8, hzero, rfl, kPan_values.1, kPan_values.2, hmaster,
    by decide, by decide, hs3.1, hs3.2,
    by decide, by decide, by decide, by decide, ?_, ?_,
    hfail.1, slope_threshold k, slope_threshold_sum k⟩
  · rw [hzero, Nat.add_zero]; decide
  · rw [hzero, Nat.add_zero]; decide

/-- Theorem 5 (`non_vacuous_and_tight`): Complete strict hierarchy across all six-pass and
`bs+32` block-storage envelopes under the 8-pass `t_ssa_cse_mid_tail_chain`:
`11,029,669,988 < 11,029,683,788 < 22,059,344,444 < 121,459,456,007 < 122,620,608,536 <
242,918,888,882 < 459,244,490,549 < 485,837,754,632 < 500,060,306,876 < 900,719,925,474`. -/
theorem ssa_cse_complete_strict_budget_hierarchy_and_gaps_non_vacuous_and_tight
    {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp argc : Nat) (b : Bool)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true) (m : Nat) :
    storeConstsAllowance (ssaCseMidTailChain c temp argc b p) = 0 ∧
    sixPassUnrolledCopyLoopK = 11_029_669_988 ∧
    sixPassReducedK = 11_029_683_788 ∧
    isoReducedCandidateK = 22_059_344_444 ∧
    jointBlockGasSlope3K = 121_459_456_007 ∧
    perTxSixPassTargetK = 122_620_608_536 ∧
    jointBlockGasSlope6K = 242_918_888_882 ∧
    bs32JointSlope3K = 459_244_490_549 ∧
    jointBlockGasSlope12K = 485_837_754_632 ∧
    bs32SumSlope3K = 500_060_306_876 ∧
    yukon = 900_719_925_474 ∧
    sixPassUnrolledCopyLoopK < sixPassReducedK ∧
    sixPassReducedK < isoReducedCandidateK ∧
    isoReducedCandidateK < jointBlockGasSlope3K ∧
    jointBlockGasSlope3K < perTxSixPassTargetK ∧
    perTxSixPassTargetK < jointBlockGasSlope6K ∧
    jointBlockGasSlope6K < bs32JointSlope3K ∧
    bs32JointSlope3K < jointBlockGasSlope12K ∧
    jointBlockGasSlope12K < bs32SumSlope3K ∧
    bs32SumSlope3K < yukon ∧
    bs32SumSlope3K - bs32JointSlope3K = 40_815_816_327 ∧
    yukon - bs32SumSlope3K = 400_659_618_598 ∧
    yukon - bs32JointSlope3K = 441_475_434_925 ∧
    (m * bs32JointSlope3K < yukon ↔ m ≤ 1) := by
  have h8 : NoSt (ssaCseMidTailChain c temp argc b p) = true :=
    t_ssa_cse_mid_tail_chain c temp argc b p hp
  have hzero : storeConstsAllowance (ssaCseMidTailChain c temp argc b p) = 0 :=
    noSt_allowance_zero _ h8
  have hdry4 := dry_run_eight_tier_candidate_hierarchy_with_unrolled_copyloop_non_vacuous_and_tight 0
  have hptx : perTxSixPassTargetK = 122_620_608_536 :=
    (eight_tier_portfolio_strict_ordering_and_gaps_non_vacuous_and_tight 0).2.2.2.2.2.1
  have hunr : sixPassUnrolledCopyLoopK = 11_029_669_988 := hdry4.1
  have hred : sixPassReducedK = 11_029_683_788 := hdry4.2.1
  have hiso : isoReducedCandidateK = 22_059_344_444 := hdry4.2.2.2.1
  rw [hunr, hred, hiso, hptx]
  refine ⟨hzero, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, by decide, rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  have hbs32 : bs32JointSlope3K = 459_244_490_549 := by decide
  have hyuk : yukon = 900_719_925_474 := rfl
  rw [hbs32, hyuk]
  omega

/-- Theorem 6 (`non_vacuous_and_tight`): Unified `yukonScore` IEEE-754 float64 representability
(`< 2^53 - 1`) and strict ordering across all candidates including `bs32JointSlope3K = 459,244,490,549`
and `bs32SumSlope3K = 500,060,306,876`, with zero score shift under
`storeConstsAllowance (ssaCseMidTailChain c temp argc b p)`. -/
theorem ssa_cse_yukonScore_strict_order_with_bs32_envelopes_non_vacuous_and_tight
    {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp argc : Nat) (b : Bool)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true)
    (tier : DryRunCandidateTier) (minutes K : Nat) :
    storeConstsAllowance (ssaCseMidTailChain c temp argc b p) = 0 ∧
    yukonScore (bs32JointSlope3K + storeConstsAllowance (ssaCseMidTailChain c temp argc b p)) minutes =
      yukonScore bs32JointSlope3K minutes ∧
    yukonScore (bs32SumSlope3K + storeConstsAllowance (ssaCseMidTailChain c temp argc b p)) minutes =
      yukonScore bs32SumSlope3K minutes ∧
    yukonScore sixPassUnrolledCopyLoopK minutes < yukonScore sixPassReducedK minutes ∧
    yukonScore sixPassReducedK minutes < yukonScore isoReducedCandidateK minutes ∧
    yukonScore isoReducedCandidateK minutes < yukonScore jointBlockGasSlope3K minutes ∧
    yukonScore jointBlockGasSlope3K minutes < yukonScore perTxSixPassTargetK minutes ∧
    yukonScore perTxSixPassTargetK minutes < yukonScore jointBlockGasSlope6K minutes ∧
    yukonScore jointBlockGasSlope6K minutes < yukonScore bs32JointSlope3K minutes ∧
    yukonScore bs32JointSlope3K minutes < yukonScore jointBlockGasSlope12K minutes ∧
    yukonScore jointBlockGasSlope12K minutes < yukonScore bs32SumSlope3K minutes ∧
    yukonScore bs32JointSlope3K minutes < 2 ^ 53 - 1 ∧
    yukonScore bs32SumSlope3K minutes < 2 ^ 53 - 1 ∧
    yukonScore (selectDryRunCandidateK tier) minutes < 2 ^ 53 - 1 ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have h8 : NoSt (ssaCseMidTailChain c temp argc b p) = true :=
    t_ssa_cse_mid_tail_chain c temp argc b p hp
  have hzero : storeConstsAllowance (ssaCseMidTailChain c temp argc b p) = 0 :=
    noSt_allowance_zero _ h8
  have hmid6 := mid_tail_joint_and_dry_run_yukonScore_strict_order_non_vacuous_and_tight
    c temp b p hp tier minutes K
  have hmono : ∀ {A B : Nat}, A < B → yukonScore A minutes < yukonScore B minutes := by
    intro A B hab
    unfold yukonScore
    omega
  have hj6_lt_bs32j : yukonScore jointBlockGasSlope6K minutes < yukonScore bs32JointSlope3K minutes :=
    hmono (by decide)
  have hbs32j_lt_j12 : yukonScore bs32JointSlope3K minutes < yukonScore jointBlockGasSlope12K minutes :=
    hmono (by decide)
  have hj12_lt_bs32s : yukonScore jointBlockGasSlope12K minutes < yukonScore bs32SumSlope3K minutes :=
    hmono (by decide)
  have hbs32s_rep : yukonScore bs32SumSlope3K minutes < 2 ^ 53 - 1 :=
    yukonScore_lt_two_pow_53_sub_one (by decide)
  have hbs32j_rep : yukonScore bs32JointSlope3K minutes < 2 ^ 53 - 1 :=
    Nat.lt_trans (Nat.lt_trans hbs32j_lt_j12 hj12_lt_bs32s) hbs32s_rep
  refine ⟨hzero, ?_, ?_, hmid6.2.2.1, hmid6.2.2.2.1, hmid6.2.2.2.2.1, hmid6.2.2.2.2.2.1,
    hmid6.2.2.2.2.2.2.1, hj6_lt_bs32j, hbs32j_lt_j12, hj12_lt_bs32s,
    hbs32j_rep, hbs32s_rep, hmid6.2.2.2.2.2.2.2.2.2.1, hmid6.2.2.2.2.2.2.2.2.2.2⟩
  · rw [hzero, Nat.add_zero]
  · rw [hzero, Nat.add_zero]

/-- Theorem 7 (`non_vacuous_and_tight`): Finite `InitE.Certificate` at `bs32JointSlope3K = 459,244,490,549`
and upward transfer to `bs32SumSlope3K = 500,060,306,876`, paired with 8-pass `ssaCseMidTailChain`
`NoSt`, `storeConstsAllowance = 0`, and `stackRemoveMidTailClock = k_sn + 1`. -/
theorem ssa_cse_bs32_slope3_certificate_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (temp argc : Nat) (b : Bool)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true) (k_sn : Nat)
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
        bs32JointSlope3K (baselineInitialState input)).1 ≠ .timeOut) :
    NoSt (ssaCseMidTailChain ac temp argc b p) = true ∧
    storeConstsAllowance (ssaCseMidTailChain ac temp argc b p) = 0 ∧
    stackRemoveMidTailClock (ssaCseMidTailChain ac temp argc b p) k_sn = k_sn + 1 ∧
    InitE.Certificate (baselineWithFiniteK bs32JointSlope3K) (.finite bs32JointSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK 459_244_490_549) (.finite 459_244_490_549) ∧
    InitE.Certificate (baselineWithFiniteK bs32SumSlope3K) (.finite bs32SumSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK 500_060_306_876) (.finite 500_060_306_876) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    ¬ (bootstrapSteps + 3 * kPanBs32Joint ≤ bs32JointSlope3K - 1) := by
  have h8 : NoSt (ssaCseMidTailChain ac temp argc b p) = true :=
    t_ssa_cse_mid_tail_chain ac temp argc b p hp
  have hzero : storeConstsAllowance (ssaCseMidTailChain ac temp argc b p) = 0 :=
    noSt_allowance_zero _ h8
  have hclk : stackRemoveMidTailClock (ssaCseMidTailChain ac temp argc b p) k_sn = k_sn + 1 := by
    unfold stackRemoveMidTailClock C_sn D_sn
    rw [hzero]
    omega
  have hj_val : bs32JointSlope3K = 459_244_490_549 := by decide
  have hs_val : bs32SumSlope3K = 500_060_306_876 := by decide
  have hcert_j_lit : InitE.Certificate (baselineWithFiniteK 459_244_490_549)
      (.finite 459_244_490_549) := by
    have h := finite_certificate_of_uniform_post_bootstrap_not_timeOut
      oracles c depth (459_244_490_549 - 23_132) hlab compiled depthBound
      (by simpa only [bootstrapSteps_eq, hj_val] using not_timeOut)
    simpa only [bootstrapSteps_eq] using h
  have hcert_j : InitE.Certificate (baselineWithFiniteK bs32JointSlope3K)
      (.finite bs32JointSlope3K) := by
    simpa only [hj_val] using hcert_j_lit
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
  have hcert_s : InitE.Certificate (baselineWithFiniteK bs32SumSlope3K)
      (.finite bs32SumSlope3K) :=
    hmono (by decide) hcert_j
  have hcert_s_lit : InitE.Certificate (baselineWithFiniteK 500_060_306_876)
      (.finite 500_060_306_876) := by
    simpa only [hs_val] using hcert_s
  have hcert_inf : InitE.Certificate InitE.baselineSubmission .infinity := by
    refine ⟨rfl, InitE.baselineSubmission_admitted, ?_⟩
    intro input gas outcome events source covered
    obtain ⟨steps, _, execution⟩ := hcert_j.correct input gas outcome events source covered
    exact ⟨steps, trivial,
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission
        (.finite bs32JointSlope3K) input outcome events steps).mp execution⟩
  have htight : ¬ (bootstrapSteps + 3 * kPanBs32Joint ≤ bs32JointSlope3K - 1) := by
    rw [bootstrapSteps_eq]
    decide
  exact ⟨h8, hzero, hclk, hcert_j, hcert_j_lit, hcert_s, hcert_s_lit,
    hcert_inf, htight⟩

/-- Theorem 8 (`non_vacuous_and_tight`): Monotone upward certificate transfer from
`sixPassUnrolledCopyLoopK = 11_029_669_988` across all 8 dry-run tiers, all three joint block-gas
budgets, and both `bs+32` slope-`3x` budgets (`bs32JointSlope3K = 459,244,490,549` and
`bs32SumSlope3K = 500,060,306,876`), paired with 8-pass `ssaCseMidTailChain` `storeConstsAllowance = 0`. -/
theorem ssa_cse_unrolled_copyloop_lifts_to_bs32_joint_and_sum_slope3_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (temp argc : Nat) (b : Bool)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true) (k_sn : Nat)
    (hcert_unr : InitE.Certificate (baselineWithFiniteK sixPassUnrolledCopyLoopK)
      (.finite sixPassUnrolledCopyLoopK))
    (dryTier : DryRunCandidateTier) (subTier : YukonCandidateTier) :
    NoSt (ssaCseMidTailChain ac temp argc b p) = true ∧
    storeConstsAllowance (ssaCseMidTailChain ac temp argc b p) = 0 ∧
    stackRemoveMidTailClock (ssaCseMidTailChain ac temp argc b p) k_sn = k_sn + 1 ∧
    InitE.Certificate (baselineWithFiniteK sixPassUnrolledCopyLoopK)
      (.finite sixPassUnrolledCopyLoopK) ∧
    InitE.Certificate (baselineWithFiniteK sixPassReducedK) (.finite sixPassReducedK) ∧
    InitE.Certificate (baselineWithFiniteK isoReducedCandidateK) (.finite isoReducedCandidateK) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope3K) (.finite jointBlockGasSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK) (.finite perTxSixPassTargetK) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope6K) (.finite jointBlockGasSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK bs32JointSlope3K) (.finite bs32JointSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope12K) (.finite jointBlockGasSlope12K) ∧
    InitE.Certificate (baselineWithFiniteK bs32SumSlope3K) (.finite bs32SumSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK (selectDryRunCandidateK dryTier))
      (.finite (selectDryRunCandidateK dryTier)) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    (∀ K₁ K₂ : Nat, (baselineWithFiniteK K₁).K = .finite K₂ ↔ K₁ = K₂) := by
  have h8 : NoSt (ssaCseMidTailChain ac temp argc b p) = true :=
    t_ssa_cse_mid_tail_chain ac temp argc b p hp
  have hzero : storeConstsAllowance (ssaCseMidTailChain ac temp argc b p) = 0 :=
    noSt_allowance_zero _ h8
  have hclk : stackRemoveMidTailClock (ssaCseMidTailChain ac temp argc b p) k_sn = k_sn + 1 := by
    unfold stackRemoveMidTailClock C_sn D_sn
    rw [hzero]
    omega
  have hmid8 := mid_tail_unrolled_copyloop_lifts_to_joint_and_dry_run_tiers_non_vacuous_and_tight
    ac temp b p hp k_sn hcert_unr dryTier subTier
  have hcert_j6 : InitE.Certificate (baselineWithFiniteK jointBlockGasSlope6K)
      (.finite jointBlockGasSlope6K) := hmid8.2.2.2.2.2.2.2.2.1
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
  have hcert_bs32j : InitE.Certificate (baselineWithFiniteK bs32JointSlope3K)
      (.finite bs32JointSlope3K) :=
    hmono (by decide) hcert_j6
  have hcert_bs32s : InitE.Certificate (baselineWithFiniteK bs32SumSlope3K)
      (.finite bs32SumSlope3K) :=
    hmono (by decide) hcert_bs32j
  exact ⟨h8, hzero, hclk, hmid8.2.2.2.1, hmid8.2.2.2.2.1, hmid8.2.2.2.2.2.1,
    hmid8.2.2.2.2.2.2.1, hmid8.2.2.2.2.2.2.2.1, hcert_j6,
    hcert_bs32j, hmid8.2.2.2.2.2.2.2.2.2.1, hcert_bs32s,
    hmid8.2.2.2.2.2.2.2.2.2.2.1, hmid8.2.2.2.2.2.2.2.2.2.2.2.1,
    hmid8.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 9 (`non_vacuous_and_tight`): Master end-to-end synthesis of
`WordSsaCsePreserveNoStoreConsts` (`t_ssa_cse_mid_tail_chain`, `storeConstsAllowance_chain_zero`),
`WordMidTailNoStoreConstsBridge` (`storeConstsAllowance = 0`, `stackRemoveMidTailClock = k_sn + 1`),
and `GuestBs32BlockStorageEnvelope` (`kPanBs32Joint = 153,081,489,139`,
`kPanBs32Sum = 166,686,761,248`, `459,244,490,549 < 500,060,306,876 < 900,719,925,474`,
`0 sorryAx`, `zeroBoundedImportCount = 0`). -/
theorem end_to_end_word_ssa_cse_six_pass_and_bs32_envelope_master_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (temp argc : Nat) (b : Bool)
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
    NoSt (ssaCseMidTailChain ac temp argc b p) = true ∧
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance (ssaCseMidTailChain ac temp argc b p) = 0 ∧
    storeConstsAllowance (ssaCseMidTailChain ac temp argc b p) = 0 ∧
    stackRemoveMidTailClock (ssaCseMidTailChain ac temp argc b p) k_sn = k_sn + 1 ∧
    threePassSlope = 3 ∧
    3 * kPanBs32Joint < yukon ∧
    3 * kPanBs32Sum < yukon ∧
    459_244_490_549 < 500_060_306_876 ∧
    500_060_306_876 < 900_719_925_474 ∧
    InitE.Certificate (baselineWithFiniteK sixPassReducedK) (.finite sixPassReducedK) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope3K) (.finite jointBlockGasSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK) (.finite perTxSixPassTargetK) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope6K) (.finite jointBlockGasSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK bs32JointSlope3K) (.finite bs32JointSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope12K) (.finite jointBlockGasSlope12K) ∧
    InitE.Certificate (baselineWithFiniteK bs32SumSlope3K) (.finite bs32SumSlope3K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    validFiniteClaim (selectDryRunCandidateK dryTier) (selectDryRunClaimJson dryTier) = true ∧
    (selectDryRunClaimJson dryTier).utf8ByteSize ≤ MAX_CLAIM_BYTES ∧
    yukonScore bs32JointSlope3K minutes < 2 ^ 53 - 1 ∧
    yukonScore bs32SumSlope3K minutes < 2 ^ 53 - 1 ∧
    zeroBoundedImportCount = 0 ∧
    (stackRemoveMidTailClock (ssaCseMidTailChain ac temp argc b p) k_sn ≤ k_sn + 1 ↔ True) := by
  have h8 : NoSt (ssaCseMidTailChain ac temp argc b p) = true :=
    t_ssa_cse_mid_tail_chain ac temp argc b p hp
  have h8_zero_ssa :
      WordSsaCsePreserveNoStoreConsts.storeConstsAllowance (ssaCseMidTailChain ac temp argc b p) = 0 :=
    storeConstsAllowance_chain_zero ac temp argc b p hp
  have hzero : storeConstsAllowance (ssaCseMidTailChain ac temp argc b p) = 0 :=
    noSt_allowance_zero _ h8
  have hclk : stackRemoveMidTailClock (ssaCseMidTailChain ac temp argc b p) k_sn = k_sn + 1 := by
    unfold stackRemoveMidTailClock C_sn D_sn
    rw [hzero]
    omega
  have hmid9 := end_to_end_word_mid_tail_joint_block_gas_and_yukon_dry_run_master_non_vacuous_and_tight
    ac temp b p hp k_sn ctx lprog labels dryTier oracles c depth minutes hlab compiled depthBound
    not_timeOut_sixPassReduced
  have hcert_j6 : InitE.Certificate (baselineWithFiniteK jointBlockGasSlope6K)
      (.finite jointBlockGasSlope6K) := hmid9.2.2.2.2.2.2.2.2.1
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
  have hcert_bs32j : InitE.Certificate (baselineWithFiniteK bs32JointSlope3K)
      (.finite bs32JointSlope3K) :=
    hmono (by decide) hcert_j6
  have hcert_bs32s : InitE.Certificate (baselineWithFiniteK bs32SumSlope3K)
      (.finite bs32SumSlope3K) :=
    hmono (by decide) hcert_bs32j
  have hbs32j_rep : yukonScore bs32JointSlope3K minutes < 2 ^ 53 - 1 :=
    yukonScore_lt_two_pow_53_sub_one (by decide)
  have hbs32s_rep : yukonScore bs32SumSlope3K minutes < 2 ^ 53 - 1 :=
    yukonScore_lt_two_pow_53_sub_one (by decide)
  refine ⟨h8, h8_zero_ssa, hzero, hclk, rfl, slope3_ok.1, slope3_ok.2, by decide, by decide,
    hmid9.2.2.2.2.2.1, hmid9.2.2.2.2.2.2.1, hmid9.2.2.2.2.2.2.2.1, hcert_j6,
    hcert_bs32j, hmid9.2.2.2.2.2.2.2.2.2.1, hcert_bs32s,
    hmid9.2.2.2.2.2.2.2.2.2.2.1, hmid9.2.2.2.2.2.2.2.2.2.2.2.1,
    hmid9.2.2.2.2.2.2.2.2.2.2.2.2.1, hbs32j_rep, hbs32s_rep, rfl, ?_⟩
  rw [hclk]
  simp

#print axioms ssa_cse_eight_pass_chain_preserves_noSt_and_zero_allowance_non_vacuous_and_tight
#print axioms word_prog_ssa_cse_chain_stack_remove_clock_and_slope_three_non_vacuous_and_tight
#print axioms compiled_loop_to_word_ssa_cse_chain_and_stack_remove_semantic_clock_non_vacuous_and_tight
#print axioms ssa_cse_bs32_block_storage_envelope_slope3_under_yukon_non_vacuous_and_tight
#print axioms ssa_cse_complete_strict_budget_hierarchy_and_gaps_non_vacuous_and_tight
#print axioms ssa_cse_yukonScore_strict_order_with_bs32_envelopes_non_vacuous_and_tight
#print axioms ssa_cse_bs32_slope3_certificate_bridge_non_vacuous_and_tight
#print axioms ssa_cse_unrolled_copyloop_lifts_to_bs32_joint_and_sum_slope3_non_vacuous_and_tight
#print axioms end_to_end_word_ssa_cse_six_pass_and_bs32_envelope_master_non_vacuous_and_tight

end InitECandidate.Solver.WordSsaCseSixPassBridge
