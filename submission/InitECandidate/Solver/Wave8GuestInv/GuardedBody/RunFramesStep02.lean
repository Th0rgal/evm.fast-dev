import InitECandidate.Solver.Wave8GuestInv.GuardedBody.RunFramesCuts
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

open InitECandidate.Solver.Wave8GuestInv.RunFramesRace

/-- Opcode return and EvmErr handling. -/
theorem runFramesStep02
    (bf : TerminatingFunBoundedOn FinishReady (ofString "finish_child") K.finish_child)
    (be : TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.frame_epilogue)
    (bx : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.frame_exception)
    (bd : TerminatingFunBoundedOn EvmRun (ofString "op_dispatch") K.op_dispatch)
    (h1 : FunSpec (fun s => EvmInv s ∧ ¬ EvmDone s)
      (fun s r post =>
        ((∃ v, r = some (.returned v)) → EvmInv post ∧ evmPot post < evmPot s) ∧
        (IsEvmErr r → EvmInv post ∧ (evmChain post).length = (evmChain s).length ∧
          evmR post ≤ evmR s))
      (ofString "op_dispatch"))
    (h2 : FunSpec EvmInv
      (OnReturn fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "frame_exception"))
    (h3 : FunSpec (fun s => EvmInv s ∧ EvmDone s)
      (OnReturn fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "frame_epilogue"))
    (h4 : FunSpec (fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0)
      (fun s r post => ((∃ v, r = some (.returned v)) ∨ IsEvmErr r) →
        EvmInv post ∧ (evmChain post).length + 1 = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "finish_child"))
    (p0 R0 L0 F0 : Nat)
    (hfin : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), EvmInv t → evmR t ≤ R0 →
      evmFp t < F0 → evmPot t < p0)
    (hreturn : DispatchReturnCut p0 R0 L0 F0) :
    BHoare (GPdisp p0 R0 L0 F0) rfDispatch (GA p0 R0 L0 F0) := by
  simp only [rfDispatch, rfFirst, rfSecond, rfBody, rfCode, sourceFunctionEntry,
    Guest.Software.guestFn_run_frames,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  refine BHoare.of_bound ?_ ?_
  · have hb : TerminatingProgBoundedOn (GPdisp p0 R0 L0 F0) _ _ := TerminatingProgBoundedOn.callHandle_on bd
      (fun t hP => evmInv_guestInv t hP.1.1) none (ofString "EvmErr") (ofString "err")
      (TerminatingProgBoundedOn.call_guestInv bx none [(.var .local (ofString "err"))])
      [.loadByte (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 48]),
        .var .local (ofString "pc")])]
      (P := GPdisp p0 R0 L0 F0)
      (by
        intro F t values body callee ret _ hP _ _
        exact ⟨evmInv_entry callee hP.1.1, fun hd => hP.2.2.1
          ((evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).1 hd)⟩)
    intro F u hc hi
    simpa [InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, walkCost, charge_op_dispatch, charge_finish_child, charge_frame_epilogue, charge_frame_exception, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb u hc hi
  refine Hoare.callH (Pc := fun s => EvmInv s ∧ ¬ EvmDone s) (Ph := GPh R0 L0 F0)
    h1 ?_ ?_ ?_ ?_ (fun r t h h' => ga_other p0 R0 L0 F0 r t h h')
  · intro F t values body callee ret _ hP _ _
    exact ⟨evmInv_entry callee hP.1.1, fun hd => hP.2.2.1
      ((evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).1 hd)⟩
  · intro F t callee post v _ hP hq
    obtain ⟨hi, hlt⟩ := hq.1 ⟨v, rfl⟩
    exact hreturn t callee post hP hi hlt
  · intro F t callee post v _ hP hq
    obtain ⟨hi, hlen, hR⟩ := hq.2 ⟨v, rfl⟩
    obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee)
      rfl rfl
    obtain ⟨-, fR, fL, -⟩ := evm_congr (s := post)
      (t := setVarHOLFinite (ofString "err") v { post with locals := t.locals }) rfl rfl
    refine ⟨evmInv_setVar _ _ (evmInv_locals _ hi), ?_, ?_, ?_, hP.2.2.2⟩
    · rw [fL, hlen, eL]; exact hP.1.2.2.2.1
    · rw [fR]; exact hR.trans (le_of_eq (eR.trans hP.1.2.2.1))
    · rw [locN_setVar_ne _ "done" (ofString "err") _ (by decide)]; exact hP.2.1
  · refine Hoare.call0 (Pc := EvmInv) h2 ?_ ?_
      (fun r t h h' => ga_other p0 R0 L0 F0 r t h h')
    · intro F t values body callee ret _ hP _ _
      exact evmInv_entry callee hP.1
    · intro F u callee post v _ hP hq
      obtain ⟨hi, hd, hlen, hR⟩ := hq v rfl
      obtain ⟨-, eR, eL, -⟩ := evm_congr (s := u)
        (t := callEntryStateHOLFinite u callee) rfl rfl
      obtain ⟨fp, fR, fL, fF⟩ := evm_congr (s := post)
        (t := { post with locals := u.locals }) rfl rfl
      refine ⟨fun _ => Or.inr ⟨evmInv_locals _ hi, ?_, hP.2.2.2.1⟩,
        fun h => absurd rfl h⟩
      apply hfin _ (evmInv_locals _ hi)
      · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.2.2.1)
      · rw [fF, evmFp_done hd, hlen, eL, hP.2.1, hP.2.2.2.2]; omega

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
