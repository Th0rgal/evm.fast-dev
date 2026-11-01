import InitECandidate.Solver.Wave8GuestInv.Deliveries.GBODY_RUNFRAMES_SOL.RunFramesDefs
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.RunFramesRace
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

theorem secondwalk
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
      evmFp t < F0 → evmPot t < p0) :
    BHoare (GMid p0 R0 L0 F0) rfSecond (GQ p0) := by
  simp only [rfFirst, rfSecond, rfBody, rfCode, sourceFunctionEntry,
    Guest.Software.guestFn_run_frames,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  refine BHoare.ite ?_ ?_ (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
  · refine BHoare.seq (R := GPdone p0 R0 L0 F0)
      (BHoare.skip fun t hP => ⟨fun _ => ?_, fun h => absurd rfl h⟩) ?_
    · rcases hP.1 with ⟨hp, hd, _⟩ | ⟨_, _, hz⟩
      · exact ⟨hp, hd⟩
      · exact absurd hz (condTrue_local_ne0 hP.2)
    refine BHoare.seq (R := GPepi R0 L0 F0) ?_ ?_
    · refine BHoare.of_bound ?_ ?_
      · have hb : TerminatingProgBoundedOn (GPdone p0 R0 L0 F0) _ _ := TerminatingProgBoundedOn.call_on be none []
          (P := GPdone p0 R0 L0 F0)
          (by
            intro F t values body callee ret _ hP _ _
            exact guestInv_callEntry t callee (evmInv_guestInv t hP.1.1))
        intro F u hc hi
        simpa [InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, walkCost, charge_op_dispatch, charge_finish_child, charge_frame_epilogue, charge_frame_exception] using hb u hc hi
      refine Hoare.call0 (Pc := fun s => EvmInv s ∧ EvmDone s) h3 ?_ ?_
        (fun r t h h' => ⟨fun hr => absurd hr h, fun _ => gq_other p0 r t h h'⟩)
      · intro F t values body callee ret _ hP _ _
        exact ⟨evmInv_entry callee hP.1.1,
          (evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).2 hP.2⟩
      · intro F t callee post v _ hP hq
        obtain ⟨hi, hd, hlen, hR⟩ := hq v rfl
        obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee)
          rfl rfl
        obtain ⟨-, fR, fL, -⟩ := evm_congr (s := post) (t := { post with locals := t.locals })
          rfl rfl
        refine ⟨fun _ => ⟨evmInv_locals _ hi,
          (evmDone_congr (s := post) (t := { post with locals := t.locals }) rfl rfl).2 hd,
          ?_, ?_, ?_⟩, fun h => absurd rfl h⟩
        · rw [fL, hlen, eL]; exact hP.1.2.2.2.1
        · rw [fR]; exact hR.trans (le_of_eq (eR.trans hP.1.2.2.1))
        · rw [← hP.1.2.2.2.2, evmFp_done hP.2, hP.1.2.2.2.1]
    · refine BHoare.ite ?_ ?_ (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
      · -- outermost frame: `ev`, `cur_cont` restored, `go := 0`
        refine BHoare.seq (R := fun _ => True)
          (BHoare.assign (fun _ _ _ _ => ⟨fun _ => trivial, fun h => absurd rfl h⟩)
            (fun _ _ => ⟨fun h => absurd h (by simp), fun _ => gq_other p0 _ _ (by simp)
              (by simp)⟩)) ?_
        refine BHoare.seq (R := fun _ => True)
          (BHoare.assign (fun _ _ _ _ => ⟨fun _ => trivial, fun h => absurd rfl h⟩)
            (fun _ _ => ⟨fun h => absurd h (by simp), fun _ => gq_other p0 _ _ (by simp)
              (by simp)⟩)) ?_
        refine BHoare.assign (fun t v _ hv => ?_) (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
        cases evalAt_const t 0 v hv
        intro _
        right
        show locN (setVarHOLFinite (ofString "go") (.val (.word 0)) t) "go" = 0
        rw [locN_setVar_same]; rfl
      · -- pop the done child
        refine BHoare.dec (names := ["go"]) (P' := GPfin R0 L0 F0) (by decide) ?_ ?_
          (gq_postLocals p0) (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
        · intro F t v hP hv
          cases evalAt_const t 0 v hv
          obtain ⟨⟨hi, hd, hlen, hR, hF⟩, hk⟩ := hP
          obtain ⟨-, fR, fL, -⟩ := evm_congr (s := t) (t := setVarHOLFinite _ _ t) rfl rfl
          refine ⟨⟨evmInv_setVar _ _ hi,
            (evmDone_congr (s := t) (t := setVarHOLFinite _ _ t) rfl rfl).2 hd,
            fL.trans hlen, (le_of_eq fR).trans hR, hF⟩, ?_⟩
          show memW t (globN t "cur_cont" + 16) ≠ 0
          have := condFalse_eq0 hk
          simpa using this
        · refine BHoare.of_bound ?_ ?_
          · have hb : TerminatingProgBoundedOn (GPfin R0 L0 F0) _ _ := TerminatingProgBoundedOn.callHandle_on bf
              (fun t hP => evmInv_guestInv t hP.1.1) none (ofString "EvmErr") (ofString "err2")
              (TerminatingProgBoundedOn.call_guestInv bx none [(.var .local (ofString "err2"))]) []
              (P := GPfin R0 L0 F0)
              (by
                intro F t values body callee ret _ hP _ _
                exact ⟨evmInv_entry callee hP.1.1,
                  (evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).2
                    hP.1.2.1, hP.2⟩)
            intro F u hc hi
            simpa [InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, walkCost, charge_op_dispatch, charge_finish_child, charge_frame_epilogue, charge_frame_exception, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb u hc hi
          refine Hoare.callH
            (Pc := fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0)
            (Ph := GPh4 R0 L0 F0) h4 ?_ ?_ ?_ ?_ (fun r t h h' => gq_other p0 r t h h')
          · intro F t values body callee ret _ hP _ _
            exact ⟨evmInv_entry callee hP.1.1,
              (evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).2
                hP.1.2.1, hP.2⟩
          · intro F t callee post v _ hP hq
            obtain ⟨hi, hlen, hR⟩ := hq (Or.inl ⟨v, rfl⟩)
            obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee)
              rfl rfl
            obtain ⟨-, fR, fL, fF⟩ := evm_congr (s := post)
              (t := { post with locals := t.locals }) rfl rfl
            intro _
            left
            refine ⟨evmInv_locals _ hi, hfin _ (evmInv_locals _ hi) ?_ ?_⟩
            · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.1.2.2.2.1)
            · rw [fF]
              have h1 := evmFp_le post
              have h2 := hP.1.2.2.2.2
              rw [eL, hP.1.2.2.1] at hlen
              omega
          · intro F t callee post v _ hP hq
            obtain ⟨hi, hlen, hR⟩ := hq (Or.inr ⟨v, rfl⟩)
            obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee)
              rfl rfl
            obtain ⟨-, fR, fL, -⟩ := evm_congr (s := post)
              (t := setVarHOLFinite (ofString "err2") v { post with locals := t.locals }) rfl rfl
            refine ⟨evmInv_setVar _ _ (evmInv_locals _ hi), ?_, ?_, hP.1.2.2.2.2⟩
            · rw [fL, hlen, eL]; exact hP.1.2.2.1
            · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.1.2.2.2.1)
          · refine Hoare.call0 (Pc := EvmInv) h2 ?_ ?_ (fun r t h h' => gq_other p0 r t h h')
            · intro F t values body callee ret _ hP _ _
              exact evmInv_entry callee hP.1
            · intro F u callee post v _ hP hq
              obtain ⟨hi, hd, hlen, hR⟩ := hq v rfl
              obtain ⟨-, eR, eL, -⟩ := evm_congr (s := u)
                (t := callEntryStateHOLFinite u callee) rfl rfl
              obtain ⟨-, fR, fL, fF⟩ := evm_congr (s := post)
                (t := { post with locals := u.locals }) rfl rfl
              intro _
              left
              refine ⟨evmInv_locals _ hi, hfin _ (evmInv_locals _ hi) ?_ ?_⟩
              · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.2.2.1)
              · rw [fF, evmFp_done hd, hlen, eL]
                have := hP.2.1
                have := hP.2.2.2
                omega
  · refine BHoare.skip (fun t hP => fun _ => ?_)
    rcases hP.1 with ⟨_, _, hn⟩ | ⟨hi, hp, _⟩
    · exact absurd (condFalse_local_ne0 hP.2) hn
    · exact Or.inl ⟨hi, hp⟩

end InitECandidate.Solver.Wave8GuestInv.RunFramesRace
