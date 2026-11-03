import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M05.WorldLemmas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.wk_rlp_encode_bytes
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.wk_rlp_encode_word
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.Exec
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M25.rt_alloc
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.rt_lst_new

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard01

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

private theorem lookup_alloc :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
  lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

private theorem lookupCode_one_word {fname p1 : MlS} {body : ProgHOL 64} {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one)], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, .one)) :
    ∃ w1 : BitVec 64,
      vals = [.val (.word w1)] ∧
      L.lookup p1 = some (.val (.word w1)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L .one hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | _⟩
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    exact ⟨w1, rfl, by rw [← hx]; simp⟩
  · simp at hx

private theorem worldOwned_allocated {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hWT : WorldTypedWith s S Nd) {o : Ivl} (ho : o ∈ worldOwned s S Nd) :
    o.2 = 0 ∨ Allocated s o := by
  obtain ⟨hT, _, hF, hTr⟩ := hWT
  unfold worldOwned at ho
  rcases List.mem_append.1 ho with h12 | hnd
  · rcases List.mem_append.1 h12 with htab | hfix
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 htab
      exact Or.inr (((hT.2.1 t ht).2 o hfp).1)
    · rcases hF.1 o hfix with h0 | ⟨hal, _⟩
      · exact Or.inl h0
      · exact Or.inr hal
  · unfold nodeExtents at hnd
    obtain ⟨n, hn, hni⟩ := List.mem_flatMap.1 hnd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hni
    rcases hni with rfl | rfl
    · exact Or.inr (hTr.1.1 n hn).2.1
    · unfold nodePath
      split_ifs with hp
      · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hp.1 with h0 | ⟨_, hal, _, _⟩
        · exact absurd h0 hp.2
        · exact Or.inr hal
      · exact Or.inl rfl

private theorem evaluate_call_trap_with_no_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (codeVal : BitVec 64)
    (hcode : state.code = originalRuntimeCode) :
    ¬ Resumes (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal])).1 := by
  rw [evaluateHOLFiniteState_call]
  have hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const codeVal] =
      some [.val (.word codeVal)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlookup := pan_one_word_lookup state.code.lookup (ofString "trap_with") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_trap_with) codeVal (by rw [hcode]; exact lookup_trap_with)
  rw [hargs]; dsimp only; rw [hlookup]; dsimp only
  split
  · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
  · have hout := evaluate_trap_with_body_outcomes
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
    rcases hbody : evaluateHOLFiniteState
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
      (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
    rw [hbody] at hout
    cases res with
    | none => exact absurd rfl hout.1
    | some r =>
      cases r with
      | returned v => exact absurd rfl (hout.2.1 v)
      | exception eid ev =>
        rintro (⟨_, h⟩ | ⟨e', v', h, hne⟩)
        · simp at h
        · simp at h; obtain ⟨rfl, rfl⟩ := h; exact hout.2.2 eid ev hne rfl
      | «break» | «continue» | error | timeOut | finalFfi _ =>
        rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

private theorem evaluate_alloc_body_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hres : Resumes (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)).1) :
    ∃ rv, (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)).1 = some (.returned rv) := by
  have hbody_eq : sourceFnBody Guest.Software.guestFn_alloc =
      .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip)
              (.seq
                (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hres ⊢
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only at hres ⊢
  rw [hp_eval] at hres ⊢
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only at hres ⊢
  rw [if_pos hsh_p] at hres ⊢
  dsimp only at hres ⊢
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "p" ≠ ofString "n" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (cMax - p).toNat < n.toNat then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    rfl
  by_cases hcmp1 : (cMax - p).toNat < n.toNat
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1] at hres
    have hno_none := evaluate_call_trap_with_no_none pState 1 hcode
    have hno_res := evaluate_call_trap_with_no_resumes pState 1 hcode
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_res hres
    cases r1 with
    | none => exact absurd rfl hno_none
    | some _ => exact False.elim (hno_res hres)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1] at hres ⊢
    dsimp only at hres ⊢
    rw [evaluateHOLFiniteState_dec_total] at hres ⊢
    let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (alloc_q_word_eq p n)
    dsimp only at hres ⊢
    rw [hq_eval] at hres ⊢
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only at hres ⊢
    rw [if_pos hsh_q] at hres ⊢
    dsimp only at hres ⊢
    let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
        show ofString "q" ≠ ofString "p" by decide]
    rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.const cMax) (.var .local (ofString "q"))) =
        some (.val (.word (if cMax.toNat < q.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hq_loc, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    by_cases hcmp2 : cMax.toNat < q.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2] at hres
      have hno_none := evaluate_call_trap_with_no_none qState 1 hcode
      have hno_res := evaluate_call_trap_with_no_resumes qState 1 hcode
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_res hres
      cases r2 with
      | none => exact absurd rfl hno_none
      | some _ => exact False.elim (hno_res hres)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2]
      dsimp only
      have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := hp_lookup
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "p")))) =
          (some (.returned (.val (.word p))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [heval_end]
      exact ⟨.val (.word p), rfl⟩

private theorem arenaReady_update_heap_ptr {F : Type} {s : PanSemStateFiniteExact 64 F} {q : BitVec 64}
    (hAR : ArenaReady s) (hq_lo : sourceBase ≤ q.toNat) (hq_hi : q.toNat ≤ heapLimit)
    (hq8 : q.toNat % 8 = 0) :
    ArenaReady { s with globals := s.globals.update (ofString "heap_ptr", .val (.word q)) } := by
  obtain ⟨hG, _, _, hf1, hf2, hf3, _, hf8, hs8⟩ := hAR
  let s' := { s with globals := s.globals.update (ofString "heap_ptr", .val (.word q)) }
  have hhp_eq : globN s' "heap_ptr" = q.toNat := by
    simp [s', globN, HolFiniteMapExact.lookup_update, FUPDATE]
  have hfmp_eq : globN s' "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    simp [s', globN, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
  have hsp_eq : globN s' "scratch_ptr" = globN s "scratch_ptr" := by
    simp [s', globN, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
  refine ⟨⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩, ?_⟩
  unfold ArenaOK; change sourceBase ≤ globN s' "heap_ptr" ∧ _
  rw [hhp_eq, hfmp_eq, hsp_eq]
  exact ⟨hq_lo, hq_hi, hf1, hf2, hf3, hq8, hf8, hs8⟩

theorem «wk_alloc» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc") := by
  refine ⟨_, _, _, lookup_alloc, ?_⟩
  intro F s hcode hWOK ⟨vals, hl⟩ _hnt hres
  have hAR : ArenaReady s := hWOK.1
  obtain ⟨p, hp_look, hp_nat⟩ := Wave8Contracts.M05.global_word_of_pos s "heap_ptr"
    (by have := hAR.2.1; rw [Wave8Contracts.M05.sourceBase_val] at this; omega)
  obtain ⟨nw, _, hn_look⟩ := lookupCode_one_word lookup_alloc hl
  have hn_nat : locN s "n" = nw.toNat := by simp [locN, hn_look]
  obtain ⟨rv, hret⟩ := evaluate_alloc_body_resumes s p nw hcode hp_look hn_look hres
  have hp_le : p.toNat ≤ cMax.toNat := by
    have : cMax.toNat = heapLimit := rfl
    rw [this, hp_nat]; exact hAR.2.2.1
  have hgen := Wave8GuestInv.M13.evaluate_alloc_body_general s p nw hcode hp_le hp_look hn_look rv hret
  obtain ⟨rfl, hg_post, hm_post, hpq, hqc, hq8⟩ := hgen
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2
  set q := (p + (nw + 7)) &&& ((0 : BitVec 64) - 8)
  change post.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) at hg_post
  change p.toNat + nw.toNat ≤ q.toNat at hpq
  change q.toNat ≤ cMax.toNat at hqc
  change q.toNat % 8 = 0 at hq8
  have hcMax_eq : cMax.toNat = heapLimit := rfl
  have hp_lo : sourceBase ≤ p.toNat := by rw [hp_nat]; exact hAR.2.1
  have hgb := Wave8GuestInv.M13.evaluateHOLFiniteState_guestInv_be s (sourceFnBody Guest.Software.guestFn_alloc) hAR.1
  have hAR_upd := arenaReady_update_heap_ptr (q := q) hAR (by omega) (by rw [← hcMax_eq]; exact hqc) hq8
  have hgN : ∀ nm, globN post nm = globN { s with globals := s.globals.update (ofString "heap_ptr", .val (.word q)) } nm :=
    fun nm => by dsimp only [globN]; rw [hg_post]
  have hAR_post : ArenaReady post := ⟨hgb.1, by
    have hok := hAR_upd.2; unfold ArenaOK at hok ⊢; simpa only [hgN] using hok⟩
  have hhp_post : globN post "heap_ptr" = q.toNat := by
    unfold globN; rw [hg_post, HolFiniteMapExact.lookup_update]; simp [FUPDATE]
  have hsp_post : globN post "scratch_ptr" = globN s "scratch_ptr" := by
    simp [globN, hg_post, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by
    rw [← hp_nat, hhp_post]; exact le_trans (Nat.le_add_right _ _) hpq
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hsp_post]
  have hG : GlobalsKept ["heap_ptr"] s post := by
    intro k hk
    have hne : k ≠ ofString "heap_ptr" := fun h => hk (by simp [h])
    rw [hg_post]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
  have hK : RecordsKept (fun _ => []) Wave8Contracts.M05.stdKeep s post := by
    intro _ _ _ _ _ _
    simp [memW, hm_post]
  refine ⟨hAR_post, hh, hG, hK, fun S Nd hWT _ => ?_⟩
  have hcell : Wave8Contracts.M05.SameTypedCells s post S Nd :=
    ⟨hgb.2, hgb.1.memaddrs.trans hAR.1.memaddrs.symm, hAR.1.memaddrs,
     fun _ _ => by rw [hm_post],
     fun _ _ _ _ => by rw [hm_post],
     fun b _ _ => by unfold memB; rw [hm_post, hgb.2]⟩
  have hcore_eq : ∀ g ∈ Wave8Contracts.M05.coreWorldGlobals, globN post g = globN s g := by
    intro g hg
    have hne : ofString g ≠ ofString "heap_ptr" := by revert g hg; decide
    exact (Wave8Contracts.M05.globN_eq_of_lookup_eq (hG (ofString g) (by simp [hne]))).symm
  have hgb_eq : ∀ gn ∈ globalBuffers, globN post gn.1 = globN s gn.1 := by
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
    exact (Wave8Contracts.M05.globN_eq_of_lookup_eq (hG (ofString gn.1) (by simp [hne]))).symm
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [Wave8Contracts.M05.blockOutObjects_eq hAR.2 hWT.2.2.1 hcell (hcore_eq "bo" (by decide)),
        Wave8Contracts.M05.balObjects_eq hAR.2 hWT.1 hWT.2.2.1 hcell (hcore_eq "bal_accounts" (by decide)),
        hcore_eq "journal" (by decide),
        hcore_eq "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    rw [hgb_eq gn hgn]
  have hFT_post := Wave8Contracts.M05.fixedTyped_of_eq hAR_post hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, hOG⟩ := Wave8Contracts.M05.worldTypedWith_congr_w1 hAR hAR_post hh hsc hcore_eq hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hwo_eq : worldOwned post S Nd = worldOwned s S Nd := by
    unfold worldOwned
    rw [hfeq, Wave8Contracts.M05.nodeExtents_eq hWT.2.2.2.1 hcell]
    congr 2
    apply List.flatMap_congr
    intro t ht
    exact Wave8Contracts.M05.htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  refine ⟨S, Nd, fun _ h => h, hWT_post, hOG, fun _ _ _ => by rw [hm_post], ?_⟩
  intro v hv
  rw [hret] at hv
  injection hv with hv'
  injection hv' with hv''
  subst hv''
  obtain ⟨params_rt, body_rt, ret_rt, hl_rt, hrt_spec⟩ := Wave8Contracts.M25.rt_alloc
  have hb_eq : body_rt = sourceFnBody Guest.Software.guestFn_alloc := by
    rw [lookup_alloc] at hl_rt; injection hl_rt with hl_rt'; exact (congrArg (fun x => x.2.1) hl_rt').symm
  have hr_eq : ret_rt = .one := by
    rw [lookup_alloc] at hl_rt; injection hl_rt with hl_rt'; exact (congrArg (fun x => x.2.2) hl_rt').symm
  subst hb_eq hr_eq
  obtain ⟨w', hw'_eq, _, _, hFB⟩ := hrt_spec s hcode hAR ⟨vals, hl⟩ _hnt _ hret
  injection hw'_eq with hw'_eq'
  injection hw'_eq' with hw'_eq''
  subst hw'_eq''
  refine ⟨p, rfl, ?_⟩
  intro blk hblk o ho
  simp only [List.mem_singleton] at hblk
  subst hblk
  rw [hwo_eq] at ho
  rcases worldOwned_allocated hWT ho with ho0 | hal
  · exact Or.inr (Or.inl ho0)
  · exact FreshBlock.disj_allocated hFB hAR.2 hAR_post.2 hal

private theorem lookup_bal_list_remove_idx :
    originalRuntimeCode.lookup (ofString "bal_list_remove_idx") =
      some ([(ofString "l", .one), (ofString "esz", .one), (ofString "idx", .one)],
        sourceFnBody Guest.Software.guestFn_bal_list_remove_idx, .one) :=
  lookup_of_guestAst_getElem 424 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bal_list_remove_idx) rfl

private theorem lookup_bal_remove_change :
    originalRuntimeCode.lookup (ofString "bal_remove_change") =
      some ([(ofString "addr", .one), (ofString "which", .one), (ofString "esz", .one), (ofString "idx", .one)],
        sourceFnBody Guest.Software.guestFn_bal_remove_change, .one) :=
  lookup_of_guestAst_getElem 425 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bal_remove_change) rfl

private theorem lookup_htab_find_leaf :
    originalRuntimeCode.lookup (ofString "htab_find_leaf") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_find_leaf, .one) :=
  lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_find_leaf) rfl

private theorem lookup_htab_get :
    originalRuntimeCode.lookup (ofString "htab_get") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_get, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 132 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_get) rfl

private theorem lookup_memeq :
    originalRuntimeCode.lookup (ofString "memeq") =
      some ([(ofString "a", .one), (ofString "b", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memeq, .one) :=
  lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memeq) rfl

private theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

private theorem funLocFrame_htab_find_leaf : Wave8GuestInv.M13.FunLocFrame (ofString "htab_find_leaf") :=
  Wave8GuestInv.M13.funLocFrame_of_locOnlyW 131 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_find_leaf rfl rfl

private theorem funLocFrame_memeq : Wave8GuestInv.M13.FunLocFrame (ofString "memeq") :=
  Wave8GuestInv.M13.funLocFrame_of_locOnlyW 18 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_memeq rfl rfl

private theorem funLocFrame_htab_get : Wave8GuestInv.M13.FunLocFrame (ofString "htab_get") := by
  refine ⟨_, _, _, lookup_htab_get, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htab_get,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  apply Wave8GuestInv.M13.locFrame_decCall hcode funLocFrame_htab_find_leaf
  intro s1 hc1
  apply Wave8GuestInv.M13.locFrame_seq (Wave8GuestInv.M13.locFrameW_eval _ rfl s1)
  intro s2 hs2
  have hc2 : s2.code = originalRuntimeCode := hs2.code.trans hc1
  refine Wave8GuestInv.M13.locFrame_dec _ _ _ (fun _ => ?_)
  refine Wave8GuestInv.M13.locFrame_dec _ _ _ (fun _ => ?_)
  refine Wave8GuestInv.M13.locFrame_dec _ _ _ (fun _ => ?_)
  apply Wave8GuestInv.M13.locFrame_decCall hc2 funLocFrame_memeq
  intro s6 _
  exact Wave8GuestInv.M13.locFrameW_eval _ rfl s6

private theorem htab_get_ret_in_values {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw kw : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hk : s.locals.lookup (ofString "key") = some (.val (.word kw)))
    (hW : HtabWF s tw.toNat)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_get)).1 = some (.returned v)) :
    ∃ f0 f1 : BitVec 64, v = .rStruct [.val (.word f0), .val (.word f1)] ∧
      (f0 ≠ 0 → f1.toNat ∈ htabValues s tw.toNat) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_htab_get,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map] at hret
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "t"), .var .local (ofString "key")] =
      some [.val (.word tw), .val (.word kw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ht, hk]
  have hlook := pan_two_word_lookup s.code.lookup (ofString "htab_find_leaf")
    (ofString "t") (ofString "key") (sourceFnBody Guest.Software.guestFn_htab_find_leaf) tw kw
    (by decide) (by rw [hcode]; exact lookup_htab_find_leaf)
  rw [hargs] at hret; dsimp only at hret; rw [hlook] at hret; dsimp only at hret
  by_cases hcz : s.clock = 0
  · simp [hcz] at hret
  · rw [if_neg hcz] at hret
    let cmap := (HolFiniteMapExact.empty.update (ofString "t", ValueHOL.val (.word tw))).update
      (ofString "key", ValueHOL.val (.word kw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_t : ent.locals.lookup (ofString "t") = some (.val (.word tw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "key" ≠ ofString "t" by decide]
    have hent_W : HtabWF ent tw.toNat := by
      simpa [ent, callEntryStateHOLFinite, htabWF_with_locals] using hW
    rcases hfl : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_htab_find_leaf) with ⟨rfl_res, s_fl⟩
    rw [hfl] at hret
    rcases rfl_res with _ | rfl_r
    · simp at hret
    · cases rfl_r with
      | returned v_fl =>
        obtain ⟨lw, rfl, hlf_fl, hfl_spec⟩ :=
          SoloHtabSet.find_leaf_spec_wf ent tw hent_t hent_W v_fl (by rw [hfl])
        have hfl_lf' : SoloHtabSet.LocFrame s s_fl := by
          unfold SoloHtabSet.LocFrame at hlf_fl ⊢
          rw [hlf_fl]; rfl
        dsimp only at hret
        have hsh1 : (shapeEqHOL (shapeOfHOLExact (.val (.word lw))) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word lw))) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh1] at hret; dsimp only at hret
        let s1 := setVarHOLFinite (ofString "leaf") (.val (.word lw)) { s_fl with locals := s.locals }
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
        have hs1_lw : s1.locals.lookup (ofString "leaf") = some (.val (.word lw)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hev_lw0 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
            (.cmp .equal (.var .local (ofString "leaf")) (.const 0)) =
            some (.val (.word (if lw = 0 then 1 else 0))) := by
          simp [evalHOLExact, hs1_lw, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [hev_lw0] at hret; dsimp only at hret
        by_cases hlw0 : lw = 0
        · rw [if_pos hlw0, if_neg (by decide : ¬ ((1 : BitVec 64) = 0)), evaluateHOLFiniteState_return] at hret
          simp [evalHOLExact, evalListHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
          exact ⟨0, 0, hret.symm, fun h => absurd rfl h⟩
        · rw [if_neg hlw0, if_pos rfl, evaluateHOLFiniteState_skip] at hret
          dsimp only at hret
          rcases hfl_spec with ⟨h0, _⟩ | ⟨_, _, hmemL⟩
          · exact absurd h0 hlw0
          · have ⟨hB, L0, I0, Fr0, hT0⟩ := (SoloHtabSet.htabWF_iff ent tw.toNat).mp hent_W
            have hlw_L0 : lw.toNat ∈ L0 := hmemL L0 I0 Fr0 hT0
            rw [evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
            split at hret
            · simp at hret
            · split at hret
              · rw [evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
                split at hret
                · simp at hret
                · split at hret
                  · rw [evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
                    split at hret
                    · simp at hret
                    · split at hret
                      · rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
                        split at hret
                        · simp at hret
                        · rename_i vs_m _
                          split at hret
                          · simp at hret
                          · rename_i b_m c_m rs_m hl_m
                            split at hret
                            · simp at hret
                            · have hs_m_code : s_fl.code = originalRuntimeCode := by
                                rw [hfl_lf']; exact hcode
                              have hsame_m := lookupCodeHOLFinite_installed_body s_fl.code.lookup
                                (ofString "memeq") _ (sourceFnBody Guest.Software.guestFn_memeq) b_m
                                .one rs_m vs_m c_m (by rw [hs_m_code]; exact lookup_memeq) hl_m
                              subst hsame_m
                              have hlf_m := funLocFrame_memeq.2.2.2.2 (callEntryStateHOLFinite _ c_m) hs_m_code
                              rcases hm_run : evaluateHOLFiniteState (callEntryStateHOLFinite _ c_m)
                                  (sourceFnBody Guest.Software.guestFn_memeq) with ⟨rm, sm⟩
                              rw [hm_run] at hret hlf_m
                              rcases rm with _ | rm
                              · simp at hret
                              · cases rm with
                                | returned vm =>
                                  dsimp only at hret
                                  split at hret
                                  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
                                    split at hret
                                    · split at hret
                                      · rw [evaluateHOLFiniteState_skip] at hret; dsimp only at hret
                                        rw [evaluateHOLFiniteState_return] at hret
                                        split at hret
                                        · simp at hret
                                        · rename_i retV hretV
                                          split at hret
                                          · simp only [Prod.mk.injEq, Option.some.injEq,
                                              PanSemResultExact.returned.injEq] at hret
                                            subst hret
                                            have ht_sm : (setVarHOLFinite (ofString "eq") vm _).locals.lookup (ofString "t") =
                                                some (.val (.word tw)) := by
                                              simp [setVarHOLFinite, s1, HolFiniteMapExact.lookup_update, FUPDATE, ht,
                                                show ofString "eq" ≠ ofString "t" by decide,
                                                show ofString "keys" ≠ ofString "t" by decide,
                                                show ofString "stride" ≠ ofString "t" by decide,
                                                show ofString "klen" ≠ ofString "t" by decide,
                                                show ofString "leaf" ≠ ofString "t" by decide]
                                            have hleaf_sm : (setVarHOLFinite (ofString "eq") vm _).locals.lookup (ofString "leaf") =
                                                some (.val (.word lw)) := by
                                              simp [setVarHOLFinite, s1, HolFiniteMapExact.lookup_update, FUPDATE,
                                                show ofString "eq" ≠ ofString "leaf" by decide,
                                                show ofString "keys" ≠ ofString "leaf" by decide,
                                                show ofString "stride" ≠ ofString "leaf" by decide,
                                                show ofString "klen" ≠ ofString "leaf" by decide]
                                            have hmem_sm : sm.memory = s.memory := by
                                              have h1 : sm.memory = s_fl.memory := by rw [hlf_m]; rfl
                                              have h2 : s_fl.memory = s.memory := by rw [hfl_lf']
                                              exact h1.trans h2
                                            have hma_sm : sm.memaddrs = s.memaddrs := by
                                              have h1 : sm.memaddrs = s_fl.memaddrs := by rw [hlf_m]; rfl
                                              have h2 : s_fl.memaddrs = s.memaddrs := by rw [hfl_lf']
                                              exact h1.trans h2
                                            simp only [evalHOLExact, evalListHOLExact, ht_sm, hleaf_sm,
                                              valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
                                              memLoadHOLExact, hmem_sm, hma_sm] at hretV
                                            rcases hm40 : s.memory (tw + 40) with ⟨ndw⟩
                                            rw [hm40] at hretV
                                            by_cases hd40 : s.memaddrs (tw + 40)
                                            · simp only [hd40, ↓reduceIte, List.all, List.map, Option.map,
                                                Bool.and_self, List.foldr] at hretV
                                              rcases hm_val : s.memory (ndw + (lw * 32 + (8 + 0))) with ⟨valw⟩
                                              rw [hm_val] at hretV
                                              by_cases hd_val : s.memaddrs (ndw + (lw * 32 + (8 + 0)))
                                              · simp only [hd_val, ↓reduceIte, Option.some.injEq] at hretV
                                                refine ⟨1, valw, hretV.symm, fun _ => ?_⟩
                                                obtain ⟨idx, hidx, hLidx⟩ := List.getElem_of_mem hlw_L0
                                                have hcnt_eq : L0.length = hdr s tw.toNat 3 := hT0.1
                                                have hord_eq : memW s (hdr s tw.toNat 6 + 8 * idx) = lw.toNat := by
                                                  rw [← hLidx]; exact (hT0.2.2.2.2.1 idx hidx).1
                                                unfold htabValues
                                                refine List.mem_map.2 ⟨idx, List.mem_range.2 (by omega), ?_⟩
                                                rw [hord_eq]
                                                have hhdr5 : hdr s tw.toNat 5 = ndw.toNat := by
                                                  unfold hdr memW
                                                  have htw8 : (tw + 40 : BitVec 64) = BitVec.ofNat 64 (tw.toNat + 40) := by
                                                    have htb := (hB.1 (tw.toNat, 88) (by simp [htabFootprint])).1
                                                    have h264 : heapEnd ≤ 2 ^ 64 := by decide
                                                    apply BitVec.eq_of_toNat_eq
                                                    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
                                                    change (tw.toNat + 40) % 2 ^ 64 = (tw.toNat + 40) % 2 ^ 64
                                                    rfl
                                                  rw [← htw8, hm40]
                                                rw [hhdr5]
                                                unfold nodeF memW
                                                have hlw_lt : lw.toNat ≤ hdr s tw.toNat 10 := by
                                                  have := (hT0.2.2.1 lw.toNat).1 (List.mem_append_left _ (List.mem_append_left _ hlw_L0))
                                                  omega
                                                have hfp2 : (hdr s tw.toNat 5, (hdr s tw.toNat 10 + 1) * 32) ∈ htabFootprint s tw.toNat := by
                                                  simp [htabFootprint]
                                                have hnd_bnd := (hB.1 _ hfp2).1
                                                have h264 : heapEnd ≤ 2 ^ 64 := by decide
                                                rw [hhdr5] at hnd_bnd
                                                have had_eq : BitVec.ofNat 64 (ndw.toNat + 32 * lw.toNat + 8) =
                                                    ndw + (lw * 32 + (8 + 0)) := by
                                                  apply BitVec.eq_of_toNat_eq
                                                  have hfit : ndw.toNat + 32 * lw.toNat + 8 < 2 ^ 64 := by
                                                    dsimp at hnd_bnd; omega
                                                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
                                                  have hm1 : (lw * 32).toNat = 32 * lw.toNat := by
                                                    rw [BitVec.toNat_mul]
                                                    change (lw.toNat * 32) % 2 ^ 64 = _
                                                    rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
                                                  have hm2 : (lw * 32 + (8 + 0)).toNat = 32 * lw.toNat + 8 := by
                                                    change (lw * 32 + 8).toNat = _
                                                    rw [BitVec.toNat_add, hm1]
                                                    change (32 * lw.toNat + 8) % 2 ^ 64 = _
                                                    exact Nat.mod_eq_of_lt (by omega)
                                                  rw [BitVec.toNat_add, hm2, Nat.mod_eq_of_lt (by omega)]
                                                  omega
                                                rw [had_eq, hm_val]
                                              · simp [hd_val] at hretV
                                            · simp [hd40] at hretV
                                          · simp at hret
                                      · rw [evaluateHOLFiniteState_return] at hret
                                        simp [evalHOLExact, evalListHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
                                        exact ⟨0, 0, hret.symm, fun h => absurd rfl h⟩
                                    · simp at hret
                                  · simp at hret
                                | _ => simp at hret
                      · simp at hret
                  · simp at hret
              · simp at hret
      | _ => simp at hret

end InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard01
