import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01Common

/-! Proofs of `wk_alloc`, `rt_mpt_new`, and `wk_mpt_new` for `WkShard01.lean`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Contracts.M12
open InitECandidate.Solver.Wave8Contracts.M26

/-! ## 1. `wk_alloc` -/

theorem lookup_alloc_r13 :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
  lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

theorem alloc_body_resumes_props {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hA : ArenaReady s)
    (hres : Wave8Contracts.M12.Resumes
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)
    ∃ p q : BitVec 64,
      out.1 = some (.returned (.val (.word p))) ∧
      p.toNat = globN s "heap_ptr" ∧
      q.toNat = p.toNat + (locN s "n" + 7) / 8 * 8 ∧
      q.toNat ≤ heapLimit ∧
      q.toNat % 8 = 0 ∧
      p.toNat ≤ q.toNat ∧
      out.2.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) ∧
      out.2.memory = s.memory ∧
      out.2.be = s.be ∧
      out.2.memaddrs = s.memaddrs ∧
      ArenaReady out.2 ∧
      globN out.2 "heap_ptr" = q.toNat ∧
      globN out.2 "scratch_ptr" = globN s "scratch_ptr" := by
  dsimp only
  obtain ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩ := arenaOK_globals s hA.2
  have hn_word : ∃ nw : BitVec 64, s.locals.lookup (ofString "n") = some (.val (.word nw)) := by
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
    rcases hl : s.locals.lookup (ofString "n") with _ | lv
    · exfalso
      rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hres
      have hp_ev : @evalHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a))
          (.var .global (ofString "heap_ptr")) = some (.val (.word hp)) := hhp
      dsimp only at hres; rw [hp_ev] at hres
      have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word hp))) = true := by simp [shapeEqHOL, shapeOfHOLExact]
      dsimp only at hres; rw [if_pos hsh] at hres; dsimp only at hres
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres
      have hnl : (setVarHOLFinite (ofString "p") (.val (.word hp)) s).locals.lookup (ofString "n") = none := by
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl, show ofString "p" ≠ ofString "n" by decide]
      simp [evalHOLExact, evalListHOLExact, hnl] at hres
      exact not_resumes_error hres
    · rcases lv with ⟨⟨nw⟩⟩ | fs | ⟨nm, fs⟩
      · exact ⟨nw, rfl⟩
      · exfalso
        rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hres
        have hp_ev : @evalHOLExact 64 F _ s.toExact
            (fun a => Classical.propDecidable (s.memaddrs a))
            (.var .global (ofString "heap_ptr")) = some (.val (.word hp)) := hhp
        dsimp only at hres; rw [hp_ev] at hres
        have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word hp))) = true := by simp [shapeEqHOL, shapeOfHOLExact]
        dsimp only at hres; rw [if_pos hsh] at hres; dsimp only at hres
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres
        have hnl : (setVarHOLFinite (ofString "p") (.val (.word hp)) s).locals.lookup (ofString "n") = some (.rStruct fs) := by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl, show ofString "p" ≠ ofString "n" by decide]
        simp [evalHOLExact, evalListHOLExact, hnl] at hres
        exact not_resumes_error hres
      · exfalso
        rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hres
        have hp_ev : @evalHOLExact 64 F _ s.toExact
            (fun a => Classical.propDecidable (s.memaddrs a))
            (.var .global (ofString "heap_ptr")) = some (.val (.word hp)) := hhp
        dsimp only at hres; rw [hp_ev] at hres
        have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word hp))) = true := by simp [shapeEqHOL, shapeOfHOLExact]
        dsimp only at hres; rw [if_pos hsh] at hres; dsimp only at hres
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres
        have hnl : (setVarHOLFinite (ofString "p") (.val (.word hp)) s).locals.lookup (ofString "n") = some (.nStruct nm fs) := by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl, show ofString "p" ≠ ofString "n" by decide]
        simp [evalHOLExact, evalListHOLExact, hnl] at hres
        exact not_resumes_error hres
  obtain ⟨nw, hnw⟩ := hn_word
  have hret_ex : ∃ rv, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1 = some (.returned rv) := by
    rcases hres with ⟨rv, hrv⟩ | ⟨eid, ev, hexc, hne_trap⟩
    · exact ⟨rv, hrv⟩
    · exfalso
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
      rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hexc
      have hp_ev : @evalHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a))
          (.var .global (ofString "heap_ptr")) = some (.val (.word hp)) := hhp
      dsimp only at hexc; rw [hp_ev] at hexc
      have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word hp))) = true := by simp [shapeEqHOL, shapeOfHOLExact]
      dsimp only at hexc; rw [if_pos hsh] at hexc; dsimp only at hexc
      let pState := setVarHOLFinite (ofString "p") (.val (.word hp)) s
      have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word hp)) := by
        simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnw, show ofString "p" ≠ ofString "n" by decide]
      rw [evaluateHOLFiniteState_seq_line780] at hexc
      have hev1 : @evalHOLExact 64 F _ pState.toExact
          (fun a => Classical.propDecidable (pState.memaddrs a))
          (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n"))) =
          some (.val (.word (if (cMax - hp).toNat < nw.toNat then 1 else 0))) := by
        simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
          Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]; rfl
      by_cases hcmp1 : (cMax - hp).toNat < nw.toNat
      · have hite1 : evaluateHOLFiniteState pState
            (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
                (.var .local (ofString "n")))
              (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) =
            evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
          rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
        rw [hite1] at hexc
        have hno_none := evaluate_call_trap_with_no_none pState 1 hcode
        have hno_res := evaluate_call_trap_with_no_resumes pState 1 hcode
        rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
        rw [htr] at hno_none hno_res hexc
        cases r1 with
        | none => exact hno_none rfl
        | some r1' => exact hno_res (Or.inr ⟨eid, ev, hexc, hne_trap⟩)
      · have hite1 : evaluateHOLFiniteState pState
            (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
                (.var .local (ofString "n")))
              (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) = (none, pState) := by
          rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
        rw [hite1] at hexc; dsimp only at hexc
        rw [evaluateHOLFiniteState_dec_total] at hexc
        let q : BitVec 64 := (hp + (nw + 7)) &&& ((0 : BitVec 64) - 8)
        have hq_eval : @evalHOLExact 64 F _ pState.toExact
            (fun a => Classical.propDecidable (pState.memaddrs a))
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
          simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
            wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
          exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (alloc_q_word_eq hp nw)
        dsimp only at hexc; rw [hq_eval] at hexc
        have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by simp [shapeEqHOL, shapeOfHOLExact]
        dsimp only at hexc; rw [if_pos hsh_q] at hexc; dsimp only at hexc
        let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
        have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
          simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word hp)) := by
          simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc, show ofString "q" ≠ ofString "p" by decide]
        rw [evaluateHOLFiniteState_seq_line780] at hexc
        have hev2 : @evalHOLExact 64 F _ qState.toExact
            (fun a => Classical.propDecidable (qState.memaddrs a))
            (.cmp .lower (.const cMax) (.var .local (ofString "q"))) =
            some (.val (.word (if cMax.toNat < q.toNat then 1 else 0))) := by
          simp only [evalHOLExact, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
        by_cases hcmp2 : cMax.toNat < q.toNat
        · have hite2 : evaluateHOLFiniteState qState
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) =
              evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
            rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
          rw [hite2] at hexc
          have hno_none := evaluate_call_trap_with_no_none qState 1 hcode
          have hno_res := evaluate_call_trap_with_no_resumes qState 1 hcode
          rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
          rw [htr] at hno_none hno_res hexc
          cases r2 with
          | none => exact hno_none rfl
          | some r2' => exact hno_res (Or.inr ⟨eid, ev, hexc, hne_trap⟩)
        · have hite2 : evaluateHOLFiniteState qState
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) = (none, qState) := by
            rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
          rw [hite2] at hexc; dsimp only at hexc
          have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) := hhp
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hexc
          simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
            shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
            evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL] at hexc
  obtain ⟨rv, hrv⟩ := hret_ex
  obtain ⟨hrv_eq, hcmp1, hcmp2, hpost_eq⟩ := alloc_body_run s hp nw hcode hhp hnw rv hrv
  subst hrv_eq
  rcases hA.2 with ⟨hsb_s, hhi_s, hfm_lo_s, hfm_hi_s, hsp_hi_s, hhp_al_s, hfm_al_s, hsp_al_s, hgw_s⟩
  let q := (hp + (nw + 7)) &&& ((0 : BitVec 64) - 8)
  have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hhi_s
  have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hhp_al_s
  obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ := alloc_arith hp nw hhp_hi hhp_al hcmp1 hcmp2
  have hn_loc_eq : locN s "n" = nw.toNat := by simp [locN, hnw]
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2
  have hpost_g : post.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) := by
    rw [hpost_eq]
  have hpost_hp : globN post "heap_ptr" = q.toNat := by
    unfold globN; rw [hpost_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hpost_fm : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    unfold globN; rw [hpost_g]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
  have hpost_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
    unfold globN; rw [hpost_g]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
  have hG_post : GuestInv post := by
    rw [hpost_eq]; exact ⟨hA.1.code, hA.1.memaddrs, hA.1.shMemaddrs, hA.1.baseAddr⟩
  have hA_post : ArenaReady post := by
    refine ⟨hG_post, ?_⟩
    have hgw_post : GlobalsWord post := globalsWord_update (ofString "heap_ptr") q hpost_g hgw_s
    unfold ArenaOK
    rw [hpost_hp, hpost_fm, hpost_sp]
    have hsb_le : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hsb_s
    exact ⟨le_trans hsb_le hp_le_q, hq_hi, hfm_lo_s, hfm_hi_s, hsp_hi_s,
      hq_al, hfm_al_s, hsp_al_s, hgw_post⟩
  refine ⟨hp, q, hrv, hhp_eq, ?_, hq_hi, hq_al, hp_le_q, hpost_g, ?_, ?_, ?_, hA_post, hpost_hp, hpost_sp⟩
  · rw [hn_loc_eq]; exact hq_eq
  · rw [hpost_eq]
  · rw [hpost_eq]
  · rw [hpost_eq]

theorem wk_alloc_impl :
    Wave8Contracts.M12.WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (Wave8Contracts.M12.RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc") := by
  refine ⟨_, _, _, lookup_alloc_r13, ?_⟩
  intro F s hcode hW _ _ hres
  obtain ⟨p, q, hrv, hp_eq, hq_eq, hq_hi, hq_al, hp_le_q, hpost_g, hpost_m, hpost_be, _, hA_post, hpost_hp, hpost_sp⟩ :=
    alloc_body_resumes_props s hcode hW.1 hres
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2
  have heff : WorldFrameEff s post ([] ++ ([] : List Ivl)) ["heap_ptr"] := by
    refine ⟨hA_post, by rw [← hp_eq, hpost_hp]; exact hp_le_q, by rw [hpost_sp],
      fun k hk => ?_, hpost_be,
      fun a _ => by rw [hpost_m],
      fun a _ _ => by rw [hpost_m],
      fun b _ _ _ => by unfold memB; rw [hpost_m, hpost_be]⟩
    have hne : ofString "heap_ptr" ≠ k := fun h => hk (by simp [h])
    rw [hpost_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
  refine heff.to_worldStep (extra := fun _ => []) hW
    (fun g hg => Or.inl (by simpa using hg))
    (fun _ h => by simp at h)
    (fun S Nd hWT _ _ hno_new v hv => ?_)
  rw [hrv] at hv
  injection hv with hv'; injection hv' with hv''; subst hv''
  refine ⟨p, rfl, ?_⟩
  refine disj_fresh_heap_of_worldOwned hW.1 hA_post hWT
    (fun o ho => by rcases hno_new o ho with rfl | h; exact Or.inl rfl; exact Or.inr (Or.inl h))
    hno_new ?_
  rw [← hp_eq, hpost_hp]
  exact ⟨le_rfl, le_of_eq hq_eq.symm⟩

/-! ## 2. `rt_mpt_new` and `wk_mpt_new` -/

theorem lookup_mpt_new_r13 :
    originalRuntimeCode.lookup (ofString "mpt_new") =
      some ([(ofString "root_node", .one), (ofString "secured", .one)],
        sourceFnBody Guest.Software.guestFn_mpt_new, .one) :=
  lookup_of_guestAst_getElem 268 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_new) rfl

theorem mpt_new_resumes_props {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w_rn w_sec : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hA : ArenaReady s)
    (hrn : s.locals.lookup (ofString "root_node") = some (.val (.word w_rn)))
    (hsec : s.locals.lookup (ofString "secured") = some (.val (.word w_sec)))
    (hres : Wave8Contracts.M12.Resumes
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mpt_new)).1) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mpt_new)
    ∃ hp q : BitVec 64,
      out.1 = some (.returned (.val (.word hp))) ∧
      hp.toNat = globN s "heap_ptr" ∧
      hp.toNat % 8 = 0 ∧
      q.toNat = hp.toNat + 16 ∧
      q.toNat ≤ heapLimit ∧
      q.toNat % 8 = 0 ∧
      out.2.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) ∧
      out.2.memory = updW (updW s.memory (hp + 0) w_rn) (hp + 8) w_sec ∧
      out.2.be = s.be ∧
      ArenaReady out.2 ∧
      AllocatorGrows s out.2 ∧
      Wave8Contracts.M26.FreshBlock s out.2 hp.toNat 16 ∧
      memW out.2 hp.toNat = locN s "root_node" ∧
      memW out.2 (hp.toNat + 8) = locN s "secured" := by
  dsimp only
  obtain ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩ := arenaOK_globals s hA.2
  have hbody : sourceFnBody Guest.Software.guestFn_mpt_new =
      .decCall (ofString "m") .one (ofString "alloc") [.const 16]
        (.seq
          (.store (.op .add [.var .local (ofString "m"), .const 0]) (.var .local (ofString "root_node")))
          (.seq
            (.store (.op .add [.var .local (ofString "m"), .const 8]) (.var .local (ofString "secured")))
            (.return (.var .local (ofString "m"))))) := rfl
  have hret_ex : ∃ rv, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mpt_new)).1 = some (.returned rv) := by
    rcases hres with ⟨rv, hrv⟩ | ⟨eid, ev_val, hexc, hne_trap⟩
    · exact ⟨rv, hrv⟩
    · exfalso
      rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hexc
      have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const 16] =
          some [.val (.word 16)] := by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
      have hl := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
        (sourceFnBody Guest.Software.guestFn_alloc) 16 (by rw [hcode]; exact lookup_alloc_r13)
      rw [hargs] at hexc; dsimp only at hexc; rw [hl] at hexc; dsimp only at hexc
      split at hexc
      · simp at hexc
      · let centry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 16)))
        have hA_ce : ArenaReady centry := ⟨guestInv_callEntry s _ hA.1, hA.2⟩
        rcases hal : evaluateHOLFiniteState centry (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ral, sal⟩
        dsimp only [centry] at hal
        rw [hal] at hexc
        cases ral with
        | none => simp at hexc
        | some ral' =>
          cases ral' with
          | exception eid' ev' =>
            injection hexc with h1; injection h1 with h2 h3; subst h2 h3
            obtain ⟨_, _, hret_al, _⟩ := alloc_body_resumes_props centry hcode hA_ce
              (by dsimp only [centry]; rw [hal]; exact Or.inr ⟨eid', ev', rfl, hne_trap⟩)
            dsimp only [centry] at hret_al; rw [hal] at hret_al; simp at hret_al
          | returned rv_al =>
            dsimp only at hexc
            split at hexc
            · let s_m := setVarHOLFinite (ofString "m") rv_al { sal with locals := s.locals }
              rw [evaluateHOLFiniteState_seq_line780] at hexc
              rcases hst1 : evaluateHOLFiniteState s_m
                  (.store (.op .add [.var .local (ofString "m"), .const 0]) (.var .local (ofString "root_node"))) with ⟨r_st1, m_st1⟩
              rw [hst1] at hexc
              rcases (evaluate_store_control_frame s_m _ _).1 with h1 | h1
              · rw [hst1] at h1; dsimp only at h1; subst h1
                dsimp only at hexc
                rw [evaluateHOLFiniteState_seq_line780] at hexc
                rcases hst2 : evaluateHOLFiniteState m_st1
                    (.store (.op .add [.var .local (ofString "m"), .const 8]) (.var .local (ofString "secured"))) with ⟨r_st2, m_st2⟩
                rw [hst2] at hexc
                rcases (evaluate_store_control_frame m_st1 _ _).1 with h2 | h2
                · rw [hst2] at h2; dsimp only at h2; subst h2
                  dsimp only at hexc
                  rw [evaluateHOLFiniteState_return] at hexc
                  split at hexc
                  · simp at hexc
                  · split at hexc <;> simp at hexc
                · rw [hst2] at h2; dsimp only at h2; subst h2; simp at hexc
              · rw [hst1] at h1; dsimp only at h1; subst h1; simp at hexc
            · simp at hexc
          | _ => simp at hexc
  obtain ⟨rv, hrv⟩ := hret_ex
  have hrun : Ret s (sourceFnBody Guest.Software.guestFn_mpt_new)
      (fun rv' post =>
        ∃ q : BitVec 64,
          rv' = .val (.word hp) ∧
          hp.toNat = globN s "heap_ptr" ∧
          hp.toNat % 8 = 0 ∧
          q.toNat = hp.toNat + 16 ∧
          q.toNat ≤ heapLimit ∧
          q.toNat % 8 = 0 ∧
          post.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) ∧
          post.memory = updW (updW s.memory (hp + 0) w_rn) (hp + 8) w_sec ∧
          post.be = s.be ∧
          ArenaReady post ∧
          AllocatorGrows s post ∧
          Wave8Contracts.M26.FreshBlock s post hp.toNat 16 ∧
          memW post hp.toNat = locN s "root_node" ∧
          memW post (hp.toNat + 8) = locN s "secured") := by
    rw [hbody]
    apply Ret.of_NS
    refine Ret.ns_alloc hcode 16 rfl hp hhp ?_
    intro hcmp1 hcmp2
    set q : BitVec 64 := (hp + (16 + 7)) &&& ((0 : BitVec 64) - 8)
    set L1 := s.locals.update (ofString "m", .val (.word hp))
    set G1 := s.globals.update (ofString "heap_ptr", .val (.word q))
    have hev_m0 : ev (NS s L1 G1 s.memory (s.clock - 1))
        (.op .add [.var .local (ofString "m"), .const 0]) = some (.val (.word (hp + 0))) := by
      simp [ev, evalHOLExact, evalListHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        valueIsWord, valueWord, wordOpHOL, wordOp]
    have hev_rn : ev (NS s L1 G1 s.memory (s.clock - 1))
        (.var .local (ofString "root_node")) = some (.val (.word w_rn)) := by
      simp [ev, evalHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "m" ≠ ofString "root_node" by decide, hrn]
    refine Ret.ns_storeW (hp + 0) w_rn hev_m0 hev_rn ?_
    intro _hdom0
    set M1 := updW s.memory (hp + 0) w_rn
    have hev_m8 : ev (NS s L1 G1 M1 (s.clock - 1))
        (.op .add [.var .local (ofString "m"), .const 8]) = some (.val (.word (hp + 8))) := by
      simp [ev, evalHOLExact, evalListHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        valueIsWord, valueWord, wordOpHOL, wordOp]
    have hev_sec : ev (NS s L1 G1 M1 (s.clock - 1))
        (.var .local (ofString "secured")) = some (.val (.word w_sec)) := by
      simp [ev, evalHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "m" ≠ ofString "secured" by decide, hsec]
    refine Ret.ns_storeW (hp + 8) w_sec hev_m8 hev_sec ?_
    intro _hdom8
    set M2 := updW M1 (hp + 8) w_sec
    refine Ret.ns_ret ?_
    intro val hval
    have hval_eq : val = .val (.word hp) := by
      simp [ev, evalHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE] at hval
      exact hval.symm
    subst hval_eq
    dsimp only
    set post : PanSemStateFiniteExact 64 F :=
      { locals := HolFiniteMapExact.resVarEq
          (emptyLocalsHOLFinite (NS s L1 G1 M2 (s.clock - 1))).locals
          (ofString "m", s.locals.lookup (ofString "m")),
        globals := G1,
        structs := s.structs,
        code := s.code,
        eshapes := s.eshapes,
        memory := M2,
        memaddrs := s.memaddrs,
        shMemaddrs := s.shMemaddrs,
        clock := s.clock - 1,
        be := s.be,
        ffi := s.ffi,
        baseAddr := s.baseAddr,
        topAddr := s.topAddr }
    rcases hA.2 with ⟨hsb_s, hhi_s, hfm_lo_s, hfm_hi_s, hsp_hi_s, hhp_al_s, hfm_al_s, hsp_al_s, hgw_s⟩
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hhi_s
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hhp_al_s
    have hsb_le : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hsb_s
    obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ := alloc_arith hp 16 hhp_hi hhp_al hcmp1 hcmp2
    change q.toNat = _ at hq_eq
    change q.toNat ≤ heapLimit at hq_hi
    change q.toNat % 8 = 0 at hq_al
    change hp.toNat ≤ q.toNat at hp_le_q
    have h16 : ((16 : BitVec 64).toNat + 7) / 8 * 8 = 16 := by decide
    rw [h16] at hq_eq
    have hpost_hp : globN post "heap_ptr" = q.toNat := by
      simp [post, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE]
    have hpost_fp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
      simp [post, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
    have hpost_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
      simp [post, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
    have hG_post : GuestInv post := ⟨hA.1.code, hA.1.memaddrs, hA.1.shMemaddrs, hA.1.baseAddr⟩
    have hA_post : ArenaReady post := by
      refine ⟨hG_post, ?_⟩
      have hgw_post : GlobalsWord post := globalsWord_update (ofString "heap_ptr") q rfl hgw_s
      unfold ArenaOK
      rw [hpost_hp, hpost_fp, hpost_sp]
      exact ⟨le_trans hsb_le hp_le_q, hq_hi, hfm_lo_s, hfm_hi_s, hsp_hi_s,
        hq_al, hfm_al_s, hsp_al_s, hgw_post⟩
    have hAG : AllocatorGrows s post := by
      refine ⟨?_, by rw [hpost_sp]⟩
      rw [hpost_hp, ← hhp_eq]; exact hp_le_q
    have hlim_le_he : heapLimit ≤ heapEnd := by decide
    have hFB : Wave8Contracts.M26.FreshBlock s post hp.toNat 16 := by
      refine ⟨hhp_al, ?_, ?_⟩
      · change Inside (hp.toNat, 16) (globN s "heap_ptr") (globN post "heap_ptr")
        rw [← hhp_eq, hpost_hp]
        exact ⟨le_rfl, le_of_eq hq_eq.symm⟩
      · change WordsOK post (hp.toNat, 16)
        exact wordsOK_of_guestInv post hG_post hp.toNat 16 hhp_al (by decide) hsb_le (by omega)
    have hp0_ne_8 : hp + 0 ≠ hp + 8 := by
      intro h; have h1 := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at h1; omega
    have hp_eq_0 : BitVec.ofNat 64 hp.toNat = hp + 0 := by simp [BitVec.ofNat_toNat]
    have hp8_eq : BitVec.ofNat 64 (hp.toNat + 8) = hp + 8 := ofNat_add_toNat_eq hp 8
    have hmem0 : memW post hp.toNat = locN s "root_node" := by
      unfold memW
      change (match M2 (BitVec.ofNat 64 hp.toNat) with | .word w => w.toNat) = locN s "root_node"
      rw [show M2 (BitVec.ofNat 64 hp.toNat) = .word w_rn by
        rw [hp_eq_0]; simp only [M2, M1, updW, hp0_ne_8, ↓reduceIte]]
      simp [locN, hrn]
    have hmem8 : memW post (hp.toNat + 8) = locN s "secured" := by
      unfold memW
      change (match M2 (BitVec.ofNat 64 (hp.toNat + 8)) with | .word w => w.toNat) = locN s "secured"
      rw [show M2 (BitVec.ofNat 64 (hp.toNat + 8)) = .word w_sec by
        rw [hp8_eq]; simp only [M2, updW, ↓reduceIte]]
      simp [locN, hsec]
    exact ⟨q, rfl, hhp_eq, hhp_al, hq_eq, hq_hi, hq_al, rfl, rfl, rfl, hA_post, hAG, hFB, hmem0, hmem8⟩
  obtain ⟨q, hrv_eq, rest⟩ := hrun rv hrv
  subst hrv_eq
  exact ⟨hp, q, hrv, rest⟩

theorem rt_mpt_new_impl :
    Wave8Contracts.M26.Returns ArenaReady (fun s post m =>
      Wave8Contracts.M26.FreshBlock s post m 16 ∧
      memW post m = locN s "root_node" ∧ memW post (m + 8) = locN s "secured")
    (ofString "mpt_new") := by
  refine ⟨_, _, _, lookup_mpt_new_r13, ?_⟩
  intro F s hcode hAR ⟨vals, hl⟩ _ v hret
  obtain ⟨w_rn, w_sec, _, hrn, hsec⟩ := lookupCode_two_words (by decide) lookup_mpt_new_r13 hl
  obtain ⟨hp, _, hrv, _, _, _, _, _, _, _, _, hA_post, hAG, hFB, hmem0, hmem8⟩ :=
    mpt_new_resumes_props s w_rn w_sec hcode hAR hrn hsec (Or.inl ⟨v, hret⟩)
  rw [hrv] at hret
  injection hret with h1; injection h1 with h2; subst h2
  exact ⟨hp, rfl, hA_post, hAG, hFB, hmem0, hmem8⟩

theorem wk_mpt_new_impl :
    Wave8Contracts.M12.WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (Wave8Contracts.M12.RetAvoids (fun _ _ w => [(w, 16)])) (ofString "mpt_new") := by
  refine ⟨_, _, _, lookup_mpt_new_r13, ?_⟩
  intro F s hcode hW ⟨vals, hl⟩ _ hres
  obtain ⟨w_rn, w_sec, _, hrn, hsec⟩ := lookupCode_two_words (by decide) lookup_mpt_new_r13 hl
  obtain ⟨hp, q, hrv, hhp_eq, hhp_al, hq_eq, hq_hi, _, hpost_g, hpost_m, hpost_be, hA_post, hAG, _, _, _⟩ :=
    mpt_new_resumes_props s w_rn w_sec hcode hW.1 hrn hsec hres
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mpt_new)).2
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hp_lo_sb : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hW.1.2.1
  have hp8_nat : (hp + 8#64).toNat = hp.toNat + 8 :=
    BitVec.toNat_add_of_lt (by rw [Wave8Contracts.M12.heapLimit_val] at hq_hi; change hp.toNat + 8 < 2 ^ 64; omega)
  have hdom_hp0 : s.memaddrs hp := by
    rw [hW.1.1.memaddrs]
    have h := ordinaryDomain_of_nat hp.toNat hp_lo_sb (by omega) hhp_al
    rwa [BitVec.ofNat_toNat] at h
  have hdom_hp8 : s.memaddrs (hp + 8#64) := by
    rw [hW.1.1.memaddrs]
    have h := ordinaryDomain_of_nat (hp.toNat + 8) (by omega) (by omega) (by omega)
    rwa [ofNat_add_toNat_eq hp 8] at h
  have hpost_m' : post.memory = updW (updW s.memory hp w_rn) (hp + 8#64) w_sec := by
    simpa [BitVec.add_zero] using hpost_m
  have heff : WorldFrameEff s post ([] ++ ([] : List Ivl)) ["heap_ptr"] := by
    refine ⟨hA_post, hAG.1, hAG.2, fun k hk => ?_, hpost_be, ?_, ?_, ?_⟩
    · have hne : ofString "heap_ptr" ≠ k := fun h => hk (by simp [h])
      rw [hpost_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
    · intro a hna
      have hne0 : a ≠ hp := by rintro rfl; exact hna hdom_hp0
      have hne8 : a ≠ hp + 8#64 := by rintro rfl; exact hna hdom_hp8
      rw [hpost_m']; simp [updW, hne8, hne0]
    · intro a _ hnhf
      have hne0 : a ≠ hp := by
        rintro rfl
        apply hnhf
        unfold CellHits Wave8Contracts.M12.heapFree
        rw [← hhp_eq]
        exact ⟨by omega, by omega⟩
      have hne8 : a ≠ hp + 8#64 := by
        rintro rfl
        apply hnhf
        unfold CellHits Wave8Contracts.M12.heapFree
        rw [hp8_nat, ← hhp_eq]
        exact ⟨by omega, by omega⟩
      rw [hpost_m']; simp [updW, hne8, hne0]
    · intro b hb _ hnhf
      unfold memB
      have hal_nat : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
        rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      have hne0 : panByteAlignHOL (BitVec.ofNat 64 b) ≠ hp := by
        intro heq
        have ht := congrArg BitVec.toNat heq
        rw [hal_nat] at ht
        apply hnhf
        unfold InIvl Wave8Contracts.M12.heapFree
        rw [← hhp_eq]; omega
      have hne8 : panByteAlignHOL (BitVec.ofNat 64 b) ≠ hp + 8#64 := by
        intro heq
        have ht := congrArg BitVec.toNat heq
        rw [hal_nat, hp8_nat] at ht
        apply hnhf
        unfold InIvl Wave8Contracts.M12.heapFree
        rw [← hhp_eq]; omega
      rw [hpost_m', hpost_be]
      simp only [updW, if_neg hne8, if_neg hne0]
  refine heff.to_worldStep (extra := fun _ => []) hW
    (fun g hg => Or.inl (by simpa using hg))
    (fun _ h => by simp at h)
    (fun S Nd hWT _ _ hno_new v hv => ?_)
  rw [hrv] at hv
  injection hv with hv'; injection hv' with hv''; subst hv''
  refine ⟨hp, rfl, ?_⟩
  refine disj_fresh_heap_of_worldOwned hW.1 hA_post hWT
    (fun o ho => by rcases hno_new o ho with rfl | h; exact Or.inl rfl; exact Or.inr (Or.inl h))
    hno_new ?_
  have hpost_hp : globN post "heap_ptr" = q.toNat := by
    unfold globN; rw [hpost_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  rw [← hhp_eq, hpost_hp]
  exact ⟨le_rfl, le_of_eq hq_eq.symm⟩

end InitECandidate.Solver.Wave8GuestInv.R13Shards
