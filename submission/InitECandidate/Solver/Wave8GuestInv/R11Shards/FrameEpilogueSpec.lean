import InitECandidate.Solver.Wave8GuestInv.R11Shards.StateRestoreStep

/-! Proof of `state_restore_preserves_head_frames` and `frame_epilogue_spec_of` (`< 350` LOC). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R11Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.S06
open InitECandidate.Solver.Wave8Contracts.M08 (globN_eq_of_lookup ivl_allocated_bound
  htabFootprint_eq_of_hdr_unhit htabWF_congr_unhit)
open InitECandidate.Solver.Wave8Contracts.M23 (frameWF_bounds)

/-- `state_restore` preserves all `(ec.1, 280)` and `(ec.2, 104)` cells across `evmChain s0`. -/
theorem state_restore_preserves_head_frames
    (hset : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set"))
    (hdel : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_del"))
    {F : Type} (s0 : PanSemStateFiniteExact 64 F) (hcode : s0.code = originalRuntimeCode)
    (hInv : EvmInv s0) (v : ValueHOL 64)
    (hv : (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_state_restore)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_state_restore)).2
    ∀ ec ∈ evmChain s0, IvlUnhit s0 post (ec.1, 280) ∧ IvlUnhit s0 post (ec.2, 104) := by
  intro post
  have hbody : sourceFnBody Guest.Software.guestFn_state_restore =
      .seq (.while stateRestoreCond (.seq stateRestoreAssign stateRestoreTail)) (.return (.const 0)) := rfl
  rw [hbody] at hv
  have hwh_noret : ∀ u, (evaluateHOLFiniteState s0
      (.while stateRestoreCond (.seq stateRestoreAssign stateRestoreTail))).1 ≠ some (.returned u) := by
    intro u
    suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
        (evaluateHOLFiniteState st
          (.while stateRestoreCond (.seq stateRestoreAssign stateRestoreTail))).1 ≠ some (.returned u) from
      this s0.clock s0 rfl
    intro k; induction k using Nat.strongRecOn with
    | ind k ih =>
      intro st hk
      rw [evaluateHOLFiniteState_while_total]
      split
      · split
        · split
          · simp
          · dsimp only; rw [fixClockHOLFinite_evaluateState]
            have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st)
              (.seq stateRestoreAssign stateRestoreTail)
            rcases hb : evaluateHOLFiniteState (decClockHOLFinite st)
              (.seq stateRestoreAssign stateRestoreTail) with ⟨r1, mid⟩
            have hlt : mid.clock < k := by rw [hb] at hrem; change mid.clock ≤ st.clock - 1 at hrem; omega
            cases r1 with
            | none => exact ih mid.clock hlt mid rfl
            | some r1' =>
              cases r1' with
              | «continue» => exact ih mid.clock hlt mid rfl
              | «break» => simp
              | returned u' =>
                exfalso; revert hb
                rw [evaluateHOLFiniteState_seq_line780]
                rcases ha : evaluateHOLFiniteState (decClockHOLFinite st) stateRestoreAssign with ⟨ra, ma⟩
                cases ra with
                | none =>
                  dsimp only
                  intro h; exact stateRestoreTail_ne_returned ma u' (by rw [h])
                | some ra' =>
                  have hne_ret : ra' ≠ .returned u' := by
                    revert ha; rw [evaluateHOLFiniteState_assign]
                    split
                    · intro h; injection h with h1 _; injection h1 with h2; subst h2; intro hc; cases hc
                    · split
                      · intro h; injection h with h1 _; cases h1
                      · intro h; injection h with h1 _; injection h1 with h2; subst h2; intro hc; cases hc
                  dsimp only; intro h; injection h with h1 _; injection h1 with h2; exact hne_ret h2
              | _ => simp
        · simp
      · simp
  obtain ⟨m1, hm1_wh, hrest1⟩ := seq_returned_inv hv hwh_noret
  have hpost_eq : post = emptyLocalsHOLFinite m1 := by
    show (evaluateHOLFiniteState s0 _).2 = emptyLocalsHOLFinite m1
    rw [hbody, ← hrest1, evaluateHOLFiniteState_return]
    have hc0 : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
        (.const 0) = some (.val (.word 0)) := rfl
    have hle32 : sizeOfShapeWithContextHOL m1.structs
        (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by simp [shapeOfHOLExact]
    rw [hc0]; dsimp only; rw [if_pos hle32]
  obtain ⟨hAs, S, ⟨hT, hJ, _, _⟩, _, _, _, hFrames, _, _, _, hFO_disj, _⟩ := (evmInv_iff_at s0).1 hInv
  set FO : List Ivl := ((evmChain s0).map fun ec => [(ec.1, 280), (ec.2, 104)]).flatten
  have hFO_mem : ∀ ec ∈ evmChain s0, (ec.1, 280) ∈ FO ∧ (ec.2, 104) ∈ FO := fun ec hec => by
    simp only [FO, List.mem_flatten, List.mem_map]
    exact ⟨⟨[(ec.1, 280), (ec.2, 104)], ⟨ec, hec, rfl⟩, by simp⟩,
           ⟨[(ec.1, 280), (ec.2, 104)], ⟨ec, hec, rfl⟩, by simp⟩⟩
  have hjr_in_fix : globN s0 "journal_cap" ≠ 0 →
      (globN s0 "journal", 32 * globN s0 "journal_cap") ∈ fixedObjects s0 := fun hnz => by
    unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right; simp [hnz]
  have halign_s0 : (∀ o ∈ FO, o.1 % 8 = 0 ∧ o.2 % 8 = 0) ∧
      (globN s0 "journal_cap" ≠ 0 → (globN s0 "journal") % 8 = 0 ∧
        globN s0 "journal" + 32 * globN s0 "journal_cap" ≤ 2 ^ 64) := by
    refine ⟨fun o ho => ?_, fun hnz => ?_⟩
    · simp only [FO, List.mem_flatten, List.mem_map] at ho
      rcases ho with ⟨l, ⟨ec, hec, rfl⟩, hl⟩; have hwf := hFrames ec hec
      rcases List.mem_cons.1 hl with rfl | hl
      · exact ⟨(hwf.1 (ec.1, 280) (by simp)).2.1, by omega⟩
      · rcases List.mem_cons.1 hl with rfl | hl; · exact ⟨(hwf.1 (ec.2, 104) (by simp)).2.1, by omega⟩
        cases hl
    · rcases hJ.2.2.1 with h0 | ⟨hal_j, hw_j⟩; · exact absurd h0 hnz
      exact ⟨hw_j.1, (ivl_allocated_bound hAs.2 hal_j).2⟩
  have hInit : StateRestoreLoopInv s0.memory S FO
      (globN s0 "journal") (globN s0 "journal_cap") (globN s0 "journal_n") s0 := by
    refine ⟨hAs, fun o ho => ?_,
      fun hnz => by rcases hJ.2.2.1 with h0 | ⟨hal_j, _⟩; exact absurd h0 hnz; exact hal_j,
      fun u hu => ⟨(hT.2.1 u hu).1, fun i hi => ⟨((hT.2.1 u hu).2 i hi).1, fun o ho => ?_,
        fun hnz => ((hT.2.1 u hu).2 i hi).2 _ (hjr_in_fix hnz)⟩⟩,
      hT.2.2.1, rfl, rfl, le_rfl, hJ.2.2.2, fun _ _ _ => rfl⟩
    · simp only [FO, List.mem_flatten, List.mem_map] at ho
      rcases ho with ⟨l, ⟨ec, hec, rfl⟩, hl⟩; have hwf := hFrames ec hec
      rcases List.mem_cons.1 hl with rfl | hl; · exact Or.inr (hwf.1 (ec.1, 280) (by simp)).1
      rcases List.mem_cons.1 hl with rfl | hl; · exact Or.inr (hwf.1 (ec.2, 104) (by simp)).1
      cases hl
    · simp only [FO, List.mem_flatten, List.mem_map] at ho
      rcases ho with ⟨l, ⟨ec, hec, rfl⟩, hl⟩
      rcases List.mem_cons.1 hl with rfl | hl
      · exact ((hFO_disj ec hec (ec.1, 280) (by simp [frameObjects])).1 u hu i hi).flip
      · rcases List.mem_cons.1 hl with rfl | hl
        · exact ((hFO_disj ec hec (ec.2, 104) (by simp [frameObjects])).1 u hu i hi).flip
        · cases hl
  have hbody_hoare : Hoare
      (fun s => StateRestoreLoopInv s0.memory S FO
        (globN s0 "journal") (globN s0 "journal_cap") (globN s0 "journal_n") s ∧
        CondTrue stateRestoreCond s)
      (.seq stateRestoreAssign stateRestoreTail)
      (fun r t => (r = none ∨ r = some .continue ∨ r = some .break) →
        StateRestoreLoopInv s0.memory S FO
          (globN s0 "journal") (globN s0 "journal_cap") (globN s0 "journal_n") t) := by
    refine ⟨fun {F'} st hc ⟨hIst, hct⟩ hnt hflow => ?_⟩
    obtain ⟨word, hw, hnz⟩ := hct
    obtain ⟨a, b, _, hb, hword⟩ := S06.evalAt_cmp st .lower _ _ word hw
    have hjb : st.globals.lookup (ofString "journal_n") = some (.val (.word b)) := by
      simpa [S06.evalAt, evalHOLExact] using hb
    have hcmp : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower a b = true := by
      by_contra hc'; simp [hc'] at hword; exact hnz hword
    have hlt : a.toNat < b.toNat := by
      simpa [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, decide_eq_true_eq, BitVec.lt_def] using hcmp
    have hassign : evaluateHOLFiniteState st stateRestoreAssign =
        (none, setGlobalHOLFinite (ofString "journal_n") (.val (.word (b - 1))) st) := by
      simp [stateRestoreAssign, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact,
        hjb, wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
        setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    rw [evaluateHOLFiniteState_seq_line780, hassign] at hnt hflow ⊢
    dsimp only at hnt hflow ⊢
    set s1 := setGlobalHOLFinite (ofString "journal_n") (.val (.word (b - 1))) st
    have hb_nat : globN st "journal_n" = b.toNat := by simp [globN, hjb]
    have hb1_lt : (b - 1).toNat < globN st "journal_n" := by
      have := b.isLt; rw [hb_nat]; simp [BitVec.toNat_sub]; omega
    have hs1_Inv : StateRestoreLoopInv s0.memory S FO
        (globN s0 "journal") (globN s0 "journal_cap") (globN s0 "journal_n") s1 ∧
        globN s1 "journal_n" < globN s0 "journal_n" := by
      obtain ⟨hA, hFOA, hjrA, hT', hPW, hj, hjc, hjn, hje, hmem⟩ := hIst
      have hg_other : ∀ k : MlS, k ≠ ofString "journal_n" → s1.globals.lookup k = st.globals.lookup k :=
        fun k hk => by simp [s1, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk.symm]
      have hg_nat : ∀ g : String, ofString g ≠ ofString "journal_n" → globN s1 g = globN st g :=
        fun g hg => globN_eq_of_lookup (hg_other (ofString g) hg).symm
      have hjn1 : globN s1 "journal_n" = (b - 1).toNat := by
        simp [s1, globN, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hal_eq : ∀ i, Allocated s1 i ↔ Allocated st i := fun i => by
        simp [Allocated, hg_nat "heap_ptr" (by decide), hg_nat "scratch_ptr" (by decide)]
      have hA1 : ArenaReady s1 := by
        obtain ⟨hg_st, hA_ok⟩ := hA
        refine ⟨guestInv_congr (s := st) (t := s1) rfl rfl rfl rfl hg_st, ?_⟩
        unfold ArenaOK at hA_ok ⊢
        rw [hg_nat "heap_ptr" (by decide), hg_nat "frame_mem_ptr" (by decide),
          hg_nat "scratch_ptr" (by decide)]
        exact ⟨hA_ok.1, hA_ok.2.1, hA_ok.2.2.1, hA_ok.2.2.2.1, hA_ok.2.2.2.2.1,
          hA_ok.2.2.2.2.2.1, hA_ok.2.2.2.2.2.2.1, hA_ok.2.2.2.2.2.2.2.1,
          globalsWord_update (s := st) (t := s1) (ofString "journal_n") (b - 1) rfl hA_ok.2.2.2.2.2.2.2.2⟩
      have hwf_eq : ∀ u ∈ S, HtabWF s1 u := fun u hu =>
        htabWF_congr_unhit hA.1 hA1.1 (hT' u hu).1 (fun _ _ _ _ _ _ => rfl)
      have hfp_eq : ∀ u ∈ S, htabFootprint s1 u = htabFootprint st u := fun u hu => by
        have hfp := (hT' u hu).1.1
        have ht_fp : (u, 88) ∈ htabFootprint st u := by simp [htabFootprint]
        have h264 : heapEnd ≤ 2 ^ 64 := by decide
        exact (htabFootprint_eq_of_hdr_unhit ((hfp _ ht_fp).2.1)
          (by have := (hfp _ ht_fp).1.2; omega) (fun _ _ _ _ => rfl)).2
      refine ⟨⟨hA1, fun o ho => (hal_eq _).2 (hFOA o ho), fun hnz => (hal_eq _).2 (hjrA hnz),
        fun u hu => ⟨hwf_eq u hu, fun i hi => ?_⟩, fun u hu v hv huv i hi j hj' => ?_,
        (hg_nat "journal" (by decide)).trans hj, (hg_nat "journal_cap" (by decide)).trans hjc,
        by omega, hje, hmem⟩, by omega⟩
      · rw [hfp_eq u hu] at hi; exact ⟨(hal_eq _).2 ((hT' u hu).2 i hi).1, ((hT' u hu).2 i hi).2⟩
      · rw [hfp_eq u hu] at hi; rw [hfp_eq v hv] at hj'; exact hPW u hu v hv huv i hi j hj'
    exact (hoare_stateRestoreTail s0.memory S FO
      (globN s0 "journal") (globN s0 "journal_cap") (globN s0 "journal_n") hJ.1 halign_s0 hset hdel).run
      s1 hc hs1_Inv hnt hflow
  have hwh := (Hoare.while_preserve
    (fun s hs => stateRestoreLoopInv_localsFree _ _ _ _ _ _ s s.locals (s.clock - 1) hs)
    hbody_hoare).run s0 hcode hInit (by rw [hm1_wh]; simp) (by rw [hm1_wh])
  rw [hm1_wh] at hwh; dsimp only at hwh
  intro ec hec; obtain ⟨ho1, ho2⟩ := hFO_mem ec hec
  exact ⟨fun a ha8 hc => by rw [hpost_eq]; exact hwh.2.2.2.2.2.2.2.2.2 a ha8 ⟨(ec.1, 280), ho1, hc⟩,
         fun a ha8 hc => by rw [hpost_eq]; exact hwh.2.2.2.2.2.2.2.2.2 a ha8 ⟨(ec.2, 104), ho2, hc⟩⟩

/-- `state_restore` called via `.call (some (none, none))` preserves `EvmInv`, `evmChain`, and `evmR`. -/
theorem call_state_restore_preserves_evmR
    (hek_sr : EvmKeeps EvmInv ["heap_ptr", "journal_n"] (ofString "state_restore"))
    (hset : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set"))
    (hdel : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_del"))
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {arg : ExpHOL 64}
    (hcode : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (hcall : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "state_restore") [arg]) =
      (none, post)) :
    EvmInv post ∧
    GlobalsKept ["heap_ptr", "journal_n"] s post ∧
    evmChain post = evmChain s ∧
    evmR post = evmR s ∧
    (∀ ec ∈ evmChain s, IvlUnhit s post (ec.1, 280) ∧ IvlUnhit s post (ec.2, 104)) := by
  obtain ⟨vals, body1, cal1, ret1, rv1, cpost1, _, hl1, hrun1, hpost_eq⟩ := call0_returned_inv hcall
  subst hpost_eq
  have hcode_lk1 : s.code.lookup (ofString "state_restore") =
      some ([(ofString "snap", .one)], sourceFnBody Guest.Software.guestFn_state_restore, .one) := by
    rw [hcode]; exact lookup_state_restore
  have hbody1 : body1 = sourceFnBody Guest.Software.guestFn_state_restore :=
    lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ _ _ _ _ _ hcode_lk1 hl1
  subst hbody1
  have hInv_ce : EvmInv (callEntryStateHOLFinite s cal1) := evmInv_congr_lc s cal1 (s.clock - 1) hInv
  have hStep := FunSpec.at_lookup hek_sr s hcode vals _ cal1 ret1 hl1 hInv_ce (by rw [hrun1]; simp)
  rw [hrun1] at hStep
  have hStep' := hStep (Or.inl ⟨rv1, rfl⟩)
  have hInv_cp : EvmInv cpost1 := hStep'.1
  have hg_cp : GlobalsKept ["heap_ptr", "journal_n"] (callEntryStateHOLFinite s cal1) cpost1 := hStep'.2.2.1
  have hch_cp : evmChain cpost1 = evmChain (callEntryStateHOLFinite s cal1) := hStep'.2.2.2
  have hpre_unhit := state_restore_preserves_head_frames hset hdel
    (callEntryStateHOLFinite s cal1) hcode hInv_ce rv1 (by rw [hrun1])
  have hcpost_eq : (evaluateHOLFiniteState (callEntryStateHOLFinite s cal1)
      (sourceFnBody Guest.Software.guestFn_state_restore)).2 = cpost1 := by rw [hrun1]
  rw [hcpost_eq] at hpre_unhit
  have hch_ce : evmChain (callEntryStateHOLFinite s cal1) = evmChain s :=
    evmChain_congr_lc s cal1 (s.clock - 1)
  rw [hch_ce] at hpre_unhit
  obtain ⟨hAs, _, _, _, _, _, hFrames, _, _, _, _, _, _⟩ := (evmInv_iff_at s).1 hInv
  have hR_post : evmR { cpost1 with locals := s.locals } = evmR s := by
    rw [evmR_congr_lc cpost1 _ cpost1.clock]
    unfold evmR
    rw [hch_cp, hch_ce]
    congr 1
    apply List.map_congr_left
    intro ec hec
    obtain ⟨hu1, _⟩ := hpre_unhit ec hec
    have hwf := hFrames ec hec
    obtain ⟨he1_lt, _, _, _⟩ := frameWF_bounds hAs.2 hwf
    have hec8 : ec.1 % 8 = 0 := (hwf.1 (ec.1, 280) (by simp)).2.1
    have hm64 : memW cpost1 (ec.1 + 64) = memW s (ec.1 + 64) :=
      memW_eq_of_ivlUnhit hu1 (by omega) he1_lt ⟨by omega, by omega⟩
    have hm192 : memW cpost1 (ec.1 + 192) = memW s (ec.1 + 192) :=
      memW_eq_of_ivlUnhit hu1 (by omega) he1_lt ⟨by omega, by omega⟩
    rw [hm64, hm192]
  exact ⟨evmInv_congr_lc cpost1 _ cpost1.clock hInv_cp,
    hg_cp,
    (evmChain_congr_lc cpost1 _ cpost1.clock).trans (hch_cp.trans hch_ce),
    hR_post,
    hpre_unhit⟩

/-- `frame_epilogue_spec` proved from `ek_state_restore`, `htab_set_spec`, and `htab_del_spec`. -/
theorem frame_epilogue_spec_of
    (hek_sr : EvmKeeps EvmInv ["heap_ptr", "journal_n"] (ofString "state_restore"))
    (hset : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set"))
    (hdel : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_del")) :
    FunSpec (fun s => EvmInv s ∧ EvmDone s)
      (OnReturn fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "frame_epilogue") := by
  refine ⟨[], sourceFnBody Guest.Software.guestFn_frame_epilogue, .one, lookup_frame_epilogue, ?_⟩
  intro F s hcode ⟨hInv, hDone⟩ _ _ v hv
  have hbody : sourceFnBody Guest.Software.guestFn_frame_epilogue =
      .seq (.ite (.cmp .notEqual
          (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 160)]))
          (.const (BitVec.ofNat 64 0)))
        (.call (some (none, none)) (ofString "state_restore")
          [.load .one (.op .add [.var .global (ofString "cur_cont"), .const (BitVec.ofNat 64 24)])])
        .skip) (.return (.const 0)) := rfl
  rw [hbody] at hv
  have hite_noret : ∀ u, (evaluateHOLFiniteState s
      (.ite (.cmp .notEqual
          (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 160)]))
          (.const (BitVec.ofNat 64 0)))
        (.call (some (none, none)) (ofString "state_restore")
          [.load .one (.op .add [.var .global (ofString "cur_cont"), .const (BitVec.ofNat 64 24)])])
        .skip)).1 ≠ some (.returned u) :=
    ite_ne_returned (fun t u => call0_ne_returned t _ _ u) (fun t u => by simp [evaluateHOLFiniteState_skip])
  obtain ⟨m1, hm1_ite, hrest1⟩ := seq_returned_inv hv hite_noret
  have hpost_eq : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_epilogue)).2 =
      emptyLocalsHOLFinite m1 := by
    rw [hbody, ← hrest1, evaluateHOLFiniteState_return]
    have hc0 : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
        (.const 0) = some (.val (.word 0)) := rfl
    have hle32 : sizeOfShapeWithContextHOL m1.structs
        (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by simp [shapeOfHOLExact]
    rw [hc0]; dsimp only; rw [if_pos hle32]
  change EvmInv (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_epilogue)).2 ∧
    EvmDone (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_epilogue)).2 ∧
    (evmChain (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_epilogue)).2).length =
      (evmChain s).length ∧
    evmR (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_epilogue)).2 ≤ evmR s
  rw [hpost_eq]; rw [evaluateHOLFiniteState_ite] at hm1_ite; revert hm1_ite
  split
  · split
    · rw [evaluateHOLFiniteState_skip]; intro hm1; injection hm1 with _ hm1_eq; subst hm1_eq
      exact ⟨evmInv_congr_lc s _ _ hInv, hDone,
        by rw [emptyLocalsHOLFinite, evmChain_congr_lc s _ s.clock],
        by rw [emptyLocalsHOLFinite, evmR_congr_lc s _ s.clock]⟩
    · intro hm1_call
      obtain ⟨hInv_m1, hg_m1, hch_m1, hR_m1, hpre_unhit⟩ :=
        call_state_restore_preserves_evmR hek_sr hset hdel hcode hInv hm1_call
      have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
      obtain ⟨hu_ev, hu_cc⟩ := hpre_unhit _ hhead_mem
      have hev_eq : globN m1 "ev" = globN s "ev" := globN_eq_of_lookup (hg_m1 (ofString "ev") (by decide))
      have hcc_eq : globN m1 "cur_cont" = globN s "cur_cont" :=
        globN_eq_of_lookup (hg_m1 (ofString "cur_cont") (by decide))
      obtain ⟨hAs, _, _, _, _, _, hFrames, _, _, _, _, _, _⟩ := (evmInv_iff_at s).1 hInv
      have hhead_wf := hFrames (globN s "ev", globN s "cur_cont") hhead_mem
      obtain ⟨he_lt, hc_lt, _, _⟩ := frameWF_bounds hAs.2 hhead_wf
      have hev8 : (globN s "ev") % 8 = 0 := (hhead_wf.1 (globN s "ev", 280) (by simp)).2.1
      have hcc8 : (globN s "cur_cont") % 8 = 0 := (hhead_wf.1 (globN s "cur_cont", 104) (by simp)).2.1
      have hm_cc32 := memW_eq_of_ivlUnhit hu_cc (a := globN s "cur_cont" + 32) (by omega) hc_lt ⟨by omega, by omega⟩
      have hm_ev104 := memW_eq_of_ivlUnhit hu_ev (a := globN s "ev" + 104) (by omega) he_lt ⟨by omega, by omega⟩
      have hm_ev56 := memW_eq_of_ivlUnhit hu_ev (a := globN s "ev" + 56) (by omega) he_lt ⟨by omega, by omega⟩
      have hm_ev0 := memW_eq_of_ivlUnhit hu_ev (a := globN s "ev") (by omega) he_lt ⟨by omega, by omega⟩
      have hDone_post : EvmDone (emptyLocalsHOLFinite m1) := by
        unfold EvmDone at hDone ⊢
        change memW m1 (globN m1 "cur_cont" + 32) ≠ 0 ∨
          memW m1 (globN m1 "ev" + 104) = 0 ∨ memW m1 (globN m1 "ev" + 56) ≤ memW m1 (globN m1 "ev")
        rw [hev_eq, hcc_eq, hm_cc32, hm_ev104, hm_ev56, hm_ev0]; exact hDone
      exact ⟨evmInv_congr_lc m1 _ m1.clock hInv_m1, hDone_post,
        by rw [emptyLocalsHOLFinite, evmChain_congr_lc m1 _ m1.clock, hch_m1],
        by rw [emptyLocalsHOLFinite, evmR_congr_lc m1 _ m1.clock, hR_m1]⟩
  · simp

end InitECandidate.Solver.Wave8GuestInv.R11Shards
