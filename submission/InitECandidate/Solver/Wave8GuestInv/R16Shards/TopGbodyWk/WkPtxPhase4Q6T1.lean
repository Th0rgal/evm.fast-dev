import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4Q6A

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase (stdKeep)
open InitECandidate.Solver.Wave8GuestInv.R13Shards
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

/-! # Phase 4Q6T1: the final receipt-list push runner

Instruction 39 pushes the fresh `stable_logs` list onto the block-out
receipt list (`bo + 72`).  This file provides the argument evaluation of
that call and a `lst_push` decCall runner that, on top of the generic
`p4Run_decCall_lst_push` facts, also exposes that the pushed list's backing
word stays nonzero across the callee (the block-out typing of the post
state needs it for the slot store). -/

/-- The final push arguments: the first loads the receipt-list header word
at `bo + 72`, the second is the constant `8`. -/
theorem p4Q8T_harg {F : Type} {u : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady u) {S Nd : List Nat} (hWT : WorldTypedWith u S Nd) (hE : TxEnv u)
    {w_l : BitVec 64} (hl72 : w_l.toNat = memW u (globN u "bo" + 72)) :
    evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a))
        [(.load .one (.op .add [(.var .global (ofString "bo")),
            (.const 0x0000000000000048#64)])),
         (.const 0x0000000000000008#64)] = some [.val (.word w_l), .val (.word 8)] := by
  have ⟨halloc, hwords⟩ := bo_words hWT.2.2.1 hE.bo_nz
  have hbo264 : globN u "bo" + 88 ≤ 2 ^ 64 := (ivl_allocated_bound hAR.2 halloc).2
  obtain ⟨bw, hgl, hbwn⟩ := p4Loop31_boWord hE.bo_nz (by omega)
  have h48 : (0x0000000000000048#64 : BitVec 64).toNat = 72 := rfl
  have hb72 : BitVec.ofNat 64 (globN u "bo" + 72) = bw + 0x0000000000000048#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    have hadd : (bw + 0x0000000000000048#64).toNat = bw.toNat + 72 := by
      rw [BitVec.toNat_add, h48]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hadd, hbwn]
    exact Nat.mod_eq_of_lt (by omega)
  have hw72 : WordAt u (globN u "bo" + 72) := by
    have h9 : WordAt u (globN u "bo" + 8 * 9) := hwords.2.2 9 (show 9 < 88 / 8 by decide)
    have heq : globN u "bo" + 8 * 9 = globN u "bo" + 72 := by ring
    rwa [heq] at h9
  obtain ⟨w', hdom', hcell'⟩ := hw72
  rw [hb72] at hdom' hcell'
  have hload0 : @evalHOLExact 64 F _ u.toExact
      (fun x => Classical.propDecidable (u.memaddrs x))
      (.load .one (.op .add [.var .global (ofString "bo"), (.const 0x0000000000000048#64)])) =
      some (.val (.word w')) := by
    have hz : (0x0000000000000048#64 : BitVec 64) + 0 = 0x0000000000000048#64 :=
      BitVec.add_zero _
    simp only [evalAt, evalHOLExact, evalListHOLExact, toExact, hgl, valueIsWord, valueWord,
      wordOpHOL, wordOp, List.all, List.map, Option.map, ↓reduceIte, List.foldr, Bool.and_self,
      memLoadHOLExact, isWfShapeExactHOL, hz, hdom', hcell']
  have hm : memW u (bw + 0x0000000000000048#64).toNat = w_l.toNat := by
    have h1 : (bw + 0x0000000000000048#64).toNat = globN u "bo" + 72 := by
      rw [BitVec.toNat_add, h48, ← hbwn]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, hl72]
  have hw'w : w' = w_l := by
    apply BitVec.eq_of_toNat_eq
    have hmem : memW u (bw + 0x0000000000000048#64).toNat = w'.toNat := by
      have hround : ∀ x : BitVec 64, BitVec.ofNat 64 x.toNat = x := fun x => by simp
      unfold memW
      rw [hround (bw + 0x0000000000000048#64), hcell']
    rw [← hm, hmem]
  rw [hw'w] at hload0
  have hconst : @evalHOLExact 64 F _ u.toExact
      (fun x => Classical.propDecidable (u.memaddrs x))
      (.const 0x0000000000000008#64) = some (.val (.word 0x0000000000000008#64)) := rfl
  rw [evalListHOLFinite_eq_toExact]
  simp only [evalListHOLExact, hload0, hconst]
  rfl

/-- The `lst_push` decCall runner of `p4Run_decCall_lst_push`, additionally
handing the continuation the nonzero backing word of the pushed list at the
callee's post state. -/
theorem p4Q8T_decCall_lst_push {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    (hbase : PtxRelBase true entry s)
    (hc : s.code = originalRuntimeCode)
    (w_l : BitVec 64)
    (hl_choice : w_l.toNat = memW s (globN s "bo" + 40) ∨
      w_l.toNat = memW s (globN s "bo" + 72))
    (hlist_nz : memW s w_l.toNat ≠ 0)
    (name : MlS) (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (harg : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
      some [.val (.word w_l), .val (.word 8)])
    (htail : ∀ (w : BitVec 64) (post : PanSemStateFiniteExact 64 F),
      (∀ a : BitVec 64, ¬ CellHits a.toNat (w_l.toNat, 24) →
        ¬ CellHits a.toNat (InitECandidate.Solver.Wave8Contracts.M08.heapFree s) →
        post.memory a = s.memory a) →
      (w.toNat % 8 = 0 ∧
        Inside (w.toNat, 8) (memW post w_l.toNat)
          (memW post w_l.toNat + 8 * memW post (w_l.toNat + 16)) ∧
        memW post (w_l.toNat + 8) = memW s (w_l.toNat + 8) + 1 ∧
        w.toNat = memW post w_l.toNat + 8 * memW s (w_l.toNat + 8) ∧
        (memW s w_l.toNat ≠ 0 → ∀ k, k < memW s (w_l.toNat + 8) →
          memW post (memW post w_l.toNat + 8 * k) = memW s (memW s w_l.toNat + 8 * k))) →
      memW post w_l.toNat ≠ 0 →
      WorldStep (fun _ => []) ["heap_ptr"] stdKeep RetListSlotStrong
        (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update
          (ofString "l", .val (.word w_l))).update (ofString "esz", .val (.word 8))))
        (some (.returned (.val (.word w)))) post →
      post.code = originalRuntimeCode →
      PtxRelRunStrong entry tail
        (setVarHOLFinite name (.val (.word w)) { post with locals := s.locals })) :
    PtxRelRunStrong entry (.decCall name .one (ofString "lst_push") args tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres ⊢
  rw [harg] at hres ⊢
  dsimp only at hres ⊢
  have hlk := pan_two_word_lookup s.code.lookup (ofString "lst_push")
    (ofString "l") (ofString "esz") (sourceFnBody Guest.Software.guestFn_lst_push) w_l 8
    (by decide) (by rw [hc]; exact R13Shards.lookup_lst_push)
  rw [hlk] at hres ⊢
  dsimp only at hres ⊢
  by_cases hcz : s.clock = 0
  · simp only [hcz, ↓reduceIte] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hcz, ↓reduceIte] at hres ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "l", (.val (.word w_l) : ValueHOL 64))).update
        (ofString "esz", (.val (.word 8) : ValueHOL 64)) with hcmap_def
    have hW_ent : WorldOK (callEntryStateHOLFinite s cmap) :=
      PtxP1.worldOK_callEntry hbase.world cmap
    have hent_l : (callEntryStateHOLFinite s cmap).locals.lookup (ofString "l") =
        some (.val (.word w_l)) := by
      simp [callEntryStateHOLFinite, hcmap_def, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "l" ≠ ofString "esz" by decide,
        show ofString "esz" ≠ ofString "l" by decide]
    have hent_esz : (callEntryStateHOLFinite s cmap).locals.lookup (ofString "esz") =
        some (.val (.word 8)) := by
      simp [callEntryStateHOLFinite, hcmap_def, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "esz" ≠ ofString "l" by decide]
    have hentl : locN (callEntryStateHOLFinite s cmap) "l" = w_l.toNat := by
      simp [locN, hent_l]
    have hentesz : locN (callEntryStateHOLFinite s cmap) "esz" = 8 := by
      simp [locN, hent_esz]
    have hbo_nz : globN s "bo" ≠ 0 := by
      obtain ⟨⟨_, hbo_nz_e, _, _, _⟩, _, _, _, _⟩ := hbase.ready_entry
      have hge : globN s "bo" = globN entry "bo" :=
        globN_eq_of_lookup (hbase.globals _ (by decide))
      rw [hge]; exact hbo_nz_e
    have hPre_ent : BoListArgStrong (callEntryStateHOLFinite s cmap) :=
      ⟨hW_ent, ⟨hW_ent, hbo_nz, by rw [hentl]; exact hl_choice, hentesz⟩, by
        rw [hentl]; exact hlist_nz⟩
    have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
      (callEntryStateHOLFinite s cmap) (sourceFnBody Guest.Software.guestFn_lst_push)).1
    rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_lst_push) with ⟨rb, post⟩
    have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_lst_push) = (rb, post) := hb
    rw [hb] at hmeta
    simp only [hb] at hres ⊢
    cases rb with
    | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    | some cr =>
      cases cr with
      | timeOut | error | «break» | «continue» | finalFfi _ =>
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      | exception eid ev =>
        dsimp only at hres ⊢
        have hspec := wk_lst_push_strong.at_lookup s hc
          [.val (.word w_l), .val (.word 8)] (sourceFnBody Guest.Software.guestFn_lst_push)
          cmap .one hlk hPre_ent (by rw [hb']; simp)
        rw [hb'] at hspec
        have hstep0 := hspec hres
        have hstep_s : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra s
            (some (.exception eid ev)) post := by
          refine worldStep_congr_R ?_
            (R13Shards.worldStep_with_locals hstep0 s.locals s.clock)
          rfl
        have hex := ptxRelBase_exception_worldStep hbase
          (by intro p hp; cases hp) (by intro p hp; cases hp)
          (by intro g hg
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
              subst hg; decide)
          ptxKeepSub_stdKeep hstep_s
        exact ptxWorldStep_strong_with_locals_right' .empty post.clock hex
      | returned v =>
        dsimp only at hres ⊢
        have hspec := wk_lst_push_strong.at_lookup s hc
          [.val (.word w_l), .val (.word 8)] (sourceFnBody Guest.Software.guestFn_lst_push)
          cmap .one hlk hPre_ent (by rw [hb']; simp)
        rw [hb'] at hspec
        have hstep0 := hspec (Or.inl ⟨v, rfl⟩)
        obtain ⟨S_e, hWT_e_ex⟩ := hW_ent.2
        obtain ⟨Nd_e, hWT_e⟩ := (worldTyped_iff_with (callEntryStateHOLFinite s cmap) S_e).1 hWT_e_ex
        obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hQ⟩ :=
          hstep0.2.2.2.2 S_e Nd_e hWT_e (by intro i hi; cases hi)
        obtain ⟨w, hvw, hal, hin, hlen, hslot, hprefix⟩ := hQ.2 v rfl
        rw [hvw] at hstep0 hres ⊢
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh, ↓reduceIte] at hres ⊢
        have hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (w_l.toNat, 24) →
            ¬ CellHits a.toNat (InitECandidate.Solver.Wave8Contracts.M08.heapFree s) →
            post.memory a = s.memory a := by
          intro a h1 h2
          refine hQ.1 a (by rw [hentl]; exact h1) h2
        have hback : memW post w_l.toNat ≠ 0 :=
          p4Q_lst_push_body_backing_nonzero (callEntryStateHOLFinite s cmap) post w_l v hc
            hW_ent.1 hent_l hlist_nz hb'
        have hpush : w.toNat % 8 = 0 ∧
            Inside (w.toNat, 8) (memW post w_l.toNat)
              (memW post w_l.toNat + 8 * memW post (w_l.toNat + 16)) ∧
            memW post (w_l.toNat + 8) = memW s (w_l.toNat + 8) + 1 ∧
            w.toNat = memW post w_l.toNat + 8 * memW s (w_l.toNat + 8) ∧
            (memW s w_l.toNat ≠ 0 → ∀ k, k < memW s (w_l.toNat + 8) →
              memW post (memW post w_l.toNat + 8 * k) = memW s (memW s w_l.toNat + 8 * k)) := by
          rw [hentl] at hin hlen hslot hprefix
          exact ⟨hal, hin, hlen, hslot, hprefix⟩
        exact ptxWorldStep_strong_with_locals_right'
          (HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState
              (setVarHOLFinite name (.val (.word w)) { post with locals := s.locals }) tail).2.locals
            (name, s.locals.lookup name))
          (evaluateHOLFiniteState
            (setVarHOLFinite name (.val (.word w)) { post with locals := s.locals }) tail).2.clock
          (htail w post hmem hpush hback hstep0 (hmeta.trans hc) hres)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
