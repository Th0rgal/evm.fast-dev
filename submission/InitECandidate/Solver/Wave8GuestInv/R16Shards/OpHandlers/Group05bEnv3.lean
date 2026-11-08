import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.FrameBase

/-! # OpHandlerSpec Group 05bEnv3 (`OpHandlers-A`): `bs+56..72` world-state congruence -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8Contracts.M23

def bufRegBs {F : Type} (s : PanSemStateFiniteExact 64 F) (gn : String × Nat) : Ivl :=
  (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)

def noBsState {F : Type} (s : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F :=
  { s with globals := s.globals.update (ofString "bs", .val (.word 0#64)) }

theorem bs56_disj_worldTypedIvls {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hWT : WorldTypedWith s S Nd) (hbs_nz : globN s "bs" ≠ 0) :
    ∀ i ∈ worldTypedIvls s S Nd,
      i = (globN s "bs", 80) ∨ i.2 = 0 ∨ Disj (globN s "bs" + 56, 16) i := by
  obtain ⟨hT, _, hF, hTr⟩ := hWT
  have hsz : (if globN s "bs" = 0 then 0 else 80) = 80 := if_neg hbs_nz
  have hmem_fix : (globN s "bs", 80) ∈ fixedObjects s := by
    have := typedRec_in_fixedObjects s (g := "bs") (sz := 80) (by decide)
    rwa [hsz] at this
  have hsub : ∀ i : Ivl, Disj (globN s "bs", 80) i → Disj (globN s "bs" + 56, 16) i := fun i hd => by
    rcases hd with h | h | h | h
    · exact Or.inl (by dsimp only at h ⊢; omega)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (by dsimp only at h ⊢; omega)))
    · exact Or.inr (Or.inr (Or.inr (by dsimp only at h ⊢; omega)))
  intro i hi
  unfold worldTypedIvls at hi; simp only [List.mem_append] at hi
  rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
  · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
    exact Or.inr (Or.inr (hsub i (Wave8Contracts.M23.Disj.symm (((hT.2.1 t ht).2 i hfp).2 _ hmem_fix))))
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
    by_cases hrb : r.1 = "bs"
    · have hrsz : r = ("bs", 80) := by
        simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp at hrb ⊢
      subst hrsz; exact Or.inl (by simp [hsz])
    · by_cases hr0 : globN s r.1 = 0
      · exact Or.inr (Or.inl (by simp [hr0]))
      · right; right; apply hsub
        have hbs_gb : ("bs", 80) ∈ globalBuffers := by decide
        have hr_gb : r ∈ globalBuffers := by
          simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with h | h | h | h <;> (rw [h]; decide)
        have hpw_gb : (globalBuffers.map (bufRegBs s)).Pairwise Disj :=
          (List.pairwise_append.1 (List.pairwise_append.1 (List.pairwise_append.1 hF.2).1).1).1
        have : Std.Symm (fun a b : String × Nat => Disj (bufRegBs s a) (bufRegBs s b)) :=
          ⟨fun _ _ h => Wave8Contracts.M23.Disj.symm h⟩
        have hne : ("bs", 80) ≠ r := fun h => hrb (congrArg Prod.fst h).symm
        simpa [bufRegBs, hsz] using (List.pairwise_map.1 hpw_gb).forall hbs_gb hr_gb hne
  · simp only [List.mem_singleton] at h3; subst h3
    right; right; apply hsub
    have hpw12 := (List.pairwise_append.1 (List.pairwise_append.1 hF.2).1).1
    have hm1 : (globN s "bs", 80) ∈ globalBuffers.map (bufRegBs s) := by
      rw [← hsz]; exact List.mem_map.2 ⟨("bs", 80), by decide, rfl⟩
    exact (List.pairwise_append.1 hpw12).2.2 _ hm1 _ (List.mem_singleton.2 rfl)
  · right; right; apply hsub
    have hpw13 := (List.pairwise_append.1 hF.2).1
    have hm1 : (globN s "bs", 80) ∈ globalBuffers.map (bufRegBs s) ++
        [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] := by
      apply List.mem_append_left; rw [← hsz]; exact List.mem_map.2 ⟨("bs", 80), by decide, rfl⟩
    exact (List.pairwise_append.1 hpw13).2.2 _ hm1 _ h4
  · right; right; apply hsub
    have hm1 : (globN s "bs", 80) ∈ globalBuffers.map (bufRegBs s) ++
        [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
        blockOutObjects s := by
      apply List.mem_append_left; apply List.mem_append_left
      rw [← hsz]; exact List.mem_map.2 ⟨("bs", 80), by decide, rfl⟩
    exact (List.pairwise_append.1 hF.2).2.2 _ hm1 _ h5
  · right; right; apply hsub
    exact Wave8Contracts.M23.Disj.symm ((hTr.2.1 i h6).2 _ hmem_fix)

theorem bs56_noBs_typed {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) (S : List Nat) (hW : WorldTyped s S)
    (Nd : List Nat) (hTr : TriesTypedWith s S Nd) (hbs0 : globN s "bs" ≠ 0)
    (heff : ByteRegionEffect s post [(globN s "bs" + 56, 16)]) :
    ArenaReady (noBsState s) ∧
    ArenaReady (noBsState post) ∧
    TablesTyped (noBsState s) S ∧
    JournalTyped (noBsState s) S ∧
    FixedTyped (noBsState s) ∧
    (∀ t, HtabWF s t → HtabWF (noBsState s) t) ∧
    (∀ t, HtabWF (noBsState post) t → HtabWF post t) ∧
    (∀ {Nd' : List Nat}, TriesTypedWith s S Nd' →
      TriesTypedWith (noBsState s) S Nd' ∧ SameTypedCells (noBsState s) (noBsState post) S Nd') := by
  have hWT : WorldTypedWith s S Nd := ⟨hW.1, hW.2.1, hW.2.2.1, hTr⟩
  have hApost : ArenaReady post :=
    ⟨guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAs.1,
     arenaOK_congr heff.globals hAs.2⟩
  have hsz : (if globN s "bs" = 0 then 0 else 80) = 80 := if_neg hbs0
  have hfix_bs : (globN s "bs", 80) ∈ fixedObjects s := by
    have := typedRec_in_fixedObjects s (g := "bs") (sz := 80) (by decide); rwa [hsz] at this
  rcases hWT.2.2.1.1 _ hfix_bs with h0 | ⟨_, hbs_wok⟩
  · dsimp at h0; omega
  let sNoBs := noBsState s
  let pNoBs := noBsState post
  have hsNoBs_bs : globN sNoBs "bs" = 0 := by simp [sNoBs, noBsState, globN, HolFiniteMapExact.lookup_update, FUPDATE]
  have hsNoBs_other : ∀ g : String, ofString "bs" ≠ ofString g → globN sNoBs g = globN s g := fun g hne => by
    simp [sNoBs, noBsState, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have hpNoBs_other : ∀ g : String, ofString "bs" ≠ ofString g → globN pNoBs g = globN s g := fun g hne => by
    simp [pNoBs, noBsState, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne, heff.globals]
  have hbo_s : blockOutObjects sNoBs = blockOutObjects s := by
    unfold blockOutObjects; rw [hsNoBs_other "bo" (by decide)]; rfl
  have hbrec_s : balRecords sNoBs = balRecords s := by
    unfold balRecords; rw [hsNoBs_other "bal_accounts" (by decide)]; rfl
  have hbal_s : balObjects sNoBs = balObjects s := by
    unfold balObjects; rw [hbrec_s]; rfl
  have hAR_sNoBs : ArenaReady sNoBs :=
    ⟨guestInv_congr (s := s) (t := sNoBs) rfl rfl rfl rfl hAs.1, by
      unfold ArenaOK
      simp only [hsNoBs_other "heap_ptr" (by decide), hsNoBs_other "frame_mem_ptr" (by decide),
        hsNoBs_other "scratch_ptr" (by decide)]
      exact ⟨hAs.2.1, hAs.2.2.1, hAs.2.2.2.1, hAs.2.2.2.2.1, hAs.2.2.2.2.2.1,
        hAs.2.2.2.2.2.2.1, hAs.2.2.2.2.2.2.2.1, hAs.2.2.2.2.2.2.2.2.1,
        globalsWord_update (s := s) (t := sNoBs) (ofString "bs") 0#64 rfl hAs.2.2.2.2.2.2.2.2.2⟩⟩
  have hAR_pNoBs : ArenaReady pNoBs :=
    ⟨guestInv_congr (s := post) (t := pNoBs) rfl rfl rfl rfl hApost.1, by
      unfold ArenaOK
      simp only [hpNoBs_other "heap_ptr" (by decide), hpNoBs_other "frame_mem_ptr" (by decide),
        hpNoBs_other "scratch_ptr" (by decide)]
      exact ⟨hAs.2.1, hAs.2.2.1, hAs.2.2.2.1, hAs.2.2.2.2.1, hAs.2.2.2.2.2.1,
        hAs.2.2.2.2.2.2.1, hAs.2.2.2.2.2.2.2.1, hAs.2.2.2.2.2.2.2.2.1,
        globalsWord_update (s := post) (t := pNoBs) (ofString "bs") 0#64 rfl hApost.2.2.2.2.2.2.2.2.2⟩⟩
  have hfc_eq : ∀ (x y : PanSemStateFiniteExact 64 F), x.memory = y.memory →
      ∀ nodes hd Fr, FreeChain x nodes hd Fr ↔ FreeChain y nodes hd Fr := by
    intro x y hmem nodes hd Fr
    induction Fr generalizing hd with
    | nil => exact Iff.rfl
    | cons f rest ih => simp only [FreeChain, nodeF, memW, hmem]; exact and_congr Iff.rfl (ih _)
  have hhtabWF_s : ∀ t, HtabWF s t → HtabWF sNoBs t := fun t h => by
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, L, I, Fr, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20⟩ := h
    exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, L, I, Fr, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
      (hfc_eq s sNoBs rfl _ _ Fr).1 c20⟩
  have hhtabWF_p : ∀ t, HtabWF pNoBs t → HtabWF post t := fun t h => by
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, L, I, Fr, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20⟩ := h
    exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, L, I, Fr, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
      (hfc_eq pNoBs post rfl _ _ Fr).1 c20⟩
  have hfix_sub_nobs : ∀ j ∈ fixedObjects sNoBs, j = (0, 0) ∨ j ∈ fixedObjects s := by
    unfold fixedObjects
    rw [hbo_s, hbal_s, hsNoBs_other "journal" (by decide), hsNoBs_other "journal_cap" (by decide)]
    intro j hj
    rcases List.mem_append.1 hj with h123 | h4
    · rcases List.mem_append.1 h123 with h12 | h3
      · rcases List.mem_append.1 h12 with h1 | h2
        · obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 h1
          by_cases hb : gn.1 = "bs"
          · exact Or.inl (by simp [hb, hsNoBs_bs])
          · have hne : ofString "bs" ≠ ofString gn.1 :=
              (show ∀ x ∈ globalBuffers, x.1 ≠ "bs" → ofString "bs" ≠ ofString x.1 by decide) gn hgn hb
            rw [hsNoBs_other _ hne]
            exact Or.inr (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
              (List.mem_map.2 ⟨gn, hgn, rfl⟩))))
        · exact Or.inr (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h2)))
      · exact Or.inr (List.mem_append_left _ (List.mem_append_right _ h3))
    · exact Or.inr (List.mem_append_right _ h4)
  have hF_sNoBs : FixedTyped sNoBs := by
    let tailIvls := [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
      blockOutObjects s ++ balObjects s
    have hf1 : fixedObjects sNoBs = globalBuffers.map (bufRegBs sNoBs) ++ tailIvls := by
      unfold fixedObjects bufRegBs
      rw [hbo_s, hbal_s, hsNoBs_other "journal" (by decide), hsNoBs_other "journal_cap" (by decide)]
      simp [tailIvls, List.append_assoc]
    have hf2 : fixedObjects s = globalBuffers.map (bufRegBs s) ++ tailIvls := by
      unfold fixedObjects bufRegBs; simp [tailIvls, List.append_assoc]
    have hpw_s := hWT.2.2.1.2; rw [hf2] at hpw_s
    have hpw_gb_s := List.pairwise_map.1 (List.pairwise_append.1 hpw_s).1
    have hbuf_eq : ∀ gn ∈ globalBuffers, bufRegBs sNoBs gn = (0, 0) ∨ bufRegBs sNoBs gn = bufRegBs s gn := by
      intro gn hgn
      by_cases hb : gn.1 = "bs"
      · exact Or.inl (by simp [bufRegBs, hb, hsNoBs_bs])
      · have hne : ofString "bs" ≠ ofString gn.1 :=
          (show ∀ x ∈ globalBuffers, x.1 ≠ "bs" → ofString "bs" ≠ ofString x.1 by decide) gn hgn hb
        exact Or.inr (by simp [bufRegBs, hsNoBs_other _ hne])
    unfold FixedTyped; refine ⟨fun o ho => ?_, ?_⟩
    · rcases hfix_sub_nobs o ho with rfl | hos
      · exact Or.inl rfl
      · rcases hWT.2.2.1.1 o hos with hz | ⟨hal, hw⟩
        · exact Or.inl hz
        · refine Or.inr ⟨?_, hw⟩; unfold Allocated at hal ⊢
          rwa [hsNoBs_other "heap_ptr" (by decide), hsNoBs_other "scratch_ptr" (by decide)]
    · rw [hf1]
      refine List.pairwise_append.2 ⟨List.pairwise_map.2 ?_, (List.pairwise_append.1 hpw_s).2.1, fun x hx y hy => ?_⟩
      · rw [List.pairwise_iff_getElem] at hpw_gb_s ⊢
        intro i j hi hj hij
        rcases hbuf_eq _ (List.getElem_mem hi) with h01 | he1
        · rw [h01]; exact Or.inl rfl
        · rcases hbuf_eq _ (List.getElem_mem hj) with h02 | he2
          · rw [h02]; exact Or.inr (Or.inl rfl)
          · rw [he1, he2]; exact hpw_gb_s i j hi hj hij
      · obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hx
        rcases hbuf_eq gn hgn with h0 | heq
        · rw [h0]; exact Or.inl rfl
        · rw [heq]; exact (List.pairwise_append.1 hpw_s).2.2 _ (List.mem_map.2 ⟨gn, hgn, rfl⟩) y hy
  have hj_s : journalRoleSlots sNoBs = journalRoleSlots s := by
    unfold journalRoleSlots journalRole
    rw [hsNoBs_other "journal_n" (by decide), hsNoBs_other "journal" (by decide),
        hsNoBs_other "ts" (by decide)]; rfl
  have hT_sNoBs : TablesTyped sNoBs S := by
    obtain ⟨hnd, htwf, htpw, hws, _, hts, hgr, _, hts32, hbal_ok, hbo_ok, hroles⟩ := hWT.1
    have hsl : (worldRoleSlots sNoBs).Sublist (worldRoleSlots s) := by
      unfold worldRoleSlots
      rw [show recRoles sNoBs "ws" [(16, "ws+16"), (32, "ws+32")] =
            recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] by
            unfold recRoles; rw [hsNoBs_other "ws" (by decide)]; rfl,
          show recRoles sNoBs "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
            (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] = [] by
            unfold recRoles; simp [hsNoBs_bs],
          show recRoles sNoBs "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
            (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
            recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
              (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] by
            unfold recRoles; rw [hsNoBs_other "ts" (by decide)]; rfl,
          hsNoBs_other "bal_accounts" (by decide), hsNoBs_other "bal_idx_accts" (by decide),
          hsNoBs_other "bal_idx_stor" (by decide),
          show nestRoles sNoBs "bs" "bs.inner" = [] by unfold nestRoles; simp [hsNoBs_bs],
          show nestRoles sNoBs "ts" "ts.inner" = nestRoles s "ts" "ts.inner" by
            unfold nestRoles; rw [hsNoBs_other "ts" (by decide)]; rfl,
          hbrec_s]
      exact List.Sublist.filter _ (List.Sublist.append (List.Sublist.append (List.Sublist.append
        (List.Sublist.append (List.Sublist.append (List.Sublist.append (List.Sublist.refl _)
          (List.nil_sublist _)) (List.Sublist.refl _)) (List.Sublist.refl _)) (List.nil_sublist _))
        (List.Sublist.refl _)) (List.Sublist.refl _))
    refine ⟨hnd, ?_, htpw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht; refine ⟨hhtabWF_s t (htwf t ht).1, fun i hi => ⟨?_, fun j hj => ?_⟩⟩
      · have hal := ((htwf t ht).2 i hi).1; unfold Allocated at hal ⊢
        rwa [hsNoBs_other "heap_ptr" (by decide), hsNoBs_other "scratch_ptr" (by decide)]
      · rcases hfix_sub_nobs j hj with rfl | hjs
        · exact Or.inr (Or.inl rfl)
        · exact ((htwf t ht).2 i hi).2 j hjs
    · intro k hk; rw [hsNoBs_other "ws" (by decide)]; exact hws k hk
    · intro _ _ h; exact absurd hsNoBs_bs h
    · intro k hk; rw [hsNoBs_other "ts" (by decide)]; exact hts k hk
    · intro g hg
      have hne : ofString "bs" ≠ ofString g :=
        (show ∀ x ∈ globalTableRoots, ofString "bs" ≠ ofString x by decide) g hg
      rw [hsNoBs_other g hne]; exact hgr g hg
    · intro h; exact absurd hsNoBs_bs h
    · rw [hsNoBs_other "ts" (by decide)]; exact hts32
    · rw [hbrec_s]; exact hbal_ok
    · rw [hsNoBs_other "bo" (by decide)]; exact hbo_ok
    · unfold RolesOK at hroles ⊢; rw [hj_s]
      have hmem_sub : ∀ x ∈ worldRoleSlots sNoBs ++ journalRoleSlots s,
          x ∈ worldRoleSlots s ++ journalRoleSlots s := fun x hx => by
        rcases List.mem_append.1 hx with h1 | h2
        · exact List.mem_append_left _ (hsl.subset h1)
        · exact List.mem_append_right _ h2
      exact ⟨fun a ha => hroles.1 a (hmem_sub a ha), hroles.2.1.sublist hsl,
        fun a ha b hb => hroles.2.2 a ha b (hmem_sub b hb)⟩
  have hJ_sNoBs : JournalTyped sNoBs S := by
    obtain ⟨j1, j2, j3, j4⟩ := hWT.2.1
    unfold JournalTyped
    simp only [hsNoBs_other "journal_n" (by decide), hsNoBs_other "journal_cap" (by decide),
      hsNoBs_other "journal" (by decide)]
    refine ⟨j1, j2, ?_, j4⟩
    rcases j3 with hz | ⟨hal, hw⟩
    · exact Or.inl hz
    · refine Or.inr ⟨?_, hw⟩; unfold Allocated at hal ⊢
      rwa [hsNoBs_other "heap_ptr" (by decide), hsNoBs_other "scratch_ptr" (by decide)]
  have hTr_sNoBs : ∀ {Nd' : List Nat}, TriesTypedWith s S Nd' → TriesTypedWith sNoBs S Nd' := by
    intro Nd' hTr'
    refine ⟨⟨fun n hn => ?_, hTr'.1.2⟩, fun o ho => ⟨(hTr'.2.1 o ho).1, fun j hj => ?_⟩, ?_⟩
    · obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hTr'.1.1 n hn
      have hal_c : ∀ i : Ivl, Allocated s i → Allocated sNoBs i := fun i h => by
        unfold Allocated at h ⊢
        rwa [hsNoBs_other "heap_ptr" (by decide), hsNoBs_other "scratch_ptr" (by decide)]
      refine ⟨c1, hal_c _ c2, c3, c4, c5, c6, fun h12 => ?_, c8, c9, c10⟩
      rcases c7 h12 with hz | ⟨hnib, hal, hin, hdj⟩
      · exact Or.inl hz
      · exact Or.inr ⟨hnib, hal_c _ hal, hin, hdj⟩
    · rcases hfix_sub_nobs j hj with rfl | hjs
      · exact Or.inr (Or.inl rfl)
      · exact (hTr'.2.1 o ho).2 j hjs
    · rw [hsNoBs_other "ws" (by decide)]; exact hTr'.2.2
  have hcell_of : ∀ {Nd' : List Nat}, TriesTypedWith s S Nd' → SameTypedCells sNoBs pNoBs S Nd' := by
    intro Nd' hTr'
    have hWT' : WorldTypedWith s S Nd' := ⟨hW.1, hW.2.1, hW.2.2.1, hTr'⟩
    have hwti' : ∀ i ∈ worldTypedIvls sNoBs S Nd',
        i = (0, 0) ∨ (i ∈ worldTypedIvls s S Nd' ∧ i ≠ (globN s "bs", 80)) := by
      intro i hi; unfold worldTypedIvls at hi
      rw [hbo_s, hbal_s, hsNoBs_other "journal" (by decide), hsNoBs_other "journal_cap" (by decide)] at hi
      simp only [List.mem_append] at hi
      rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
      · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
        exact Or.inr ⟨mem_worldTypedIvls_htab ht hfp, fun heq => by
          have hd := ((hWT'.1.2.1 t ht).2 i hfp).2 _ hfix_bs
          rw [heq] at hd; rcases hd with c | c | c | c <;> dsimp at c <;> omega⟩
      · obtain ⟨rec, hr, rfl⟩ := List.mem_map.1 h2
        by_cases hrb : rec.1 = "bs"
        · exact Or.inl (by simp [hrb, hsNoBs_bs])
        · have hne_ml : ofString "bs" ≠ ofString rec.1 :=
            (show ∀ x ∈ typedRecords, x.1 ≠ "bs" → ofString "bs" ≠ ofString x.1 by decide) rec hr hrb
          rw [hsNoBs_other rec.1 hne_ml]
          refine Or.inr ⟨mem_worldTypedIvls_typedRec hr, fun heq => ?_⟩
          have h2' := congrArg Prod.snd heq; dsimp only at h2'
          by_cases h0 : globN s rec.1 = 0
          · rw [if_pos h0] at h2'; omega
          · rw [if_neg h0] at h2'
            exact hrb ((show ∀ x ∈ typedRecords, x.2 = 80 → x.1 = "bs" by decide) rec hr h2')
      · simp only [List.mem_singleton] at h3; subst h3
        by_cases hjc0 : globN s "journal_cap" = 0
        · exact Or.inl (by simp [hjc0])
        · rw [if_neg hjc0]; refine Or.inr ⟨mem_worldTypedIvls_journal hjc0, fun heq => ?_⟩
          have hpw12 := (List.pairwise_append.1 (List.pairwise_append.1 hWT'.2.2.1.2).1).1
          have hm1 : (globN s "bs", 80) ∈ globalBuffers.map (bufRegBs s) := by
            rw [← hsz]; exact List.mem_map.2 ⟨("bs", 80), by decide, rfl⟩
          have hd := (List.pairwise_append.1 hpw12).2.2 _ hm1 _ (List.mem_singleton.2 rfl)
          rw [if_neg hjc0] at hd; rw [heq] at hd; rcases hd with c | c | c | c <;> dsimp at c <;> omega
      · refine Or.inr ⟨mem_worldTypedIvls_blockOut h4, fun heq => ?_⟩
        have hpw13 := (List.pairwise_append.1 hWT'.2.2.1.2).1
        have hm1 : (globN s "bs", 80) ∈ globalBuffers.map (bufRegBs s) ++
            [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] := by
          apply List.mem_append_left; rw [← hsz]; exact List.mem_map.2 ⟨("bs", 80), by decide, rfl⟩
        have hd := (List.pairwise_append.1 hpw13).2.2 _ hm1 _ h4
        rw [heq] at hd; rcases hd with c | c | c | c <;> dsimp at c <;> omega
      · refine Or.inr ⟨mem_worldTypedIvls_bal h5, fun heq => ?_⟩
        have hm1 : (globN s "bs", 80) ∈ globalBuffers.map (bufRegBs s) ++
            [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
            blockOutObjects s := by
          apply List.mem_append_left; apply List.mem_append_left
          rw [← hsz]; exact List.mem_map.2 ⟨("bs", 80), by decide, rfl⟩
        have hd := (List.pairwise_append.1 hWT'.2.2.1.2).2.2 _ hm1 _ h5
        rw [heq] at hd; rcases hd with c | c | c | c <;> dsimp at c <;> omega
      · refine Or.inr ⟨List.mem_append_right _ h6, fun heq => ?_⟩
        have hd := (hTr'.2.1 i h6).2 _ hfix_bs
        rw [heq] at hd; rcases hd with c | c | c | c <;> dsimp at c <;> omega
    refine ⟨heff.be, heff.memaddrs, hAs.1.memaddrs, fun a hna => heff.out_dom a (hAs.1.memaddrs ▸ hna), ?_, ?_⟩
    · intro a ha ha8 ⟨i, hi, ha1, ha2⟩
      rcases hwti' i hi with rfl | ⟨hi_s, hne_bs⟩
      · dsimp at ha1 ha2; omega
      · rcases bs56_disj_worldTypedIvls hWT' hbs0 i hi_s with heq | hz | hdj
        · exact absurd heq hne_bs
        · omega
        · exact heff.cell_frame _ (fun x hx => by
            simp at hx; subst hx; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
            have hb8 := hbs_wok.1; dsimp at hb8
            exact not_cellHits_of_disj_aligned ha8 (by dsimp; omega) ha1 ha2 (Wave8Contracts.M23.Disj.symm hdj))
    · intro b hb ⟨i, hi, hb1, hb2⟩
      rcases hwti' i hi with rfl | ⟨hi_s, hne_bs⟩
      · dsimp at hb1 hb2; omega
      · rcases bs56_disj_worldTypedIvls hWT' hbs0 i hi_s with heq | hz | hdj
        · exact absurd heq hne_bs
        · omega
        · exact heff.byte_frame b hb (fun x hx ⟨c1, c2⟩ => by
            simp at hx; subst hx; rcases hdj with h | h | h | h <;> dsimp at h c1 c2 <;> omega)
  exact ⟨hAR_sNoBs, hAR_pNoBs, hT_sNoBs, hJ_sNoBs, hF_sNoBs, hhtabWF_s, hhtabWF_p,
    fun hTr' => ⟨hTr_sNoBs hTr', hcell_of hTr'⟩⟩

theorem bs56_world_congr {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) (S : List Nat) (hW : WorldTyped s S)
    (Nd : List Nat) (hTr : TriesTypedWith s S Nd) (hbs0 : globN s "bs" ≠ 0)
    (heff : ByteRegionEffect s post [(globN s "bs" + 56, 16)]) :
    WorldTyped post S ∧
    fixedObjects post = fixedObjects s ∧
    (∀ t ∈ S, htabFootprint post t = htabFootprint s t) ∧
    (∀ t ∈ S, ∀ k < 11, hdr post t k = hdr s t k) ∧
    worldRoleSlots post = worldRoleSlots s ∧
    journalRoleSlots post = journalRoleSlots s ∧
    worldTableRefs post S = worldTableRefs s S ∧
    (∀ {Nd' : List Nat}, TriesTypedWith s S Nd' →
      TriesTypedWith post S Nd' ∧ nodeExtents post Nd' = nodeExtents s Nd') ∧
    (globN s "bs", 80) ∈ fixedObjects s ∧
    (∀ x ∈ ([(globN s "bs" + 56, 16)] : List Ivl), x.1 % 8 = 0) ∧
    (∀ i : Ivl, Disj (globN s "bs", 80) i → Disj (globN s "bs" + 56, 16) i) := by
  have hWT : WorldTypedWith s S Nd := ⟨hW.1, hW.2.1, hW.2.2.1, hTr⟩
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hApost : ArenaReady post :=
    ⟨guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAs.1,
     arenaOK_congr heff.globals hAs.2⟩
  have hsz : (if globN s "bs" = 0 then 0 else 80) = 80 := if_neg hbs0
  have hfix_bs : (globN s "bs", 80) ∈ fixedObjects s := by
    have := typedRec_in_fixedObjects s (g := "bs") (sz := 80) (by decide); rwa [hsz] at this
  rcases hWT.2.2.1.1 _ hfix_bs with h0 | ⟨hbs_al, hbs_wok⟩
  · dsimp at h0; omega
  have hbs_bnd : globN s "bs" + 80 ≤ 2 ^ 64 := allocated_le_2pow64 hAs.2 hbs_al
  have hRl8 : ∀ x ∈ ([(globN s "bs" + 56, 16)] : List Ivl), x.1 % 8 = 0 := fun x hx => by
    simp at hx; subst hx; have := hbs_wok.1; dsimp at this ⊢; omega
  have hsub_bs : ∀ i : Ivl, Disj (globN s "bs", 80) i → Disj (globN s "bs" + 56, 16) i := fun i hd => by
    rcases hd with h | h | h | h
    · exact Or.inl (by dsimp only at h ⊢; omega)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (by dsimp only at h ⊢; omega)))
    · exact Or.inr (Or.inr (Or.inr (by dsimp only at h ⊢; omega)))
  have hbs_slot_eq : ∀ k : Nat, k % 8 = 0 → (k + 8 ≤ 56 ∨ k = 72) →
      memW post (globN s "bs" + k) = memW s (globN s "bs" + k) := fun k hk8 hk =>
    memW_eq_of_disj_eff (base := globN s "bs" + k) (sz := 8) (k := 0)
      heff hRl8 (by omega) (by have := hbs_wok.1; dsimp at this; omega) (by omega) (by omega)
      (fun x hx => by
        simp at hx; subst hx
        rcases hk with h | rfl
        · exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))
        · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega))))
  set sNoBs := noBsState s
  set pNoBs := noBsState post
  obtain ⟨hAR_sNoBs, hAR_pNoBs, hT_sNoBs, hJ_sNoBs, hF_sNoBs, hhtabWF_s, hhtabWF_p, hTr_cell⟩ :=
    bs56_noBs_typed hAs S hW Nd hTr hbs0 heff
  change ArenaReady sNoBs at hAR_sNoBs
  change ArenaReady pNoBs at hAR_pNoBs
  have hsNoBs_bs : globN sNoBs "bs" = 0 := by simp [sNoBs, noBsState, globN, HolFiniteMapExact.lookup_update, FUPDATE]
  have hpNoBs_bs : globN pNoBs "bs" = 0 := by simp [pNoBs, noBsState, globN, HolFiniteMapExact.lookup_update, FUPDATE]
  have hsNoBs_other : ∀ g : String, ofString "bs" ≠ ofString g → globN sNoBs g = globN s g := fun g hne => by
    simp [sNoBs, noBsState, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have hpNoBs_other : ∀ g : String, ofString "bs" ≠ ofString g → globN pNoBs g = globN s g := fun g hne => by
    simp [pNoBs, noBsState, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne, heff.globals]
  have hbo_s : blockOutObjects sNoBs = blockOutObjects s := by
    unfold blockOutObjects; rw [hsNoBs_other "bo" (by decide)]; rfl
  have hbrec_s : balRecords sNoBs = balRecords s := by
    unfold balRecords; rw [hsNoBs_other "bal_accounts" (by decide)]; rfl
  have hbal_s : balObjects sNoBs = balObjects s := by
    unfold balObjects; rw [hbrec_s]; rfl
  have hj_s : journalRoleSlots sNoBs = journalRoleSlots s := by
    unfold journalRoleSlots journalRole
    rw [hsNoBs_other "journal_n" (by decide), hsNoBs_other "journal" (by decide),
        hsNoBs_other "ts" (by decide)]; rfl
  have hcell_nobs : SameTypedCells sNoBs pNoBs S Nd := (hTr_cell hTr).2
  have hh_nb : globN sNoBs "heap_ptr" ≤ globN pNoBs "heap_ptr" := by
    rw [hpNoBs_other "heap_ptr" (by decide), hsNoBs_other "heap_ptr" (by decide)]
  have hsc_nb : globN pNoBs "scratch_ptr" ≤ globN sNoBs "scratch_ptr" := by
    rw [hpNoBs_other "scratch_ptr" (by decide), hsNoBs_other "scratch_ptr" (by decide)]
  have hg_nb : ∀ g ∈ coreWorldGlobals, globN pNoBs g = globN sNoBs g := by
    intro g hg
    by_cases hb : g = "bs"
    · subst hb; rw [hpNoBs_bs, hsNoBs_bs]
    · have hne : ofString "bs" ≠ ofString g :=
        (show ∀ x ∈ coreWorldGlobals, x ≠ "bs" → ofString "bs" ≠ ofString x by decide) g hg hb
      rw [hpNoBs_other g hne, hsNoBs_other g hne]
  have hWT_sNoBs : WorldTypedWith sNoBs S Nd := ⟨hT_sNoBs, hJ_sNoBs, hF_sNoBs, (hTr_cell hTr).1⟩
  have hfeq_nb := fixedObjects_eq_of_nonHeapGlobalsKept hAR_sNoBs.2 hT_sNoBs hF_sNoBs hcell_nobs
    (fun _ _ _ _ => by dsimp only [sNoBs, pNoBs, noBsState]; rw [heff.globals])
  have hFT_pnb := fixedTyped_of_eq hAR_pNoBs hF_sNoBs hh_nb hsc_nb hfeq_nb
  obtain ⟨hWT_pnb, _⟩ := worldTypedWith_congr_w1 hAR_sNoBs hAR_pNoBs hh_nb hsc_nb hg_nb
    hcell_nobs hWT_sNoBs ⟨hFT_pnb, fun o ho => Or.inl (hfeq_nb ▸ ho)⟩
  have hbo_eq : blockOutObjects post = blockOutObjects s := by
    have hbo_p : blockOutObjects pNoBs = blockOutObjects post := by
      unfold blockOutObjects; rw [hpNoBs_other "bo" (by decide), hglob_eq "bo"]; rfl
    rw [← hbo_p, ← hbo_s]
    exact blockOutObjects_eq hAR_sNoBs.2 hF_sNoBs hcell_nobs
      (by rw [hpNoBs_other "bo" (by decide), hsNoBs_other "bo" (by decide)])
  have hbrec_p : balRecords pNoBs = balRecords post := by
    unfold balRecords; rw [hpNoBs_other "bal_accounts" (by decide), hglob_eq "bal_accounts"]; rfl
  have hbrec_eq : balRecords post = balRecords s := by
    rw [← hbrec_p, ← hbrec_s]
    exact balRecords_eq hT_sNoBs hcell_nobs
      (by rw [hpNoBs_other "bal_accounts" (by decide), hsNoBs_other "bal_accounts" (by decide)])
  have hbal_eq : balObjects post = balObjects s := by
    have hbal_p : balObjects pNoBs = balObjects post := by unfold balObjects; rw [hbrec_p]; rfl
    rw [← hbal_p, ← hbal_s]
    exact balObjects_eq hAR_sNoBs.2 hT_sNoBs hF_sNoBs hcell_nobs
      (by rw [hpNoBs_other "bal_accounts" (by decide), hsNoBs_other "bal_accounts" (by decide)])
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [hbo_eq, hbal_eq, hglob_eq "journal", hglob_eq "journal_cap"]
    congr 3; exact List.map_congr_left fun gn _ => by simp only [hglob_eq]
  have hFix_post : FixedTyped post := fixedTyped_of_eq hApost hWT.2.2.1 hh hsc hfeq
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => htabFootprint_eq (s := sNoBs) (post := pNoBs) hcell_nobs ht (hhtabWF_s t (hWT.1.2.1 t ht).1)
  have hhtabVals_eq : ∀ t ∈ S, htabValues post t = htabValues s t :=
    fun t ht => htabValues_eq (s := sNoBs) (post := pNoBs) hcell_nobs ht (hhtabWF_s t (hWT.1.2.1 t ht).1)
  have hhtabHdr_eq : ∀ t ∈ S, ∀ k < 11, hdr post t k = hdr s t k :=
    fun t ht k hk => htab_hdr_eq (s := sNoBs) (post := pNoBs) hcell_nobs ht
      ((hWT.1.2.1 t ht).1.1 (t, 88) (by simp [htabFootprint])).1 k hk
  have hjrs_eq : journalRoleSlots post = journalRoleSlots s := by
    have hj_p : journalRoleSlots pNoBs = journalRoleSlots post := by
      unfold journalRoleSlots journalRole
      rw [hpNoBs_other "journal_n" (by decide), hpNoBs_other "journal" (by decide),
          hpNoBs_other "ts" (by decide), ← hglob_eq "journal_n", ← hglob_eq "journal", ← hglob_eq "ts"]; rfl
    rw [← hj_p, ← hj_s]; exact journalRoleSlots_eq hAR_sNoBs.2 hJ_sNoBs hF_sNoBs hcell_nobs hg_nb
  have hwrs_eq : worldRoleSlots post = worldRoleSlots s := by
    have hrs_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] =
        recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
      have hp : recRoles pNoBs "ws" [(16, "ws+16"), (32, "ws+32")] = recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] := by
        unfold recRoles; rw [hpNoBs_other "ws" (by decide), hglob_eq "ws"]; rfl
      have hs : recRoles sNoBs "ws" [(16, "ws+16"), (32, "ws+32")] = recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
        unfold recRoles; rw [hsNoBs_other "ws" (by decide)]; rfl
      rw [← hp, ← hs]
      exact recRoles_eq hAR_sNoBs.2 hF_sNoBs hcell_nobs (sz := 40) (by decide)
        (by rw [hpNoBs_other "ws" (by decide), hsNoBs_other "ws" (by decide)])
        (fun p hp => by simp at hp; rcases hp with rfl | rfl <;> omega)
    have hrs_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
        recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
          (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
      unfold recRoles; rw [hglob_eq "bs"]; simp only [hbs0, ↓reduceIte]
      exact List.map_congr_left fun p hp => by
        have hk : p.1 % 8 = 0 ∧ (p.1 + 8 ≤ 56 ∨ p.1 = 72) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
        rw [hbs_slot_eq p.1 hk.1 hk.2]
    have hrs_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
        recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
          (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
      have hp : recRoles pNoBs "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
          (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
          recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
            (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
        unfold recRoles; rw [hpNoBs_other "ts" (by decide), hglob_eq "ts"]; rfl
      have hs : recRoles sNoBs "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
          (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
          recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
            (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
        unfold recRoles; rw [hsNoBs_other "ts" (by decide)]; rfl
      rw [← hp, ← hs]
      exact recRoles_eq hAR_sNoBs.2 hF_sNoBs hcell_nobs (sz := 72) (by decide)
        (by rw [hpNoBs_other "ts" (by decide), hsNoBs_other "ts" (by decide)])
        (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    have hnr_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
      unfold nestRoles; rw [hglob_eq "bs"]
      simp only [hbs0, ↓reduceIte, hbs_slot_eq 32 (by omega) (Or.inl (by omega))]
      split_ifs with ht0
      · rfl
      · rcases hWT.1.2.2.2.2.1 32 (by decide) hbs0 with h0 | hm
        · exact absurd h0 ht0
        · rw [hhtabVals_eq _ hm]
    have hnr_ts : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
      have hp : nestRoles pNoBs "ts" "ts.inner" = nestRoles post "ts" "ts.inner" := by
        unfold nestRoles; rw [hpNoBs_other "ts" (by decide), hglob_eq "ts"]; rfl
      have hs : nestRoles sNoBs "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
        unfold nestRoles; rw [hsNoBs_other "ts" (by decide)]; rfl
      rw [← hp, ← hs]
      exact nestRoles_eq hAR_sNoBs.2 hT_sNoBs hF_sNoBs hcell_nobs (sz := 72) (by decide) (by omega)
        (by rw [hpNoBs_other "ts" (by decide), hsNoBs_other "ts" (by decide)])
        (fun hne => by rw [hsNoBs_other "ts" (by decide)] at hne ⊢; exact hWT.1.2.2.2.2.2.1 32 (by decide) hne)
    unfold worldRoleSlots
    rw [hrs_ws, hrs_bs, hrs_ts, hglob_eq "bal_accounts", hglob_eq "bal_idx_accts",
        hglob_eq "bal_idx_stor", hnr_bs, hnr_ts, hbrec_eq]
    congr 1; congr 1; apply List.flatMap_congr; intro ad had
    have hm_nb : (ad, 40) ∈ balObjects sNoBs := hbal_s.symm ▸ balRecord_ivl_mem had
    rcases fixedObject_le_2pow64 hAR_sNoBs.2 hF_sNoBs (bal_in_fixedObjects hm_nb) with h0 | hbnd
    · dsimp at h0; omega
    · dsimp at hbnd
      have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd) hm_nb
      rw [show memW post ad = memW pNoBs ad from rfl, show memW s ad = memW sNoBs ad from rfl,
          memW_eq_of_cellHits hcell_nobs (by omega) hwti_ad ⟨by dsimp; omega, by dsimp; omega⟩,
          show memW post (ad + 8) = memW pNoBs (ad + 8) from rfl, show memW s (ad + 8) = memW sNoBs (ad + 8) from rfl,
          memW_eq_of_cellHits hcell_nobs (by omega) hwti_ad ⟨by dsimp; omega, by dsimp; omega⟩]
  have hJrn_post : JournalTyped post S := by
    obtain ⟨j1, j2, j3, j4⟩ := hWT_pnb.2.1
    unfold JournalTyped
    simp only [hpNoBs_other "journal_n" (by decide), hpNoBs_other "journal_cap" (by decide),
        hpNoBs_other "journal" (by decide)] at j1 j2 j3 j4
    simp only [hglob_eq]
    refine ⟨j1, j2, ?_, j4⟩
    rcases j3 with hz | ⟨hal, hw⟩
    · exact Or.inl hz
    · refine Or.inr ⟨?_, hw⟩; unfold Allocated at hal ⊢
      rwa [hpNoBs_other "heap_ptr" (by decide), hpNoBs_other "scratch_ptr" (by decide),
          ← hglob_eq "heap_ptr", ← hglob_eq "scratch_ptr"] at hal
  have hTab_post : TablesTyped post S := by
    obtain ⟨hnd, htwf_p, htpw_p, hws_p, _, hts_p, _, _, hts32_p, hbal_p, hbo_p, _⟩ := hWT_pnb.1
    obtain ⟨_, htwf_s, _, _, hbs_s, _, hgr_s, hbs32_s, _, _, _, hroles_s⟩ := hWT.1
    refine ⟨hnd, ?_, htpw_p, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      rw [hfp_eq_all t ht, hfeq]
      exact ⟨hhtabWF_p t (htwf_p t ht).1, fun i hi =>
        ⟨by unfold Allocated; simp only [hglob_eq]; exact ((htwf_s t ht).2 i hi).1, ((htwf_s t ht).2 i hi).2⟩⟩
    · intro k hk; rw [hglob_eq "ws", ← hpNoBs_other "ws" (by decide)]; exact hws_p k hk
    · intro k hk; rw [hglob_eq "bs"]; intro hnz
      have hk_ok : k % 8 = 0 ∧ (k + 8 ≤ 56 ∨ k = 72) := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [hbs_slot_eq k hk_ok.1 hk_ok.2]; exact hbs_s k hk hnz
    · intro k hk; rw [hglob_eq "ts", ← hpNoBs_other "ts" (by decide)]; exact hts_p k hk
    · intro g hg; rw [hglob_eq g]; exact hgr_s g hg
    · rw [hglob_eq "bs"]; intro hnz; rw [hbs_slot_eq 32 (by omega) (Or.inl (by omega))]; intro hmS
      exact htabValuesIn_congr hcell_nobs hmS (hhtabWF_s _ (htwf_s _ hmS).1) (fun _ h => h) (hbs32_s hnz hmS)
    · rw [hglob_eq "ts", ← hpNoBs_other "ts" (by decide)]; exact hts32_p
    · rw [← hbrec_p]; exact hbal_p
    · rw [hglob_eq "bo", ← hpNoBs_other "bo" (by decide)]; exact hbo_p
    · unfold RolesOK at hroles_s ⊢; rw [hwrs_eq, hjrs_eq]
      exact ⟨fun a ha => ⟨(hroles_s.1 a ha).1, by
        rw [hhtabHdr_eq a.1 (hroles_s.1 a ha).1 0 (by omega)]; exact (hroles_s.1 a ha).2⟩, hroles_s.2⟩
  have hTr_lift : ∀ {Nd' : List Nat}, TriesTypedWith s S Nd' →
      TriesTypedWith post S Nd' ∧ nodeExtents post Nd' = nodeExtents s Nd' := by
    intro Nd' hTr'
    obtain ⟨hTr_nb', hc'⟩ := hTr_cell hTr'
    have hWT_nb' : WorldTypedWith sNoBs S Nd' := ⟨hT_sNoBs, hJ_sNoBs, hF_sNoBs, hTr_nb'⟩
    have hfeq_nb' := fixedObjects_eq_of_nonHeapGlobalsKept hAR_sNoBs.2 hT_sNoBs hF_sNoBs hc'
      (fun _ _ _ _ => by dsimp only [sNoBs, pNoBs, noBsState]; rw [heff.globals])
    obtain ⟨hWT_pnb', _⟩ := worldTypedWith_congr_w1 hAR_sNoBs hAR_pNoBs hh_nb hsc_nb hg_nb
      hc' hWT_nb' ⟨fixedTyped_of_eq hAR_pNoBs hF_sNoBs hh_nb hsc_nb hfeq_nb', fun o ho => Or.inl (hfeq_nb' ▸ ho)⟩
    have hNH_p := hWT_pnb'.2.2.2.1
    have hNH_post : NodeHeap post Nd' := by
      refine ⟨fun n hn => ?_, hNH_p.2⟩
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hNH_p.1 n hn
      have hal_p : ∀ i : Ivl, Allocated pNoBs i → Allocated post i := fun i h => by
        unfold Allocated at h ⊢
        rwa [hpNoBs_other "heap_ptr" (by decide), hpNoBs_other "scratch_ptr" (by decide),
            ← hglob_eq "heap_ptr", ← hglob_eq "scratch_ptr"] at h
      refine ⟨c1, hal_p _ c2, c3, c4, c5, c6, fun h12 => ?_, c8, c9, c10⟩
      rcases c7 h12 with hz | ⟨hnib, hal, hin, hdj⟩
      · exact Or.inl hz
      · exact Or.inr ⟨hnib, hal_p _ hal, hin, hdj⟩
    have hne_eq' : nodeExtents post Nd' = nodeExtents s Nd' :=
      nodeExtents_eq (s := sNoBs) (post := pNoBs) hWT_nb'.2.2.2.1 hc'
    refine ⟨⟨hNH_post, ?_, ?_⟩, hne_eq'⟩
    · rw [hne_eq', hfeq]
      exact fun o ho => ⟨fun t ht i hi => by
        rw [hfp_eq_all t ht] at hi; exact (hTr'.2.1 o ho).1 t ht i hi, (hTr'.2.1 o ho).2⟩
    · rw [hglob_eq "ws", ← hpNoBs_other "ws" (by decide)]; exact hWT_pnb'.2.2.2.2.2
  have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
    unfold worldTableRefs recordSlots
    rw [hglob_eq "ws", hglob_eq "bs", hglob_eq "ts",
        show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
          simp only [globalTableRoots, List.map, hglob_eq],
        hbrec_eq, hglob_eq "journal_n", hglob_eq "journal"]
    have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
        (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
      split; · rfl
      rename_i hnz; apply List.map_congr_left; intro k hk
      have hnz_nb : globN sNoBs "ws" ≠ 0 := by rwa [hsNoBs_other "ws" (by decide)]
      have eqk := memW_typedRec_eq hAR_sNoBs.2 hF_sNoBs hcell_nobs (g := "ws") (sz := 40) (k := k)
        (by decide) hnz_nb
        (by simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> omega)
      rw [hsNoBs_other "ws" (by decide)] at eqk; exact eqk
    have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
        (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
      simp only [hbs0, ↓reduceIte]; apply List.map_congr_left; intro k hk
      have hk_ok : k % 8 = 0 ∧ (k + 8 ≤ 56 ∨ k = 72) := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      exact hbs_slot_eq k hk_ok.1 hk_ok.2
    have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
        (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
      split; · rfl
      rename_i hnz; apply List.map_congr_left; intro k hk
      have hnz_nb : globN sNoBs "ts" ≠ 0 := by rwa [hsNoBs_other "ts" (by decide)]
      have eqk := memW_typedRec_eq hAR_sNoBs.2 hF_sNoBs hcell_nobs (g := "ts") (sz := 72) (k := k)
        (by decide) hnz_nb
        (by simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      rw [hsNoBs_other "ts" (by decide)] at eqk; exact eqk
    have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
        (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
      rw [hbs_slot_eq 32 (by omega) (Or.inl (by omega))]
      by_cases hmS : memW s (globN s "bs" + 32) ∈ S <;> simp [hbs0, hmS, hhtabVals_eq]
    have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
        (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
      by_cases hnz : globN s "ts" = 0
      · simp [hnz]
      · have hnz_nb : globN sNoBs "ts" ≠ 0 := by rwa [hsNoBs_other "ts" (by decide)]
        have eq32 : memW post (globN s "ts" + 32) = memW s (globN s "ts" + 32) := by
          have h := memW_typedRec_eq hAR_sNoBs.2 hF_sNoBs hcell_nobs (g := "ts") (sz := 72) (k := 32) (by decide) hnz_nb (by omega)
          rw [hsNoBs_other "ts" (by decide)] at h; exact h
        rw [eq32]
        by_cases hmS : memW s (globN s "ts" + 32) ∈ S <;> simp [hnz, hmS, hhtabVals_eq]
    have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
        (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
      apply List.flatMap_congr; intro ad had
      have had_mem : (ad, 40) ∈ balObjects sNoBs := hbal_s.symm ▸ balRecord_ivl_mem had
      rcases fixedObject_le_2pow64 hAR_sNoBs.2 hF_sNoBs (bal_in_fixedObjects had_mem) with h0 | had_bnd
      · dsimp only at h0; omega
      · dsimp only at had_bnd
        have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd) had_mem
        rw [show memW post ad = memW pNoBs ad from rfl, show memW s ad = memW sNoBs ad from rfl,
            memW_eq_of_cellHits hcell_nobs (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
            show memW post (ad + 8) = memW pNoBs (ad + 8) from rfl, show memW s (ad + 8) = memW sNoBs (ad + 8) from rfl,
            memW_eq_of_cellHits hcell_nobs (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]
    have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
        (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
      apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
      have hjc_le := hWT.2.1.1
      have hjc_ne : globN sNoBs "journal_cap" ≠ 0 := by rw [hsNoBs_other "journal_cap" (by decide)]; omega
      rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
      · omega
      · have hbnd := allocated_le_2pow64 hAs.2 hal; dsimp only at hbnd
        have hj_mem := mem_worldTypedIvls_journal (s := sNoBs) (S := S) (Nd := Nd) hjc_ne
        rw [hsNoBs_other "journal" (by decide), hsNoBs_other "journal_cap" (by decide)] at hj_mem
        exact memW_eq_of_cellHits hcell_nobs (by omega) hj_mem ⟨by dsimp only; omega, by dsimp only; omega⟩
    dsimp only
    rw [hglob_eq "bs", hglob_eq "ts", hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
  exact ⟨⟨hTab_post, hJrn_post, hFix_post, Nd, (hTr_lift hTr).1⟩,
    hfeq, hfp_eq_all, hhtabHdr_eq, hwrs_eq, hjrs_eq, hworldRefs_eq, hTr_lift, hfix_bs, hRl8, hsub_bs⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
