import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M12.StepLemmas

/-! Shard `R12-Wk08`: 5 `WorldKeeps` Process/Ancestor Leaves. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.R11Shards.WkShard08

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Contracts.M12 (ByteRegionEffect SameTypedCells sourceBase_val
  heapLimit_val scratchStart_val scratchEnd_val heapEnd_val ordinaryDomain_iff
  typedRec_in_fixedObjects allocated_le_2pow64 fixedObject_le_2pow64 blockOut_in_fixedObjects
  bal_in_fixedObjects mem_worldTypedIvls_typedRec not_cellHits_of_disj_aligned
  htabWF_congr htabValues_eq htabValuesIn_congr blockOutObjects_eq balRecords_eq balObjects_eq
  nodeExtents_eq nodeHeap_congr recRoles_eq nestRoles_eq journalRoleSlots_eq fixedTyped_of_eq
  memW_eq_of_cellHits lstOK_congr_of_ivl htab_hdr_eq htabFootprint_eq nodeF_eq_of_lt
  htabCount_le_ncap htabOrder_entry_le_ncap mem_worldTypedIvls_htab mem_worldTypedIvls_blockOut
  mem_worldTypedIvls_bal mem_worldTypedIvls_journal balRecord_ivl_mem balRecord_lst_ivl_mem
  balRecord_storLst_ivl_mem memW_eq_of_lt_sourceBase wordsOK_congr_of_ivl)

private theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem lookup_track_ancestor_access :
    originalRuntimeCode.lookup (ofString "track_ancestor_access") =
      some ([(ofString "offset", .one)],
        sourceFnBody Guest.Software.guestFn_track_ancestor_access, .one) :=
  lookup_of_guestAst_getElem 402 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_track_ancestor_access) rfl

private theorem one_word_param {fname param : MlS} {body : ProgHOL 64}
    {locals : HolFiniteMapExact MlS (ValueHOL 64)}
    (hlook : originalRuntimeCode.lookup fname = some ([(param, .one)], body, .one))
    (hex : ∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
      some (body, locals, .one)) :
    ∃ w : BitVec 64, locals.lookup param = some (.val (.word w)) := by
  obtain ⟨values, hl⟩ := hex
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname values body locals .one hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases values with _ | ⟨v0, _ | _⟩
  · simp at hx
  · rcases v0 with ⟨⟨w⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    exact ⟨w, by rw [← hx]; simp⟩
  · simp at hx

private def bsUntypedKeep : List (String × List Nat) :=
  [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
   ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]

private theorem bs56_disj_worldTypedIvls {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hWT : WorldTypedWith s S Nd) (hbs_nz : globN s "bs" ≠ 0) :
    ∀ i ∈ worldTypedIvls s S Nd,
      i = (globN s "bs", if globN s "bs" = 0 then 0 else 80) ∨ i.2 = 0 ∨ Disj (globN s "bs" + 56, 16) i := by
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
    exact Or.inr (Or.inr (hsub i (((hT.2.1 t ht).2 i hfp).2 _ hmem_fix).flip))
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
    by_cases hrb : r.1 = "bs"
    · have hrsz : r = ("bs", 80) := by
        simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp at hrb ⊢
      exact hrsz ▸ Or.inl rfl
    · by_cases hr0 : globN s r.1 = 0
      · exact Or.inr (Or.inl (by simp [hr0]))
      · right; right; apply hsub
        have hbs_gb : ("bs", 80) ∈ globalBuffers := by decide
        have hr_gb : r ∈ globalBuffers := by
          simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with h | h | h | h <;> (rw [h]; decide)
        have hpw_gb : (globalBuffers.map (bufferRegion s)).Pairwise Disj :=
          (List.pairwise_append.1 (List.pairwise_append.1 (List.pairwise_append.1 hF.2).1).1).1
        letI : Std.Symm (fun a b : String × Nat => Disj (bufferRegion s a) (bufferRegion s b)) :=
          ⟨fun _ _ h => h.flip⟩
        have hne : ("bs", 80) ≠ r := fun h => hrb (congrArg Prod.fst h).symm
        simpa [bufferRegion, hsz] using (List.pairwise_map.1 hpw_gb).forall hbs_gb hr_gb hne
  · simp only [List.mem_singleton] at h3; subst h3
    right; right; apply hsub
    have hpw12 := (List.pairwise_append.1 (List.pairwise_append.1 hF.2).1).1
    have hm1 : (globN s "bs", 80) ∈ globalBuffers.map (bufferRegion s) := by
      rw [← hsz]; exact List.mem_map.2 ⟨("bs", 80), by decide, rfl⟩
    exact (List.pairwise_append.1 hpw12).2.2 _ hm1 _ (List.mem_singleton.2 rfl)
  · right; right; apply hsub
    have hpw13 := (List.pairwise_append.1 hF.2).1
    have hm1 : (globN s "bs", 80) ∈ globalBuffers.map (bufferRegion s) ++
        [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] := by
      apply List.mem_append_left; rw [← hsz]; exact List.mem_map.2 ⟨("bs", 80), by decide, rfl⟩
    exact (List.pairwise_append.1 hpw13).2.2 _ hm1 _ h4
  · right; right; apply hsub
    have hm1 : (globN s "bs", 80) ∈ globalBuffers.map (bufferRegion s) ++
        [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
        blockOutObjects s := by
      apply List.mem_append_left; apply List.mem_append_left
      rw [← hsz]; exact List.mem_map.2 ⟨("bs", 80), by decide, rfl⟩
    exact (List.pairwise_append.1 hF.2).2.2 _ hm1 _ h5
  · exact Or.inr (Or.inr (hsub i ((hTr.2.1 i h6).2 _ hmem_fix).flip))

private theorem worldStep_of_bs56_effect {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hW : WorldOK s)
    (heff : ByteRegionEffect s post (if globN s "bs" = 0 then [] else [(globN s "bs" + 56, 16)])) :
    WorldStep (fun _ => []) [] bsUntypedKeep NoExtra s r post := by
  have hinv_post : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hW.1.1
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  have hA_post : ArenaReady post :=
    ⟨hinv_post, arenaOK_congr heff.globals hW.1.2⟩
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hG : GlobalsKept [] s post := fun _ _ => by rw [heff.globals]
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hTr0⟩ := hWT0_ex.2.2.2
  have hWT0 : WorldTypedWith s S0 Nd0 := ⟨hWT0_ex.1, hWT0_ex.2.1, hWT0_ex.2.2.1, hTr0⟩
  by_cases hbs0 : globN s "bs" = 0
  · simp only [hbs0, ↓reduceIte] at heff
    have hws := ByteRegionEffect.to_worldStep (R := fun _ => []) (extra := fun _ => []) (r := r)
      hW (fun _ h => by simp at h) (by simpa using heff)
    refine ⟨hA_post, hh, hG, fun rec _ _ k _ _ => ?_, hws.2.2.2.2⟩
    unfold memW; rw [heff.cell_frame _ (fun _ h => by simp at h)]
  · simp only [hbs0, ↓reduceIte] at heff
    have hfix_bs := typedRec_in_fixedObjects s (g := "bs") (sz := 80) (by decide)
    have hsz : (if globN s "bs" = 0 then 0 else 80) = 80 := if_neg hbs0
    have hbs_al_bnd : globN s "bs" % 8 = 0 ∧ globN s "bs" + 80 ≤ 2 ^ 64 := by
      rcases hWT0.2.2.1.1 _ hfix_bs with h0 | ⟨hal, hw⟩
      · dsimp only at h0; rw [hsz] at h0; omega
      · have hb := allocated_le_2pow64 hW.1.2 hal; dsimp only at hb; rw [hsz] at hb
        exact ⟨hw.1, hb⟩
    have hnot_bs56 : ∀ a : Nat, a < 2 ^ 64 → ¬ CellHits a (globN s "bs" + 56, 16) →
        memW post a = memW s a := fun a ha hno => by
      unfold memW
      rw [heff.cell_frame _ (fun x hx => by
        simp at hx; subst hx; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha])]
    have hother_rec : ∀ (S Nd : List Nat), WorldTypedWith s S Nd →
        ∀ (g : String) (sz : Nat), (g, sz) ∈ typedRecords → g ≠ "bs" →
        globN s g ≠ 0 → ∀ k : Nat, k % 8 = 0 → k + 8 ≤ sz →
        memW post (globN s g + k) = memW s (globN s g + k) := by
      intro S Nd hWT g sz htr hgne hgnz k hk8 hkle
      rcases hWT.2.2.1.1 _ (typedRec_in_fixedObjects s htr) with h0 | ⟨hal, hw⟩
      · dsimp only at h0; rw [if_neg hgnz] at h0; omega
      · have hb := allocated_le_2pow64 hW.1.2 hal; dsimp only at hb; rw [if_neg hgnz] at hb
        have hg8 := hw.1
        rcases bs56_disj_worldTypedIvls hWT hbs0 _ (mem_worldTypedIvls_typedRec htr) with heq | h0 | hdj
        · exfalso
          have h2 := congrArg Prod.snd heq; dsimp only at h2; rw [if_neg hgnz, hsz] at h2
          simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at htr
          rcases htr with h | h | h | h <;> (rw [Prod.mk.injEq] at h; try omega)
          exact hgne h.1
        · dsimp only at h0; rw [if_neg hgnz] at h0; omega
        · rw [if_neg hgnz] at hdj
          exact hnot_bs56 _ (by omega) (not_cellHits_of_disj_aligned (i := (globN s g, sz))
            (by omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) hdj.flip)
    have hRK : RecordsKept (fun _ => []) bsUntypedKeep s post := by
      intro rec hrec hgnz k hk _
      simp only [bsUntypedKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · exact hother_rec S0 Nd0 hWT0 "ws" 40 (by decide) (by decide) hgnz k (by simp at hk; omega) (by simp at hk; omega)
      · have hk_sep : (k + 8 ≤ 56 ∨ k = 72) ∧ k + 8 ≤ 80 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
        exact hnot_bs56 (globN s "bs" + k) (by omega) (fun ⟨c1, c2⟩ => by dsimp only at c1 c2; omega)
      · exact hother_rec S0 Nd0 hWT0 "ts" 72 (by decide) (by decide) hgnz k (by simp at hk; omega) (by simp at hk; omega)
      · exact hother_rec S0 Nd0 hWT0 "bo" 88 (by decide) (by decide) hgnz k (by simp at hk; omega) (by simp at hk; omega)
    refine ⟨hA_post, hh, hG, hRK, fun S Nd hWT _ => ?_⟩
    -- Overwrite ONLY `bs+56` and `bs+64` in `s` with `post`'s values!
    let a56 := BitVec.ofNat 64 (globN s "bs" + 56)
    let a64 := BitVec.ofNat 64 (globN s "bs" + 64)
    let sAlt : PanSemStateFiniteExact 64 F :=
      { s with memory := fun a => if a = a56 ∨ a = a64 then post.memory a else s.memory a }
    have hsAlt_mem_post : post.memory = sAlt.memory := by
      funext a; dsimp only [sAlt]
      split_ifs with h_eq
      · rfl
      · by_cases hdom : s.memaddrs a
        · have hdom' := hW.1.1.memaddrs ▸ hdom
          rw [ordinaryDomain_iff] at hdom'
          apply heff.cell_frame a
          intro x hx; simp at hx; subst hx
          rintro ⟨c1, c2⟩; dsimp only at c1 c2
          apply h_eq
          rcases (show a.toNat = globN s "bs" + 56 ∨ a.toNat = globN s "bs" + 64 by omega) with h1 | h2
          · exact Or.inl (BitVec.eq_of_toNat_eq (by rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]))
          · exact Or.inr (BitVec.eq_of_toNat_eq (by rw [h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]))
        · exact heff.out_dom a hdom
    -- Notice: `sNoBs` and `pNoBs` satisfy `SameTypedCells sNoBs pNoBs S Nd`!
    let sNoBs : PanSemStateFiniteExact 64 F := { s with globals := s.globals.update (ofString "bs", .val (.word 0#64)) }
    let pNoBs : PanSemStateFiniteExact 64 F := { post with globals := post.globals.update (ofString "bs", .val (.word 0#64)) }
    have hsNoBs_bs : globN sNoBs "bs" = 0 := by simp [sNoBs, globN, HolFiniteMapExact.lookup_update, FUPDATE]
    have hpNoBs_bs : globN pNoBs "bs" = 0 := by simp [pNoBs, globN, HolFiniteMapExact.lookup_update, FUPDATE]
    have hsNoBs_other : ∀ g : String, ofString "bs" ≠ ofString g → globN sNoBs g = globN s g := fun g hne => by
      simp [sNoBs, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne]
    have hpNoBs_other : ∀ g : String, ofString "bs" ≠ ofString g → globN pNoBs g = globN s g := fun g hne => by
      simp [pNoBs, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne, heff.globals]
    have hbo_s : blockOutObjects sNoBs = blockOutObjects s := by
      unfold blockOutObjects; rw [hsNoBs_other "bo" (by decide)]; rfl
    have hbrec_s : balRecords sNoBs = balRecords s := by
      unfold balRecords; rw [hsNoBs_other "bal_accounts" (by decide)]; rfl
    have hbal_s : balObjects sNoBs = balObjects s := by
      unfold balObjects; rw [hbrec_s]; rfl
    have hwti_nobs : ∀ i ∈ InitECandidate.Solver.Wave8Contracts.M12.worldTypedIvls sNoBs S Nd,
        i = (0, 0) ∨ (i ∈ worldTypedIvls s S Nd ∧ i ≠ (globN s "bs", 80)) := by
      intro i hi
      unfold InitECandidate.Solver.Wave8Contracts.M12.worldTypedIvls at hi
      rw [hbo_s, hbal_s, hsNoBs_other "journal" (by decide), hsNoBs_other "journal_cap" (by decide)] at hi
      simp only [List.mem_append] at hi
      rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
      · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
        have hm := mem_worldTypedIvls_htab (s := s) (S := S) (Nd := Nd) ht hfp
        exact Or.inr ⟨hm, fun heq => by
          have hd := ((hWT.1.2.1 t ht).2 i hfp).2 _ (hsz ▸ hfix_bs)
          rw [heq] at hd; rcases hd with c | c | c | c <;> dsimp at c <;> omega⟩
      · obtain ⟨rec, hr, rfl⟩ := List.mem_map.1 h2
        by_cases hrb : rec.1 = "bs"
        · exact Or.inl (by simp [hrb, hsNoBs_bs])
        · have hne_ml : ofString "bs" ≠ ofString rec.1 :=
            (show ∀ x ∈ InitECandidate.Solver.Wave8Contracts.M12.typedRecords, x.1 ≠ "bs" → ofString "bs" ≠ ofString x.1 by decide) rec hr hrb
          rw [hsNoBs_other rec.1 hne_ml]
          refine Or.inr ⟨mem_worldTypedIvls_typedRec hr, fun heq => ?_⟩
          have h2' := congrArg Prod.snd heq; dsimp only at h2'
          by_cases h0 : globN s rec.1 = 0
          · rw [if_pos h0] at h2'; omega
          · rw [if_neg h0] at h2'
            exact hrb ((show ∀ x ∈ InitECandidate.Solver.Wave8Contracts.M12.typedRecords, x.2 = 80 → x.1 = "bs" by decide) rec hr h2')
      · simp only [List.mem_singleton] at h3; subst h3
        by_cases hjc0 : globN s "journal_cap" = 0
        · exact Or.inl (by simp [hjc0])
        · rw [if_neg hjc0]
          refine Or.inr ⟨mem_worldTypedIvls_journal hjc0, fun heq => ?_⟩
          have hpw12 := (List.pairwise_append.1 (List.pairwise_append.1 hWT.2.2.1.2).1).1
          have hm1 : (globN s "bs", 80) ∈ globalBuffers.map (bufferRegion s) := by
            rw [← hsz]; exact List.mem_map.2 ⟨("bs", 80), by decide, rfl⟩
          have hd := (List.pairwise_append.1 hpw12).2.2 _ hm1 _ (List.mem_singleton.2 rfl)
          rw [if_neg hjc0] at hd; rw [heq] at hd; rcases hd with c | c | c | c <;> dsimp at c <;> omega
      · refine Or.inr ⟨mem_worldTypedIvls_blockOut h4, fun heq => ?_⟩
        have hpw13 := (List.pairwise_append.1 hWT.2.2.1.2).1
        have hm1 : (globN s "bs", 80) ∈ globalBuffers.map (bufferRegion s) ++
            [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] := by
          apply List.mem_append_left; rw [← hsz]; exact List.mem_map.2 ⟨("bs", 80), by decide, rfl⟩
        have hd := (List.pairwise_append.1 hpw13).2.2 _ hm1 _ h4
        rw [heq] at hd; rcases hd with c | c | c | c <;> dsimp at c <;> omega
      · refine Or.inr ⟨mem_worldTypedIvls_bal h5, fun heq => ?_⟩
        have hm1 : (globN s "bs", 80) ∈ globalBuffers.map (bufferRegion s) ++
            [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
            blockOutObjects s := by
          apply List.mem_append_left; apply List.mem_append_left
          rw [← hsz]; exact List.mem_map.2 ⟨("bs", 80), by decide, rfl⟩
        have hd := (List.pairwise_append.1 hWT.2.2.1.2).2.2 _ hm1 _ h5
        rw [heq] at hd; rcases hd with c | c | c | c <;> dsimp at c <;> omega
      · refine Or.inr ⟨List.mem_append_right _ h6, fun heq => ?_⟩
        have hd := (hWT.2.2.2.2.1 i h6).2 _ (hsz ▸ hfix_bs)
        rw [heq] at hd; rcases hd with c | c | c | c <;> dsimp at c <;> omega
    have hcell_nobs : SameTypedCells sNoBs pNoBs S Nd := by
      refine ⟨heff.be, heff.memaddrs, hW.1.1.memaddrs, fun a hna => heff.out_dom a (hW.1.1.memaddrs ▸ hna), ?_, ?_⟩
      · intro a ha ha8 ⟨i, hi, ha1, ha2⟩
        rcases hwti_nobs i hi with rfl | ⟨hi_s, hne_bs⟩
        · dsimp at ha1 ha2; omega
        · rcases bs56_disj_worldTypedIvls hWT hbs0 i hi_s with heq | hz | hdj
          · exact absurd (hsz ▸ heq) hne_bs
          · omega
          · exact heff.cell_frame _ (fun x hx => by
              simp at hx; subst hx; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
              exact not_cellHits_of_disj_aligned ha8 (by dsimp; omega) ha1 ha2 hdj.flip)
      · intro b hb ⟨i, hi, hb1, hb2⟩
        rcases hwti_nobs i hi with rfl | ⟨hi_s, hne_bs⟩
        · dsimp at hb1 hb2; omega
        · rcases bs56_disj_worldTypedIvls hWT hbs0 i hi_s with heq | hz | hdj
          · exact absurd (hsz ▸ heq) hne_bs
          · omega
          · exact heff.byte_frame b hb (fun x hx ⟨c1, c2⟩ => by
              simp at hx; subst hx; rcases hdj with h | h | h | h <;> dsimp at h c1 c2 <;> omega)
    have hA_sNoBs : ArenaOK sNoBs := by
      unfold ArenaOK
      simp only [hsNoBs_other "heap_ptr" (by decide), hsNoBs_other "frame_mem_ptr" (by decide),
        hsNoBs_other "scratch_ptr" (by decide)]
      exact ⟨hW.1.2.1, hW.1.2.2.1, hW.1.2.2.2.1, hW.1.2.2.2.2.1, hW.1.2.2.2.2.2.1,
        hW.1.2.2.2.2.2.2.1, hW.1.2.2.2.2.2.2.2.1, hW.1.2.2.2.2.2.2.2.2.1,
        globalsWord_update (s := s) (t := sNoBs) (ofString "bs") 0#64 rfl hW.1.2.2.2.2.2.2.2.2.2⟩
    have hF_sNoBs : FixedTyped sNoBs := by
      let tailIvls := [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
        blockOutObjects s ++ balObjects s
      have hf1 : fixedObjects sNoBs = globalBuffers.map (bufferRegion sNoBs) ++ tailIvls := by
        unfold fixedObjects bufferRegion
        rw [hbo_s, hbal_s, hsNoBs_other "journal" (by decide), hsNoBs_other "journal_cap" (by decide)]
        simp [tailIvls, List.append_assoc]
      have hf2 : fixedObjects s = globalBuffers.map (bufferRegion s) ++ tailIvls := by
        unfold fixedObjects bufferRegion; simp [tailIvls, List.append_assoc]
      have hpw_s := hWT.2.2.1.2
      rw [hf2] at hpw_s
      have hpw_gb_s := List.pairwise_map.1 (List.pairwise_append.1 hpw_s).1
      have hpw_tail := (List.pairwise_append.1 hpw_s).2.1
      have hpw_cross_s := (List.pairwise_append.1 hpw_s).2.2
      have hbuf_eq : ∀ gn ∈ globalBuffers,
          bufferRegion sNoBs gn = (0, 0) ∨ bufferRegion sNoBs gn = bufferRegion s gn := by
        intro gn hgn
        by_cases hb : gn.1 = "bs"
        · exact Or.inl (by simp [bufferRegion, hb, hsNoBs_bs])
        · have hne : ofString "bs" ≠ ofString gn.1 := by revert hb; revert gn hgn; decide
          exact Or.inr (by simp [bufferRegion, hsNoBs_other _ hne])
      unfold FixedTyped; rw [hf1]
      refine ⟨fun o ho => ?_, List.pairwise_append.2 ⟨List.pairwise_map.2 ?_, hpw_tail, fun x hx y hy => ?_⟩⟩
      · rcases List.mem_append.1 ho with hgb | htl
        · obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hgb
          rcases hbuf_eq gn hgn with h0 | heq
          · exact Or.inl (by rw [h0])
          · rw [heq]
            rcases hWT.2.2.1.1 _ (by rw [hf2]; exact List.mem_append_left _ (List.mem_map.2 ⟨gn, hgn, rfl⟩)) with hz | ⟨hal, hw⟩
            · exact Or.inl hz
            · refine Or.inr ⟨?_, hw⟩
              unfold Allocated at hal ⊢
              rwa [hsNoBs_other "heap_ptr" (by decide), hsNoBs_other "scratch_ptr" (by decide)]
        · rcases hWT.2.2.1.1 _ (by rw [hf2]; exact List.mem_append_right _ htl) with hz | ⟨hal, hw⟩
          · exact Or.inl hz
          · refine Or.inr ⟨?_, hw⟩
            unfold Allocated at hal ⊢
            rwa [hsNoBs_other "heap_ptr" (by decide), hsNoBs_other "scratch_ptr" (by decide)]
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
        · rw [heq]; exact hpw_cross_s _ (List.mem_map.2 ⟨gn, hgn, rfl⟩) y hy
    -- Helper bridges between `s`/`post` and `sNoBs`/`pNoBs` for globals-free views:
    have hfc_eq : ∀ (x y : PanSemStateFiniteExact 64 F), x.memory = y.memory →
        ∀ nodes hd Fr, FreeChain x nodes hd Fr ↔ FreeChain y nodes hd Fr := by
      intro x y hmem nodes hd Fr
      induction Fr generalizing hd with
      | nil => exact Iff.rfl
      | cons f rest ih =>
        simp only [FreeChain, nodeF, memW, hmem]
        exact and_congr Iff.rfl (ih _)
    have hhtabWF_s : ∀ t, HtabWF s t → HtabWF sNoBs t := fun t h => by
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, L, I, Fr, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20⟩ := h
      exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, L, I, Fr, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, (hfc_eq s sNoBs rfl _ _ Fr).1 c20⟩
    have hhtabWF_p : ∀ t, HtabWF pNoBs t → HtabWF post t := fun t h => by
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, L, I, Fr, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20⟩ := h
      exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, L, I, Fr, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, (hfc_eq pNoBs post rfl _ _ Fr).1 c20⟩
    have hhtabVals_eq : ∀ t, t ∈ S → htabValues post t = htabValues s t := fun t ht =>
      htabValues_eq (s := sNoBs) (post := pNoBs) hcell_nobs ht (hhtabWF_s t (hWT.1.2.1 t ht).1)
    have hhtabFP_eq : ∀ t, t ∈ S → htabFootprint post t = htabFootprint s t := fun t ht =>
      htabFootprint_eq (s := sNoBs) (post := pNoBs) hcell_nobs ht (hhtabWF_s t (hWT.1.2.1 t ht).1)
    have hhtabHdr_eq : ∀ t, t ∈ S → ∀ k < 11, hdr post t k = hdr s t k := fun t ht k hk =>
      htab_hdr_eq (s := sNoBs) (post := pNoBs) hcell_nobs ht ((hWT.1.2.1 t ht).1.1 (t, 88) (by simp [htabFootprint])).1 k hk
    have hbo_p : blockOutObjects pNoBs = blockOutObjects post := by
      unfold blockOutObjects; rw [hpNoBs_other "bo" (by decide), hglob_eq "bo"]; rfl
    have hbo_eq : blockOutObjects post = blockOutObjects s := by
      rw [← hbo_p, ← hbo_s]
      exact blockOutObjects_eq hA_sNoBs hF_sNoBs hcell_nobs
        (by rw [hpNoBs_other "bo" (by decide), hsNoBs_other "bo" (by decide)])
    have hbrec_eq : balRecords post = balRecords s := by
      unfold balRecords; dsimp only; rw [hglob_eq "bal_accounts"]
      split_ifs with h0
      · rfl
      · rcases hWT.1.2.2.2.2.2.2.1 "bal_accounts" (by decide) with hz | hm
        · exact absurd hz h0
        · exact hhtabVals_eq _ hm
    have hbal_eq : balObjects post = balObjects s := by
      unfold balObjects; rw [hbrec_eq]
      apply List.flatMap_congr; intro ad had
      have hm_nb : (ad, 40) ∈ balObjects sNoBs := hbal_s.symm ▸ balRecord_ivl_mem had
      rcases fixedObject_le_2pow64 hA_sNoBs hF_sNoBs (bal_in_fixedObjects hm_nb) with h0 | had_bnd
      · dsimp at h0; omega
      · dsimp at had_bnd
        have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd) hm_nb
        have e_off : ∀ off : Nat, off + 8 ≤ 40 → memW post (ad + off) = memW s (ad + off) := fun off hoff =>
          memW_eq_of_cellHits hcell_nobs (by omega) hwti_ad ⟨by dsimp; omega, by dsimp; omega⟩
        have e0 := e_off 0 (by omega); simp only [Nat.add_zero] at e0
        have hl_eq : ∀ (k esz : Nat), k ∈ ([16, 24, 32] : List Nat) →
            lstObjects post (memW s (ad + k)) esz = lstObjects s (memW s (ad + k)) esz := by
          intro k esz hk
          by_cases hk0 : memW s (ad + k) = 0
          · simp [lstObjects, hk0]
          · have hm_nb' : (memW s (ad + k), 24) ∈ balObjects sNoBs :=
              hbal_s.symm ▸ balRecord_lst_ivl_mem had hk hk0
            rcases fixedObject_le_2pow64 hA_sNoBs hF_sNoBs (bal_in_fixedObjects hm_nb') with h0 | hbnd
            · dsimp at h0; omega
            · exact InitECandidate.Solver.Wave8Contracts.M12.lstObjects_eq_of_ivl hcell_nobs hbnd (mem_worldTypedIvls_bal hm_nb')
        have hc1 := (hWT.1.2.2.2.2.2.2.2.2.2.1 ad had).1
        have hval_eq : htabValues post (memW s ad) = htabValues s (memW s ad) := hhtabVals_eq _ hc1
        have hfl : (htabValues s (memW s ad)).flatMap (fun l => lstObjects post l 40) =
            (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
          apply List.flatMap_congr; intro l hl
          by_cases hl0 : l = 0
          · simp [lstObjects, hl0]
          · have hm_nb' : (l, 24) ∈ balObjects sNoBs :=
              hbal_s.symm ▸ balRecord_storLst_ivl_mem had hl hl0
            rcases fixedObject_le_2pow64 hA_sNoBs hF_sNoBs (bal_in_fixedObjects hm_nb') with h0 | hbnd
            · dsimp at h0; omega
            · exact InitECandidate.Solver.Wave8Contracts.M12.lstObjects_eq_of_ivl hcell_nobs hbnd (mem_worldTypedIvls_bal hm_nb')
        rw [e0, e_off 16 (by omega), e_off 24 (by omega), e_off 32 (by omega),
            hl_eq 16 40 (by simp), hl_eq 24 16 (by simp), hl_eq 32 24 (by simp), hval_eq, hfl]
    have hfix_eq : fixedObjects post = fixedObjects s := by
      unfold fixedObjects
      rw [hbo_eq, hbal_eq, hglob_eq "journal", hglob_eq "journal_cap"]
      congr 3; exact List.map_congr_left fun gn _ => by simp only [bufferRegion, hglob_eq]
    have hFix_post : FixedTyped post := fixedTyped_of_eq hA_post hWT.2.2.1 hh hsc hfix_eq
    have hNH_sNoBs : NodeHeap sNoBs Nd := by
      refine ⟨fun n hn => ?_, hWT.2.2.2.1.2⟩
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hWT.2.2.2.1.1 n hn
      have hal_c : ∀ i : Ivl, Allocated s i → Allocated sNoBs i := fun i h => by
        unfold Allocated at h ⊢
        rwa [hsNoBs_other "heap_ptr" (by decide), hsNoBs_other "scratch_ptr" (by decide)]
      refine ⟨c1, hal_c _ c2, c3, c4, c5, c6, fun h12 => ?_, c8, c9, c10⟩
      rcases c7 h12 with hz | ⟨hnib, hal, hin, hdj⟩
      · exact Or.inl hz
      · exact Or.inr ⟨hnib, hal_c _ hal, hin, hdj⟩
    have hne_eq : nodeExtents post Nd = nodeExtents s Nd :=
      nodeExtents_eq (s := sNoBs) (post := pNoBs) hNH_sNoBs hcell_nobs
    have hNH_post : NodeHeap post Nd := by
      have hNH_p := nodeHeap_congr hNH_sNoBs hcell_nobs
        (by rw [hpNoBs_other "heap_ptr" (by decide), hsNoBs_other "heap_ptr" (by decide)])
        (by rw [hpNoBs_other "scratch_ptr" (by decide), hsNoBs_other "scratch_ptr" (by decide)])
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
    have hTr_post : TriesTypedWith post S Nd := by
      refine ⟨hNH_post, ?_, ?_⟩
      · rw [hne_eq, hfix_eq]
        exact fun o ho => ⟨fun t ht i hi => by
          rw [hhtabFP_eq t ht] at hi
          exact (hWT.2.2.2.2.1 o ho).1 t ht i hi, (hWT.2.2.2.2.1 o ho).2⟩
      · rw [hglob_eq "ws"]; intro hws_nz
        rw [hother_rec S Nd hWT "ws" 40 (by decide) (by decide) hws_nz 24 (by omega) (by omega),
            hother_rec S Nd hWT "ws" 40 (by decide) (by decide) hws_nz 32 (by omega) (by omega)]
        obtain ⟨hr24, hr32⟩ := hWT.2.2.2.2.2 hws_nz
        refine ⟨hr24, fun htS i hi => ?_⟩
        have hW32 := (hWT.1.2.1 _ htS).1
        rw [hhtabHdr_eq _ htS 3 (by omega)] at hi
        rw [hhtabHdr_eq _ htS 5 (by omega), hhtabHdr_eq _ htS 6 (by omega)]
        have hfp3 : (hdr sNoBs (memW s (globN s "ws" + 32)) 6, (hdr sNoBs (memW s (globN s "ws" + 32)) 10 + 1) * 8) ∈
            htabFootprint sNoBs (memW s (globN s "ws" + 32)) := by simp [htabFootprint]
        have hob := (hW32.1 _ hfp3).1
        have hcnt32 := htabCount_le_ncap hW32
        have h264 : heapEnd ≤ 2 ^ 64 := by rw [heapEnd_val]; decide
        have hh6 : hdr sNoBs (memW s (globN s "ws" + 32)) 6 = hdr s (memW s (globN s "ws" + 32)) 6 := rfl
        have hh10 : hdr sNoBs (memW s (globN s "ws" + 32)) 10 = hdr s (memW s (globN s "ws" + 32)) 10 := rfl
        have hob' : hdr s (memW s (globN s "ws" + 32)) 6 + (hdr s (memW s (globN s "ws" + 32)) 10 + 1) * 8 ≤ heapEnd := by
          simpa [Inside, hh6, hh10] using hob.2
        have ho_eq : memW post (hdr s (memW s (globN s "ws" + 32)) 6 + 8 * i) =
            memW s (hdr s (memW s (globN s "ws" + 32)) 6 + 8 * i) :=
          memW_eq_of_cellHits hcell_nobs (by omega)
            (mem_worldTypedIvls_htab htS hfp3) ⟨by dsimp; rw [hh6]; omega, by dsimp; rw [hh6, hh10]; omega⟩
        have hnf_eq : nodeF post (hdr s (memW s (globN s "ws" + 32)) 5) (memW s (hdr s (memW s (globN s "ws" + 32)) 6 + 8 * i)) 8 =
            nodeF s (hdr s (memW s (globN s "ws" + 32)) 5) (memW s (hdr s (memW s (globN s "ws" + 32)) 6 + 8 * i)) 8 :=
          nodeF_eq_of_lt (s := sNoBs) (post := pNoBs) hcell_nobs htS (hhtabWF_s _ hW32) (htabOrder_entry_le_ncap hW32 hi) (by omega)
        rw [ho_eq, hnf_eq]
        exact hr32 htS i hi
    have hJ_nobs : JournalTyped sNoBs S := by
      obtain ⟨j1, j2, j3, j4⟩ := hWT.2.1
      unfold JournalTyped
      simp only [hsNoBs_other "journal_n" (by decide), hsNoBs_other "journal_cap" (by decide),
        hsNoBs_other "journal" (by decide)]
      refine ⟨j1, j2, ?_, j4⟩
      rcases j3 with hz | ⟨hal, hw⟩
      · exact Or.inl hz
      · refine Or.inr ⟨?_, hw⟩
        unfold Allocated at hal ⊢
        rwa [hsNoBs_other "heap_ptr" (by decide), hsNoBs_other "scratch_ptr" (by decide)]
    have hjrs_eq : journalRoleSlots post = journalRoleSlots s := by
      have h1 : journalRoleSlots pNoBs = journalRoleSlots sNoBs :=
        journalRoleSlots_eq hA_sNoBs hJ_nobs hF_sNoBs hcell_nobs (fun g hg => by
          simp only [InitECandidate.Solver.Wave8Contracts.M12.coreWorldGlobals, List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · rw [hpNoBs_other "ws" (by decide), hsNoBs_other "ws" (by decide)]
          · rw [hpNoBs_bs, hsNoBs_bs]
          · rw [hpNoBs_other "ts" (by decide), hsNoBs_other "ts" (by decide)]
          · rw [hpNoBs_other "bo" (by decide), hsNoBs_other "bo" (by decide)]
          · rw [hpNoBs_other "bal_accounts" (by decide), hsNoBs_other "bal_accounts" (by decide)]
          · rw [hpNoBs_other "bal_idx_accts" (by decide), hsNoBs_other "bal_idx_accts" (by decide)]
          · rw [hpNoBs_other "bal_idx_stor" (by decide), hsNoBs_other "bal_idx_stor" (by decide)]
          · rw [hpNoBs_other "journal" (by decide), hsNoBs_other "journal" (by decide)]
          · rw [hpNoBs_other "journal_cap" (by decide), hsNoBs_other "journal_cap" (by decide)]
          · rw [hpNoBs_other "journal_n" (by decide), hsNoBs_other "journal_n" (by decide)])
      have hs_j : journalRoleSlots sNoBs = journalRoleSlots s := by
        unfold journalRoleSlots journalRole
        rw [hsNoBs_other "journal_n" (by decide), hsNoBs_other "journal" (by decide),
            hsNoBs_other "ts" (by decide)]; rfl
      have hp_j : journalRoleSlots pNoBs = journalRoleSlots post := by
        unfold journalRoleSlots journalRole
        rw [hpNoBs_other "journal_n" (by decide), hpNoBs_other "journal" (by decide),
            hpNoBs_other "ts" (by decide), ← hglob_eq "journal_n", ← hglob_eq "journal",
            ← hglob_eq "ts"]; rfl
      rw [← hp_j, ← hs_j, h1]
    have hbs_slot_eq : ∀ k : Nat, (k + 8 ≤ 56 ∨ k = 72) →
        memW post (globN s "bs" + k) = memW s (globN s "bs" + k) := fun k hk =>
      hnot_bs56 _ (by omega) (fun ⟨c1, c2⟩ => by dsimp only at c1 c2; omega)
    have hwrs_eq : worldRoleSlots post = worldRoleSlots s := by
      have hrs_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] = recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
        unfold recRoles; rw [hglob_eq "ws"]; split_ifs with h0
        · rfl
        · exact List.map_congr_left fun p hp => by
            have hk : p.1 % 8 = 0 ∧ p.1 + 8 ≤ 40 := by simp at hp; rcases hp with rfl | rfl <;> omega
            rw [hother_rec S Nd hWT "ws" 40 (by decide) (by decide) h0 p.1 hk.1 hk.2]
      have hrs_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
          (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
          recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
            (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
        unfold recRoles; rw [hglob_eq "bs"]; simp only [hbs0, ↓reduceIte]
        exact List.map_congr_left fun p hp => by
          have hk : p.1 + 8 ≤ 56 ∨ p.1 = 72 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
          rw [hbs_slot_eq p.1 hk]
      have hrs_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
          (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
          recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
            (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
        unfold recRoles; rw [hglob_eq "ts"]; split_ifs with h0
        · rfl
        · exact List.map_congr_left fun p hp => by
            have hk : p.1 % 8 = 0 ∧ p.1 + 8 ≤ 72 := by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
              rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
            rw [hother_rec S Nd hWT "ts" 72 (by decide) (by decide) h0 p.1 hk.1 hk.2]
      have hnr_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
        unfold nestRoles; rw [hglob_eq "bs"]
        simp only [hbs0, ↓reduceIte, hbs_slot_eq 32 (Or.inl (by omega))]
        split_ifs with ht0
        · rfl
        · rcases hWT.1.2.2.2.2.1 32 (by decide) hbs0 with h0 | hm
          · exact absurd h0 ht0
          · rw [hhtabVals_eq _ hm]
      have hnr_ts : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
        unfold nestRoles; rw [hglob_eq "ts"]
        by_cases h0 : globN s "ts" = 0
        · simp [h0]
        · simp only [h0, ↓reduceIte, hother_rec S Nd hWT "ts" 72 (by decide) (by decide) h0 32 (by omega) (by omega)]
          split_ifs with ht0
          · rfl
          · rcases hWT.1.2.2.2.2.2.1 32 (by decide) h0 with hz | hm
            · exact absurd hz ht0
            · rw [hhtabVals_eq _ hm]
      unfold worldRoleSlots
      rw [hrs_ws, hrs_bs, hrs_ts, hglob_eq "bal_accounts", hglob_eq "bal_idx_accts",
          hglob_eq "bal_idx_stor", hnr_bs, hnr_ts, hbrec_eq]
      congr 1; congr 1
      apply List.flatMap_congr; intro ad had
      have hm_nb : (ad, 40) ∈ balObjects sNoBs := hbal_s.symm ▸ balRecord_ivl_mem had
      rcases fixedObject_le_2pow64 hA_sNoBs hF_sNoBs (bal_in_fixedObjects hm_nb) with h0 | hbnd
      · dsimp at h0; omega
      · dsimp at hbnd
        rw [show memW post ad = memW pNoBs ad from rfl,
            show memW s ad = memW sNoBs ad from rfl,
            memW_eq_of_cellHits hcell_nobs (by omega) (mem_worldTypedIvls_bal hm_nb) ⟨by dsimp; omega, by dsimp; omega⟩,
            show memW post (ad + 8) = memW pNoBs (ad + 8) from rfl,
            show memW s (ad + 8) = memW sNoBs (ad + 8) from rfl,
            memW_eq_of_cellHits hcell_nobs (by omega) (mem_worldTypedIvls_bal hm_nb) ⟨by dsimp; omega, by dsimp; omega⟩]
    have hJrn_post : JournalTyped post S := by
      obtain ⟨j1, j2, j3, j4⟩ := hWT.2.1
      unfold JournalTyped; simp only [hglob_eq]
      refine ⟨j1, j2, ?_, fun i hi => ?_⟩
      · by_cases hjc0 : globN s "journal_cap" = 0
        · exact Or.inl hjc0
        · rcases j3 with hz | ⟨hal, hw⟩
          · exact Or.inl hz
          · have hal' : Allocated post (globN s "journal", 32 * globN s "journal_cap") := by
              unfold Allocated at hal ⊢; simp only [hglob_eq]; exact hal
            exact Or.inr ⟨hal', InitECandidate.Solver.Wave8Contracts.M12.wordsOK_of_allocated hA_post hal' hw.1 hw.2.1⟩
      · have hjc0 : globN sNoBs "journal_cap" ≠ 0 := by rw [hsNoBs_other "journal_cap" (by decide)]; omega
        rcases j3 with hz | ⟨hal, _⟩
        · omega
        · have hbnd := allocated_le_2pow64 hW.1.2 hal; dsimp only at hbnd
          have hj_mem := mem_worldTypedIvls_journal (s := sNoBs) (S := S) (Nd := Nd) hjc0
          rw [hsNoBs_other "journal" (by decide), hsNoBs_other "journal_cap" (by decide)] at hj_mem
          have e0 : memW post (globN s "journal" + 32 * i) = memW s (globN s "journal" + 32 * i) :=
            memW_eq_of_cellHits hcell_nobs (by omega) hj_mem ⟨by dsimp; omega, by dsimp; omega⟩
          rw [e0]; exact j4 i hi
    have hTab_post : TablesTyped post S := by
      obtain ⟨hnd, htwf, htpw, hws, hbs, hts, hgr, hbs32, hts32, hbal_ok, hbo_ok, hroles⟩ := hWT.1
      refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro t ht
        rw [hhtabFP_eq t ht, hfix_eq]
        exact ⟨hhtabWF_p t (htabWF_congr hcell_nobs ht (hhtabWF_s t (htwf t ht).1)), fun i hi =>
          ⟨by unfold Allocated; simp only [hglob_eq]; exact ((htwf t ht).2 i hi).1, ((htwf t ht).2 i hi).2⟩⟩
      · intro t ht u hu htu i hi j hj
        rw [hhtabFP_eq t ht] at hi; rw [hhtabFP_eq u hu] at hj
        exact htpw t ht u hu htu i hi j hj
      · intro k hk; rw [hglob_eq "ws"]; intro hnz
        have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by simp [wsTableSlots] at hk; rcases hk with rfl | rfl <;> omega
        rw [hother_rec S Nd hWT "ws" 40 (by decide) (by decide) hnz k hk8.1 hk8.2]; exact hws k hk hnz
      · intro k hk; rw [hglob_eq "bs"]; intro hnz
        have hk_ok : k + 8 ≤ 56 ∨ k = 72 := by
          simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
        rw [hbs_slot_eq k hk_ok]; exact hbs k hk hnz
      · intro k hk; rw [hglob_eq "ts"]; intro hnz
        have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
          simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
        rw [hother_rec S Nd hWT "ts" 72 (by decide) (by decide) hnz k hk8.1 hk8.2]; exact hts k hk hnz
      · intro g hg; rw [hglob_eq g]; exact hgr g hg
      · rw [hglob_eq "bs"]; intro hnz
        rw [hbs_slot_eq 32 (Or.inl (by omega))]; intro hmS
        exact htabValuesIn_congr hcell_nobs hmS (hhtabWF_s _ (htwf _ hmS).1) (fun _ h => h) (hbs32 hnz hmS)
      · rw [hglob_eq "ts"]; intro hnz
        rw [hother_rec S Nd hWT "ts" 72 (by decide) (by decide) hnz 32 (by omega) (by omega)]; intro hmS
        exact htabValuesIn_congr hcell_nobs hmS (hhtabWF_s _ (htwf _ hmS).1) (fun _ h => h) (hts32 hnz hmS)
      · rw [hbrec_eq]; intro ad had
        have hm_nb : (ad, 40) ∈ balObjects sNoBs := hbal_s.symm ▸ balRecord_ivl_mem had
        rcases fixedObject_le_2pow64 hA_sNoBs hF_sNoBs (bal_in_fixedObjects hm_nb) with h0 | hbnd
        · dsimp at h0; omega
        · dsimp at hbnd
          obtain ⟨c1, c2, c3, c4⟩ := hbal_ok ad had
          have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd) hm_nb
          have e0 : memW post ad = memW s ad :=
            memW_eq_of_cellHits hcell_nobs (by omega) hwti_ad ⟨by dsimp; omega, by dsimp; omega⟩
          have e8 : memW post (ad + 8) = memW s (ad + 8) :=
            memW_eq_of_cellHits hcell_nobs (by omega) hwti_ad ⟨by dsimp; omega, by dsimp; omega⟩
          rw [e0, e8]; refine ⟨c1, c2, ?_, ?_⟩
          · intro k hk
            have hk_le : k + 8 ≤ 40 := by simp at hk; rcases hk with rfl | rfl | rfl <;> omega
            have ek : memW post (ad + k) = memW s (ad + k) :=
              memW_eq_of_cellHits hcell_nobs (by omega) hwti_ad ⟨by dsimp; omega, by dsimp; omega⟩
            rw [ek]
            by_cases hk0 : memW s (ad + k) = 0
            · unfold LstOK
              have h08 : memW post 8 = memW s 8 := memW_eq_of_lt_sourceBase hcell_nobs (by rw [sourceBase_val]; omega)
              have h16 : memW post 16 = memW s 16 := memW_eq_of_lt_sourceBase hcell_nobs (by rw [sourceBase_val]; omega)
              have hc3k := c3 k hk; unfold LstOK at hc3k
              simpa [hk0, h08, h16] using hc3k
            · have hm_k : (memW s (ad + k), 24) ∈ balObjects sNoBs :=
                hbal_s.symm ▸ balRecord_lst_ivl_mem had hk hk0
              rcases fixedObject_le_2pow64 hA_sNoBs hF_sNoBs (bal_in_fixedObjects hm_k) with h0 | hb_k
              · dsimp at h0; omega
              · exact (lstOK_congr_of_ivl hcell_nobs hb_k (mem_worldTypedIvls_bal hm_k)).2 (c3 k hk)
          · rw [hhtabVals_eq (memW s ad) c1]
            intro l hl
            by_cases hl0 : l = 0
            · subst hl0; unfold LstOK
              have h08 : memW post 8 = memW s 8 := memW_eq_of_lt_sourceBase hcell_nobs (by rw [sourceBase_val]; omega)
              have h16 : memW post 16 = memW s 16 := memW_eq_of_lt_sourceBase hcell_nobs (by rw [sourceBase_val]; omega)
              have hc4l := c4 0 hl; unfold LstOK at hc4l
              simpa [h08, h16] using hc4l
            · have hm_l : (l, 24) ∈ balObjects sNoBs :=
                hbal_s.symm ▸ balRecord_storLst_ivl_mem had hl hl0
              rcases fixedObject_le_2pow64 hA_sNoBs hF_sNoBs (bal_in_fixedObjects hm_l) with h0 | hb_l
              · dsimp at h0; omega
              · exact (lstOK_congr_of_ivl hcell_nobs hb_l (mem_worldTypedIvls_bal hm_l)).2 (c4 l hl)
      · rw [hglob_eq "bo"]; intro hnz k hk
        have hk8 : k % 8 = 0 ∧ k + 8 ≤ 88 := by simp at hk; rcases hk with rfl | rfl <;> omega
        rw [hother_rec S Nd hWT "bo" 88 (by decide) (by decide) hnz k hk8.1 hk8.2]; intro hp0
        have hm_bo : (memW s (globN s "bo" + k), 24) ∈ blockOutObjects sNoBs := by
          rw [hbo_s]; unfold blockOutObjects
          simp at hk; rcases hk with rfl | rfl <;> simp [hnz, hp0]
        rcases fixedObject_le_2pow64 hA_sNoBs hF_sNoBs (blockOut_in_fixedObjects hm_bo) with h0 | hb_bo
        · dsimp at h0; omega
        · exact (lstOK_congr_of_ivl hcell_nobs hb_bo (mem_worldTypedIvls_blockOut hm_bo)).2 (hbo_ok hnz k hk hp0)
      · unfold RolesOK at hroles ⊢; rw [hwrs_eq, hjrs_eq]
        exact ⟨fun a ha => ⟨(hroles.1 a ha).1, by
          rw [hhtabHdr_eq a.1 (hroles.1 a ha).1 0 (by omega)]; exact (hroles.1 a ha).2⟩, hroles.2⟩
    have hwo_eq : worldOwned post S Nd = worldOwned s S Nd := by
      unfold worldOwned; rw [hfix_eq, hne_eq]; congr 2
      exact List.flatMap_congr fun t ht => hhtabFP_eq t ht
    refine ⟨S, Nd, fun _ h => h, ⟨hTab_post, hJrn_post, hFix_post, hTr_post⟩, ?_, ?_, trivial⟩
    · rw [hwo_eq]; exact fun o ho => Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩)
    · intro a ha _
      apply heff.cell_frame a
      intro x hx; simp at hx; subst hx
      have hbs_in_wo : (globN s "bs", 80) ∈ worldOwned s S Nd :=
        List.mem_append_left _ (List.mem_append_right _ (hsz ▸ hfix_bs))
      have hno_bs := ha (globN s "bs", 80) (List.mem_append_left [freeGap s] (List.mem_append_left [] hbs_in_wo))
      rintro ⟨c1, c2⟩; exact hno_bs ⟨by dsimp at c1 ⊢; omega, by dsimp at c2 ⊢; omega⟩

/-- 5. `wk_track_ancestor_access` (`Primitives.lean:416`). -/
theorem «wk_track_ancestor_access» :
    WorldKeeps WorldOK (fun _ => [])
      []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "track_ancestor_access") := by
  refine ⟨_, _, _, lookup_track_ancestor_access, ?_⟩
  intro F s _hcode hW hex _hnt hres
  obtain ⟨offw0, hoffw0⟩ := one_word_param lookup_track_ancestor_access hex
  let Rbs : List Ivl := if globN s "bs" = 0 then [] else [(globN s "bs" + 56, 16)]
  suffices heff : ByteRegionEffect s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_track_ancestor_access)).2 Rbs by
    exact worldStep_of_bs56_effect hW heff
  have hb : sourceFnBody Guest.Software.guestFn_track_ancestor_access =
      .seq
        (.ite (.cmp .equal (.load .one (.op .add [.var .global (ofString "bs"), .const 56])) (.const 0))
          (.seq
            (.store (.op .add [.var .global (ofString "bs"), .const 56]) (.const 1))
            (.store (.op .add [.var .global (ofString "bs"), .const 64]) (.var .local (ofString "offset"))))
          (.ite (.cmp .lower (.load .one (.op .add [.var .global (ofString "bs"), .const 64]))
              (.var .local (ofString "offset")))
            (.store (.op .add [.var .global (ofString "bs"), .const 64]) (.var .local (ofString "offset")))
            .skip))
        (.return (.const 0)) := rfl
  rw [hb] at hres ⊢
  have hbs_info : ∃ bsw : BitVec 64,
      s.globals.lookup (ofString "bs") = some (.val (.word bsw)) ∧
      globN s "bs" = bsw.toNat ∧ globN s "bs" ≠ 0 ∧ bsw.toNat + 64 < heapEnd := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres
    rcases hg : s.globals.lookup (ofString "bs") with _ | gv
    · simp [evalHOLExact, evalListHOLExact, hg] at hres; exact False.elim (not_resumes_error hres)
    · rcases gv with ⟨⟨bsw⟩⟩ | _ | _
      · by_cases hdom56 : s.memaddrs (bsw + 56#64)
        · obtain ⟨_, _, _, hF0, _⟩ := hW.2
          have hglob_bs : globN s "bs" = bsw.toNat := by simp [globN, hg]
          have hbs_nz : bsw.toNat ≠ 0 := by
            intro hz
            have h0 : bsw = 0#64 := BitVec.eq_of_toNat_eq hz
            subst h0
            have hdom' := hW.1.1.memaddrs ▸ hdom56
            rw [ordinaryDomain_iff] at hdom'
            have : (0#64 + 56#64).toNat = 56 := by decide
            omega
          have hfix0 := typedRec_in_fixedObjects s (g := "bs") (sz := 80) (by decide)
          rw [hglob_bs, if_neg hbs_nz] at hfix0
          rcases hF0.1 _ hfix0 with h0 | ⟨hal0, _⟩
          · dsimp at h0; omega
          · have hb_le : bsw.toNat + 80 ≤ scratchEnd := by
              rcases hal0 with ⟨_, hhi⟩ | ⟨_, hhi⟩
              · have := hW.1.2.2.1; rw [heapLimit_val] at this; rw [scratchEnd_val]; dsimp at hhi; omega
              · exact hhi
            rw [scratchEnd_val] at hb_le; rw [heapEnd_val]
            exact ⟨bsw, rfl, hglob_bs, by omega, by omega⟩
        · have hc1_none : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
              (.cmp .equal (.load .one (.op .add [.var .global (ofString "bs"), .const 56])) (.const 0)) = none := by
            simp [evalHOLExact, evalListHOLExact, hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, hdom56]
          rw [hc1_none] at hres; exact False.elim (not_resumes_error hres)
      · simp [evalHOLExact, evalListHOLExact, hg, valueIsWord] at hres; exact False.elim (not_resumes_error hres)
      · simp [evalHOLExact, evalListHOLExact, hg, valueIsWord] at hres; exact False.elim (not_resumes_error hres)
  obtain ⟨bsw, hbsw, hbs_nat, hbs_nz, hbs_lt_he⟩ := hbs_info
  rw [show Rbs = [(globN s "bs" + 56, 16)] from if_neg hbs_nz]
  have hhe := heapEnd_val
  have hbs56_nat : (bsw + 56).toNat = globN s "bs" + 56 := by
    rw [BitVec.toNat_add, show (56 : BitVec 64).toNat = 56 from rfl, ← hbs_nat]; exact Nat.mod_eq_of_lt (by omega)
  have hbs64_nat : (bsw + 64).toNat = globN s "bs" + 64 := by
    rw [BitVec.toNat_add, show (64 : BitVec 64).toNat = 64 from rfl, ← hbs_nat]; exact Nat.mod_eq_of_lt (by omega)
  have hstore_res : ∀ (t : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64),
      (evaluateHOLFiniteState t (.store d e)).1 = none ∨ (evaluateHOLFiniteState t (.store d e)).1 = some .error := by
    intro t d e; rw [evaluateHOLFiniteState_store]
    split <;> [ (split <;> [ (split <;> [exact Or.inl rfl; exact Or.inr rfl]); exact Or.inr rfl ]); exact Or.inr rfl ]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres ⊢
  rcases hc1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.load .one (.op .add [.var .global (ofString "bs"), .const 56])) (.const 0)) with _ | cv1
  · simp only [hc1] at hres; exact False.elim (not_resumes_error hres)
  · simp only [hc1] at hres ⊢
    rcases cv1 with ⟨⟨cw1⟩⟩ | _ | _
    · dsimp only at hres ⊢
      by_cases hcw1 : cw1 = 0
      · rw [if_pos hcw1, evaluateHOLFiniteState_ite] at hres ⊢
        rcases hc2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
            (.cmp .lower (.load .one (.op .add [.var .global (ofString "bs"), .const 64]))
              (.var .local (ofString "offset"))) with _ | cv2
        · simp only [hc2] at hres; exact False.elim (not_resumes_error hres)
        · simp only [hc2] at hres ⊢
          rcases cv2 with ⟨⟨cw2⟩⟩ | _ | _
          · dsimp only at hres ⊢
            by_cases hcw2 : cw2 = 0
            · rw [if_pos hcw2, evaluateHOLFiniteState_skip, evaluateHOLFiniteState_return]
              simp [evalHOLExact, shapeOfHOLExact]
              exact ByteRegionEffect.refl s _ |>.with_locals_clock _ _
            · rw [if_neg hcw2] at hres ⊢
              rcases hst : evaluateHOLFiniteState s
                  (.store (.op .add [.var .global (ofString "bs"), .const 64]) (.var .local (ofString "offset"))) with ⟨rs, s1⟩
              simp only [hst] at hres ⊢
              rcases hstore_res s (.op .add [.var .global (ofString "bs"), .const 64]) (.var .local (ofString "offset")) with hsn | hse
              · rw [hst] at hsn; dsimp at hsn; subst hsn; dsimp only
                obtain ⟨heff1, _⟩ := ByteRegionEffect.of_store_word hW.1.1.memaddrs hst
                  (Rl := [(globN s "bs" + 56, 16)])
                  (fun v hv => by simp [evalHOLExact, hoffw0] at hv; exact ⟨offw0, hv.symm⟩)
                  (fun addr hdst _ => by
                    have haddr : addr = bsw + 64 := by
                      simp [evalHOLExact, evalListHOLExact, hbsw, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero] at hdst
                      exact hdst.symm
                    subst haddr
                    exact ⟨_, List.mem_singleton.2 rfl, by dsimp only; rw [hbs64_nat]; omega, by dsimp only; rw [hbs64_nat]⟩)
                rw [evaluateHOLFiniteState_return]; simp [evalHOLExact, shapeOfHOLExact]
                exact heff1.with_locals_clock _ _
              · rw [hst] at hse; dsimp at hse; subst hse; exact False.elim (not_resumes_error hres)
          · simp at hres; exact False.elim (not_resumes_error hres)
          · simp at hres; exact False.elim (not_resumes_error hres)
      · rw [if_neg hcw1, evaluateHOLFiniteState_seq_line780] at hres ⊢
        rcases hst1 : evaluateHOLFiniteState s
            (.store (.op .add [.var .global (ofString "bs"), .const 56]) (.const 1)) with ⟨rs1, s1⟩
        simp only [hst1] at hres ⊢
        rcases hstore_res s (.op .add [.var .global (ofString "bs"), .const 56]) (.const 1) with hsn1 | hse1
        · rw [hst1] at hsn1; dsimp at hsn1; subst hsn1; dsimp only at hres ⊢
          obtain ⟨heff1, hs1_loc⟩ := ByteRegionEffect.of_store_word hW.1.1.memaddrs hst1
            (Rl := [(globN s "bs" + 56, 16)])
            (fun v hv => by simp [evalHOLExact] at hv; exact ⟨1, hv.symm⟩)
            (fun addr hdst _ => by
              have haddr : addr = bsw + 56 := by
                simp [evalHOLExact, evalListHOLExact, hbsw, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero] at hdst
                exact hdst.symm
              subst haddr
              exact ⟨_, List.mem_singleton.2 rfl, by dsimp only; rw [hbs56_nat], by dsimp only; rw [hbs56_nat]; omega⟩)
          have hs1_ma : s1.memaddrs = ordinaryDomain := heff1.memaddrs.trans hW.1.1.memaddrs
          have hs1_bs : s1.globals.lookup (ofString "bs") = some (.val (.word bsw)) := heff1.globals ▸ hbsw
          rcases hst2 : evaluateHOLFiniteState s1
              (.store (.op .add [.var .global (ofString "bs"), .const 64]) (.var .local (ofString "offset"))) with ⟨rs2, s2⟩
          simp only [hst2] at hres ⊢
          rcases hstore_res s1 (.op .add [.var .global (ofString "bs"), .const 64]) (.var .local (ofString "offset")) with hsn2 | hse2
          · rw [hst2] at hsn2; dsimp at hsn2; subst hsn2; dsimp only
            have hs1_off : s1.locals.lookup (ofString "offset") = some (.val (.word offw0)) := hs1_loc ▸ hoffw0
            obtain ⟨heff2, _⟩ := ByteRegionEffect.of_store_word hs1_ma hst2
              (Rl := [(globN s "bs" + 56, 16)])
              (fun v hv => by simp [evalHOLExact, hs1_off] at hv; exact ⟨offw0, hv.symm⟩)
              (fun addr hdst _ => by
                have haddr : addr = bsw + 64 := by
                  simp [evalHOLExact, evalListHOLExact, hs1_bs, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero] at hdst
                  exact hdst.symm
                subst haddr
                exact ⟨_, List.mem_singleton.2 rfl, by dsimp only; rw [hbs64_nat]; omega, by dsimp only; rw [hbs64_nat]⟩)
            rw [evaluateHOLFiniteState_return]; simp [evalHOLExact, shapeOfHOLExact]
            exact (heff1.trans heff2).with_locals_clock _ _
          · rw [hst2] at hse2; dsimp at hse2; subst hse2; exact False.elim (not_resumes_error hres)
        · rw [hst1] at hse1; dsimp at hse1; subst hse1; exact False.elim (not_resumes_error hres)
    · simp at hres; exact False.elim (not_resumes_error hres)
    · simp at hres; exact False.elim (not_resumes_error hres)

end InitECandidate.Solver.Wave8GuestInv.R11Shards.WkShard08
