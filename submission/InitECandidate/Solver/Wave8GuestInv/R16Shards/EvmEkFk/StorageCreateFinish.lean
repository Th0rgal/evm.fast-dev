import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.EkWarmStorageKey
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkGetAccount
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.AccountWk

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup

theorem lookup_create_finish :
    originalRuntimeCode.lookup (ofString "create_finish") =
      some ((sourceFunctionEntry Guest.Software.guestFn_create_finish).2) :=
  lookup_of_guestAst_getElem 589 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_create_finish) rfl

theorem lookup_set_code :
    originalRuntimeCode.lookup (ofString "set_code") =
      some ((sourceFunctionEntry Guest.Software.guestFn_set_code).2) :=
  lookup_of_guestAst_getElem 399 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_set_code) rfl

theorem lookup_get_storage_original :
    originalRuntimeCode.lookup (ofString "get_storage_original") =
      some ((sourceFunctionEntry Guest.Software.guestFn_get_storage_original).2) :=
  lookup_of_guestAst_getElem 379 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_get_storage_original) rfl

theorem lookup_ws_storage_trie :
    originalRuntimeCode.lookup (ofString "ws_storage_trie") =
      some ((sourceFunctionEntry Guest.Software.guestFn_ws_storage_trie).2) :=
  lookup_of_guestAst_getElem 368 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ws_storage_trie) rfl

theorem lookup_ws_get_storage :
    originalRuntimeCode.lookup (ofString "ws_get_storage") =
      some ((sourceFunctionEntry Guest.Software.guestFn_ws_get_storage).2) :=
  lookup_of_guestAst_getElem 369 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ws_get_storage) rfl

theorem allocated_disj_fresh_extent {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {o j : Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (ho : Allocated s o)
    (hj : Inside j (globN s "heap_ptr") (globN post "heap_ptr")) :
    Disj o j := by
  have hd := R16Shards.disj_fresh_of_allocated hAs hAp hhp ho
  unfold Inside at hj
  unfold Disj at hd ⊢
  dsimp only at hd ⊢
  rcases hd with h | h | h | h
  · exact Or.inl h
  · by_cases hz : globN post "heap_ptr" = globN s "heap_ptr"
    · right; left; omega
    · omega
  · right; right; left; omega
  · right; right; right; omega

theorem allocated_disj_old_or_fresh_extent {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {o j : Ivl} {old : List Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (ho : Allocated s o)
    (hold : ∀ i ∈ old, Disj o i)
    (hj : (∃ i ∈ old, Inside j i.1 (i.1 + i.2)) ∨
      Inside j (globN s "heap_ptr") (globN post "heap_ptr")) :
    Disj o j := by
  rcases hj with ⟨i, hi, hin⟩ | hfresh
  · have hd := hold i hi
    unfold Inside at hin
    unfold Disj at hd ⊢
    rcases hd with hz | hz | hbefore | hafter
    · exact Or.inl hz
    · right; left; omega
    · right; right; left; omega
    · right; right; right; omega
  · exact allocated_disj_fresh_extent hAs hAp hhp ho hfresh

theorem allocated_disj_growing_nodeExtents {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {o : Ivl} {Nd Nd' : List Nat}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (ho : Allocated s o)
    (hold : ∀ i ∈ nodeExtents s Nd, Disj o i)
    (hgrow : ∀ j ∈ nodeExtents post Nd',
      (∃ i ∈ nodeExtents s Nd, Inside j i.1 (i.1 + i.2)) ∨
        Inside j (globN s "heap_ptr") (globN post "heap_ptr")) :
    ∀ j ∈ nodeExtents post Nd', Disj o j := by
  intro j hj
  exact allocated_disj_old_or_fresh_extent hAs hAp hhp ho hold (hgrow j hj)

theorem rootIn_lt_word_limit {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {node : Nat} (hh : NodeHeap s Nd) (hr : RootIn Nd node) :
    node + 1 < 2 ^ 64 := by
  rcases hr with hz | hn
  · subst node; decide
  · have hi := (hh.1 node hn).2.2.1
    change sourceBase ≤ node ∧ node + nodeSize (memW s node) ≤ heapLimit at hi
    have hlim : heapLimit + 1 < 2 ^ 64 := by decide
    omega

theorem rootIn_tagged_word {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {node : Nat} (hh : NodeHeap s Nd) (hr : RootIn Nd node) :
    RootIn Nd ((BitVec.ofNat 64 (node + 1)).toNat - 1) := by
  have hlt := rootIn_lt_word_limit hh hr
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.add_sub_cancel] using hr

theorem allocated_disj_ownedGrows {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {o : Ivl} {old new : List Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (ho : Allocated s o)
    (hold : ∀ i ∈ old, Disj o i)
    (hgrow : OwnedGrows s post old new) :
    ∀ j ∈ new, Disj o j := by
  intro j hj
  rcases hgrow j hj with hz | hcontained
  · subst j
    exact Or.inr (Or.inl rfl)
  · exact allocated_disj_old_or_fresh_extent hAs hAp hhp ho hold hcontained

theorem allocated_regions_disj_ownedGrows {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {os old new : List Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hos : ∀ o ∈ os, Allocated s o)
    (hold : IvlsDisj os old)
    (hgrow : OwnedGrows s post old new) :
    IvlsDisj os new := by
  intro o ho
  exact allocated_disj_ownedGrows hAs hAp hhp (hos o ho) (hold o ho) hgrow

theorem worldStep_preserves_allocated_separation
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
      Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F →
      List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {S Nd : List Nat} {os : List Ivl}
    (hAs : ArenaOK s) (hstep : WorldStep R gw keep Q s r post)
    (hW : WorldTypedWith s S Nd)
    (hR : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hos : ∀ o ∈ os, Allocated s o)
    (hdisj : IvlsDisj os (worldOwned s S Nd)) :
    ∃ S' Nd', (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post S' Nd' ∧
      IvlsDisj os (worldOwned post S' Nd') ∧ Q s r post S' Nd' := by
  obtain ⟨hAp, hhp, _, _, htyped⟩ := hstep
  obtain ⟨S', Nd', hsub, hW', hgrow, _, hQ⟩ := htyped S Nd hW hR
  exact ⟨S', Nd', hsub, hW',
    allocated_regions_disj_ownedGrows hAs hAp.2 hhp hos hdisj hgrow, hQ⟩

theorem allocated_disj_free_regions {F : Type}
    {s : PanSemStateFiniteExact 64 F} {o : Ivl}
    (hA : ArenaOK s) (ho : Allocated s o) :
    Disj o (freeGap s) ∧ Disj o (heapFree s) := by
  have hsep : heapLimit ≤ scratchStart := by decide
  have hhp : globN s "heap_ptr" ≤ heapLimit := hA.2.1
  have hfm : scratchStart ≤ globN s "frame_mem_ptr" := hA.2.2.1
  have hsc : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hA.2.2.2.1
  rcases ho with ⟨_, hhi⟩ | ⟨hlo, _⟩
  · constructor
    · right; right; left; unfold freeGap; dsimp only; omega
    · right; right; left; unfold heapFree; exact hhi
  · constructor
    · right; right; right; unfold freeGap; dsimp only; omega
    · right; right; right; unfold heapFree; dsimp only; omega

theorem aligned_cell_unhit_of_frameOutside {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {keep : List Ivl} {fresh o : Ivl}
    (hfr : FrameOutside s post keep fresh)
    (hk : ∀ j ∈ keep, j = (0, 0) ∨ j.1 % 8 = 0 ∨ j.2 ≠ 0)
    (hf : fresh = (0, 0) ∨ fresh.1 % 8 = 0 ∨ fresh.2 ≠ 0)
    (hd : ∀ j ∈ keep, Disj o j) (hdf : Disj o fresh) :
    InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post o := by
  intro a ha hlo hhi
  have havoid : ∀ j : Ivl,
      (j = (0, 0) ∨ j.1 % 8 = 0 ∨ j.2 ≠ 0) →
      Disj o j → ¬ CellHits a.toNat j := by
    intro j hj hdj hhit
    obtain ⟨hc1, hc2⟩ := hhit
    rcases hdj with hz | hz | hb | hb
    · omega
    · rcases hj with he | hal | hn
      · subst j; dsimp only at hc1 hc2; omega
      · omega
      · exact hn hz
    · omega
    · omega
  exact hfr a (fun j hj => havoid j (hk j hj) (hd j hj)) (havoid fresh hf hdf)

theorem allocated_survives_world_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {old new R : List Ivl} {o : Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (ho : Allocated s o)
    (hd : ∀ j ∈ old, Disj o j) (hR : ∀ j ∈ R, Disj o j)
    (hshape : ∀ j ∈ old ++ R ++ [freeGap s],
      j = (0, 0) ∨ j.1 % 8 = 0 ∨ j.2 ≠ 0)
    (hfr : FrameOutside s post (old ++ R ++ [freeGap s]) (heapFree s))
    (hgrow : OwnedGrows s post old new) :
    InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post o ∧
      ∀ j ∈ new, Disj o j := by
  obtain ⟨hgap, hheap⟩ := allocated_disj_free_regions hAs ho
  refine ⟨aligned_cell_unhit_of_frameOutside hfr hshape ?_ ?_ hheap,
    allocated_disj_ownedGrows hAs hAp hhp ho hd hgrow⟩
  · right; left; exact hAs.2.2.2.2.2.1
  · intro j hj
    rcases List.mem_append.1 hj with hj | hj
    · rcases List.mem_append.1 hj with hj | hj
      · exact hd j hj
      · exact hR j hj
    · have he := List.mem_singleton.1 hj
      subst j
      exact hgap

theorem arena_survives_world_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {old new R : List Ivl} {o : Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (ho : Allocated s o ∨ Inside o scratchStart (globN s "frame_mem_ptr"))
    (hd : ∀ j ∈ old, Disj o j) (hR : ∀ j ∈ R, Disj o j)
    (hshape : ∀ j ∈ old ++ R ++ [freeGap s],
      j = (0, 0) ∨ j.1 % 8 = 0 ∨ j.2 ≠ 0)
    (hfr : FrameOutside s post (old ++ R ++ [freeGap s]) (heapFree s))
    (hgrow : OwnedGrows s post old new) :
    InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post o ∧
      ∀ j ∈ new, Disj o j := by
  rcases ho with hal | hfm
  · exact allocated_survives_world_frame hAs hAp hhp hal hd hR hshape hfr hgrow
  · have hsep : heapLimit ≤ scratchStart := by decide
    have hgap : Disj o (freeGap s) := Or.inr (Or.inr (Or.inl hfm.2))
    have hheap : Disj o (heapFree s) := by
      right; right; right
      have := hAs.2.1; have := hfm.1
      unfold heapFree; dsimp only; omega
    refine ⟨aligned_cell_unhit_of_frameOutside hfr hshape ?_ ?_ hheap, ?_⟩
    · right; left; exact hAs.2.2.2.2.2.1
    · intro j hj
      rcases List.mem_append.1 hj with hj | hj
      · rcases List.mem_append.1 hj with hj | hj
        · exact hd j hj
        · exact hR j hj
      · exact List.mem_singleton.1 hj ▸ hgap
    · intro j hj
      rcases hgrow j hj with rfl | ⟨i, hi, hin⟩ | hfresh
      · exact Or.inr (Or.inl rfl)
      · exact InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right hin (hd i hi)
      · right; right; right
        have := hAp.2.1
        exact le_trans hfresh.2 (le_trans this (le_trans hsep hfm.1))

private theorem globalBuffers_sz_pos : ∀ gn ∈ globalBuffers, gn.2 ≠ 0 := by decide

private theorem lstObjects_well_shaped {F : Type} (s : PanSemStateFiniteExact 64 F) (l esz : Nat) :
    ∀ x ∈ lstObjects s l esz, x = (0, 0) ∨ x.2 ≠ 0 := by
  intro x hx
  unfold lstObjects at hx
  by_cases hl0 : l = 0
  · rw [if_pos hl0] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact Or.inl rfl
  · rw [if_neg hl0] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inr (by dsimp only; omega)
    · by_cases hm0 : esz * memW s (l + 16) = 0
      · rw [if_pos hm0]; exact Or.inl (Prod.ext rfl hm0)
      · exact Or.inr hm0

private theorem blockOutObjects_well_shaped {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ∀ j ∈ blockOutObjects s, j = (0, 0) ∨ j.2 ≠ 0 := by
  have hobj : ∀ b p len : Nat,
      (if b = 0 ∨ p = 0 ∨ len = 0 then (0, 0) else (p, len)) = (0, 0) ∨
      (if b = 0 ∨ p = 0 ∨ len = 0 then (0, 0) else (p, len)).2 ≠ 0 := by
    intro b p len
    by_cases hc : b = 0 ∨ p = 0 ∨ len = 0
    · exact Or.inl (if_pos hc)
    · rw [if_neg hc]
      exact Or.inr (fun h0 => hc (Or.inr (Or.inr h0)))
  intro j hj
  unfold blockOutObjects at hj
  dsimp only at hj
  rcases List.mem_append.1 hj with h1 | h72
  · rcases List.mem_append.1 h1 with hhead | h40
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hhead
      rcases hhead with rfl | rfl | rfl <;> exact hobj _ _ _
    · by_cases hc : globN s "bo" = 0 ∨ memW s (globN s "bo" + 40) = 0
      · rw [if_pos hc] at h40
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h40
        rcases h40 with rfl | rfl <;> exact Or.inl rfl
      · rw [if_neg hc] at h40
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h40
        rcases h40 with rfl | rfl <;> exact hobj _ _ _
  · by_cases hc : globN s "bo" = 0 ∨ memW s (globN s "bo" + 72) = 0
    · rw [if_pos hc] at h72
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h72
      rcases h72 with rfl | rfl <;> exact Or.inl rfl
    · rw [if_neg hc] at h72
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h72
      rcases h72 with rfl | rfl <;> exact hobj _ _ _

theorem worldOwned_well_shaped {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hWT : WorldTypedWith s S Nd) :
    ∀ j ∈ worldOwned s S Nd, j = (0, 0) ∨ j.1 % 8 = 0 ∨ j.2 ≠ 0 := by
  obtain ⟨hT, _, _, hTr⟩ := hWT
  intro j hj
  unfold worldOwned at hj
  rcases List.mem_append.1 hj with h1 | hnd
  · rcases List.mem_append.1 h1 with htab | hfix
    · obtain ⟨t, ht, hj_fp⟩ := List.mem_flatMap.1 htab
      exact Or.inr (Or.inl (((hT.2.1 t ht).1.1 j hj_fp).2.1))
    · unfold fixedObjects at hfix
      rcases List.mem_append.1 hfix with h2 | hbal
      · rcases List.mem_append.1 h2 with h3 | hbo
        · rcases List.mem_append.1 h3 with hbuf | hjr
          · obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hbuf
            by_cases hg0 : globN s gn.1 = 0
            · exact Or.inl (by simp [hg0])
            · exact Or.inr (Or.inr (by simp [hg0, globalBuffers_sz_pos gn hgn]))
          · simp only [List.mem_singleton] at hjr; subst hjr
            by_cases hjc : globN s "journal_cap" = 0
            · exact Or.inl (by simp [hjc])
            · exact Or.inr (Or.inr (by dsimp only; omega))
        · rcases blockOutObjects_well_shaped s j hbo with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      · unfold balObjects at hbal
        obtain ⟨ad, _, hj_ad⟩ := List.mem_flatMap.1 hbal
        rcases List.mem_append.1 hj_ad with hhead3 | hslot
        · rcases List.mem_append.1 hhead3 with hhead2 | h32
          · rcases List.mem_append.1 hhead2 with hhead1 | h24
            · rw [List.mem_cons] at hhead1
              rcases hhead1 with rfl | h16
              · exact Or.inr (Or.inr (by dsimp only; omega))
              · rcases lstObjects_well_shaped s _ _ j h16 with h | h; exact Or.inl h; exact Or.inr (Or.inr h)
            · rcases lstObjects_well_shaped s _ _ j h24 with h | h; exact Or.inl h; exact Or.inr (Or.inr h)
          · rcases lstObjects_well_shaped s _ _ j h32 with h | h; exact Or.inl h; exact Or.inr (Or.inr h)
        · obtain ⟨l, _, hjl⟩ := List.mem_flatMap.1 hslot
          rcases lstObjects_well_shaped s _ _ j hjl with h | h; exact Or.inl h; exact Or.inr (Or.inr h)
  · unfold nodeExtents at hnd
    obtain ⟨n, hn, hj_n⟩ := List.mem_flatMap.1 hnd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj_n
    rcases hj_n with rfl | rfl
    · exact Or.inr (Or.inl ((hTr.1.1 n hn).2.2.2.1.1))
    · unfold nodePath
      split_ifs with hc
      · exact Or.inr (Or.inr hc.2)
      · exact Or.inl rfl

private theorem zero_not_mem_S {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hT : TablesTyped s S) : 0 ∉ S := by
  intro h0
  have hlo := ((hT.2.1 0 h0).1.1 (0, 88) (by simp [htabFootprint])).1.1
  have hsb : 0 < sourceBase := by decide
  dsimp at hlo; omega

theorem worldTypedWith_erase_local {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) {t : Nat}
    (hlocal : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t) :
    WorldTypedWith s (S.erase t) Nd := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hW
  have h0S : 0 ∉ S := zero_not_mem_S hT
  have hmem_er : ∀ {x}, x ∈ S → x ≠ t → x ∈ S.erase t := fun hx hne =>
    (List.Nodup.mem_erase_iff hT.1).2 ⟨hne, hx⟩
  have hsub_er : ∀ {x}, x ∈ S.erase t → x ∈ S := fun hx => List.mem_of_mem_erase hx
  have hwrs_ne : ∀ x r, x ≠ 0 → (x, r) ∈
      (recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] ++
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"),
        (48, "bs+48"), (72, "bs+72")] ++
      recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"),
        (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] ++
      [(globN s "bal_accounts", "bal_accounts"), (globN s "bal_idx_accts", "bal_idx_accts"),
        (globN s "bal_idx_stor", "bal_idx_stor")] ++
      nestRoles s "bs" "bs.inner" ++ nestRoles s "ts" "ts.inner" ++
      (balRecords s).flatMap fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]) →
      x ≠ t := by
    intro x r hxnz hmem
    have hfw : (x, r) ∈ worldRoleSlots s := by
      unfold worldRoleSlots
      exact List.mem_filter.2 ⟨hmem, by simp [hxnz]⟩
    exact hlocal (x, r) (List.mem_append.2 (Or.inl hfw))
  obtain ⟨hnd, hTt, hTp, hws, hbs, hts, hg, hbsN, htsN, hbal, hbo, hroles⟩ := hT
  refine ⟨⟨hnd.erase t,
    fun u hu => hTt u (hsub_er hu),
    fun u hu v hv => hTp u (hsub_er hu) v (hsub_er hv),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo, ?_⟩, ?_, hF, ?_⟩
  · intro k hk hnz
    rcases hws k hk hnz with h0 | hm
    · exact Or.inl h0
    · right; apply hmem_er hm
      have hnz_v : memW s (globN s "ws" + k) ≠ 0 := fun h0 => h0S (h0 ▸ hm)
      have hw_in : ∃ r, (memW s (globN s "ws" + k), r) ∈
          recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
        unfold recRoles; simp only [hnz, ↓reduceIte]
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        · exact ⟨"ws+16", by simp⟩
        · exact ⟨"ws+32", by simp⟩
      obtain ⟨r, hr_mem⟩ := hw_in
      apply hwrs_ne _ r hnz_v
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; left; exact List.mem_append.2 (Or.inl hr_mem)
  · intro k hk hnz
    rcases hbs k hk hnz with h0 | hm
    · exact Or.inl h0
    · right; apply hmem_er hm
      have hnz_v : memW s (globN s "bs" + k) ≠ 0 := fun h0 => h0S (h0 ▸ hm)
      have hb_in : ∃ r, (memW s (globN s "bs" + k), r) ∈
          recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
        unfold recRoles; simp only [hnz, ↓reduceIte]
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨"bs+8", by simp⟩
        · exact ⟨"bs+16", by simp⟩
        · exact ⟨"bs+24", by simp⟩
        · exact ⟨"bs+32", by simp⟩
        · exact ⟨"bs+40", by simp⟩
        · exact ⟨"bs+48", by simp⟩
        · exact ⟨"bs+72", by simp⟩
      obtain ⟨r, hr_mem⟩ := hb_in
      apply hwrs_ne _ r hnz_v
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; left; exact List.mem_append.2 (Or.inr hr_mem)
  · intro k hk hnz
    rcases hts k hk hnz with h0 | hm
    · exact Or.inl h0
    · right; apply hmem_er hm
      have hnz_v : memW s (globN s "ts" + k) ≠ 0 := fun h0 => h0S (h0 ▸ hm)
      have ht_in : ∃ r, (memW s (globN s "ts" + k), r) ∈
          recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
        unfold recRoles; simp only [hnz, ↓reduceIte]
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨"ts+8", by simp⟩
        · exact ⟨"ts+16", by simp⟩
        · exact ⟨"ts+24", by simp⟩
        · exact ⟨"ts+32", by simp⟩
        · exact ⟨"ts+40", by simp⟩
        · exact ⟨"ts+48", by simp⟩
        · exact ⟨"ts+56", by simp⟩
        · exact ⟨"ts+64", by simp⟩
      obtain ⟨r, hr_mem⟩ := ht_in
      apply hwrs_ne _ r hnz_v
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; exact List.mem_append.2 (Or.inr hr_mem)
  · intro g hgm
    rcases hg g hgm with h0 | hm
    · exact Or.inl h0
    · right; apply hmem_er hm
      have hnz_v : globN s g ≠ 0 := fun h0 => h0S (h0 ▸ hm)
      have hg_in : (globN s g, g) ∈
          [(globN s "bal_accounts", "bal_accounts"), (globN s "bal_idx_accts", "bal_idx_accts"),
           (globN s "bal_idx_stor", "bal_idx_stor")] := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hgm
        rcases hgm with rfl | rfl | rfl <;> simp
      apply hwrs_ne _ g hnz_v
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      exact List.mem_append.2 (Or.inr hg_in)
  · intro hnz hm i hi
    have hmS := hsub_er hm
    have hvS := hbsN hnz hmS i hi
    have hvnz : nodeF s (hdr s (memW s (globN s "bs" + 32)) 5) (memW s (hdr s (memW s (globN s "bs" + 32)) 6 + 8 * i)) 8 ≠ 0 :=
      fun h0 => h0S (h0 ▸ hvS)
    have h32nz : memW s (globN s "bs" + 32) ≠ 0 := fun h0 => h0S (h0 ▸ hmS)
    apply hmem_er hvS
    apply hwrs_ne _ "bs.inner" hvnz
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
    unfold nestRoles; simp only [hnz, h32nz, ↓reduceIte]
    exact List.mem_map.2 ⟨_, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩, rfl⟩
  · intro hnz hm i hi
    have hmS := hsub_er hm
    have hvS := htsN hnz hmS i hi
    have hvnz : nodeF s (hdr s (memW s (globN s "ts" + 32)) 5) (memW s (hdr s (memW s (globN s "ts" + 32)) 6 + 8 * i)) 8 ≠ 0 :=
      fun h0 => h0S (h0 ▸ hvS)
    have h32nz : memW s (globN s "ts" + 32) ≠ 0 := fun h0 => h0S (h0 ▸ hmS)
    apply hmem_er hvS
    apply hwrs_ne _ "ts.inner" hvnz
    apply List.mem_append.2; left; apply List.mem_append.2; right
    unfold nestRoles; simp only [hnz, h32nz, ↓reduceIte]
    exact List.mem_map.2 ⟨_, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩, rfl⟩
  · intro ad had
    obtain ⟨h0, h8, hrest⟩ := hbal ad had
    have h0nz : memW s ad ≠ 0 := fun h => h0S (h ▸ h0)
    have h8nz : memW s (ad + 8) ≠ 0 := fun h => h0S (h ▸ h8)
    refine ⟨hmem_er h0 ?_, hmem_er h8 ?_, hrest⟩
    · apply hwrs_ne _ "bal.stor" h0nz
      apply List.mem_append.2; right; exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
    · apply hwrs_ne _ "bal.reads" h8nz
      apply List.mem_append.2; right; exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
  · exact ⟨fun a ha => ⟨hmem_er (hroles.1 a ha).1 (hlocal a ha), (hroles.1 a ha).2⟩, hroles.2⟩
  · refine ⟨hJ.1, hJ.2.1, hJ.2.2.1, fun i hi => hmem_er (hJ.2.2.2 i hi) ?_⟩
    have hj_in : (memW s (globN s "journal" + 32 * i), journalRole s (memW s (globN s "journal" + 32 * i))) ∈ journalRoleSlots s := by
      unfold journalRoleSlots
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by simp⟩
    exact hlocal _ (List.mem_append.2 (Or.inr hj_in))
  · exact ⟨hTr.1, fun o ho => ⟨fun u hu => (hTr.2.1 o ho).1 u (hsub_er hu), (hTr.2.1 o ho).2⟩,
      fun hnz => ⟨(hTr.2.2 hnz).1, fun hm => (hTr.2.2 hnz).2 (hsub_er hm)⟩⟩

theorem adjoin_local_table {F : Type} {post : PanSemStateFiniteExact 64 F}
    {U Nd' : List Nat} {t klen : Nat}
    (hWU : WorldTypedWith post U Nd')
    (hwf_t : HtabWF post t)
    (hfp_t : ∀ i ∈ htabFootprint post t, Allocated post i ∧ ∀ o ∈ worldOwned post U Nd', Disj i o)
    (hklen : hdr post t 0 = klen) :
    t ∉ U ∧ t ≠ 0 ∧
    (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ t) ∧
    WorldTypedWith post (U ++ [t]) Nd' := by
  have ht_nz : t ≠ 0 := by
    have hlo := (hwf_t.1 (t, 88) (by simp [htabFootprint])).1.1
    have hsb0 : 0 < sourceBase := by decide
    dsimp at hlo; omega
  have ht_not_U : t ∉ U := by
    intro htU
    have hmem_ow : (t, 88) ∈ worldOwned post U Nd' := by
      unfold worldOwned
      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨t, htU, by simp [htabFootprint]⟩))))
    rcases (hfp_t (t, 88) (by simp [htabFootprint])).2 (t, 88) hmem_ow with hd | hd | hd | hd <;> dsimp at hd <;> omega
  obtain ⟨hTU, hJU, hFU, hTrU⟩ := hWU
  have ht_unass : ∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ t := by
    intro a ha heq
    have haU := (hTU.2.2.2.2.2.2.2.2.2.2.2.1 a ha).1
    rw [heq] at haU; exact ht_not_U haU
  have hsub_Ut : ∀ u ∈ U, u ∈ U ++ [t] := fun u hu => List.mem_append.2 (Or.inl hu)
  have hroot_Ut : ∀ {v}, RootIn U v → RootIn (U ++ [t]) v := by
    rintro v (rfl | hv); exact Or.inl rfl; exact Or.inr (hsub_Ut v hv)
  have hval_Ut : ∀ {u}, HtabValuesIn post u U → HtabValuesIn post u (U ++ [t]) :=
    fun hv i hi => hsub_Ut _ (hv i hi)
  obtain ⟨hndU, hTtU, hTpU, hwsU, hbsU, htsU, hgU, hbsNU, htsNU, hbalU, hboU, hrolesU⟩ := hTU
  have hTU' : TablesTyped post (U ++ [t]) := by
    refine ⟨List.nodup_append.2 ⟨hndU, List.nodup_singleton t, fun x hx y hy heq => by
        have := List.mem_singleton.1 hy; subst this; subst heq; exact ht_not_U hx⟩,
      ?_, ?_,
      fun k hk hnz => hroot_Ut (hwsU k hk hnz),
      fun k hk hnz => hroot_Ut (hbsU k hk hnz),
      fun k hk hnz => hroot_Ut (htsU k hk hnz),
      fun g hg => hroot_Ut (hgU g hg),
      ?_, ?_,
      fun ad had => ⟨hsub_Ut _ (hbalU ad had).1, hsub_Ut _ (hbalU ad had).2.1, (hbalU ad had).2.2⟩,
      hboU,
      ⟨fun a ha => ⟨hsub_Ut _ (hrolesU.1 a ha).1, (hrolesU.1 a ha).2⟩, hrolesU.2⟩⟩
    · intro u hu
      rcases List.mem_append.1 hu with huU | hut
      · exact hTtU u huU
      · simp only [List.mem_singleton] at hut; subst hut
        refine ⟨hwf_t, fun i hi => ⟨(hfp_t i hi).1, fun j hj => ?_⟩⟩
        apply (hfp_t i hi).2 j
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj)))
    · intro u hu v hv hne i hi j hj
      rcases List.mem_append.1 hu with huU | hut <;> rcases List.mem_append.1 hv with hvU | hvt
      · exact hTpU u huU v hvU hne i hi j hj
      · simp only [List.mem_singleton] at hvt; subst hvt
        exact R11Shards.Disj.symm ((hfp_t j hj).2 i (by
          unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨u, huU, hi⟩))))))
      · simp only [List.mem_singleton] at hut; subst hut
        apply (hfp_t i hi).2 j
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨v, hvU, hj⟩))))
      · simp only [List.mem_singleton] at hut hvt; subst hut; exact absurd hvt.symm hne
    · intro hnz hm
      rcases List.mem_append.1 hm with hmU | hmt
      · exact hval_Ut (hbsNU hnz hmU)
      · simp only [List.mem_singleton] at hmt
        rcases hbsU 32 (by simp [bsTableSlots]) hnz with h0 | hmU
        · exact absurd (h0.symm.trans hmt).symm ht_nz
        · exact absurd (hmt ▸ hmU) ht_not_U
    · intro hnz hm
      rcases List.mem_append.1 hm with hmU | hmt
      · exact hval_Ut (htsNU hnz hmU)
      · simp only [List.mem_singleton] at hmt
        rcases htsU 32 (by simp [tsTableSlots]) hnz with h0 | hmU
        · exact absurd (h0.symm.trans hmt).symm ht_nz
        · exact absurd (hmt ▸ hmU) ht_not_U
  have hJU' : JournalTyped post (U ++ [t]) :=
    ⟨hJU.1, hJU.2.1, hJU.2.2.1, fun i hi => hsub_Ut _ (hJU.2.2.2 i hi)⟩
  have hTrU' : TriesTypedWith post (U ++ [t]) Nd' := by
    refine ⟨hTrU.1, fun o ho => ⟨fun u hu i hi => ?_, (hTrU.2.1 o ho).2⟩, ?_⟩
    · rcases List.mem_append.1 hu with huU | hut
      · exact (hTrU.2.1 o ho).1 u huU i hi
      · simp only [List.mem_singleton] at hut; subst hut
        exact R11Shards.Disj.symm ((hfp_t i hi).2 o (by
          unfold worldOwned; exact List.mem_append.2 (Or.inr ho)))
    · intro hnz
      refine ⟨(hTrU.2.2 hnz).1, fun hm => ?_⟩
      rcases List.mem_append.1 hm with hmU | hmt
      · exact (hTrU.2.2 hnz).2 hmU
      · simp only [List.mem_singleton] at hmt
        rcases hwsU 32 (by simp [wsTableSlots]) hnz with h0 | hmU
        · exact absurd (h0.symm.trans hmt).symm ht_nz
        · exact absurd (hmt ▸ hmU) ht_not_U
  exact ⟨ht_not_U, ht_nz, ht_unass, hTU', hJU', hFU, hTrU'⟩

theorem worldTypedWith_erase_many {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) :
    ∀ L : List Nat,
      (∀ t ∈ L, ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t) →
      ∃ S0 : List Nat,
        (∀ u ∈ S0, u ∈ S) ∧
        (∀ u ∈ S, u ∉ L → u ∈ S0) ∧
        (∀ t ∈ L, t ∉ S0) ∧
        WorldTypedWith s S0 Nd
  | [], _ => ⟨S, fun _ h => h, fun _ h _ => h, fun _ h => False.elim (List.not_mem_nil h), hW⟩
  | t :: rest, hL => by
    obtain ⟨S1, hsub1, hin1, hnot1, hW1⟩ :=
      worldTypedWith_erase_many hW rest (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    have hW0 := worldTypedWith_erase_local hW1 (hL t (List.mem_cons_self ..))
    refine ⟨S1.erase t,
      fun u hu => hsub1 u (List.mem_of_mem_erase hu),
      fun u hu hnu => (List.Nodup.mem_erase_iff hW1.1.1).2
        ⟨fun heq => hnu (heq ▸ List.mem_cons_self ..),
         hin1 u hu (fun hm => hnu (List.mem_cons_of_mem _ hm))⟩,
      ?_, hW0⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hxr
    · exact List.Nodup.not_mem_erase hW1.1.1
    · exact fun hm => hnot1 x hxr (List.mem_of_mem_erase hm)

theorem adjoin_local_tables {F : Type} {post : PanSemStateFiniteExact 64 F}
    {U Nd' : List Nat} :
    ∀ L : List Nat, L.Nodup →
      WorldTypedWith post U Nd' →
      (∀ t ∈ L, HtabWF post t ∧
        (∀ i ∈ htabFootprint post t, Allocated post i ∧ ∀ o ∈ worldOwned post U Nd', Disj i o)) →
      (∀ t ∈ L, ∀ u ∈ L, t ≠ u → ∀ i ∈ htabFootprint post t, ∀ j ∈ htabFootprint post u, Disj i j) →
      (∀ t ∈ L, t ∉ U ∧ t ≠ 0 ∧ ∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ t) ∧
        WorldTypedWith post (U ++ L) Nd'
  | [], _, hWU, _, _ => ⟨fun _ h => False.elim (List.not_mem_nil h), by simpa using hWU⟩
  | t :: rest, hnd, hWU, htabs, hpw => by
    obtain ⟨ht_not_rest, hnd_rest⟩ := List.nodup_cons.1 hnd
    obtain ⟨hwf_t, hfp_t⟩ := htabs t (List.mem_cons_self ..)
    obtain ⟨ht_not_U, ht_nz, ht_unass, hWUt⟩ := adjoin_local_table hWU hwf_t hfp_t rfl
    have htabs_rest : ∀ u ∈ rest, HtabWF post u ∧
        (∀ i ∈ htabFootprint post u, Allocated post i ∧ ∀ o ∈ worldOwned post (U ++ [t]) Nd', Disj i o) := by
      intro u hu
      obtain ⟨hwf_u, hfp_u⟩ := htabs u (List.mem_cons_of_mem _ hu)
      have hne : u ≠ t := fun heq => ht_not_rest (heq ▸ hu)
      refine ⟨hwf_u, fun i hi => ⟨(hfp_u i hi).1, fun o ho => ?_⟩⟩
      unfold worldOwned at ho
      rcases List.mem_append.1 ho with h1 | hnd_o
      · rcases List.mem_append.1 h1 with htab | hfix
        · obtain ⟨v, hv, ho_fp⟩ := List.mem_flatMap.1 htab
          rcases List.mem_append.1 hv with hvU | hvt
          · apply (hfp_u i hi).2 o
            unfold worldOwned
            exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨v, hvU, ho_fp⟩))))
          · simp only [List.mem_singleton] at hvt; subst hvt
            exact hpw u (List.mem_cons_of_mem _ hu) v (List.mem_cons_self ..) hne i hi o ho_fp
        · apply (hfp_u i hi).2 o
          unfold worldOwned
          exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
      · apply (hfp_u i hi).2 o
        unfold worldOwned
        exact List.mem_append.2 (Or.inr hnd_o)
    obtain ⟨hrest_props, hW_all⟩ := adjoin_local_tables rest hnd_rest hWUt htabs_rest
      (fun u hu v hv => hpw u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv))
    have hU_assoc : (U ++ [t]) ++ rest = U ++ (t :: rest) := by simp
    rw [hU_assoc] at hW_all
    refine ⟨?_, hW_all⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hxr
    · exact ⟨ht_not_U, ht_nz, ht_unass⟩
    · obtain ⟨hnot_Ut, hnz_x, hunass_x⟩ := hrest_props x hxr
      exact ⟨fun hxU => hnot_Ut (List.mem_append.2 (Or.inl hxU)), hnz_x, hunass_x⟩

theorem worldTableRefs_mem_S {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hT : TablesTyped s S) (hJ : JournalTyped s S) {u : Nat}
    (hu : u ∈ worldTableRefs s S) (hnz : u ≠ 0) : u ∈ S := by
  obtain ⟨_, _, _, hws, hbs, hts, hg, hbsN, htsN, hbal, _, _⟩ := hT
  unfold worldTableRefs recordSlots at hu
  dsimp only at hu
  rcases List.mem_append.1 hu with h1 | hjr
  · rcases List.mem_append.1 h1 with h2 | hbal_m
    · rcases List.mem_append.1 h2 with h3 | hnts
      · rcases List.mem_append.1 h3 with h4 | hnbs
        · rcases List.mem_append.1 h4 with h5 | hgl
          · rcases List.mem_append.1 h5 with h6 | hts_m
            · rcases List.mem_append.1 h6 with hws_m | hbs_m
              · split at hws_m
                · cases hws_m
                · rename_i hgnz
                  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hws_m
                  exact (hws k hk hgnz).resolve_left hnz
              · split at hbs_m
                · cases hbs_m
                · rename_i hgnz
                  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hbs_m
                  exact (hbs k hk hgnz).resolve_left hnz
            · split at hts_m
              · cases hts_m
              · rename_i hgnz
                obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hts_m
                exact (hts k hk hgnz).resolve_left hnz
          · obtain ⟨g, hgm, rfl⟩ := List.mem_map.1 hgl
            exact (hg g hgm).resolve_left hnz
        · split at hnbs
          · rename_i hc
            obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hnbs
            exact hbsN hc.1 hc.2 i (List.mem_range.1 hi)
          · cases hnbs
      · split at hnts
        · rename_i hc
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hnts
          exact htsN hc.1 hc.2 i (List.mem_range.1 hi)
        · cases hnts
    · obtain ⟨ad, had, hm⟩ := List.mem_flatMap.1 hbal_m
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact (hbal ad had).1
      · exact (hbal ad had).2.1
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hjr
    exact hJ.2.2.2 k (List.mem_range.1 hk)

theorem frameObject_zero_or_allocated {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} {ec o : Ivl} (hA : ArenaOK s) (hFW : FrameWF s S ec)
    (ho : o ∈ frameObjects s ec) :
    o.2 = 0 ∨ Allocated s o ∨ Inside o scratchStart (globN s "frame_mem_ptr") := by
  obtain ⟨hscr, hmem_in, _, _, _, _, _, _, _, _, _, _, hlogs_in, _, hret_in, hll_ok, _⟩ := hFW
  unfold frameObjects at ho
  rcases List.mem_append.1 ho with ho7 | holog
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
    rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl (Or.inr (hscr (ec.1, 280) (by simp)).1))
    · exact Or.inr (Or.inl (Or.inr (hscr (ec.2, 104) (by simp)).1))
    · exact Or.inr (Or.inl (Or.inr (hscr (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)) (by simp)).1))
    · exact Or.inr (Or.inr hmem_in)
    · exact Or.inr (Or.inl (Or.inr (hscr (memW s (ec.1 + 88), 24) (by simp)).1))
    · exact Or.inr (Or.inl hlogs_in)
    · rcases hret_in with ⟨hz, _⟩ | ⟨h, _⟩
      · unfold frameRet; simp [hz]
      · exact Or.inr (Or.inl (Or.inl h))
  · unfold frameLogObjects at holog; dsimp only at holog
    obtain ⟨idx, hidx_mem, ho_own⟩ := List.mem_flatMap.1 holog
    rw [List.mem_range] at hidx_mem
    rcases hll_ok with hz | ⟨_, _, _, _, hent⟩
    · exfalso
      have hs0 := (hscr (memW s (ec.1 + 88), 24) (by simp)).1.1
      rw [hz] at hs0
      have hsc := hA.2.2.1; have hgap := hA.2.2.2.1
      have hss0 : 0 < scratchStart := by decide
      dsimp only at hs0; omega
    · have hle := (hent idx hidx_mem).2
      have ho_rec := (List.mem_filter.1 ho_own).1
      simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho_rec
      rcases ho_rec with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl (Or.inl hle.2.1))
      · exact Or.inr (Or.inl (Or.inl hle.2.2.2.2.1))
      · exact Or.inr (Or.inl (Or.inl hle.2.2.2.2.2.1))
      · exact Or.inr (Or.inl (Or.inl hle.2.2.2.2.2.2))

theorem triesTypedWith_inter {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd1 Nd2 : List Nat}
    (h1 : TriesTypedWith s S Nd1) (h2 : TriesTypedWith s S Nd2) :
    TriesTypedWith s S (Nd1.filter (fun n => decide (n ∈ Nd2))) := by
  set Nd := Nd1.filter (fun n => decide (n ∈ Nd2))
  have hsub1 : ∀ n ∈ Nd, n ∈ Nd1 := fun _ h => (List.mem_filter.1 h).1
  have hsub2 : ∀ n ∈ Nd, n ∈ Nd2 := fun _ h => of_decide_eq_true (List.mem_filter.1 h).2
  have hmem_iff : ∀ n, n ∈ Nd ↔ n ∈ Nd1 ∧ n ∈ Nd2 := fun n => by
    simp only [Nd, List.mem_filter, decide_eq_true_eq]
  have hroot_iff : ∀ r, RootIn Nd1 r → RootIn Nd2 r → RootIn Nd r := by
    intro r hr1 hr2
    rcases hr1 with rfl | hr1
    · exact Or.inl rfl
    · rcases hr2 with rfl | hr2
      · exact Or.inl rfl
      · exact Or.inr ((hmem_iff r).2 ⟨hr1, hr2⟩)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro n hn
    obtain ⟨k1, k2, k3, k4, k5_1, k6_1, k7_1, k8, k9, k10⟩ := h1.1.1 n (hsub1 n hn)
    obtain ⟨_, _, _, _, k5_2, k6_2, _, _, _, _⟩ := h2.1.1 n (hsub2 n hn)
    refine ⟨k1, k2, k3, k4, ?_, ?_, ?_, k8, k9, k10⟩
    · intro hm2; exact hroot_iff _ (k5_1 hm2) (k5_2 hm2)
    · intro hm3 i hi; exact hroot_iff _ (k6_1 hm3 i hi) (k6_2 hm3 i hi)
    · intro hm12
      rcases k7_1 hm12 with hz | ⟨hnib, hal, hin, hdj⟩
      · exact Or.inl hz
      · exact Or.inr ⟨hnib, hal, hin, fun m hm => hdj m (hsub1 m hm)⟩
  · intro n hn m hm hne
    exact h1.1.2 n (hsub1 n hn) m (hsub1 m hm) hne
  · intro o ho
    obtain ⟨n, hn, ho_n⟩ := List.mem_flatMap.1 ho
    exact h1.2.1 o (List.mem_flatMap.2 ⟨n, hsub1 n hn, ho_n⟩)
  · intro hws
    obtain ⟨hw1, hs1⟩ := h1.2.2 hws
    obtain ⟨hw2, hs2⟩ := h2.2.2 hws
    exact ⟨hroot_iff _ hw1 hw2, fun hm i hi => hroot_iff _ (hs1 hm i hi) (hs2 hm i hi)⟩

theorem avoidsTries_combine {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    {os1 os2 : List Ivl}
    (h1 : AvoidsTries s S os1) (h2 : AvoidsTries s S os2) :
    AvoidsTries s S (os1 ++ os2) := by
  obtain ⟨Nd1, hT1, hd1⟩ := h1
  obtain ⟨Nd2, hT2, hd2⟩ := h2
  refine ⟨Nd1.filter (fun n => decide (n ∈ Nd2)), triesTypedWith_inter hT1 hT2, ?_⟩
  intro o ho j hj
  obtain ⟨n, hn, hj_n⟩ := List.mem_flatMap.1 hj
  have hn1 : n ∈ Nd1 := (List.mem_filter.1 hn).1
  have hn2 : n ∈ Nd2 := of_decide_eq_true (List.mem_filter.1 hn).2
  rcases List.mem_append.1 ho with ho1 | ho2
  · exact hd1 o ho1 j (List.mem_flatMap.2 ⟨n, hn1, hj_n⟩)
  · exact hd2 o ho2 j (List.mem_flatMap.2 ⟨n, hn2, hj_n⟩)

theorem avoidsTries_list_combine {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (h0 : AvoidsTries s S []) :
    ∀ (xs : List Ivl), (∀ x ∈ xs, AvoidsTries s S [x]) → AvoidsTries s S xs
  | [], _ => h0
  | x :: xs, hx => by
    have hcomb := avoidsTries_combine (hx x (List.mem_cons_self ..))
      (avoidsTries_list_combine h0 xs (fun y hy => hx y (List.mem_cons_of_mem _ hy)))
    simpa using hcomb

theorem not_frame_role_of_world_or_journal {F : Type} {s : PanSemStateFiniteExact 64 F}
    {a : Nat × String} (ha : a ∈ worldRoleSlots s ++ journalRoleSlots s) :
    a.2 ∉ ["frame.del", "frame.addr", "frame.key"] := by
  intro hm
  rcases List.mem_append.1 ha with hw | hjr
  · unfold worldRoleSlots at hw
    obtain ⟨hw, _⟩ := List.mem_filter.1 hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with (((((hws | hbs) | hts) | hg) | hnbs) | hnts) | hbal
    · unfold recRoles at hws; split at hws
      · simp at hws
      · obtain ⟨k, hk, heq_k⟩ := List.mem_map.1 hws
        rw [← heq_k] at hm; simp at hk hm; rcases hk with rfl | rfl <;> simp at hm
    · unfold recRoles at hbs; split at hbs
      · simp at hbs
      · obtain ⟨k, hk, heq_k⟩ := List.mem_map.1 hbs
        rw [← heq_k] at hm; simp at hk hm
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hm
    · unfold recRoles at hts; split at hts
      · simp at hts
      · obtain ⟨k, hk, heq_k⟩ := List.mem_map.1 hts
        rw [← heq_k] at hm; simp at hk hm
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hm
    · rcases hg with rfl | rfl | rfl <;> simp at hm
    · unfold nestRoles at hnbs; split at hnbs
      · simp at hnbs
      · split at hnbs
        · simp at hnbs
        · obtain ⟨_, _, heq_v⟩ := List.mem_map.1 hnbs; rw [← heq_v] at hm; simp at hm
    · unfold nestRoles at hnts; split at hnts
      · simp at hnts
      · split at hnts
        · simp at hnts
        · obtain ⟨_, _, heq_v⟩ := List.mem_map.1 hnts; rw [← heq_v] at hm; simp at hm
    · obtain ⟨_, _, had_m⟩ := List.mem_flatMap.1 hbal
      simp at had_m; rcases had_m with rfl | rfl <;> simp at hm
  · unfold journalRoleSlots at hjr
    obtain ⟨_, _, hitem⟩ := List.mem_flatMap.1 hjr
    simp only [List.mem_cons] at hitem
    rcases hitem with rfl | hrest
    · dsimp only at hm; unfold journalRole at hm; split_ifs at hm <;> simp at hm
    · split_ifs at hrest
      · simp only [List.mem_singleton] at hrest; rw [hrest] at hm; simp at hm
      · simp at hrest

theorem frameRoleSlots_role_mem {F : Type} {s : PanSemStateFiniteExact 64 F} {ch : List Ivl}
    {b : Nat × String} (hb : b ∈ frameRoleSlots s ch) :
    b.2 ∈ ["frame.del", "frame.addr", "frame.key"] := by
  unfold frameRoleSlots at hb
  obtain ⟨_, _, hb3⟩ := List.mem_flatMap.1 hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb3
  rcases hb3 with rfl | rfl | rfl <;> simp

theorem create_finish_deposit_mul_no_wrap (n : BitVec 64)
    (hn : n.toNat ≤ 65536) :
    (n * 1530).toNat = n.toNat * 1530 := by
  rw [BitVec.toNat_mul]
  change n.toNat * 1530 % 2 ^ 64 = n.toNat * 1530
  exact Nat.mod_eq_of_lt (by omega)

theorem create_finish_alloc_add_no_wrap (n : BitVec 64)
    (hn : n.toNat ≤ 65536) :
    (n + 8).toNat = n.toNat + 8 := by
  apply BitVec.toNat_add_of_lt
  change n.toNat + 8 < 2 ^ 64
  omega

theorem create_finish_word_charge_no_wrap (w : BitVec 64)
    (hw : w.toNat ≤ 2048) :
    (6 * w).toNat = 6 * w.toNat := by
  rw [BitVec.toNat_mul]
  change 6 * w.toNat % 2 ^ 64 = 6 * w.toNat
  exact Nat.mod_eq_of_lt (by omega)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish
