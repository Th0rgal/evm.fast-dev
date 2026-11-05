import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.EkWarmStorageKey
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkGetAccount
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.AccountWk
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.StateGasHelpers

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

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

theorem ownedGrows_nodeExtents_of_fresh {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd Nd' : List Nat}
    (hold : ∀ n ∈ Nd, n ∈ Nd' ∧ nodeIvl post n = nodeIvl s n ∧ nodePath post n = nodePath s n)
    (hfresh : ∀ x ∈ Nd', x ∉ Nd →
      Inside (nodeIvl post x) (globN s "heap_ptr") (globN post "heap_ptr") ∧
      (nodePath post x = (0, 0) ∨
        Inside (nodePath post x) (globN s "heap_ptr") (globN post "heap_ptr"))) :
    OwnedGrows s post (nodeExtents s Nd) (nodeExtents post Nd') := by
  intro j hj
  simp only [nodeExtents, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with ⟨x, hx, rfl | rfl⟩
  · by_cases hxNd : x ∈ Nd
    · obtain ⟨_, hivl, _⟩ := hold x hxNd
      refine Or.inr (Or.inl ⟨nodeIvl s x, ?_, ?_⟩)
      · simp only [nodeExtents, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
        exact ⟨x, hxNd, Or.inl rfl⟩
      · rw [hivl]; exact ⟨le_rfl, le_rfl⟩
    · exact Or.inr (Or.inr (hfresh x hx hxNd).1)
  · by_cases hxNd : x ∈ Nd
    · obtain ⟨_, _, hpath⟩ := hold x hxNd
      refine Or.inr (Or.inl ⟨nodePath s x, ?_, ?_⟩)
      · simp only [nodeExtents, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
        exact ⟨x, hxNd, Or.inr rfl⟩
      · rw [hpath]; exact ⟨le_rfl, le_rfl⟩
    · rcases (hfresh x hx hxNd).2 with hz | hin
      · exact Or.inl hz
      · exact Or.inr (Or.inr hin)

theorem keyIn_of_fresh_nibbles {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {p len : Nat}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hNd : NodeHeap s Nd)
    (hkinds : ∀ n ∈ Nd, memW post n = memW s n)
    (hnib : NibblesOK post p len)
    (hfresh : Inside (p, len) (globN s "heap_ptr") (globN post "heap_ptr")) :
    KeyIn post Nd p len := by
  by_cases hz : len = 0
  · exact Or.inl hz
  · right
    have hlo : sourceBase ≤ globN s "heap_ptr" := hAs.1
    have hhi : globN post "heap_ptr" ≤ heapLimit := hAp.2.1
    refine ⟨hnib, Or.inl ⟨?_, hfresh.2⟩, ⟨?_, ?_⟩, ?_⟩
    · exact Nat.le_trans hlo hfresh.1
    · exact Nat.le_trans hlo hfresh.1
    · exact Nat.le_trans hfresh.2 hhi
    · intro n hn
      have hd := allocated_disj_fresh_extent hAs hAp hhp (hNd.1 n hn).2.1 hfresh
      have hivl : nodeIvl post n = nodeIvl s n := by
        simp only [nodeIvl, hkinds n hn]
      rw [hivl]
      unfold Disj at hd ⊢
      rcases hd with h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))

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

theorem frame_table_not_world_or_journal {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} {ch : List Ivl} {b : Nat × String}
    (hRoles : RolesOK s S (worldRoleSlots s ++ frameRoleSlots s ch) (journalRoleSlots s))
    (hb : b ∈ frameRoleSlots s ch) :
    ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ b.1 := by
  intro a ha heq
  have hr : a.2 = b.2 := by
    rcases List.mem_append.1 ha with hw | hj
    · exact ((List.pairwise_append.1 hRoles.2.1).2.2 a hw b hb heq).1
    · exact hRoles.2.2 a hj b (List.mem_append_left _ (List.mem_append_right _ hb)) heq
  exact not_frame_role_of_world_or_journal ha (hr ▸ frameRoleSlots_role_mem hb)

theorem evmStep_of_worldStepSc {F : Type}
    {B : R16WkAcctWs.BufList} {gw : List String} {keep : List (String × List Nat)}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hB : R16WkAcctWs.ValidBufList B)
    (hgw : R16WkAcctWs.SafeStepGlobals gw)
    (hAs : ArenaReady s)
    (hInv : ∃ S, InitECandidate.Solver.Wave8GuestInv.EvmInvAt s S)
    (hstep : R16WkAcctWs.WorldStepSc (R16WkAcctWs.bufRegions B) gw keep NoExtra s r post) :
    InitECandidate.Solver.Wave8GuestInv.EvmStep gw s post := by
  obtain ⟨S, hW_s, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj,
    hAT_fo, hMarks, hRoles, hGas⟩ := hInv
  have hAT_msgs : AvoidsTries s S ((evmChain s).map (fun ec => (memW s (ec.1 + 112), 176))) := by
    obtain ⟨Nd0, hTr0, _⟩ := hAT_fo
    refine avoidsTries_list_combine ⟨Nd0, hTr0, fun _ h => False.elim (List.not_mem_nil h)⟩ _ ?_
    intro x hx
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hx
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, c17⟩ := hFW_all ec hec
    exact c17.2.2.2.2.2
  obtain ⟨Nd_at, hTr_at, hAT_both⟩ := avoidsTries_combine hAT_fo hAT_msgs
  have hAT_at : ∀ o ∈ ((evmChain s).map (frameObjects s)).flatten,
      ∀ j ∈ nodeExtents s Nd_at, Disj o j :=
    fun o ho => hAT_both o (List.mem_append_left _ ho)
  have hAT_msg : ∀ ec ∈ evmChain s, ∀ j ∈ nodeExtents s Nd_at,
      Disj (memW s (ec.1 + 112), 176) j :=
    fun ec hec => hAT_both _ (List.mem_append_right _ (List.mem_map.2 ⟨ec, hec, rfl⟩))
  obtain ⟨⟨hAp, hhp, hG, _, hWS⟩, hsc⟩ := hstep
  have hag : AllocatorGrows s post := ⟨hhp, hsc⟩
  have hdom_eq : post.memaddrs = s.memaddrs := by rw [hAp.1.memaddrs, hAs.1.memaddrs]
  have hnot_gw : ∀ g : String,
      ofString g ∉ (["heap_ptr", "scratch_ptr", "journal_n"] : List String).map ofString →
      globN post g = globN s g := fun g hg =>
    InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup (hG (ofString g) (hgw.not_mem_map hg))
  have hev_eq : globN post "ev" = globN s "ev" := hnot_gw "ev" (by decide)
  have hcc_eq : globN post "cur_cont" = globN s "cur_cont" := hnot_gw "cur_cont" (by decide)
  have hfm_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := hnot_gw "frame_mem_ptr" (by decide)
  have hevm_empty_eq : globN post "evm_empty" = globN s "evm_empty" := hnot_gw "evm_empty" (by decide)
  have hvmsa_eq : globN post "vm_system_address" = globN s "vm_system_address" :=
    hnot_gw "vm_system_address" (by decide)
  set L : List Nat := S.filter (fun t => decide (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t))
  have hL_nd : L.Nodup := hW_s.1.1.filter _
  have hL_sub_S : ∀ t ∈ L, t ∈ S := fun _ ht => (List.mem_filter.1 ht).1
  have hL_local : ∀ t ∈ L, ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ t := by
    intro t ht; exact of_decide_eq_true (List.mem_filter.1 ht).2
  have hWT_at_s : WorldTypedWith s S Nd_at := ⟨hW_s.1, hW_s.2.1, hW_s.2.2.1, hTr_at⟩
  obtain ⟨S0, hS0_sub, hS0_in, hL_not_S0, hWT0⟩ := worldTypedWith_erase_many hWT_at_s L hL_local
  have hS_split : ∀ u ∈ S, u ∈ S0 ∨ u ∈ L := by
    intro u hu
    by_cases hloc : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ u
    · exact Or.inr (List.mem_filter.2 ⟨hu, decide_eq_true hloc⟩)
    · exact Or.inl (hS0_in u hu (fun hm => hloc (hL_local u hm)))
  obtain ⟨S0', Nd', hS0_sub', hWT0', hog0, hfr0, _⟩ :=
    hWS S0 Nd_at hWT0 (R16WkAcctWs.validBufList_disj hB hWT0)
  obtain ⟨S_full', _, hS_sub_full', hWT_full', _, _, _⟩ :=
    hWS S Nd_at hWT_at_s (R16WkAcctWs.validBufList_disj hB hWT_at_s)
  have hkeep_shape : ∀ j ∈ worldOwned s S0 Nd_at ++ R16WkAcctWs.bufRegions B s ++ [freeGap s],
      j = (0, 0) ∨ j.1 % 8 = 0 ∨ j.2 ≠ 0 := by
    intro j hj
    rcases List.mem_append.1 hj with hj12 | hfg
    · rcases List.mem_append.1 hj12 with hj_ow | hj_R
      · exact worldOwned_well_shaped hWT0 j hj_ow
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj_R
        unfold bufferRegion
        by_cases hz : globN s p.1 = 0
        · exact Or.inl (by simp [hz])
        · by_cases hp2 : p.2 = 0
          · right; left
            obtain ⟨sz, hgb, _⟩ := hB p hp
            have hfix : (globN s p.1, if globN s p.1 = 0 then 0 else sz) ∈ fixedObjects s := by
              unfold fixedObjects
              apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
              exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
            rcases hWT0.2.2.1.1 _ hfix with h0 | ⟨_, hw⟩
            · simp [hz] at h0; exact absurd h0 (globalBuffers_sz_pos (p.1, sz) hgb)
            · exact hw.1
          · exact Or.inr (Or.inr (by simp [hz, hp2]))
    · rw [List.mem_singleton] at hfg; subst hfg
      exact Or.inr (Or.inl hAs.2.2.2.2.2.2.2.1)
  have hdisj_bufs_of_fixed : ∀ b : Ivl, (∀ j ∈ fixedObjects s, Disj b j) →
      ∀ j ∈ R16WkAcctWs.bufRegions B s, Disj b j := by
    intro b hbfix j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
    obtain ⟨sz, hgb, _, hle⟩ := hB p hp
    have hfix : bufferRegion s (p.1, sz) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
    have hd := hbfix _ hfix
    by_cases hz : globN s p.1 = 0
    · exact Or.inr (Or.inl (by simp [bufferRegion, hz]))
    · simp only [bufferRegion, hz, ↓reduceIte] at hd ⊢
      rcases hd with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by dsimp only at h ⊢; omega))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (by dsimp only at h ⊢; omega)))
  have hL_surv : ∀ t ∈ L,
      HtabWF post t ∧ htabFootprint post t = htabFootprint s t ∧
      (∀ k, k < 11 → hdr post t k = hdr s t k) ∧
      (∀ i ∈ htabFootprint post t, Allocated post i ∧ ∀ o ∈ worldOwned post S0' Nd', Disj i o) := by
    intro t htL
    have htS := hL_sub_S t htL
    have hTt_t := hW_s.1.2.1 t htS
    have hwf_t := hTt_t.1
    have ht_ne_S0 : ∀ u ∈ S0, t ≠ u := fun u hu heq => hL_not_S0 t htL (heq ▸ hu)
    have hfp_surv : ∀ i ∈ htabFootprint s t,
        InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i ∧
        ∀ o ∈ worldOwned post S0' Nd', Disj i o := by
      intro i hi
      have hi_al := (hTt_t.2 i hi).1
      have hi_fix := (hTt_t.2 i hi).2
      have hi_ow0 : ∀ j ∈ worldOwned s S0 Nd_at, Disj i j := by
        intro j hj
        unfold worldOwned at hj
        rcases List.mem_append.1 hj with h1 | hnd
        · rcases List.mem_append.1 h1 with htab | hfix
          · obtain ⟨u, hu0, hj_fp⟩ := List.mem_flatMap.1 htab
            exact hW_s.1.2.2.1 t htS u (hS0_sub u hu0) (ht_ne_S0 u hu0) i hi j hj_fp
          · exact hi_fix j hfix
        · exact R11Shards.Disj.symm ((hTr_at.2.1 j hnd).1 t htS i hi)
      exact allocated_survives_world_frame hAs.2 hAp.2 hhp hi_al hi_ow0
        (hdisj_bufs_of_fixed i hi_fix) hkeep_shape hfr0 hog0
    have hhdr_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf_t.1 _ hhdr_fp).2.1
    have ht_hi : t + 88 ≤ 2 ^ 64 := by
      have h264 : heapEnd ≤ 2 ^ 64 := by decide
      have := (hwf_t.1 _ hhdr_fp).1.2; omega
    obtain ⟨hhdr_eq, hfp_eq⟩ :=
      InitECandidate.Solver.Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit ht8 ht_hi (hfp_surv _ hhdr_fp).1
    have hwf_post :=
      InitECandidate.Solver.Wave8Contracts.M08.htabWF_congr_unhit hAs.1 hAp.1 hwf_t (fun i hi => (hfp_surv i hi).1)
    refine ⟨hwf_post, hfp_eq, hhdr_eq, fun i hi => ?_⟩
    have hi_s : i ∈ htabFootprint s t := hfp_eq ▸ hi
    exact ⟨((hWT_full'.1.2.1 t (hS_sub_full' t htS)).2 i hi).1, (hfp_surv i hi_s).2⟩
  have hL_pw : ∀ t ∈ L, ∀ u ∈ L, t ≠ u →
      ∀ i ∈ htabFootprint post t, ∀ j ∈ htabFootprint post u, Disj i j := by
    intro t ht u hu hne i hi j hj
    rw [(hL_surv t ht).2.1] at hi
    rw [(hL_surv u hu).2.1] at hj
    exact hW_s.1.2.2.1 t (hL_sub_S t ht) u (hL_sub_S u hu) hne i hi j hj
  obtain ⟨hL_adj_props, hWT_post⟩ := adjoin_local_tables L hL_nd hWT0'
    (fun t ht => ⟨(hL_surv t ht).1, (hL_surv t ht).2.2.2⟩) hL_pw
  set S' := S0' ++ L
  have hS_sub_S' : ∀ u ∈ S, u ∈ S' := by
    intro u hu
    rcases hS_split u hu with hu0 | huL
    · exact List.mem_append_left _ (hS0_sub' u hu0)
    · exact List.mem_append_right _ huL
  have hsurv_full : ∀ o : Ivl,
      (o.2 = 0 ∨ Allocated s o ∨ Inside o scratchStart (globN s "frame_mem_ptr")) →
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj o i) →
      (∀ j ∈ fixedObjects s, Disj o j) →
      (∀ j ∈ nodeExtents s Nd_at, Disj o j) →
      (o.2 = 0 ∨ InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post o) ∧
      (∀ u ∈ S', ∀ i ∈ htabFootprint post u, Disj o i) ∧
      (∀ j ∈ fixedObjects post, Disj o j) ∧
      (∀ j ∈ nodeExtents post Nd', Disj o j) := by
    intro o ho_al ho_tab ho_fix ho_nd
    rcases ho_al with hz | harena
    · exact ⟨Or.inl hz, fun _ _ _ _ => Or.inl hz, fun _ _ => Or.inl hz, fun _ _ => Or.inl hz⟩
    · have ho_ow0 : ∀ j ∈ worldOwned s S0 Nd_at, Disj o j := by
        intro j hj
        unfold worldOwned at hj
        rcases List.mem_append.1 hj with h1 | hnd
        · rcases List.mem_append.1 h1 with htab | hfix
          · obtain ⟨u, hu0, hj_fp⟩ := List.mem_flatMap.1 htab
            exact ho_tab u (hS0_sub u hu0) j hj_fp
          · exact ho_fix j hfix
        · exact ho_nd j hnd
      obtain ⟨hu_o, ho_ow0'⟩ := arena_survives_world_frame hAs.2 hAp.2 hhp harena ho_ow0
        (hdisj_bufs_of_fixed o ho_fix) hkeep_shape hfr0 hog0
      refine ⟨Or.inr hu_o, ?_, ?_, ?_⟩
      · intro u hu i hi
        rcases List.mem_append.1 hu with hu0' | huL
        · apply ho_ow0' i
          unfold worldOwned
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, hu0', hi⟩))
        · rw [(hL_surv u huL).2.1] at hi
          exact ho_tab u (hL_sub_S u huL) i hi
      · intro j hj
        apply ho_ow0' j
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_right _ hj)
      · intro j hj
        apply ho_ow0' j
        unfold worldOwned
        exact List.mem_append_right _ hj
  have hfo_surv : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec,
      (o.2 = 0 ∨ InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post o) ∧
      (∀ u ∈ S', ∀ i ∈ htabFootprint post u, Disj o i) ∧
      (∀ j ∈ fixedObjects post, Disj o j) ∧
      (∀ j ∈ nodeExtents post Nd', Disj o j) := by
    intro ec hec o ho
    have ho_fl : o ∈ ((evmChain s).map (frameObjects s)).flatten :=
      List.mem_flatten.2 ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, ho⟩
    exact hsurv_full o (frameObject_zero_or_allocated hAs.2 (hFW_all ec hec) ho)
      (hFO_disj ec hec o ho).1 (hFO_disj ec hec o ho).2 (hAT_at o ho_fl)
  have hu_fo_m08 : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, o.2 ≠ 0 →
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post o := by
    intro ec hec o ho hnz
    exact ((hfo_surv ec hec o ho).1).resolve_left hnz
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb1, hb2, hb88, _⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hFW
    have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have he2_8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have he88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    refine ⟨fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo_m08 ec hec (ec.1, 280) (by simp [frameObjects]) (by simp)) (by omega) hb1 ⟨by omega, by omega⟩,
            fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo_m08 ec hec (ec.2, 104) (by simp [frameObjects]) (by simp)) (by omega) hb2 ⟨by omega, by omega⟩,
            fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo_m08 ec hec (memW s (ec.1 + 88), 24) (by simp [frameObjects]) (by simp)) (by omega) hb88 ⟨by omega, by omega⟩⟩
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq, _⟩ := hrec_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih]; intro ec' hec'; exact hsub ec' (by simp [evmChainFrom, hne16, hec'])
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain; rw [hev_eq, hcc_eq]
    exact hchain_aux _ _ _ (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hAs.2 hFW
    obtain ⟨hscr_ec, _, _, _, _, _, _, _, _, _, hll_cap1, hlen_le, _, hfl_w, _, hll_ok_ec, _⟩ := hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    set logs := memW s (ec.1 + 88)
    have hl0 : memW post logs = memW s logs := by simpa [logs] using h88_eq 0 (by omega) (by omega)
    have hl8 : memW post (logs + 8) = memW s (logs + 8) := h88_eq 8 (by omega) (by omega)
    have hl16 : memW post (logs + 16) = memW s (logs + 16) := h88_eq 16 (by omega) (by omega)
    have harr_eq : ∀ i, i < memW s (logs + 8) →
        memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i) := by
      intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hfl_nz : (frameLogs s ec).2 ≠ 0 := by
        unfold frameLogs; dsimp only [logs] at hi hlen_le ⊢; omega
      have hfl_b : memW s logs + 8 * memW s (logs + 16) ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · exact absurd h0 hfl_nz
        · simpa [frameLogs, logs] using hb
      have hfl_8 : (memW s logs) % 8 = 0 := hfl_w.1
      have hfl_u : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (memW s logs, 8 * memW s (logs + 16)) :=
        hu_fo_m08 ec hec (frameLogs s ec) hfl_in hfl_nz
      exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
        hfl_u (by omega) hfl_b ⟨by dsimp only; omega, by dsimp only; omega⟩
    have hlr_eq : ∀ i (hi : i < memW s (logs + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post (memW s (memW s logs + 8 * i) + off) = memW s (memW s (memW s logs + 8 * i) + off) := by
      intro i hi off hoff hoff8
      have hlr_in : (memW s (memW s logs + 8 * i), 40) ∈ frameObjects s ec := by
        unfold frameObjects; apply List.mem_append_right
        unfold frameLogObjects; dsimp only [logs]
        refine List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, ?_⟩
        unfold logOwnedIvls logRecordIvls
        exact List.mem_filter.2 ⟨by simp, by simp⟩
      have hlr_b : memW s (memW s logs + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s logs + 8 * i)) % 8 = 0 := by
        rcases hll_ok_ec with hz | ⟨_, _, _, _, hent⟩
        · exfalso
          have he88_in := (hscr_ec (logs, 24) (by simp [logs])).1.1
          change globN s "scratch_ptr" ≤ logs at he88_in
          rw [hz] at he88_in
          have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
          have hss0 : 0 < scratchStart := by decide
          omega
        · exact (hent i hi).2.1.1
      exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
        (hu_fo_m08 ec hec _ hlr_in (by simp)) (by omega) hlr_b ⟨by omega, by omega⟩
    refine ⟨?_, ?_⟩
    · unfold frameLogObjects; dsimp only
      rw [he_eq 88 (by omega) (by omega), hl8]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
      rw [hl0, harr_eq i hi]
      have r0 := hlr_eq i hi 0 (by omega) (by omega)
      have r8 := hlr_eq i hi 8 (by omega) (by omega)
      have r16 := hlr_eq i hi 16 (by omega) (by omega)
      have r24 := hlr_eq i hi 24 (by omega) (by omega)
      have r32 := hlr_eq i hi 32 (by omega) (by omega)
      simp only [Nat.add_zero] at r0
      unfold logOwnedIvls logRecordIvls
      rw [r0, r8, r16, r24, r32, hvmsa_eq]
    · rw [he_eq 88 (by omega) (by omega)]
      rcases hll_ok_ec with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hw_l,
          hag.allocated hal_l, by rw [hl8]; exact hlt28, by rw [hl8, hl16]; exact hle_cap, fun i hi => ?_⟩
        rw [hl8] at hi; rw [hl0]
        obtain ⟨hwa, hle⟩ := hent i hi
        have hwa_post : WordAt post (memW s logs + 8 * i) := by
          obtain ⟨_, hdom, _⟩ := hwa
          rcases hm : post.memory (BitVec.ofNat 64 (memW s logs + 8 * i)) with ⟨w⟩
          exact ⟨w, hdom_eq ▸ hdom, hm⟩
        refine ⟨hwa_post, ?_⟩
        rw [harr_eq i hi]
        have r0 := hlr_eq i hi 0 (by omega) (by omega)
        have r8 := hlr_eq i hi 8 (by omega) (by omega)
        have r16 := hlr_eq i hi 16 (by omega) (by omega)
        have r24 := hlr_eq i hi 24 (by omega) (by omega)
        have r32 := hlr_eq i hi 32 (by omega) (by omega)
        simp only [Nat.add_zero] at r0
        unfold LogEntryOK at hle ⊢
        rw [r0, r8, r16, r24, r32]
        exact ⟨InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hle.1,
          ⟨hle.2.1.1, le_trans hle.2.1.2 hhp⟩,
          hle.2.2.1, hle.2.2.2.1,
          ⟨hle.2.2.2.2.1.1, le_trans hle.2.2.2.2.1.2 hhp⟩,
          ⟨hle.2.2.2.2.2.1.1, le_trans hle.2.2.2.2.2.1.2 hhp⟩,
          ⟨hle.2.2.2.2.2.2.1, le_trans hle.2.2.2.2.2.2.2 hhp⟩⟩
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), hframeLogs_eq ec hec, hframeRet_eq ec hec,
        (hlogs_congr ec hec).1]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega), he_eq 88 (by omega) (by omega)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hfrs_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by omega), he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega)]
  have hfrs_in_L : ∀ b ∈ frameRoleSlots s (evmChain s), b.1 ∈ L := by
    intro b hb
    have hb_old : b ∈ (worldRoleSlots s ++ frameRoleSlots s (evmChain s)) ++ journalRoleSlots s :=
      List.mem_append_left _ (List.mem_append_right _ hb)
    exact List.mem_filter.2 ⟨(hRoles.1 b hb_old).1, decide_eq_true (frame_table_not_world_or_journal hRoles hb)⟩
  have hRoles_post : RolesOK post S'
      (worldRoleSlots post ++ frameRoleSlots post (evmChain s))
      (journalRoleSlots post) := by
    obtain ⟨hr1_0', hr2_0', hr3_0'⟩ := hWT0'.1.2.2.2.2.2.2.2.2.2.2.2
    rw [hfrs_eq]
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      rw [List.append_assoc] at ha
      rcases List.mem_append.1 ha with hw | hrest
      · have h := hr1_0' a (List.mem_append_left _ hw)
        exact ⟨List.mem_append_left _ h.1, h.2⟩
      · rcases List.mem_append.1 hrest with hfr_a | hjr
        · have haL := hfrs_in_L a hfr_a
          have h_old := hRoles.1 a (List.mem_append_left _ (List.mem_append_right _ hfr_a))
          exact ⟨List.mem_append_right _ haL, ((hL_surv a.1 haL).2.2.1 0 (by omega)).trans h_old.2⟩
        · have h := hr1_0' a (List.mem_append_right _ hjr)
          exact ⟨List.mem_append_left _ h.1, h.2⟩
    · rw [List.pairwise_append]
      refine ⟨hr2_0', (List.pairwise_append.1 hRoles.2.1).2.1, ?_⟩
      intro a haw b hfr_b heq
      have hbL := hfrs_in_L b hfr_b
      exact absurd heq ((hL_adj_props b.1 hbL).2.2 a (List.mem_append_left _ haw))
    · intro a hjr b hb heq
      rw [List.append_assoc] at hb
      rcases List.mem_append.1 hb with hw | hrest
      · exact hr3_0' a hjr b (List.mem_append_left _ hw) heq
      · rcases List.mem_append.1 hrest with hfr_b | hjr_b
        · have hbL := hfrs_in_L b hfr_b
          exact absurd heq ((hL_adj_props b.1 hbL).2.2 a (List.mem_append_right _ hjr))
        · exact hr3_0' a hjr b (List.mem_append_right _ hjr_b) heq
  have hMarks_post : MarksOK post S' (evmChain s) := by
    intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega) (by omega)
    have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega) (by omega)
    have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by omega)
    have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega)
    have hM := hMarks i hi
    dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    set m := memW s (((evmChain s)[i]'(by omega)).2 + 48)
    have hgrow_in_mark : ∀ o : Ivl,
        (o = (0, 0) ∨ (∃ j ∈ worldOwned s S0 Nd_at, Inside o j.1 (j.1 + j.2)) ∨
          Inside o (globN s "heap_ptr") (globN post "heap_ptr")) →
        o.2 = 0 ∨ Inside o sourceBase heapLimit ∨ Inside o m scratchEnd := by
      intro o hog_o
      rcases hog_o with rfl | ⟨j, hj, hin⟩ | hfresh
      · exact Or.inl rfl
      · unfold worldOwned at hj
        rcases List.mem_append.1 hj with h1 | hnd
        · rcases List.mem_append.1 h1 with htab | hfix
          · obtain ⟨u, hu0, hj_fp⟩ := List.mem_flatMap.1 htab
            have huS := hS0_sub u hu0
            rcases m8 u huS with ⟨htake, _⟩ | hloc
            · exfalso
              obtain ⟨ec_u, hec_take, hu_eq136⟩ := List.mem_map.1 htake
              have hu_frs : (u, "frame.del") ∈ frameRoleSlots s (evmChain s) := by
                unfold frameRoleSlots; rw [← hu_eq136]
                exact List.mem_flatMap.2 ⟨ec_u, List.mem_of_mem_take hec_take, by simp⟩
              exact hL_not_S0 u (hfrs_in_L (u, "frame.del") hu_frs) hu0
            · rcases hloc j hj_fp with hh | hm
              · exact Or.inr (Or.inl ⟨le_trans hh.1 hin.1, le_trans hin.2 hh.2⟩)
              · exact Or.inr (Or.inr ⟨le_trans hm.1 hin.1, le_trans hin.2 hm.2⟩)
          · rcases m9 j hfix with hj0 | hh | hm
            · left; unfold Inside at hin; omega
            · exact Or.inr (Or.inl ⟨le_trans hh.1 hin.1, le_trans hin.2 hh.2⟩)
            · exact Or.inr (Or.inr ⟨le_trans hm.1 hin.1, le_trans hin.2 hm.2⟩)
        · unfold nodeExtents at hnd
          obtain ⟨n, hn, hj_n⟩ := List.mem_flatMap.1 hnd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hj_n
          rcases hj_n with rfl | rfl
          · have hni := (hTr_at.1.1 n hn).2.2.1
            exact Or.inr (Or.inl ⟨le_trans hni.1 hin.1, le_trans hin.2 hni.2⟩)
          · unfold nodePath at hin
            split_ifs at hin with hc
            · rcases (hTr_at.1.1 n hn).2.2.2.2.2.2.1 hc.1 with h0 | ⟨_, _, hk_in, _⟩
              · exact absurd h0 hc.2
              · exact Or.inr (Or.inl ⟨le_trans hk_in.1 hin.1, le_trans hin.2 hk_in.2⟩)
            · left; dsimp only [Inside] at hin; omega
      · exact Or.inr (Or.inl ⟨le_trans hAs.2.1 hfresh.1, le_trans hfresh.2 hAp.2.2.1⟩)
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, ?_⟩
    · intro j hj hij
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem,
          (hrec_eq _ hj_mem).1 112 (by omega) (by omega)]
      exact m5 j hj hij
    · intro t ht
      rcases List.mem_append.1 ht with ht0' | htL
      · right
        intro o ho
        have ho_ow : o ∈ worldOwned post S0' Nd' := by
          unfold worldOwned
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, ht0', ho⟩))
        rcases hgrow_in_mark o (hog0 o ho_ow) with ho0 | hmark
        · exfalso
          have hwf_t := (hWT0'.1.2.1 t ht0').1
          have hkl1 := hwf_t.2.2.1
          have hstr := hwf_t.2.2.2.2.1
          have hncap := hwf_t.2.2.2.2.2.1
          simp only [htabFootprint, List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl | rfl
          · dsimp only at ho0; omega
          · dsimp only at ho0
            rcases Nat.eq_zero_or_pos (hdr post t 10 + 1) with hz1 | hp1
            · omega
            · have : hdr post t 1 = 0 := by
                rcases Nat.mul_eq_zero.1 ho0 with h1 | h2
                · omega
                · exact h2
              omega
          · dsimp only at ho0; omega
          · dsimp only at ho0; omega
        · exact hmark
      · rw [(hL_surv t htL).2.1]
        rcases m8 t (hL_sub_S t htL) with ⟨htake, hu_not_wref, hu_frames⟩ | hloc
        · left
          refine ⟨htake, ?_, ?_⟩
          · intro hw_post
            have ht_nz : t ≠ 0 := (hL_adj_props t htL).2.1
            have hw_S0' : t ∈ worldTableRefs post S0' := by
              unfold worldTableRefs at hw_post ⊢
              dsimp only at hw_post ⊢
              have hnest_eq : ∀ g : String,
                  (g = "bs" ∨ g = "ts") →
                  (if globN post g ≠ 0 ∧ memW post (globN post g + 32) ∈ S' then htabValues post (memW post (globN post g + 32)) else []) =
                  (if globN post g ≠ 0 ∧ memW post (globN post g + 32) ∈ S0' then htabValues post (memW post (globN post g + 32)) else []) := by
                intro g hg_or
                by_cases hgnz : globN post g = 0
                · simp [hgnz]
                · have h32_root : RootIn S0' (memW post (globN post g + 32)) := by
                    rcases hg_or with rfl | rfl
                    · exact hWT0'.1.2.2.2.2.1 32 (by simp [bsTableSlots]) hgnz
                    · exact hWT0'.1.2.2.2.2.2.1 32 (by simp [tsTableSlots]) hgnz
                  have hiff : memW post (globN post g + 32) ∈ S' ↔ memW post (globN post g + 32) ∈ S0' := by
                    constructor
                    · intro hm'
                      rcases h32_root with h0 | hm0'
                      · exact absurd (h0 ▸ hm') (zero_not_mem_S hWT_post.1)
                      · exact hm0'
                    · exact List.mem_append_left _
                  simp only [hiff]
              rw [hnest_eq "bs" (Or.inl rfl), hnest_eq "ts" (Or.inr rfl)] at hw_post
              exact hw_post
            exact (hL_adj_props t htL).1 (worldTableRefs_mem_S hWT0'.1 hWT0'.2.1 hw_S0' ht_nz)
          · intro j hj k hk hmem_eq
            have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
            have hk_le : k + 8 ≤ 280 ∧ k % 8 = 0 := by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
              rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
            rw [(hrec_eq _ hj_mem).1 k hk_le.1 hk_le.2] at hmem_eq
            exact hu_frames j hj k hk hmem_eq
        · exact Or.inr hloc
    · intro o ho
      have ho_ow : o ∈ worldOwned post S0' Nd' := by
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_right _ ho)
      exact hgrow_in_mark o (hog0 o ho_ow)
  have hmap_gas : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
      ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
    apply List.map_congr_left; intro ec hec
    rw [(hrec_eq ec hec).1 64 (by decide) (by decide), (hrec_eq ec hec).1 192 (by decide) (by decide)]
  have hW_post : WorldTyped post S' := ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd', hWT_post.2.2.2⟩
  refine ⟨⟨hAp, S', hW_post, ?_⟩, hhp, hG, hchain_eq⟩
  dsimp only; rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, hmap_fo_eq ▸ hFO_pw, ?_, ?_, hMarks_post, hRoles_post, hmap_gas ▸ hGas⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
    have hlo_ok := (hlogs_congr ec hec).2
    have hmsg_ok : MsgOwned post S' (memW post (ec.1 + 112)) := by
      rw [he_eq 112 (by omega) (by omega)]
      obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, _⟩ := c17
      have hmsg_surv := hsurv_full (memW s (ec.1 + 112), 176)
        (Or.inr (Or.inl hal_m)) hdt hdf (hAT_msg ec hec)
      refine ⟨hag.allocated hal_m,
        InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hw_m,
        hmsg_surv.2.1, hmsg_surv.2.2.1, ?_, Nd', hWT_post.2.2.2, ?_⟩
      · rw [hchain_eq]
        intro ec' hec' o ho
        rw [hframeObjects_eq ec' hec'] at ho
        exact hdfo ec' hec' o ho
      · intro o ho j hj
        rw [List.mem_singleton] at ho; subst ho
        exact hmsg_surv.2.2.2 j hj
    unfold FrameWF; dsimp only
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), he_eq 24 (by omega) (by omega),
        he_eq 40 (by omega) (by omega), he_eq 16 (by omega) (by omega),
        he_eq 32 (by omega) (by omega), he_eq 136 (by omega) (by omega),
        he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
        hframeLogs_eq ec hec, he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega),
        hframeRet_eq ec hec, hfm_eq, hevm_empty_eq]
    rw [he_eq 88 (by omega) (by omega)] at hlo_ok
    refine ⟨?_, c2, InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 c3,
      c4, c5, c6, c7, hS_sub_S' _ c8, hS_sub_S' _ c9, hS_sub_S' _ c10, c11, c12,
      ?_, InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 c14, ?_, hlo_ok, hmsg_ok⟩
    · intro i hi
      obtain ⟨hin, hw⟩ := c1 i hi
      exact ⟨⟨le_trans hsc hin.1, hin.2⟩,
        InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hw⟩
    · rcases c13 with h | h
      · exact Or.inl ⟨h.1, le_trans h.2 hhp⟩
      · exact Or.inr ⟨le_trans hsc h.1, h.2⟩
    · rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨⟨hin.1, le_trans hin.2 hhp⟩,
          InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hw⟩
  · intro ec hec
    have hec_mem := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [(hrec_eq ec hec_mem).1 16 (by omega) (by omega), (hrec_eq ec hec_mem).1 232 (by omega) (by omega)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [(hrec_eq _ hi0).2.1 80 (by decide) (by decide),
        (hrec_eq _ hi0).2.1 72 (by decide) (by decide),
        (hrec_eq _ hi1).1 40 (by decide) (by decide)]
    exact hRW i hi
  · intro ec hec o ho
    rw [hframeObjects_eq ec hec] at ho
    exact ⟨(hfo_surv ec hec o ho).2.1, (hfo_surv ec hec o ho).2.2.1⟩
  · rw [hmap_fo_eq]
    refine ⟨Nd', hWT_post.2.2.2, fun o ho j hj => ?_⟩
    obtain ⟨_, hfo_m, ho_fo⟩ := List.mem_flatten.1 ho
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hfo_m
    exact (hfo_surv ec hec o ho_fo).2.2.2 j hj

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

theorem nonValueSlot_ts48 {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + (48 : BitVec 64).toNat) ≠ 0) :
    let t0 := memW s (globN s "ts" + (48 : BitVec 64).toNat)
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) := by
  have hc : (48 : BitVec 64).toNat = 48 := by decide
  rw [hc] at ht0_nz ⊢
  have ht0_S : memW s (globN s "ts" + 48) ∈ S := by
    rcases hT.2.2.2.2.2.1 48 (by simp [tsTableSlots]) hts_nz with h0 | hm
    · exact absurd h0 ht0_nz
    · exact hm
  have ht0_wrs : (memW s (globN s "ts" + 48), "ts+48") ∈ worldRoleSlots s := by
    apply R16WkAcctWs.mem_worldRoleSlots_recRole s "ts" 48 "ts+48" hts_nz ht0_nz
    apply List.mem_append.2; right
    unfold recRoles; simp [hts_nz]
  exact R16WkAcctWs.nonValueSlot_of_wrs s S _ "ts+48" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem journalRole_ts48 {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + 48) ≠ 0) :
    journalRole s (memW s (globN s "ts" + 48)) = "ts+48" := by
  have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
  have ht48_wrs : (memW s (globN s "ts" + 48), "ts+48") ∈ worldRoleSlots s := by
    apply R16WkAcctWs.mem_worldRoleSlots_recRole s "ts" 48 "ts+48" hts_nz ht0_nz
    apply List.mem_append.2; right
    unfold recRoles; simp [hts_nz]
  have hne16 : memW s (globN s "ts" + 48) ≠ memW s (globN s "ts" + 16) := by
    intro heq
    have h16_nz : memW s (globN s "ts" + 16) ≠ 0 := by rw [← heq]; exact ht0_nz
    have ht16_wrs : (memW s (globN s "ts" + 16), "ts+16") ∈ worldRoleSlots s := by
      apply R16WkAcctWs.mem_worldRoleSlots_recRole s "ts" 16 "ts+16" hts_nz h16_nz
      apply List.mem_append.2; right
      unfold recRoles; simp [hts_nz]
    exact R16WkAcctWs.slot_ne_of_diff_nonshared_role hroles ht48_wrs ht16_wrs (by decide) heq
  have hne32 : memW s (globN s "ts" + 48) ≠ memW s (globN s "ts" + 32) := by
    have hc : (48 : BitVec 64).toNat = 48 := by decide
    have hnvs := nonValueSlot_ts48 s S hT hts_nz (by rw [hc]; exact ht0_nz)
    dsimp only at hnvs
    rw [hc] at hnvs
    exact (hnvs.2.2.1 hts_nz).symm
  unfold journalRole
  rw [if_neg (by rintro ⟨_, h⟩; exact hne16 h), if_neg (by rintro ⟨_, h⟩; exact hne32 h),
      if_pos ⟨hts_nz, rfl⟩]

section SetCode

open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

private theorem call0_or_resumes_sc {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fname : MlS) (args : List (ExpHOL 64))
    (hcr : ContOrRes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none ∨
    Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 := by
  rcases hcr with h | h | h | hr
  · exact Or.inl h
  · exfalso
    rw [evaluateHOLFiniteState_call] at h
    revert h; split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
    rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨rc, _⟩
    rcases rc with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
  · exfalso
    rw [evaluateHOLFiniteState_call] at h
    revert h; split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
    rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨rc, _⟩
    rcases rc with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
  · exact Or.inr hr

private theorem call0_none_locals_sc {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fn : MlS) (args : List (ExpHOL 64))
    (hnone : (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 = none) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_call] at hnone ⊢
  unfold evalListHOLFinite at hnone ⊢
  rcases h1 : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [h1] at hnone
  · simp only [h1] at hnone ⊢
    rcases h2 : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn vs with _ | ⟨b, c, r⟩
    · simp [h2] at hnone
    · simp only [h2] at hnone ⊢
      split at hnone
      · simp at hnone
      · rename_i hcz; rw [if_neg hcz]
        rcases h3 : evaluateHOLFiniteState (callEntryStateHOLFinite s c) b with ⟨rb, sb⟩
        simp only [h3] at hnone ⊢
        rcases rb with _ | rb'
        · simp at hnone
        · cases rb' with
          | returned rv =>
            dsimp only at hnone ⊢
            split at hnone
            · rename_i hsh; rw [if_pos hsh]
            · simp at hnone
          | _ => simp at hnone

private theorem worldEff_call0_funByteEff_sc {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    {fname : MlS} {argR : List (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → List Ivl}
    (hf : Fast_C08WkShard03.FunByteEff fname argR)
    (args : List (ExpHOL 64)) (Sub : List Ivl)
    (hsub_args : ∀ vals,
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals →
      ∀ i ∈ argR vals cur.globals, 0 < i.2 → ∃ j ∈ Sub, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hsub_world : ∀ iv ∈ Sub, 0 < iv.2 →
      (∃ j ∈ Rl, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
      (∃ gs ∈ B, (bufferRegion s gs).1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
      (globN s "frame_mem_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit))
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).2 Rl B gw :=
  h.of_byteEff
    (Fast_C08WkShard03.call0_byteEff hf cur args Sub h.code h.arena.1 hsub_args hnt (call0_or_resumes_sc cur fname args hcr))
    hsub_world

private theorem worldEff_call0_memcpy_sc {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (dstExp srcExp nExp : ExpHOL 64)
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy")
      [dstExp, srcExp, nExp])).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy")
      [dstExp, srcExp, nExp])).1 = none ∨
      Resumes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy")
      [dstExp, srcExp, nExp])).1)
    (hin : ∀ (dstw srcw nw : BitVec 64),
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp =
        some (.val (.word dstw)) →
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) srcExp =
        some (.val (.word srcw)) →
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) nExp =
        some (.val (.word nw)) →
      0 < nw.toNat →
      (∃ j ∈ Rl, j.1 ≤ dstw.toNat ∧ dstw.toNat + nw.toNat ≤ j.1 + j.2) ∨
      (∃ gs ∈ B, (bufferRegion s gs).1 ≤ dstw.toNat ∧
        dstw.toNat + nw.toNat ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
      (globN s "frame_mem_ptr" ≤ dstw.toNat ∧ dstw.toNat + nw.toNat ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ dstw.toNat ∧ dstw.toNat + nw.toNat ≤ heapLimit)) :
    WorldEff s (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy")
      [dstExp, srcExp, nExp])).2 Rl B gw := by
  by_cases hgood : ∃ (dw sw nw : BitVec 64),
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp =
        some (.val (.word dw)) ∧
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) srcExp =
        some (.val (.word sw)) ∧
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) nExp =
        some (.val (.word nw))
  · obtain ⟨dw, sw, nw, hd, hsw, hn⟩ := hgood
    have hargs_good : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a))
        [dstExp, srcExp, nExp] = some [.val (.word dw), .val (.word sw), .val (.word nw)] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact, hd, hsw, hn]
    have hb := Fast_C08WkShard03.call0_byteEff Fast_C08WkShard03.funByteEff_memcpy cur
      [dstExp, srcExp, nExp] [(dw.toNat, nw.toNat)] h.code h.arena.1
      (fun vals hargs i hi _ => by
        rw [hargs_good] at hargs
        injection hargs with hargs_eq
        subst hargs_eq
        simp only [List.mem_singleton, Fast_C08WkShard03.valWordNat] at hi
        subst hi
        exact ⟨(dw.toNat, nw.toNat), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
      hnt hor
    exact h.of_byteEff hb (fun iv hiv hpos => by
      simp only [List.mem_singleton] at hiv
      subst hiv
      exact hin dw sw nw hd hsw hn hpos)
  · have hpost_eq : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "memcpy")
        [dstExp, srcExp, nExp])).2 = cur := by
      rw [evaluateHOLFiniteState_call]
      rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a))
          [dstExp, srcExp, nExp] with _ | vals
      · rfl
      · dsimp only
        rcases hl : lookupCodeHOLFinite cur.code.lookup (ofString "memcpy") vals with _ | ⟨b', c', r'⟩
        · rfl
        · exfalso
          have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "memcpy") vals = some (b', c', r') := by
            rwa [← h.code]
          have hinst := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "memcpy")
            _ _ b' _ r' vals c' lookup_memcpy_r16 hl'
          have hret := lookupCodeHOLFinite_installed_return cur (ofString "memcpy")
            _ _ _ _ r' vals c' (by rw [h.code]; exact lookup_memcpy_r16) hl
          subst hinst hret
          obtain ⟨dw, sw, nw, hvals, _, _, _⟩ := Fast_C08WkShard03.lookupCode_three_words
            (by decide) (by decide) (by decide) lookup_memcpy_r16 hl'
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          rcases hd : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp with _ | vd
          · simp [hd] at hargs
          · rcases hs : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) srcExp with _ | vs
            · simp [hd, hs] at hargs
            · rcases hn : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) nExp with _ | vn
              · simp [hd, hs, hn] at hargs
              · rw [hd, hs, hn] at hargs
                injection hargs with hargs_eq
                have hvals2 := hargs_eq.trans hvals
                injection hvals2 with h1 ht1; injection ht1 with h2 ht2; injection ht2 with h3 _
                subst h1 h2 h3
                exact hgood ⟨dw, sw, nw, hd, hs, hn⟩
    rwa [hpost_eq]

private theorem callee_param_two_sc {F : Type} (state : PanSemStateFiniteExact 64 F) (fname p1 p2 : MlS)
    (s1 s2 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2)], body, ret))
    (e1 e2 : ExpHOL 64)
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1 v2,
      evalAt state e1 = some v1 ∧ evalAt state e2 = some v2 ∧
      callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
  · simp [he1] at hargs
  · rcases he2 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e2 with _ | v2
    · simp [he1, he2] at hargs
    · simp only [he1, he2, Option.some.injEq] at hargs
      subst hargs
      unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
      split at hlook
      · cases hlook
      · rename_i exactBody exactLocals exactShape raw
        have heq := Option.some.inj hlook
        rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
        rcases Prod.mk.inj hrest with ⟨rfl, _⟩
        unfold lookupCodeHOLExact at raw
        rw [hl] at raw
        dsimp only at raw
        split at raw
        · rename_i hcond
          have rawEq := Option.some.inj raw
          rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
          rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
          subst hloc
          obtain ⟨hnd, -, -⟩ := hcond
          have hne : p1 ≠ p2 := by simp [List.nodup_cons] at hnd; exact hnd
          refine ⟨v1, v2, he1, he2, ?_, ?_⟩
          · simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE, hne]
          · simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE]
        · cases raw

private theorem trap_with_call_no_none_resumes_sc {F : Type}
    (state : PanSemStateFiniteExact 64 F) (codeVal : BitVec 64)
    (hcode : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal])).1 ≠ none ∧
    ¬ Resumes (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal])).1 := by
  have hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.const codeVal] = some [.val (.word codeVal)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlk := pan_one_word_lookup state.code.lookup (ofString "trap_with") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_trap_with) codeVal
    (by rw [hcode]; exact lookup_trap_with_r16)
  rw [evaluateHOLFiniteState_call, hargs]; dsimp only; rw [hlk]; dsimp only
  split
  · exact ⟨by simp, by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h⟩
  · have hout := evaluate_trap_with_body_outcomes
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
    rcases hrun : evaluateHOLFiniteState
        (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
        (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
    rw [hrun] at hout
    cases res with
    | none => exact absurd rfl hout.1
    | some r =>
      cases r with
      | returned v => exact absurd rfl (hout.2.1 v)
      | exception eid v =>
        refine ⟨by simp, ?_⟩
        rintro (⟨_, h⟩ | ⟨_, _, h, hne⟩)
        · simp at h
        · injection h with h'; injection h' with he hw; subst he hw
          exact hout.2.2 eid v hne rfl
      | _ => exact ⟨by simp, by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h⟩

private def journalAppendTailProgSc (trapCode : BitVec 64) (e16 : ExpHOL 64) (tail : ProgHOL 64) : ProgHOL 64 :=
  .seq
    (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
      (.call (some (none, none)) (ofString "trap_with") [.const trapCode])
      .skip)
    (.dec (ofString "klen") .one (.load .one (.op .add [.var .local (ofString "t"), .const 0#64]))
      (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")]
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")])
          (.dec (ofString "r") .one
            (.op .add [.var .global (ofString "journal"),
              .panop .mul [.var .global (ofString "journal_n"), .const 32#64]])
            (.seq
              (.store (.var .local (ofString "r")) (.var .local (ofString "t")))
              (.seq
                (.store (.op .add [.var .local (ofString "r"), .const 8#64]) (.var .local (ofString "kc")))
                (.seq
                  (.store (.op .add [.var .local (ofString "r"), .const 16#64]) e16)
                  (.seq
                    (.store (.op .add [.var .local (ofString "r"), .const 24#64])
                      (.rfield 1 (.var .local (ofString "old"))))
                    (.seq
                      (.assign .global (ofString "journal_n")
                        (.op .add [.var .global (ofString "journal_n"), .const 1#64]))
                      tail)))))))))

private theorem dec_ret_inv_sc {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {nm : MlS} {init : ExpHOL 64} {bd : ProgHOL 64} {rv : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.dec nm .one init bd) = (some (.returned rv), post)) :
    ∃ w : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init =
        some (.val (.word w)) ∧
      ∃ mid, evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) s) bd = (some (.returned rv), mid) ∧
        post = { mid with locals := HolFiniteMapExact.resVarEq mid.locals (nm, s.locals.lookup nm) } := by
  rw [evaluateHOLFiniteState_dec_total] at h; dsimp only at h
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init with _ | val
  · rw [hev] at h; simp at h
  · rw [hev] at h; dsimp only at h
    rcases val with ⟨⟨w⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at h; done)
    have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh] at h
    rcases hb : evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) s) bd with ⟨rb, mid⟩
    rw [hb] at h
    cases rb with
    | none => simp at h
    | some r0 =>
      cases r0 with
      | returned u =>
        dsimp only at h
        injection h with hr hso; injection hr with hr'; injection hr' with hu; subst hu
        exact ⟨w, rfl, mid, hb, hso.symm⟩
      | _ => simp at h

private theorem seq_store_ret_inv_sc {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {b : ProgHOL 64} {rv : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.seq (.store dst val) b) = (some (.returned rv), post)) :
    ∃ mid, evaluateHOLFiniteState s (.store dst val) = (none, mid) ∧
      evaluateHOLFiniteState mid b = (some (.returned rv), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases ha : evaluateHOLFiniteState s (.store dst val) with ⟨ra, mid⟩
  rw [ha] at h
  cases ra with
  | none => exact ⟨mid, rfl, h⟩
  | some _ =>
    have hcf := (PanRunBounded.evaluate_store_control_frame s dst val).1
    rw [ha] at hcf; rcases hcf with h0 | h0 <;> cases h0; simp at h

private theorem seq_assign_ret_inv_sc {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {vk : VarKind} {nm : MlS} {val : ExpHOL 64} {b : ProgHOL 64} {rv : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.seq (.assign vk nm val) b) = (some (.returned rv), post)) :
    ∃ mid, evaluateHOLFiniteState s (.assign vk nm val) = (none, mid) ∧
      evaluateHOLFiniteState mid b = (some (.returned rv), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases ha : evaluateHOLFiniteState s (.assign vk nm val) with ⟨ra, mid⟩
  rw [ha] at h
  cases ra with
  | none => exact ⟨mid, rfl, h⟩
  | some _ =>
    exfalso
    rw [evaluateHOLFiniteState_assign] at ha
    split at ha
    · injection ha with hr _; injection hr with hr'; subst hr'; simp at h
    · split at ha
      · simp at ha
      · injection ha with hr _; injection hr with hr'; subst hr'; simp at h

private theorem seq_call0_ret_inv_sc {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {fn : MlS} {args : List (ExpHOL 64)} {b : ProgHOL 64} {rv : ValueHOL 64}
    (h : evaluateHOLFiniteState s (.seq (.call (some (none, none)) fn args) b) = (some (.returned rv), post)) :
    ∃ mid, evaluateHOLFiniteState s (.call (some (none, none)) fn args) = (none, mid) ∧
      evaluateHOLFiniteState mid b = (some (.returned rv), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases ha : evaluateHOLFiniteState s (.call (some (none, none)) fn args) with ⟨ra, mid⟩
  rw [ha] at h
  cases ra with
  | none => exact ⟨mid, rfl, h⟩
  | some _ =>
    exfalso
    rw [evaluateHOLFiniteState_call] at ha
    rcases hev : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
    · rw [hev] at ha; dsimp only at ha
      injection ha with hr _; injection hr with hr'; subst hr'; simp at h
    · rw [hev] at ha; dsimp only at ha
      rcases hlk : lookupCodeHOLFinite s.code.lookup fn vals with _ | ⟨body0, cal0, ret0⟩
      · rw [hlk] at ha; dsimp only at ha
        injection ha with hr _; injection hr with hr'; subst hr'; simp at h
      · rw [hlk] at ha; dsimp only at ha
        split at ha
        · injection ha with hr _; injection hr with hr'; subst hr'; simp at h
        · rcases hrb : evaluateHOLFiniteState (callEntryStateHOLFinite s cal0) body0 with ⟨rb, mb⟩
          rw [hrb] at ha
          cases rb with
          | none =>
            dsimp only at ha
            injection ha with hr _; injection hr with hr'; subst hr'; simp at h
          | some rb0 =>
            cases rb0 <;> simp only at ha
            case returned =>
              split at ha
              · simp at ha
              · injection ha with hr _; injection hr with hr'; subst hr'; simp at h
            all_goals (injection ha with hr _; injection hr with hr'; subst hr'; simp at h)

private theorem store_word_none_inv_sc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {dstExp valExp : ExpHOL 64}
    (hrun : evaluateHOLFiniteState s (.store dstExp valExp) = (none, post))
    (hval_one : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w)) :
    ∃ (dw vw : BitVec 64),
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word dw)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
        some (.val (.word vw)) ∧
      s.memaddrs dw ∧
      post = { s with memory := fun a => if a = dw then .word vw else s.memory a } := by
  rw [evaluateHOLFiniteState_store] at hrun
  rcases hx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp with _ | dv
  · rw [hx] at hrun; simp at hrun
  · rw [hx] at hrun
    rcases dv with ⟨⟨dw⟩⟩ | _ | _ <;> try (simp at hrun; done)
    rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp with _ | val
    · rw [hv] at hrun; simp at hrun
    · obtain ⟨vw, rfl⟩ := hval_one val hv
      rw [hv] at hrun
      simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hrun
      by_cases hdom : s.memaddrs dw
      · simp only [hdom, ↓reduceIte] at hrun
        injection hrun with _ hp
        exact ⟨dw, vw, rfl, rfl, hdom, hp.symm⟩
      · simp [hdom] at hrun

private theorem journal_append_block_step_sc {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F)
    (trapCode : BitVec 64) (e16 : ExpHOL 64) (tw kw f0 f1 w16 : BitVec 64)
    (hW0 : WorldOK s0)
    (heff0 : WorldEff s0 cur [] [] ["heap_ptr"])
    (hg_all_cur : ∀ k : MlS, cur.globals.lookup k = s0.globals.lookup k)
    (hloc_t : cur.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hloc_k : cur.locals.lookup (ofString "key") = some (.val (.word kw)))
    (hloc_old : cur.locals.lookup (ofString "old") = some (.rStruct [.val (.word f0), .val (.word f1)]))
    (he16 : ∀ st : PanSemStateFiniteExact 64 F,
      st.locals.lookup (ofString "old") = some (.rStruct [.val (.word f0), .val (.word f1)]) →
      @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) e16 =
        some (.val (.word w16)))
    (htw_ok : ∀ S, TablesTyped s0 S → tw.toNat ∈ S ∧
      let jrNew :=
        (tw.toNat, journalRole s0 tw.toNat) ::
          (if w16.toNat ≠ 0 ∧ journalRole s0 tw.toNat = "ts+32" then
            [(f1.toNat, "ts.inner")] else [])
      ∀ p ∈ jrNew, p ∈ worldRoleSlots s0)
    {tail : ProgHOL 64} {rv : ValueHOL 64} {out : PanSemStateFiniteExact 64 F}
    (hflow : evaluateHOLFiniteState cur (journalAppendTailProgSc trapCode e16 tail) =
      (some (.returned rv), out)) :
    ∃ mid tailPost,
      WorldStepSc (bufRegions []) ["heap_ptr", "journal_n"] stdKeep NoExtra s0 none mid ∧
      mid.locals.lookup (ofString "t") = some (.val (.word tw)) ∧
      mid.locals.lookup (ofString "key") = some (.val (.word kw)) ∧
      mid.locals.lookup (ofString "value") = cur.locals.lookup (ofString "value") ∧
      evaluateHOLFiniteState mid tail = (some (.returned rv), tailPost) ∧
      out = { tailPost with locals := out.locals } := by
  have hAs0 := hW0.1
  have hcode : cur.code = originalRuntimeCode := heff0.code
  obtain ⟨_, S0, hWT0⟩ := hW0
  have hW0_full : WorldOK s0 := ⟨hAs0, S0, hWT0⟩
  have hJ0 := hWT0.2.1
  obtain ⟨jnw, hjn_lk0⟩ := hAs0.2.2.2.2.2.2.2.2.2 "journal_n" (by decide)
  obtain ⟨jcw, hjc_lk0⟩ := hAs0.2.2.2.2.2.2.2.2.2 "journal_cap" (by decide)
  obtain ⟨jw, hj_lk0⟩ := hAs0.2.2.2.2.2.2.2.2.2 "journal" (by decide)
  have hjn_cur : cur.globals.lookup (ofString "journal_n") = some (.val (.word jnw)) := by
    rw [hg_all_cur]; exact hjn_lk0
  have hjc_cur : cur.globals.lookup (ofString "journal_cap") = some (.val (.word jcw)) := by
    rw [hg_all_cur]; exact hjc_lk0
  have hjn_nat : globN s0 "journal_n" = jnw.toNat := by unfold GlobalWord at hjn_lk0; simp [globN, hjn_lk0]
  have hjc_nat : globN s0 "journal_cap" = jcw.toNat := by unfold GlobalWord at hjc_lk0; simp [globN, hjc_lk0]
  have hj_nat : globN s0 "journal" = jw.toNat := by unfold GlobalWord at hj_lk0; simp [globN, hj_lk0]
  unfold journalAppendTailProgSc at hflow
  rw [evaluateHOLFiniteState_seq_line780] at hflow
  have hjn_lt_jc : jnw.toNat < jcw.toNat := by
    by_contra hge
    have hnl : Compiler.Encoders.Asm.wordCmpHOL .notLower jnw jcw = true := by
      simp only [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
      have hnotlt : ¬ jnw.toNat < jcw.toNat := by omega
      simp [hnotlt]
    have hev_cmp1 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
        (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap"))) =
        some (.val (.word 1#64)) := by
      simp [evalHOLExact, toExact, hjn_cur, hjc_cur, hnl]
    have hite_tr : evaluateHOLFiniteState cur
        (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
          (.call (some (none, none)) (ofString "trap_with") [.const trapCode]) .skip) =
        evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "trap_with") [.const trapCode]) := by
      rw [evaluateHOLFiniteState_ite, hev_cmp1]
      simp [show (1#64 : BitVec 64) ≠ 0 by decide]
    rw [hite_tr] at hflow
    obtain ⟨_, htr_none, _⟩ := seq_call0_ret_inv_sc (by rw [evaluateHOLFiniteState_seq_line780]; exact hflow)
    have ⟨hno_none, _⟩ := trap_with_call_no_none_resumes_sc cur trapCode hcode
    exact hno_none (congrArg Prod.fst htr_none)
  have hite_ok : evaluateHOLFiniteState cur
      (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
        (.call (some (none, none)) (ofString "trap_with") [.const trapCode]) .skip) = (none, cur) := by
    have hnl : Compiler.Encoders.Asm.wordCmpHOL .notLower jnw jcw = false := by
      simp only [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
      simp [hjn_lt_jc]
    have hev_cmp0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
        (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap"))) =
        some (.val (.word 0#64)) := by
      simp [evalHOLExact, toExact, hjn_cur, hjc_cur, hnl]
    rw [evaluateHOLFiniteState_ite, hev_cmp0]
    simp [evaluateHOLFiniteState_skip]
  rw [hite_ok] at hflow; dsimp only at hflow
  have hjn_lt0 : globN s0 "journal_n" < globN s0 "journal_cap" := by omega
  have hjcap_nz : globN s0 "journal_cap" ≠ 0 := by omega
  rcases hJ0.2.2.1 with hjc0 | ⟨hal_jr0, hw_jr0⟩
  · exact absurd hjc0 hjcap_nz
  have hj_hi0 := (ivl_allocated_bound hAs0.2 hal_jr0).2
  set jrec : Ivl := (globN s0 "journal" + 32 * jnw.toNat, 32)
  have hjrec_hi : jrec.1 + 32 ≤ heapEnd := by
    have hhl_he : heapLimit ≤ heapEnd := by decide
    have hse_he : scratchEnd ≤ heapEnd := by decide
    rcases hal_jr0 with ⟨_, hhi⟩ | ⟨_, hhi⟩ <;> (have := hAs0.2.2.1; have := hAs0.2.2.2.2.1; dsimp [jrec] at *; omega)
  obtain ⟨klw, hkl_ev, m_kl, hflow_kl, hout_eq1⟩ := dec_ret_inv_sc hflow
  set s_kl := setVarHOLFinite (ofString "klen") (.val (.word klw)) cur
  have heff_kl : WorldEff s0 s_kl [jrec] [] ["heap_ptr"] :=
    (heff0.mono (by intro _ h; cases h) (by intro _ h; cases h) (by intro _ h; exact h)).locals_clock _ _
  change evaluateHOLFiniteState s_kl _ = (some (.returned rv), m_kl) at hflow_kl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hflow_kl
  have hkl_loc : s_kl.locals.lookup (ofString "klen") = some (.val (.word klw)) := by
    simp [s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hargs_al : evalListHOLFinite s_kl (h := fun a => Classical.propDecidable (s_kl.memaddrs a))
      [.var .local (ofString "klen")] = some [.val (.word klw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hkl_loc]
  have hlk_al := pan_one_word_lookup s_kl.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) klw (by rw [heff_kl.code]; exact lookup_alloc_r16)
  rw [hargs_al] at hflow_kl; dsimp only at hflow_kl; rw [hlk_al] at hflow_kl; dsimp only at hflow_kl
  by_cases hcz_kl : s_kl.clock = 0
  · simp [hcz_kl] at hflow_kl
  rw [if_neg hcz_kl] at hflow_kl
  obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, s_kl.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
    globalWord_of_globN_pos s_kl "heap_ptr"
      (by have := heff_kl.arena.2.1; have hsb : sourceBase = 2701131776 := rfl; omega)
  let ent_al := callEntryStateHOLFinite s_kl (HolFiniteMapExact.empty.update (ofString "n", .val (.word klw)))
  rcases hrun_al : evaluateHOLFiniteState ent_al (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res_al, pa_al⟩
  dsimp only [ent_al] at hrun_al
  rw [hrun_al] at hflow_kl
  have hres_al : Resumes res_al := by
    cases res_al with
    | none => simp at hflow_kl
    | some cra =>
      cases cra with
      | returned _ => exact Or.inl ⟨_, rfl⟩
      | exception eid _ =>
        dsimp only at hflow_kl; injection hflow_kl with hr_eq _; cases hr_eq
      | _ => simp at hflow_kl
  have hal_spec := InitECandidate.Solver.Wave8GuestInv.R13.alloc_body_resumes ent_al pw heff_kl.code hpw_lk
    (by dsimp only [ent_al]; rw [hrun_al]; exact hres_al)
  dsimp only [ent_al] at hal_spec; rw [hrun_al] at hal_spec
  obtain ⟨klw', hklw'_lk, hrv_al, hcmp1, hcmp2, hpa_al⟩ := hal_spec
  have hklw_eq : klw = klw' := by
    have : ent_al.locals.lookup (ofString "n") = some (.val (.word klw)) := by
      simp [ent_al, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rw [this] at hklw'_lk; injection hklw'_lk with h'; injection h' with h'; injection h'
  subst hklw_eq
  dsimp only at hrv_al hpa_al; subst hrv_al
  have hsh_pw_al : (shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one &&
      shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hflow_kl
  rw [if_pos hsh_pw_al] at hflow_kl
  set s_kc := setVarHOLFinite (ofString "kc") (.val (.word pw)) { pa_al with locals := s_kl.locals }
  have hs_kc_next : s_kc = { s_kl with
      globals := s_kl.globals.update (ofString "heap_ptr", .val (.word ((pw + (klw + 7)) &&& ((0 : BitVec 64) - 8)))),
      locals := s_kc.locals, clock := s_kc.clock } := by
    dsimp only [s_kc, setVarHOLFinite]; rw [hpa_al]; rfl
  obtain ⟨heff_kc, _, _, _, hpw_lo_s0, hpw_add, hhp_kc_lim, _⟩ :=
    R16Shards.worldEff_alloc_step heff_kl (by simp) hpw_lk hcmp1 hcmp2 hs_kc_next
  rcases hcont_kc : evaluateHOLFiniteState s_kc
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")])
        (.dec (ofString "r") .one
          (.op .add [.var .global (ofString "journal"),
            .panop .mul [.var .global (ofString "journal_n"), .const 32#64]])
          (.seq
            (.store (.var .local (ofString "r")) (.var .local (ofString "t")))
            (.seq
              (.store (.op .add [.var .local (ofString "r"), .const 8#64]) (.var .local (ofString "kc")))
              (.seq
                (.store (.op .add [.var .local (ofString "r"), .const 16#64]) e16)
                (.seq
                  (.store (.op .add [.var .local (ofString "r"), .const 24#64])
                    (.rfield 1 (.var .local (ofString "old"))))
                  (.seq
                    (.assign .global (ofString "journal_n")
                      (.op .add [.var .global (ofString "journal_n"), .const 1#64]))
                    tail))))))) with ⟨rkc, m_kc⟩
  rw [hcont_kc] at hflow_kl
  dsimp only at hflow_kl
  have hrv_kc_eq : rkc = some (.returned rv) := (Prod.mk.inj hflow_kl).1
  have hm_kl_eq : m_kl = { m_kc with locals := (HolFiniteMapExact.resVarEq m_kc.locals
      (ofString "kc", s_kl.locals.lookup (ofString "kc"))) } := ((Prod.mk.inj hflow_kl).2).symm
  cases rkc with
  | none => simp at hrv_kc_eq
  | some cr_kc =>
    cases cr_kc with
    | returned rv_kc =>
      injection hrv_kc_eq with hrv_kc'; injection hrv_kc' with hrv_kc''; subst hrv_kc''
      obtain ⟨s_mc, hmc, hcont_mc⟩ := seq_call0_ret_inv_sc hcont_kc
      have hkc_loc : s_kc.locals.lookup (ofString "kc") = some (.val (.word pw)) := by
        simp [s_kc, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hk_loc_kc : s_kc.locals.lookup (ofString "key") = some (.val (.word kw)) := by
        simp [s_kc, s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hloc_k,
          show ofString "kc" ≠ ofString "key" by decide, show ofString "klen" ≠ ofString "key" by decide]
      have hkl_loc_kc : s_kc.locals.lookup (ofString "klen") = some (.val (.word klw)) := by
        simp [s_kc, s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "kc" ≠ ofString "klen" by decide]
      have heff_mc : WorldEff s0 s_mc [jrec] [] ["heap_ptr"] := by
        have hm := worldEff_call0_memcpy_sc heff_kc
          (.var .local (ofString "kc")) (.var .local (ofString "key")) (.var .local (ofString "klen"))
          (by rw [hmc]; simp) (by rw [hmc]; exact Or.inl rfl)
          (fun dw sw nw hd _ hn _ => by
            simp [evalHOLExact, toExact, hkc_loc] at hd; subst hd
            simp [evalHOLExact, toExact, hkl_loc_kc] at hn; subst hn
            exact Or.inr (Or.inr (Or.inr ⟨hpw_lo_s0, by omega⟩)))
        rw [hmc] at hm; exact hm
      have hmc_g : s_mc.globals = s_kc.globals := by
        have hargs_mc : evalListHOLFinite s_kc (h := fun a => Classical.propDecidable (s_kc.memaddrs a))
            [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")] =
            some [.val (.word pw), .val (.word kw), .val (.word klw)] := by
          rw [evalListHOLFinite_eq_toExact]
          simp [evalListHOLExact, evalHOLExact, toExact, hkc_loc, hk_loc_kc, hkl_loc_kc]
        have hb_mc := Fast_C08WkShard03.call0_byteEff Fast_C08WkShard03.funByteEff_memcpy s_kc
          [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")]
          [(pw.toNat, klw.toNat)] heff_kc.code heff_kc.arena.1
          (fun vals hvs i hi _ => by
            rw [hargs_mc] at hvs; injection hvs with hvs_eq; subst hvs_eq
            simp only [List.mem_singleton, Fast_C08WkShard03.valWordNat] at hi
            subst hi
            exact ⟨(pw.toNat, klw.toNat), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
          (by rw [hmc]; simp) (by rw [hmc]; exact Or.inl rfl)
        rw [hmc] at hb_mc
        exact hb_mc.globals
      have hmc_loc : s_mc.locals = s_kc.locals := by
        have hk := fun k => evaluate_avoidsLocal_flowing k
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "kc"), .var .local (ofString "key"), .var .local (ofString "klen")])
          rfl s_kc (by rw [hmc]; exact Or.inl rfl)
        apply HolFiniteMapExact.ext; funext k; simpa [hmc] using hk k
      obtain ⟨rw, hr_ev, m_r, hflow_r, hm_kc_eq⟩ := dec_ret_inv_sc hcont_mc
      have hs_mc_g_no_hp : ∀ k : MlS, k ≠ ofString "heap_ptr" → s_mc.globals.lookup k = s0.globals.lookup k := by
        intro k hk
        rw [hmc_g, hs_kc_next]
        simp [s_kl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk.symm, hg_all_cur]
      have hrw_eq : rw = jw + jnw * 32#64 := by
        have hj_mc : s_mc.globals.lookup (ofString "journal") = some (.val (.word jw)) := by
          rw [hs_mc_g_no_hp _ (by decide)]; exact hj_lk0
        have hjn_mc : s_mc.globals.lookup (ofString "journal_n") = some (.val (.word jnw)) := by
          rw [hs_mc_g_no_hp _ (by decide)]; exact hjn_lk0
        simp only [evalHOLExact, evalListHOLExact, toExact, hj_mc, hjn_mc, List.all, List.map,
          Option.map, Bool.and_self, ↓reduceIte, List.foldr, valueIsWord, valueWord,
          wordOpHOL, wordOp, panOpHOL] at hr_ev
        have hz : jnw * 32#64 + (0 : BitVec 64) = jnw * 32#64 := BitVec.add_zero _
        rw [hz] at hr_ev
        injection hr_ev with hr'; injection hr' with hr'; injection hr' with hr'; exact hr'.symm
      have hrw_nat : rw.toNat = globN s0 "journal" + 32 * jnw.toNat := by
        subst hrw_eq
        have hmul : (jnw * 32#64).toNat = 32 * jnw.toNat := by
          rw [BitVec.toNat_mul, show (32#64 : BitVec 64).toNat = 32 from rfl]
          change (jnw.toNat * 32) % 2 ^ 64 = 32 * jnw.toNat
          rw [Nat.mul_comm, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
        rw [BitVec.toNat_add, hj_nat, hmul, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
      set s_r := setVarHOLFinite (ofString "r") (.val (.word rw)) s_mc
      have heff_r : WorldEff s0 s_r [jrec] [] ["heap_ptr"] := heff_mc.locals_clock _ _
      have hr_loc : s_r.locals.lookup (ofString "r") = some (.val (.word rw)) := by
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have ht_loc_r : s_r.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmc_loc, s_kc, s_kl, hloc_t,
          show ofString "r" ≠ ofString "t" by decide,
          show ofString "kc" ≠ ofString "t" by decide,
          show ofString "klen" ≠ ofString "t" by decide]
      have hkc_loc_r : s_r.locals.lookup (ofString "kc") = some (.val (.word pw)) := by
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmc_loc, hkc_loc,
          show ofString "r" ≠ ofString "kc" by decide]
      have hold_loc_r : s_r.locals.lookup (ofString "old") = some (.rStruct [.val (.word f0), .val (.word f1)]) := by
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmc_loc, s_kc, s_kl, hloc_old,
          show ofString "r" ≠ ofString "old" by decide,
          show ofString "kc" ≠ ofString "old" by decide,
          show ofString "klen" ≠ ofString "old" by decide]
      obtain ⟨s_st0, hst0, hflow_st0⟩ := seq_store_ret_inv_sc hflow_r
      obtain ⟨dw0, vw0, hdw0, hvw0, _, hs_st0_eq⟩ := store_word_none_inv_sc hst0
        (fun v hv => by simp [evalHOLExact, toExact, ht_loc_r] at hv; exact ⟨tw, hv.symm⟩)
      have hdw0_eq : dw0 = rw := by simp [evalHOLExact, toExact, hr_loc] at hdw0; exact hdw0.symm
      have hvw0_eq : vw0 = tw := by simp [evalHOLExact, toExact, ht_loc_r] at hvw0; exact hvw0.symm
      rw [hdw0_eq, hvw0_eq] at hs_st0_eq
      have heff_st0 : WorldEff s0 s_st0 [jrec] [] ["heap_ptr"] := by
        have hw := R16Shards.worldEff_store_word heff_r (.var .local (ofString "r")) (.var .local (ofString "t"))
          (fun v hv => by simp [evalHOLExact, toExact, ht_loc_r] at hv; exact ⟨tw, hv.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, toExact, hr_loc] at hx; subst hx
            exact Or.inl ⟨jrec, List.mem_singleton.2 rfl, by dsimp [jrec]; omega, by dsimp [jrec]; omega⟩)
        rw [hst0] at hw; exact hw
      obtain ⟨s_st8, hst8, hflow_st8⟩ := seq_store_ret_inv_sc hflow_st0
      have hst0_loc : s_st0.locals = s_r.locals := by rw [hs_st0_eq]
      obtain ⟨dw8, vw8, hdw8, hvw8, _, hs_st8_eq⟩ := store_word_none_inv_sc hst8
        (fun v hv => by simp [evalHOLExact, toExact, hst0_loc, hkc_loc_r] at hv; exact ⟨pw, hv.symm⟩)
      have hdw8_eq : dw8 = rw + 8#64 := by
        simp [evalHOLExact, evalListHOLExact, toExact, hst0_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hdw8
        exact hdw8.symm
      have hvw8_eq : vw8 = pw := by simp [evalHOLExact, toExact, hst0_loc, hkc_loc_r] at hvw8; exact hvw8.symm
      rw [hdw8_eq, hvw8_eq] at hs_st8_eq
      have hrw8_nat : (rw + 8#64).toNat = rw.toNat + 8 := by
        apply BitVec.toNat_add_of_lt; change rw.toNat + 8 < 2 ^ 64; dsimp at hj_hi0; omega
      have heff_st8 : WorldEff s0 s_st8 [jrec] [] ["heap_ptr"] := by
        have hw := R16Shards.worldEff_store_word heff_st0
          (.op .add [.var .local (ofString "r"), .const 8#64]) (.var .local (ofString "kc"))
          (fun v hv => by simp [evalHOLExact, toExact, hst0_loc, hkc_loc_r] at hv; exact ⟨pw, hv.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, toExact, hst0_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx
            exact Or.inl ⟨jrec, List.mem_singleton.2 rfl, by dsimp [jrec]; omega, by dsimp [jrec]; omega⟩)
        rw [hst8] at hw; exact hw
      obtain ⟨s_st16, hst16, hflow_st16⟩ := seq_store_ret_inv_sc hflow_st8
      have hst8_loc : s_st8.locals = s_r.locals := by rw [hs_st8_eq, hst0_loc]
      have he16_st8 := he16 s_st8 (by rw [hst8_loc]; exact hold_loc_r)
      obtain ⟨dw16, vw16, hdw16, hvw16, _, hs_st16_eq⟩ := store_word_none_inv_sc hst16
        (fun v hv => by rw [he16_st8] at hv; injection hv with hv'; exact ⟨w16, hv'.symm⟩)
      have hdw16_eq : dw16 = rw + 16#64 := by
        simp [evalHOLExact, evalListHOLExact, toExact, hst8_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hdw16
        exact hdw16.symm
      have hvw16_eq : vw16 = w16 := by
        rw [he16_st8] at hvw16; injection hvw16 with h'; injection h' with h'; injection h' with h'; exact h'.symm
      rw [hdw16_eq, hvw16_eq] at hs_st16_eq
      have hrw16_nat : (rw + 16#64).toNat = rw.toNat + 16 := by
        apply BitVec.toNat_add_of_lt; change rw.toNat + 16 < 2 ^ 64; dsimp at hj_hi0; omega
      have heff_st16 : WorldEff s0 s_st16 [jrec] [] ["heap_ptr"] := by
        have hw := R16Shards.worldEff_store_word heff_st8
          (.op .add [.var .local (ofString "r"), .const 16#64]) e16
          (fun v hv => by rw [he16_st8] at hv; injection hv with hv'; exact ⟨w16, hv'.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, toExact, hst8_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx
            exact Or.inl ⟨jrec, List.mem_singleton.2 rfl, by dsimp [jrec]; omega, by dsimp [jrec]; omega⟩)
        rw [hst16] at hw; exact hw
      obtain ⟨s_st24, hst24, hflow_st24⟩ := seq_store_ret_inv_sc hflow_st16
      have hst16_loc : s_st16.locals = s_r.locals := by rw [hs_st16_eq, hst8_loc]
      have he24 : @evalHOLExact 64 F _ s_st16.toExact (fun a => Classical.propDecidable (s_st16.memaddrs a))
          (.rfield 1 (.var .local (ofString "old"))) = some (.val (.word f1)) := by
        simp [evalHOLExact, toExact, hst16_loc, hold_loc_r]
      obtain ⟨dw24, vw24, hdw24, hvw24, _, hs_st24_eq⟩ := store_word_none_inv_sc hst24
        (fun v hv => by rw [he24] at hv; injection hv with hv'; exact ⟨f1, hv'.symm⟩)
      have hdw24_eq : dw24 = rw + 24#64 := by
        simp [evalHOLExact, evalListHOLExact, toExact, hst16_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hdw24
        exact hdw24.symm
      have hvw24_eq : vw24 = f1 := by
        rw [he24] at hvw24; injection hvw24 with h'; injection h' with h'; injection h' with h'; exact h'.symm
      rw [hdw24_eq, hvw24_eq] at hs_st24_eq
      have hrw24_nat : (rw + 24#64).toNat = rw.toNat + 24 := by
        apply BitVec.toNat_add_of_lt; change rw.toNat + 24 < 2 ^ 64; dsimp at hj_hi0; omega
      have heff_st24 : WorldEff s0 s_st24 [jrec] [] ["heap_ptr"] := by
        have hw := R16Shards.worldEff_store_word heff_st16
          (.op .add [.var .local (ofString "r"), .const 24#64]) (.rfield 1 (.var .local (ofString "old")))
          (fun v hv => by rw [he24] at hv; injection hv with hv'; exact ⟨f1, hv'.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, toExact, hst16_loc, hr_loc, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx
            exact Or.inl ⟨jrec, List.mem_singleton.2 rfl, by dsimp [jrec]; omega, by dsimp [jrec]; omega⟩)
        rw [hst24] at hw; exact hw
      obtain ⟨mid, hass_step, htail_run⟩ := seq_assign_ret_inv_sc hflow_st24
      have hst24_g : s_st24.globals = s_mc.globals := by
        rw [hs_st24_eq, hs_st16_eq, hs_st8_eq, hs_st0_eq]; rfl
      have hjn_st24 : s_st24.globals.lookup (ofString "journal_n") = some (.val (.word jnw)) := by
        rw [hst24_g, hs_mc_g_no_hp _ (by decide)]; exact hjn_lk0
      have hass : evaluateHOLFiniteState s_st24
          (.assign .global (ofString "journal_n")
            (.op .add [.var .global (ofString "journal_n"), .const 1#64])) =
          (none, setGlobalHOLFinite (ofString "journal_n") (.val (.word (jnw + 1#64))) s_st24) := by
        simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, toExact,
          hjn_st24, wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
          isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
      rw [hass] at hass_step
      have hmid_eq : mid = setGlobalHOLFinite (ofString "journal_n") (.val (.word (jnw + 1#64))) s_st24 :=
        ((Prod.mk.inj hass_step).2).symm
      have hmid_mem : mid.memory = s_st24.memory := by rw [hmid_eq]; rfl
      have hmid_g : mid.globals = s_st24.globals.update (ofString "journal_n", .val (.word (jnw + 1#64))) := by
        rw [hmid_eq]; rfl
      have hmid_be : mid.be = s0.be := by rw [hmid_eq]; exact heff_st24.be
      have hne_0_8 : rw ≠ rw + 8#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hne_0_16 : rw ≠ rw + 16#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hne_0_24 : rw ≠ rw + 24#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hne_16_24 : rw + 16#64 ≠ rw + 24#64 := fun h => by have := congrArg BitVec.toNat h; omega
      have hm_r0 : memW mid (globN s0 "journal" + 32 * jnw.toNat) = tw.toNat := by
        have hbv0 : BitVec.ofNat 64 (globN s0 "journal" + 32 * jnw.toNat) = rw := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, hrw_nat, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
        unfold memW; rw [hbv0, hmid_mem, hs_st24_eq, hs_st16_eq, hs_st8_eq, hs_st0_eq]
        simp [hne_0_24, hne_0_16, hne_0_8]
      have hm_r16 : memW mid (globN s0 "journal" + 32 * jnw.toNat + 16) = w16.toNat := by
        have hbv16 : BitVec.ofNat 64 (globN s0 "journal" + 32 * jnw.toNat + 16) = rw + 16#64 := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, hrw16_nat, hrw_nat, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
        unfold memW; rw [hbv16, hmid_mem, hs_st24_eq, hs_st16_eq]
        simp [hne_16_24]
      have hm_r24 : memW mid (globN s0 "journal" + 32 * jnw.toNat + 24) = f1.toNat := by
        have hbv24 : BitVec.ofNat 64 (globN s0 "journal" + 32 * jnw.toNat + 24) = rw + 24#64 := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, hrw24_nat, hrw_nat, Nat.mod_eq_of_lt (by dsimp at hj_hi0; omega)]
        unfold memW; rw [hbv24, hmid_mem, hs_st24_eq]
        simp
      have hhp_mid_eq : globN mid "heap_ptr" = globN s_st24 "heap_ptr" := by
        apply globN_eq_of_lookup
        rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "journal_n" ≠ ofString "heap_ptr" by decide]
      have hfmp_mid_eq : globN mid "frame_mem_ptr" = globN s_st24 "frame_mem_ptr" := by
        apply globN_eq_of_lookup
        rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "journal_n" ≠ ofString "frame_mem_ptr" by decide]
      have hsp_mid_eq : globN mid "scratch_ptr" = globN s_st24 "scratch_ptr" := by
        apply globN_eq_of_lookup
        rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "journal_n" ≠ ofString "scratch_ptr" by decide]
      have hA_mid : ArenaReady mid := by
        have hG_mid : GuestInv mid := by
          have hG24 := heff_st24.arena.1
          rw [hmid_eq]
          exact ⟨hG24.code, hG24.memaddrs, hG24.shMemaddrs, hG24.baseAddr⟩
        refine ⟨hG_mid, ?_⟩
        unfold ArenaOK
        have hA24 := heff_st24.arena.2
        rw [hhp_mid_eq, hfmp_mid_eq, hsp_mid_eq]
        refine ⟨hA24.1, hA24.2.1, hA24.2.2.1, hA24.2.2.2.1, hA24.2.2.2.2.1,
          hA24.2.2.2.2.2.1, hA24.2.2.2.2.2.2.1, hA24.2.2.2.2.2.2.2.1, ?_⟩
        intro g hg
        by_cases hgj : ofString g = ofString "journal_n"
        · refine ⟨jnw + 1#64, ?_⟩
          unfold GlobalWord; rw [hmid_g, hgj]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        · obtain ⟨w, hw⟩ := hA24.2.2.2.2.2.2.2.2 g hg
          refine ⟨w, ?_⟩
          unfold GlobalWord at hw ⊢
          rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hgj, hw]
      have hjn_mid : globN mid "journal_n" = globN s0 "journal_n" + 1 := by
        have hjc_max : globN s0 "journal_cap" ≤ journalCapMax := hJ0.2.1
        have hjcm_val : journalCapMax = 524288 := rfl
        have hadd1 : (jnw + 1#64).toNat = jnw.toNat + 1 := by
          apply BitVec.toNat_add_of_lt
          change jnw.toNat + 1 < 2 ^ 64; omega
        have hlk_mid : mid.globals.lookup (ofString "journal_n") = some (.val (.word (jnw + 1#64))) := by
          rw [hmid_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        rw [hjn_nat]
        unfold globN; simp [hlk_mid, hadd1]
      have hg_kept_mid : GlobalsKept ["heap_ptr", "journal_n"] s0 mid := by
        intro k hk
        have hne_hp : k ≠ ofString "heap_ptr" := fun h => hk (by simp [h])
        have hne_jn : k ≠ ofString "journal_n" := fun h => hk (by simp [h])
        rw [hmid_g]
        have hlk_k : (s_st24.globals.update (ofString "journal_n", .val (.word (jnw + 1#64)))).lookup k =
            s_st24.globals.lookup k := by
          simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne_jn]
        rw [hlk_k]
        exact heff_st24.gw_kept k (by simp [hne_hp])
      have hstep : WorldStepSc (bufRegions []) ["heap_ptr", "journal_n"] stdKeep NoExtra s0 none mid :=
        worldStepSc_of_journal_append jnw hW0_full hA_mid hmid_be
          (by rw [hhp_mid_eq]; exact heff_st24.hp_lo) hg_kept_mid hjn_nat hjn_lt0 hjn_mid
          (fun x hx => heff_st24.out_dom x (by rwa [← hmid_mem]))
          (fun x hx => by
            rcases heff_st24.cell_frame x (by rwa [← hmid_mem]) with ⟨iv, hiv, hhit⟩ | ⟨_, h, _⟩ | hfg | hhf
            · simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inl hhit
            · cases h
            · exact Or.inr (Or.inl hfg)
            · exact Or.inr (Or.inr hhf))
          (fun a ha hne => by
            have hmb_mid : memB mid a = memB s_st24 a := by
              unfold memB; rw [hmid_mem, hmid_be, heff_st24.be]
            rcases heff_st24.byte_frame a ha (by rwa [← hmb_mid]) with ⟨iv, hiv, hin⟩ | ⟨_, h, _⟩ | hfg | hhf
            · simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inl hin
            · cases h
            · exact Or.inr (Or.inl hfg)
            · exact Or.inr (Or.inr hhf))
          hm_r0
          (fun S hTS => by
            dsimp only
            rw [hm_r16, hm_r24]
            exact htw_ok S hTS)
      have hs_st24_loc : s_st24.locals = s_r.locals := by rw [hs_st24_eq, hst16_loc]
      have hmid_loc : mid.locals = s_r.locals := by rw [hmid_eq]; exact hs_st24_loc
      have hmid_loc_other : ∀ x : MlS, x ≠ ofString "klen" → x ≠ ofString "kc" → x ≠ ofString "r" →
          mid.locals.lookup x = cur.locals.lookup x := by
        intro x hx_kl hx_kc hx_r
        rw [hmid_loc]
        simp [s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          Ne.symm hx_r, hmc_loc, s_kc, Ne.symm hx_kc, s_kl, Ne.symm hx_kl]
      have hout_tp : out = { m_r with locals := out.locals } := by
        rw [hout_eq1, hm_kl_eq, hm_kc_eq]
      exact ⟨mid, m_r, hstep,
        (hmid_loc_other _ (by decide) (by decide) (by decide)).trans hloc_t,
        (hmid_loc_other _ (by decide) (by decide) (by decide)).trans hloc_k,
        hmid_loc_other _ (by decide) (by decide) (by decide),
        htail_run, hout_tp⟩
    | _ => simp at hflow_kl

theorem progWStep_call0_jset_ts48 (B : BufList) (gw : List String)
    (hhp_in : "heap_ptr" ∈ gw) (hjn_in : "journal_n" ∈ gw)
    (kExp vExp : ExpHOL 64) :
    ProgWStep B gw
      (.call (some (none, none)) (ofString "jset")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]), kExp, vExp]) := by
  intro F s hcode hW hnt hfr
  set argsL : List (ExpHOL 64) :=
    [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]), kExp, vExp]
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) argsL with _ | values
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    have hargs_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) argsL = some values := by
      rwa [evalListHOLFinite_eq_toExact]
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "jset") values with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        have hbody_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "jset")
          _ _ body' _ ret' values callee lookup_jset (by rwa [← hcode])
        obtain ⟨v1, v2, v3, he1, _, _, hc_t, hc_k, hc_v⟩ := callee_param_three s (ofString "jset")
          (ofString "t") (ofString "key") (ofString "value") .one .one .one _ _
          (by rw [hcode]; exact lookup_jset) _ _ _ values body' callee ret' hargs_fin hl
        obtain ⟨tw, rfl, htw_nat, hts_nz⟩ := evalAt_loadG_nz s hW.1.1 "ts" 48#64 (by decide) v1 he1
        obtain ⟨_, kw, vlw, hvals_eq, _, hc_k', hc_v'⟩ := Fast_C08WkShard03.lookupCode_three_words
          (by decide) (by decide) (by decide) lookup_jset
          (by
            have hret_eq := lookupCodeHOLFinite_installed_return s (ofString "jset")
              _ _ _ _ ret' values callee (by rw [hcode]; exact lookup_jset) hl
            subst hbody_eq hret_eq; rwa [← hcode])
        have hv23 : v2 = .val (.word kw) ∧ v3 = .val (.word vlw) := by
          rw [hc_k] at hc_k'; rw [hc_v] at hc_v'
          exact ⟨Option.some.inj hc_k', Option.some.inj hc_v'⟩
        rcases hv23 with ⟨rfl, rfl⟩
        let ent := callEntryStateHOLFinite s callee
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, post⟩
        simp only [ent, hrun] at hnt hfr ⊢
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | exception eid ev =>
            exfalso
            have hne : eid ≠ ofString "TrapErr" := by
              rcases hfr with h | h | h | ⟨_, h⟩ | ⟨_, _, h, hne⟩ <;> try simp at h
              obtain ⟨rfl, _⟩ := h; exact hne
            have hbody_ok : noCatchableRaise trapOnlyCallees body' = true :=
              trapOnlyCallees_good (ofString "jset") (by decide) values body' callee ret' (by rwa [← hcode])
            have hno := evaluate_noCatchableRaise trapOnlyCallees trapOnlyCallees_good
              body' hbody_ok ent hcode eid ev hne
            dsimp only [ent] at hno; rw [hrun] at hno; exact hno rfl
          | returned rv =>
            dsimp only at hfr ⊢
            split
            · have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
              subst hbody_eq
              have hbody_fold : sourceFnBody Guest.Software.guestFn_jset =
                  .decCall (ofString "old") (.comb [.one, .one]) (ofString "htab_get")
                    [.var .local (ofString "t"), .var .local (ofString "key")]
                    (journalAppendTailProgSc 4#64 (.rfield 0 (.var .local (ofString "old")))
                      (.seq
                        (.call (some (none, none)) (ofString "htab_set")
                          [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")])
                        (.return (.const 0#64)))) := rfl
              change evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_jset) = (some (.returned rv), post) at hrun
              rw [hbody_fold] at hrun
              rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
              have hent_t : ent.locals.lookup (ofString "t") = some (.val (.word tw)) := hc_t
              have hent_k : ent.locals.lookup (ofString "key") = some (.val (.word kw)) := hc_k
              have hent_v : ent.locals.lookup (ofString "value") = some (.val (.word vlw)) := hc_v
              have hargs_hg : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
                  [.var .local (ofString "t"), .var .local (ofString "key")] =
                  some [.val (.word tw), .val (.word kw)] := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hent_t, hent_k]
              rw [hargs_hg] at hrun; dsimp only at hrun
              rcases hlk_hg : lookupCodeHOLFinite ent.code.lookup (ofString "htab_get")
                  [.val (.word tw), .val (.word kw)] with _ | ⟨bhg, chg, rhg⟩
              · rw [hlk_hg] at hrun; simp at hrun
              · rw [hlk_hg] at hrun; dsimp only at hrun
                by_cases hcz_ent : ent.clock = 0
                · simp [hcz_ent] at hrun
                rw [if_neg hcz_ent] at hrun
                have hbhg_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "htab_get")
                  _ _ bhg _ rhg _ chg EvmFrameSpecs.lookup_htab_get (by rwa [← show ent.code = originalRuntimeCode from hcode])
                subst hbhg_eq
                have hchg_t' : chg.lookup (ofString "t") = some (.val (.word tw)) := by
                  have ht_ev : evalAt ent (.var .local (ofString "t")) = some (.val (.word tw)) := by
                    simp [evalAt, evalHOLExact, toExact, hent_t]
                  have ⟨v1', _, he1', _, hc1', _⟩ := callee_param_two_sc ent (ofString "htab_get")
                    (ofString "t") (ofString "key") .one .one _ _
                    (by rw [show ent.code = originalRuntimeCode from hcode]; exact EvmFrameSpecs.lookup_htab_get)
                    (.var .local (ofString "t")) (.var .local (ofString "key"))
                    _ _ chg rhg hargs_hg hlk_hg
                  rw [ht_ev] at he1'; injection he1' with h'; subst h'; exact hc1'
                have hchg_k' : chg.lookup (ofString "key") = some (.val (.word kw)) := by
                  have hk_ev : evalAt ent (.var .local (ofString "key")) = some (.val (.word kw)) := by
                    simp [evalAt, evalHOLExact, toExact, hent_k]
                  have ⟨_, v2', _, he2', _, hc2'⟩ := callee_param_two_sc ent (ofString "htab_get")
                    (ofString "t") (ofString "key") .one .one _ _
                    (by rw [show ent.code = originalRuntimeCode from hcode]; exact EvmFrameSpecs.lookup_htab_get)
                    (.var .local (ofString "t")) (.var .local (ofString "key"))
                    _ _ chg rhg hargs_hg hlk_hg
                  rw [hk_ev] at he2'; injection he2' with h'; subst h'; exact hc2'
                let ent_hg := callEntryStateHOLFinite ent chg
                rcases hrun_hg : evaluateHOLFiniteState ent_hg (sourceFnBody Guest.Software.guestFn_htab_get) with ⟨res_hg, p_hg⟩
                dsimp only [ent_hg] at hrun_hg
                rw [hrun_hg] at hrun
                cases res_hg with
                | none => simp at hrun
                | some cr_hg =>
                  cases cr_hg with
                  | exception eid_hg ev_hg =>
                    exfalso
                    dsimp only at hrun; injection hrun with hr_eq _
                    cases hr_eq
                  | timeOut | error | «break» | «continue» | finalFfi _ => simp at hrun
                  | returned v_old =>
                    dsimp only at hrun
                    split at hrun <;> try simp at hrun
                    have htw_nz : tw ≠ 0 := WkBal.htab_get_t_nonzero ent_hg tw kw
                      (guestInv_callEntry ent chg hWent.1.1) hchg_t' hchg_k' v_old
                      (by dsimp only [ent_hg]; rw [hrun_hg])
                    have ht0_nz : memW s (globN s "ts" + 48) ≠ 0 := by
                      intro h0; apply htw_nz; apply BitVec.eq_of_toNat_eq
                      change tw.toNat = 0; simpa [htw_nat] using h0
                    obtain ⟨_, S0, hWT0⟩ := hW
                    have htw_S0 : tw.toNat ∈ S0 := by
                      rw [htw_nat]; exact (nonValueSlot_ts48 s S0 hWT0.1 hts_nz ht0_nz).1
                    have hwf_hg : HtabWF ent_hg tw.toNat :=
                      (htabWF_with_locals s chg (ent.clock - 1) tw.toNat).2 (hWT0.1.2.1 _ htw_S0).1
                    obtain ⟨f0, f1, rfl, _⟩ := WkBal.htab_get_ret_in_values ent_hg tw kw
                      hcode hchg_t' hchg_k' hwf_hg v_old
                      (by dsimp only [ent_hg]; rw [hrun_hg])
                    have hro_hg := FunSpec.at_lookup EvmFrameSpecs.ro_htab_get ent hcode
                      _ (sourceFnBody Guest.Software.guestFn_htab_get) chg rhg hlk_hg
                      (guestInv_callEntry ent chg hWent.1.1) (by rw [hrun_hg]; simp)
                    have hro_hg' : ((evaluateHOLFiniteState ent_hg (sourceFnBody Guest.Software.guestFn_htab_get)).2) = _ :=
                      hro_hg (by rw [hrun_hg]; exact Or.inl ⟨_, rfl⟩)
                    dsimp only [ent_hg] at hro_hg'
                    rw [hrun_hg] at hro_hg'
                    dsimp only at hro_hg'
                    set s_old := setVarHOLFinite (ofString "old") (.rStruct [.val (.word f0), .val (.word f1)])
                      { p_hg with locals := ent.locals }
                    have heff_old : WorldEff ent s_old [] [] ["heap_ptr"] :=
                      ((WorldEff.refl ent [] [] ["heap_ptr"] hWent.1 hcode).of_readOnly hro_hg').locals_clock _ _
                    have hg_all_old : ∀ k : MlS, s_old.globals.lookup k = ent.globals.lookup k := by
                      intro k; dsimp only [s_old, setVarHOLFinite]; rw [hro_hg']; rfl
                    have hold_t : s_old.locals.lookup (ofString "t") = some (.val (.word tw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_t,
                        show ofString "old" ≠ ofString "t" by decide]
                    have hold_k : s_old.locals.lookup (ofString "key") = some (.val (.word kw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_k,
                        show ofString "old" ≠ ofString "key" by decide]
                    have hold_v : s_old.locals.lookup (ofString "value") = some (.val (.word vlw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_v,
                        show ofString "old" ≠ ofString "value" by decide]
                    have hold_old : s_old.locals.lookup (ofString "old") =
                        some (.rStruct [.val (.word f0), .val (.word f1)]) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                    rcases htail_old : evaluateHOLFiniteState s_old
                        (journalAppendTailProgSc 4#64 (.rfield 0 (.var .local (ofString "old")))
                          (.seq
                            (.call (some (none, none)) (ofString "htab_set")
                              [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")])
                            (.return (.const 0#64)))) with ⟨rtail, ptail⟩
                    rw [htail_old] at hrun; dsimp only at hrun
                    have hrtail_eq : rtail = some (.returned rv) := hrun.1
                    have hpost_ptail : post = { ptail with locals := (HolFiniteMapExact.resVarEq ptail.locals
                        (ofString "old", ent.locals.lookup (ofString "old"))) } := hrun.2.symm
                    obtain ⟨mid, tailPost, hstep_j, hmid_t, hmid_k, hmid_v_eq, hmid_tail, hptail_tp⟩ :=
                      journal_append_block_step_sc ent s_old
                        4#64 (.rfield 0 (.var .local (ofString "old"))) tw kw f0 f1 f0 hWent heff_old hg_all_old
                        hold_t hold_k hold_old
                        (fun st hst => by simp [evalHOLExact, toExact, hst])
                        (fun S hTS => by
                          have htw_nat' : tw.toNat = memW s (globN s "ts" + 48) := htw_nat
                          have hts_ent : globN ent "ts" = globN s "ts" := rfl
                          have hm48_ent : memW ent (globN ent "ts" + 48) = memW s (globN s "ts" + 48) := rfl
                          have ht0_ent_nz : memW ent (globN ent "ts" + 48) ≠ 0 := by rw [hm48_ent]; exact ht0_nz
                          have htw_S : tw.toNat ∈ S := by
                            rw [htw_nat']
                            exact (nonValueSlot_ts48 ent S hTS (by rwa [hts_ent]) ht0_ent_nz).1
                          have hjr_48 : journalRole ent tw.toNat = "ts+48" := by
                            rw [htw_nat', ← hm48_ent]
                            exact journalRole_ts48 ent S hTS (by rwa [hts_ent]) ht0_ent_nz
                          refine ⟨htw_S, ?_⟩
                          dsimp only
                          rw [hjr_48]
                          simp only [show ("ts+48" = "ts+32") ↔ False by decide, and_false, ↓reduceIte,
                            List.mem_singleton]
                          rintro p rfl
                          have hm48_wrs : (memW ent (globN ent "ts" + 48), "ts+48") ∈ worldRoleSlots ent := by
                            apply mem_worldRoleSlots_recRole ent "ts" 48 "ts+48" (by rwa [hts_ent]) ht0_ent_nz
                            apply List.mem_append.2; right
                            unfold recRoles; simp [hts_ent, hts_nz]
                          rwa [hm48_ent, ← htw_nat'] at hm48_wrs)
                        (by rw [htail_old, hrtail_eq])
                    have hmid_v : mid.locals.lookup (ofString "value") = some (.val (.word vlw)) :=
                      hmid_v_eq.trans hold_v
                    have hW_mid : WorldOK mid := hstep_j.worldOK_bufs (fun _ h => by cases h) hWent
                    have hmid_code : mid.code = originalRuntimeCode := hW_mid.1.1.code
                    have hts_mid : globN mid "ts" = globN ent "ts" :=
                      globN_eq_of_lookup (hstep_j.1.2.2.1 (ofString "ts") (by decide))
                    have hm48_mid : memW mid (globN mid "ts" + 48) = tw.toNat := by
                      rw [hts_mid]
                      have hrk48 := hstep_j.1.2.2.2.1
                        ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]) (by simp [stdKeep]) hts_nz
                        48 (by simp) (fun _ h => by cases h)
                      exact hrk48.trans htw_nat.symm
                    obtain ⟨s_hs, hhs, hret_hs⟩ := seq_call0_ret_inv_sc hmid_tail
                    rw [evaluateHOLFiniteState_return] at hret_hs
                    simp only [evalHOLExact, toExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                      show (1 : Nat) ≤ 32 by decide, ↓reduceIte, emptyLocalsHOLFinite] at hret_hs
                    have htp_eq : tailPost = { s_hs with locals := HolFiniteMapExact.empty } :=
                      ((Prod.mk.inj hret_hs).2).symm
                    rw [evaluateHOLFiniteState_call] at hhs
                    have hargs_hs : evalListHOLFinite mid (h := fun a => Classical.propDecidable (mid.memaddrs a))
                        [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")] =
                        some [.val (.word tw), .val (.word kw), .val (.word vlw)] := by
                      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hmid_t, hmid_k, hmid_v]
                    rw [hargs_hs] at hhs; dsimp only at hhs
                    rcases hlk_hs : lookupCodeHOLFinite mid.code.lookup (ofString "htab_set")
                        [.val (.word tw), .val (.word kw), .val (.word vlw)] with _ | ⟨bhs, chs, rhs'⟩
                    · rw [hlk_hs] at hhs; simp at hhs
                    · rw [hlk_hs] at hhs; dsimp only at hhs
                      by_cases hcz_mid : mid.clock = 0
                      · simp [hcz_mid] at hhs
                      rw [if_neg hcz_mid] at hhs
                      obtain ⟨v1_hs, _, _, he1_hs, _, _, hchs_t, _, _⟩ := callee_param_three mid (ofString "htab_set")
                        (ofString "t") (ofString "key") (ofString "value") .one .one .one _ _
                        (by rw [hmid_code]; exact EvmFrameSpecs.lookup_htab_set)
                        (.var .local (ofString "t")) (.var .local (ofString "key")) (.var .local (ofString "value"))
                        _ bhs chs rhs' hargs_hs hlk_hs
                      have hv1_hs_eq : v1_hs = .val (.word tw) := by
                        simp [evalAt, evalHOLExact, toExact, hmid_t] at he1_hs; exact he1_hs.symm
                      subst hv1_hs_eq
                      let ent_hs := callEntryStateHOLFinite mid chs
                      have hloc_t_hs : locN ent_hs "t" = memW mid (globN mid "ts" + (48#64 : BitVec 64).toNat) := by
                        change locN ent_hs "t" = memW mid (globN mid "ts" + 48)
                        simp [locN, ent_hs, callEntryStateHOLFinite, hchs_t, hm48_mid]
                      rcases hrun_hs : evaluateHOLFiniteState ent_hs bhs with ⟨res_hs, p_hs⟩
                      dsimp only [ent_hs] at hrun_hs
                      rw [hrun_hs] at hhs
                      cases res_hs with
                      | none => simp at hhs
                      | some cr_hs2 =>
                        cases cr_hs2 with
                        | returned v_hs =>
                          dsimp only at hhs
                          split at hhs <;> try simp at hhs
                          have hs_hs_eq : s_hs = { p_hs with locals := mid.locals } := hhs.symm
                          have hts_mid_nz : globN mid "ts" ≠ 0 := by rwa [hts_mid]
                          have ht0_mid_nz : memW mid (globN mid "ts" + (48#64 : BitVec 64).toNat) ≠ 0 := by
                            change memW mid (globN mid "ts" + 48) ≠ 0
                            rw [hm48_mid]; intro h0; apply htw_nz; exact BitVec.eq_of_toNat_eq h0
                          have hArg_hs : HtabArgWF ent_hs := by
                            obtain ⟨hAm, Sm, hTm, _⟩ := hW_mid
                            have ht0_Sm := (nonValueSlot_ts48 mid Sm hTm hts_mid_nz ht0_mid_nz).1
                            refine ⟨localsFree_arenaReady mid _ _ hAm, ?_, ?_⟩
                            · rw [hloc_t_hs]; exact (htabWF_with_locals mid chs (mid.clock - 1) _).2 (hTm.2.1 _ ht0_Sm).1
                            · rw [hloc_t_hs]; exact fun i hi => ((hTm.2.1 _ ht0_Sm).2 i hi).1
                          have hexit := FunSpec.at_lookup htab_set_spec mid hmid_code
                            _ bhs chs rhs' hlk_hs hArg_hs (by rw [hrun_hs]; simp)
                          rw [hrun_hs] at hexit
                          have hex := hexit v_hs rfl
                          dsimp only [HtabExit] at hex
                          rw [hloc_t_hs] at hex
                          obtain ⟨hAp_hs, hwf_hs, hh0_hs, _, hhp_hs, hfp_hs, hfr_hs, hg_hs⟩ := hex
                          have hbe_hs : p_hs.be = mid.be := by
                            have inv := (PanRunBounded.evaluateHOLFiniteState_metadata ent_hs bhs).2.2.1
                            dsimp only [ent_hs] at inv; rw [hrun_hs] at inv; exact inv
                          have hstep_hs0 : WorldStepSc (bufRegions []) ["heap_ptr"] stdKeep NoExtra mid none p_hs :=
                            worldStepSc_of_htabExit_nonValue hW_mid hbe_hs hg_hs hg_hs
                              (fun Sm hTm => nonValueSlot_ts48 mid Sm hTm hts_mid_nz ht0_mid_nz)
                              hAp_hs hwf_hs hh0_hs hhp_hs hfp_hs hfr_hs
                          have hstep_hs : WorldStepSc (bufRegions []) ["heap_ptr", "journal_n"] stdKeep NoExtra mid none post := by
                            have hp_post : post = { p_hs with locals := post.locals, clock := post.clock } := by
                              rw [hpost_ptail, hptail_tp, htp_eq, hs_hs_eq]
                            rw [hp_post]
                            exact (hstep_hs0.with_locals_clock post.locals post.clock).mono_bufs
                              (fun _ h => by cases h) (by simp)
                          have hstep_ent : WorldStepSc (bufRegions []) ["heap_ptr", "journal_n"] stdKeep NoExtra ent none post :=
                            WorldStepSc.trans (fun _ h => by cases h) (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
                              hstep_j hstep_hs
                          exact (hstep_ent.from_entry).mono_bufs
                            (fun _ h => by cases h)
                            (fun g hg => by
                              simp at hg
                              rcases hg with rfl | rfl
                              · exact hhp_in
                              · exact hjn_in)
                        | _ => simp at hhs
            · rename_i hbad; simp only [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

private theorem safeStepGlobals_acctMut_sc : SafeStepGlobals ["heap_ptr", "journal_n", "scratch_ptr"] := by
  intro g hg; simp at hg; rcases hg with rfl | rfl | rfl <;> simp

private theorem contOrRes_of_flowingOrResumes_sc {r : Option (PanSemResultExact 64)}
    (hfr : FlowingOrResumes r) : ContOrRes r := by
  rcases hfr with h | h | h | hr
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr hr))

private theorem worldEff_to_worldStepSc_wsAcct_sc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hW : WorldOK s)
    (heff : WorldEff s post [] wsAcctBufs ["heap_ptr", "scratch_ptr"]) :
    WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra s r post := by
  have heff' : WorldEff s post (bufRegions wsAcctBufs s) wsAcctBufs ["heap_ptr", "scratch_ptr"] :=
    heff.mono (fun _ hiv => by cases hiv) (fun _ h => h) (fun _ h => h)
  have hws0 : WorldStep (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra s r post :=
    heff'.to_worldStep_Q hW (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
  exact WorldStepSc.mono_bufs
    (fun p hp => by simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs])
    (fun g hg => by simp at hg; rcases hg with rfl | rfl <;> simp)
    ⟨hws0, heff.sp_hi⟩

private theorem progWStep_decCall_alloc_seq_acctMut {x : MlS} {sz : BitVec 64} {pWrite pRest : ProgHOL 64} {F : Type}
    {s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hWrite : ∀ (pw : BitVec 64) (m1 : PanSemStateFiniteExact 64 F),
      m1.locals = s.locals.update (x, .val (.word pw)) →
      (∀ k : MlS, k ≠ ofString "heap_ptr" → m1.globals.lookup k = s.globals.lookup k) →
      WorldEff s m1 [] wsAcctBufs ["heap_ptr", "scratch_ptr"] →
      globN s "heap_ptr" ≤ pw.toNat →
      pw.toNat + (sz.toNat + 7) / 8 * 8 = globN m1 "heap_ptr" →
      globN m1 "heap_ptr" ≤ heapLimit →
      (evaluateHOLFiniteState m1 pWrite).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState m1 pWrite).1 →
      WorldEff s (evaluateHOLFiniteState m1 pWrite).2 [] wsAcctBufs ["heap_ptr", "scratch_ptr"])
    (hRest : ∀ (pw : BitVec 64) (m2 : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word pw)) s) pWrite).2.locals = s.locals.update (x, .val (.word pw)) ∨ True →
      WorldEff s m2 [] wsAcctBufs ["heap_ptr", "scratch_ptr"] →
      m2.locals = s.locals.update (x, .val (.word pw)) →
      m2.code = originalRuntimeCode →
      WorldOK m2 →
      (evaluateHOLFiniteState m2 pRest).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState m2 pRest).1 →
      WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
        m2 (evaluateHOLFiniteState m2 pRest).1 (evaluateHOLFiniteState m2 pRest).2)
    (hpWrite_loc : ∀ (m1 : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState m1 pWrite).1 = none →
      (evaluateHOLFiniteState m1 pWrite).2.locals = m1.locals)
    (hnt : (evaluateHOLFiniteState s
      (.decCall x .one (ofString "alloc") [.const sz] (.seq pWrite pRest))).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.decCall x .one (ofString "alloc") [.const sz] (.seq pWrite pRest))).1) :
    WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
      s (evaluateHOLFiniteState s
        (.decCall x .one (ofString "alloc") [.const sz] (.seq pWrite pRest))).1
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "alloc") [.const sz] (.seq pWrite pRest))).2 := by
  have hB := validBufList_acctMutBufs
  have hgw := safeStepGlobals_acctMut_sc
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const sz] =
      some [.val (.word sz)] := rfl
  simp only [hargs] at hnt hfr ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") [.val (.word sz)] with
    _ | ⟨body', callee, ret'⟩
  · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hl] at hnt hfr ⊢
    by_cases hz : s.clock = 0
    · simp [hz] at hnt
    · rw [if_neg hz] at hnt hfr ⊢
      have hlk_alloc_explicit : originalRuntimeCode.lookup (ofString "alloc") =
          some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
        lookup_alloc_r16
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc") _ _ body'
        _ ret' [.val (.word sz)] callee (by rw [hc]; exact hlk_alloc_explicit) hl
      subst hsame
      have hret_eq := lookupCodeHOLFinite_installed_return s (ofString "alloc") _ _ _
        _ ret' [.val (.word sz)] callee (by rw [hc]; exact hlk_alloc_explicit) hl
      subst hret_eq
      obtain ⟨nw, hnw_eq, hnw_callee⟩ := Fast_C08WkShard03.lookupCode_one_word hlk_alloc_explicit (by rw [← hc]; exact hl)
      injection hnw_eq with hnw_eq'; injection hnw_eq' with hnw_eq'; injection hnw_eq' with hnw_eq'; subst hnw_eq'
      obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
        globalWord_of_globN_pos s "heap_ptr" (by have := hW.1.2.1; rw [sourceBase_val] at this; omega)
      rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res, pa⟩
      simp only [hrun] at hnt hfr ⊢
      have hcr_outer := contOrRes_of_flowingOrResumes_sc hfr
      have hres_a : Resumes res := by
        cases res with
        | none => rcases hcr_outer with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
        | some r1 =>
          cases r1 with
          | returned rv => exact Or.inl ⟨rv, rfl⟩
          | exception eid ev =>
            rcases hcr_outer with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨e', v', hc0, hne⟩⟩
            · simp at hc0
            · simp at hc0
            · simp at hc0
            · simp at hc0
            · change some (PanSemResultExact.exception eid ev) = some (PanSemResultExact.exception e' v') at hc0
              injection hc0 with hc0'; injection hc0' with he1 he2; subst he1 he2
              exact Or.inr ⟨eid, ev, rfl, hne⟩
          | timeOut => simp at hnt
          | _ => rcases hcr_outer with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
      have hal := R13.alloc_body_resumes (callEntryStateHOLFinite s callee) pw hc hpw_lk
        (by rw [hrun]; exact hres_a)
      rw [hrun] at hal
      obtain ⟨nw', hnw'_lk, hrv_eq, hcmp1, hcmp2, hpa_eq⟩ := hal
      have hnw_eq2 : sz = nw' := by
        have : (callEntryStateHOLFinite s callee).locals.lookup (ofString "n") = some (.val (.word sz)) := hnw_callee
        rw [this] at hnw'_lk; injection hnw'_lk with h'; injection h' with h'; injection h'
      subst hnw_eq2
      dsimp only at hrv_eq hpa_eq
      subst hrv_eq
      dsimp only at hnt hfr ⊢
      have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      rw [if_pos hsh] at hnt hfr ⊢
      dsimp only at hnt hfr ⊢
      set m1 := setVarHOLFinite x (.val (.word pw)) { pa with locals := s.locals }
      have hm1_next : m1 = { s with
          globals := s.globals.update (ofString "heap_ptr", .val (.word ((pw + (sz + 7)) &&& ((0 : BitVec 64) - 8)))),
          locals := m1.locals, clock := m1.clock } := by
        dsimp only [m1, setVarHOLFinite]; rw [hpa_eq]; rfl
      have heff_s : WorldEff s s [] wsAcctBufs ["heap_ptr", "scratch_ptr"] :=
        WorldEff.refl s [] wsAcctBufs ["heap_ptr", "scratch_ptr"] hW.1 hc
      obtain ⟨heff_m1, _, _, _, hp_lo_s, hp_add, hp_hi, _⟩ :=
        worldEff_alloc_step heff_s (by decide) hpw_lk hcmp1 hcmp2 hm1_next
      have hm1_loc : m1.locals = s.locals.update (x, .val (.word pw)) := rfl
      have hm1_g : ∀ k : MlS, k ≠ ofString "heap_ptr" → m1.globals.lookup k = s.globals.lookup k := by
        intro k hk; rw [hm1_next]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
      rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
      rcases hrw : evaluateHOLFiniteState m1 pWrite with ⟨rw1, m2⟩
      simp only [hrw] at hnt hfr ⊢
      cases rw1 with
      | none =>
        have heff_m2 := hWrite pw m1 hm1_loc hm1_g heff_m1 hp_lo_s hp_add hp_hi
          (by rw [hrw]; simp) (by rw [hrw]; exact Or.inl rfl)
        rw [hrw] at heff_m2; dsimp only at heff_m2
        have hm2_loc : m2.locals = s.locals.update (x, .val (.word pw)) := by
          have hl := hpWrite_loc m1 (by rw [hrw])
          rw [hrw] at hl; dsimp only at hl; exact hl.trans hm1_loc
        have hs12 : WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra s none m2 :=
          worldEff_to_worldStepSc_wsAcct_sc hW heff_m2
        have hW_m2 : WorldOK m2 := hs12.worldOK_bufs hB hW
        have hs23 := hRest pw m2 (Or.inr trivial) heff_m2 hm2_loc heff_m2.code hW_m2 hnt hfr
        have hs23' := hs23.with_locals_clock (r' := (evaluateHOLFiniteState m2 pRest).1)
          (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState m2 pRest).2.locals (x, s.locals.lookup x))
          (evaluateHOLFiniteState m2 pRest).2.clock
        exact WorldStepSc.trans hB hgw hs12 hs23'
      | some r =>
        have heff_m2 := hWrite pw m1 hm1_loc hm1_g heff_m1 hp_lo_s hp_add hp_hi
          (by rw [hrw]; exact hnt) (by rw [hrw]; exact contOrRes_of_flowingOrResumes_sc hfr)
        rw [hrw] at heff_m2; dsimp only at heff_m2
        have hs12 : WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra s (some r) m2 :=
          worldEff_to_worldStepSc_wsAcct_sc hW heff_m2
        exact hs12.with_locals_clock (r' := some r)
          (HolFiniteMapExact.resVarEq m2.locals (x, s.locals.lookup x))
          m2.clock

private theorem acct_copy_step_sc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")])).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")])).1) :
    let res := (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")])).1
    let post := (evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")])).2
    WorldEff s post [] [] ["heap_ptr"] ∧
    (res = none → ∃ bw : BitVec 64,
      post.locals = s.locals.update (ofString "a", .val (.word bw)) ∧
      globN s "heap_ptr" ≤ bw.toNat ∧ bw.toNat + 56 ≤ heapLimit) := by
  dsimp only
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hhl_264 : heapLimit < 2 ^ 64 := by decide
  have heff0 : WorldEff s s [] [] ["heap_ptr"] := WorldEff.refl s [] [] ["heap_ptr"] hA hcode
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "a")] with _ | vals
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "acct_copy") vals with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        have hb_eq : body' = sourceFnBody Guest.Software.guestFn_acct_copy :=
          lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "acct_copy")
            _ _ body' _ ret' vals callee lookup_acct_copy (by rwa [← hcode])
        have hr_eq : ret' = .one :=
          lookupCodeHOLFinite_installed_return s (ofString "acct_copy")
            _ _ _ _ ret' vals callee (by rw [hcode]; exact lookup_acct_copy) hl
        subst hb_eq hr_eq
        obtain ⟨aw, rfl, haw_c⟩ := Fast_C08WkShard03.lookupCode_one_word lookup_acct_copy (by rwa [← hcode])
        let ent := callEntryStateHOLFinite s callee
        have hent_a : ent.locals.lookup (ofString "a") = some (.val (.word aw)) := haw_c
        have heff_ent : WorldEff s ent [] [] ["heap_ptr"] := heff0.locals_clock _ _
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) (sourceFnBody Guest.Software.guestFn_acct_copy) with ⟨rc, pc⟩
        have hrun_ent : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_acct_copy) = (rc, pc) := hrun
        have hnt_ent : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_acct_copy)).1 ≠ some .timeOut := by
          rw [hrun_ent]; rintro rfl; simp [hrun] at hnt
        simp only [hrun] at hnt hfr ⊢
        cases rc with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have heff_pc : WorldEff s pc [] [] ["heap_ptr"] := by
              have hbody_eq2 : sourceFnBody Guest.Software.guestFn_acct_copy =
                  .decCall (ofString "b") .one (ofString "alloc") [.const 56#64]
                    (.seq
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64])
                      (.return (.var .local (ofString "b")))) := rfl
              have hex_ev : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_acct_copy)).1 =
                  some (.exception eid ev) := by dsimp only [ent]; rw [hrun]
              have hp_ev : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_acct_copy)).2 = pc := by
                dsimp only [ent]; rw [hrun]
              rw [← hp_ev, hbody_eq2]
              refine worldEff_decCall_alloc heff_ent (by decide) (ofString "b") (.const 56#64)
                (by rw [← hbody_eq2]; exact hnt_ent)
                (by rw [← hbody_eq2, hex_ev]; exact Or.inr (Or.inr (Or.inr hres_ex)))
                (fun bw nw m1 hsz_ev _ hm1_loc _ heff_m1 _ _ hbw_lo hbw_end _ _ hnt1 hcr1 => ?_)
              have hnw_eq : nw = 56#64 := by simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
              subst hnw_eq
              have hbw_hi : bw.toNat + 56 ≤ heapLimit := by
                change bw.toNat + (56 + 7) / 8 * 8 = globN m1 "heap_ptr" at hbw_end; omega
              have hm1_b : m1.locals.lookup (ofString "b") = some (.val (.word bw)) := by
                rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
              refine worldEff_seq hnt1 hcr1
                (fun hnt_mc hcr_mc => worldEff_call0_memcpy_sc heff_m1 _ _ _ hnt_mc
                  (call0_or_resumes_sc m1 (ofString "memcpy") _ hcr_mc)
                  (fun dstw _ nw' hd _ hn _ => by
                    simp [evalHOLExact, hm1_b] at hd hn
                    subst hd hn
                    exact Or.inr (Or.inr (Or.inr ⟨hbw_lo, hbw_hi⟩))))
                (fun m2 _ heff_m2 _ _ => worldEff_return heff_m2 _)
            exact ⟨heff_pc.locals_clock _ _, fun h => by simp at h⟩
          | returned rv =>
            dsimp only at hfr ⊢
            split
            · rename_i hsh_rv
              split
              · have hbody_eq2 : sourceFnBody Guest.Software.guestFn_acct_copy =
                    .decCall (ofString "b") .one (ofString "alloc") [.const 56#64]
                      (.seq
                        (.call (some (none, none)) (ofString "memcpy")
                          [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64])
                        (.return (.var .local (ofString "b")))) := rfl
                rw [hbody_eq2] at hrun_ent
                rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun_ent
                have hargs56 : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
                    [.const 56#64] = some [.val (.word 56#64)] := by
                  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
                have hlk56 := pan_one_word_lookup ent.code.lookup (ofString "alloc") (ofString "n")
                  (sourceFnBody Guest.Software.guestFn_alloc) 56#64
                  (by rw [show ent.code = originalRuntimeCode from hcode]; exact lookup_alloc_r16)
                rw [hargs56] at hrun_ent; dsimp only at hrun_ent
                rw [hlk56] at hrun_ent; dsimp only at hrun_ent
                by_cases hcz_ent : ent.clock = 0
                · simp [hcz_ent] at hrun_ent
                rw [if_neg hcz_ent] at hrun_ent
                obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, ent.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
                  globalWord_of_globN_pos ent "heap_ptr"
                    (by have := heff_ent.arena.2.1; rw [sourceBase_val] at this; omega)
                let ent_al := callEntryStateHOLFinite ent (HolFiniteMapExact.empty.update (ofString "n", .val (.word 56#64)))
                rcases hrun_al : evaluateHOLFiniteState ent_al (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ral, pal⟩
                dsimp only [ent_al] at hrun_al
                rw [hrun_al] at hrun_ent
                have hres_al : Wave8Contracts.M18.Resumes ral := by
                  cases ral with
                  | none => simp at hrun_ent
                  | some c0 =>
                    cases c0 with
                    | returned r0 => exact Or.inl ⟨r0, rfl⟩
                    | exception e0 v0 => dsimp only at hrun_ent; injection hrun_ent with hr0 _; cases hr0
                    | _ => simp at hrun_ent
                have hal := R13.alloc_body_resumes ent_al pw hcode hpw_lk
                  (by dsimp only [ent_al]; rw [hrun_al]; exact hres_al)
                dsimp only [ent_al] at hal
                rw [hrun_al] at hal
                obtain ⟨nw', hnw'_lk, hral_eq, hcmp1, hcmp2, hpal_eq⟩ := hal
                have hnw56 : nw' = 56#64 := by
                  simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] at hnw'_lk; exact hnw'_lk.symm
                subst hnw56
                dsimp only at hral_eq hpal_eq
                subst hral_eq
                dsimp only at hrun_ent
                have hsh_pw : (shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one &&
                    shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one) = true := by
                  simp [shapeOfHOLExact, shapeEqHOL]
                rw [if_pos hsh_pw] at hrun_ent
                set m1 := setVarHOLFinite (ofString "b") (.val (.word pw)) { pal with locals := ent.locals }
                have hm1_next : m1 = { ent with
                    globals := ent.globals.update (ofString "heap_ptr", .val (.word ((pw + (56#64 + 7)) &&& ((0 : BitVec 64) - 8)))),
                    locals := m1.locals, clock := m1.clock } := by
                  dsimp only [m1, setVarHOLFinite]; rw [hpal_eq]; rfl
                obtain ⟨heff_m1, _, _, _, hp_lo_s, hp_add, hp_hi, _⟩ :=
                  worldEff_alloc_step heff_ent (by decide) hpw_lk hcmp1 hcmp2 hm1_next
                have hpw_hi : pw.toNat + 56 ≤ heapLimit := by
                  change pw.toNat + (56 + 7) / 8 * 8 = globN m1 "heap_ptr" at hp_add; omega
                have hm1_b : m1.locals.lookup (ofString "b") = some (.val (.word pw)) := by
                  simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                rcases hseq_m1 : evaluateHOLFiniteState m1
                    (.seq
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64])
                      (.return (.var .local (ofString "b")))) with ⟨rseq, pseq⟩
                rw [hseq_m1] at hrun_ent
                dsimp only at hrun_ent
                have hrseq_eq : rseq = some (.returned rv) := (Prod.mk.inj hrun_ent).1
                have hpc_pseq : pc = { pseq with locals := (HolFiniteMapExact.resVarEq pseq.locals
                    (ofString "b", ent.locals.lookup (ofString "b"))) } := ((Prod.mk.inj hrun_ent).2).symm
                rw [evaluateHOLFiniteState_seq_line780] at hseq_m1
                rcases hmc : evaluateHOLFiniteState m1
                    (.call (some (none, none)) (ofString "memcpy")
                      [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64]) with ⟨rmc, m2⟩
                rw [hmc] at hseq_m1
                cases rmc with
                | some cr_mc =>
                  exfalso
                  dsimp only at hseq_m1
                  have hcr_ret : some cr_mc = some (.returned rv) := (Prod.mk.inj hseq_m1).1.trans hrseq_eq
                  injection hcr_ret with hcr_eq; subst hcr_eq
                  rw [evaluateHOLFiniteState_call] at hmc
                  rcases ha_mc : evalListHOLFinite m1 (h := fun a => Classical.propDecidable (m1.memaddrs a))
                      [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64] with _ | vs_mc
                  · rw [ha_mc] at hmc; simp at hmc
                  · rw [ha_mc] at hmc; dsimp only at hmc
                    rcases hl_mc : lookupCodeHOLFinite m1.code.lookup (ofString "memcpy") vs_mc with _ | ⟨bmc, cmc, rmc'⟩
                    · rw [hl_mc] at hmc; simp at hmc
                    · rw [hl_mc] at hmc; dsimp only at hmc
                      by_cases hcz_m1 : m1.clock = 0
                      · simp [hcz_m1] at hmc
                      · rw [if_neg hcz_m1] at hmc
                        rcases hrun_mc : evaluateHOLFiniteState (callEntryStateHOLFinite m1 cmc) bmc with ⟨rmc0, pmc0⟩
                        rw [hrun_mc] at hmc
                        cases rmc0 with
                        | none => simp at hmc
                        | some c0 =>
                          cases c0 with
                          | returned v0 =>
                            dsimp only at hmc
                            by_cases hsh0 : shapeEqHOL (shapeOfHOLExact v0) rmc' = true
                            · simp [hsh0] at hmc
                            · simp [hsh0] at hmc
                          | exception _ _ => simp at hmc
                          | _ => simp at hmc
                | none =>
                  dsimp only at hseq_m1
                  have heff_m2 : WorldEff s m2 [] [] ["heap_ptr"] := by
                    have hw := worldEff_call0_memcpy_sc heff_m1
                      (.var .local (ofString "b")) (.var .local (ofString "a")) (.const 56#64)
                      (by rw [hmc]; simp) (by rw [hmc]; exact Or.inl rfl)
                      (fun dstw _ nw' hd _ hn _ => by
                        simp [evalHOLExact, hm1_b] at hd hn
                        subst hd hn
                        exact Or.inr (Or.inr (Or.inr ⟨hp_lo_s, hpw_hi⟩)))
                    rw [hmc] at hw; exact hw
                  have hm2_loc : m2.locals = m1.locals := by
                    have hk := fun k => evaluate_avoidsLocal_flowing k
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "b"), .var .local (ofString "a"), .const 56#64])
                      rfl m1 (by rw [hmc]; exact Or.inl rfl)
                    apply HolFiniteMapExact.ext; funext k; simpa [hmc] using hk k
                  rw [evaluateHOLFiniteState_return] at hseq_m1
                  simp only [evalHOLExact, hm2_loc, hm1_b, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                    show (1 : Nat) ≤ 32 by decide, ↓reduceIte, emptyLocalsHOLFinite] at hseq_m1
                  have hrv_pw_opt : (some (PanSemResultExact.returned (.val (.word pw))) : Option (PanSemResultExact 64)) =
                      some (PanSemResultExact.returned rv) :=
                    (Prod.mk.inj hseq_m1).1.trans hrseq_eq
                  injection hrv_pw_opt with hrv_eq
                  injection hrv_eq with hrv_eq'
                  subst hrv_eq'
                  have hpseq_eq : pseq = { m2 with locals := HolFiniteMapExact.empty } :=
                    ((Prod.mk.inj hseq_m1).2).symm
                  have hpc_m2 : pc = { m2 with locals := pc.locals, clock := pc.clock } := by
                    rw [hpc_pseq, hpseq_eq]
                  have heff_out : WorldEff s (setVarHOLFinite (ofString "a") (.val (.word pw)) { pc with locals := s.locals })
                      [] [] ["heap_ptr"] := by
                    rw [hpc_m2]; exact heff_m2.locals_clock _ _
                  exact ⟨heff_out, fun _ => ⟨pw, rfl, hp_lo_s, hpw_hi⟩⟩
              · rename_i hbad; simp only [hsh_rv, hbad, ↓reduceIte] at hfr; exact absurd hfr not_flowingOrResumes_error
            · rename_i hbad; simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hfr; exact absurd hfr not_flowingOrResumes_error

private theorem progWStep_acctCopy_mut_at_sc {B : BufList} {gw : List String} {F : Type}
    {s : PanSemStateFiniteExact 64 F}
    (hhp_in : "heap_ptr" ∈ gw) (mutProg : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hmut : ∀ (s1 : PanSemStateFiniteExact 64 F) (bw : BitVec 64),
      WorldEff s s1 [] [] ["heap_ptr"] →
      s1.locals = s.locals.update (ofString "a", .val (.word bw)) →
      s1.locals.lookup (ofString "a") = some (.val (.word bw)) →
      globN s "heap_ptr" ≤ bw.toNat → bw.toNat + 56 ≤ heapLimit →
      (evaluateHOLFiniteState s1 mutProg).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState s1 mutProg).1 →
      WorldEff s (evaluateHOLFiniteState s1 mutProg).2 [] [] ["heap_ptr"])
    (hnt : (evaluateHOLFiniteState s
      (.seq
        (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
          [.var .local (ofString "a")])
        mutProg)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.seq
        (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
          [.var .local (ofString "a")])
        mutProg)).1) :
    WorldStepSc (bufRegions B) gw stdKeep NoExtra s
      (evaluateHOLFiniteState s
        (.seq
          (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
            [.var .local (ofString "a")])
          mutProg)).1
      (evaluateHOLFiniteState s
        (.seq
          (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
            [.var .local (ofString "a")])
          mutProg)).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases h1 : evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")]) with ⟨r1, s1⟩
  simp only [h1] at hnt hfr ⊢
  cases r1 with
  | some cr1 =>
    have hac := acct_copy_step_sc s hc hW.1 (by rw [h1]; exact hnt) (by rw [h1]; exact hfr)
    rw [h1] at hac
    have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra s (some cr1) s1 :=
      hac.1.to_worldStep_Q hW (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
    exact WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp [hhp_in]) ⟨hws0, hac.1.sp_hi⟩
  | none =>
    dsimp only at hnt hfr ⊢
    have hac := acct_copy_step_sc s hc hW.1 (by rw [h1]; simp) (by rw [h1]; exact Or.inl rfl)
    rw [h1] at hac; dsimp only at hac
    obtain ⟨bw, hs1_loc, hbw_lo, hbw_hi⟩ := hac.2 rfl
    have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word bw)) := by
      rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hcr := contOrRes_of_flowingOrResumes_sc hfr
    have heff2 := hmut s1 bw hac.1 hs1_loc hs1_a hbw_lo hbw_hi hnt hcr
    have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra s
        (evaluateHOLFiniteState s1 mutProg).1 (evaluateHOLFiniteState s1 mutProg).2 :=
      heff2.to_worldStep_Q hW (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
    exact WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp [hhp_in]) ⟨hws0, heff2.sp_hi⟩

private theorem progWStep_acctCopy_mut_tail_at_sc {B : BufList} {gw : List String} {F : Type}
    {s : PanSemStateFiniteExact 64 F}
    (hB : ValidBufList B) (hgw : SafeStepGlobals gw)
    (hhp_in : "heap_ptr" ∈ gw) (mutProg tailProg : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hmut : ∀ (s1 : PanSemStateFiniteExact 64 F) (bw : BitVec 64),
      WorldEff s s1 [] [] ["heap_ptr"] →
      s1.locals = s.locals.update (ofString "a", .val (.word bw)) →
      s1.locals.lookup (ofString "a") = some (.val (.word bw)) →
      globN s "heap_ptr" ≤ bw.toNat → bw.toNat + 56 ≤ heapLimit →
      (evaluateHOLFiniteState s1 mutProg).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState s1 mutProg).1 →
      WorldEff s (evaluateHOLFiniteState s1 mutProg).2 [] [] ["heap_ptr"])
    (htail : ProgWStep B gw tailProg)
    (hnt : (evaluateHOLFiniteState s
      (.seq
        (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
          [.var .local (ofString "a")])
        (.seq mutProg tailProg))).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.seq
        (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
          [.var .local (ofString "a")])
        (.seq mutProg tailProg))).1) :
    WorldStepSc (bufRegions B) gw stdKeep NoExtra s
      (evaluateHOLFiniteState s
        (.seq
          (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
            [.var .local (ofString "a")])
          (.seq mutProg tailProg))).1
      (evaluateHOLFiniteState s
        (.seq
          (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
            [.var .local (ofString "a")])
          (.seq mutProg tailProg))).2 := by
  have hassoc : evaluateHOLFiniteState s
      (.seq
        (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
          [.var .local (ofString "a")])
        (.seq mutProg tailProg)) =
      evaluateHOLFiniteState s
        (.seq
          (.seq
            (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
              [.var .local (ofString "a")])
            mutProg)
          tailProg) := by
    simp only [evaluateHOLFiniteState_seq_line780]
    rcases evaluateHOLFiniteState s _ with ⟨r1, _⟩
    cases r1 <;> rfl
  rw [hassoc] at hnt hfr ⊢
  let p1 : ProgHOL 64 :=
    .seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")]) mutProg
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s p1).1
  dsimp only [p1] at hmeta
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases h1 : evaluateHOLFiniteState s p1 with ⟨r1, m⟩
  dsimp only [p1] at h1
  simp only [h1] at hmeta hnt hfr ⊢
  cases r1 with
  | some cr1 =>
    have hs1 := progWStep_acctCopy_mut_at_sc (B := B) (gw := gw) hhp_in mutProg hc hW hmut
      (by rw [h1]; exact hnt) (by rw [h1]; exact hfr)
    simpa [h1] using hs1
  | none =>
    have hs1 := progWStep_acctCopy_mut_at_sc (B := B) (gw := gw) hhp_in mutProg hc hW hmut
      (by rw [h1]; simp) (by rw [h1]; exact Or.inl rfl)
    simp only [h1] at hs1
    have hWm : WorldOK m := hs1.worldOK_bufs hB hW
    have hs2 := htail m (hmeta.trans hc) hWm hnt hfr
    exact WorldStepSc.trans hB hgw hs1 hs2

private theorem progWStep_decCall_keepLocals_sc {B Bf : BufList} {gw gwf : List String}
    {x : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64} {F : Type}
    {s : PanSemStateFiniteExact 64 F}
    (hBvalid : ValidBufList B) (hgwSafe : SafeStepGlobals gw)
    (hB : ∀ p ∈ Bf, p ∈ B) (hgw : ∀ g ∈ gwf, g ∈ gw)
    (hf : WorldKeepsSc WorldOK (bufRegions Bf) gwf stdKeep NoExtra fname)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hcont : ∀ (v : ValueHOL 64) (s1 : PanSemStateFiniteExact 64 F),
      shapeEqHOL (shapeOfHOLExact v) sh = true →
      s1.locals = s.locals.update (x, v) →
      s1.code = originalRuntimeCode →
      WorldOK s1 →
      (evaluateHOLFiniteState s1 cont).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState s1 cont).1 →
      WorldStepSc (bufRegions B) gw stdKeep NoExtra
        s1 (evaluateHOLFiniteState s1 cont).1 (evaluateHOLFiniteState s1 cont).2)
    (hnt : (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1) :
    WorldStepSc (bufRegions B) gw stdKeep NoExtra
      s (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1
      (evaluateHOLFiniteState s (.decCall x sh fname args cont)).2 := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        let ent := callEntryStateHOLFinite s callee
        have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata ent body').1
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun hmeta
        simp only [hrun] at hmeta hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
              simp only [ent, hrun] at hspec
              have hstep1 := (hspec (Or.inl ⟨v, rfl⟩)).mono_bufs hB hgw
              set s1 := setVarHOLFinite x v { cpost with locals := s.locals }
              have hs1_step : WorldStepSc (bufRegions B) gw stdKeep NoExtra s none s1 :=
                hstep1.from_entry
              have hWs1 : WorldOK s1 := hs1_step.worldOK_bufs hBvalid hW
              have hs1_code : s1.code = originalRuntimeCode := hmeta.trans hc
              have hsh1 : shapeEqHOL (shapeOfHOLExact v) sh = true := (Bool.and_eq_true _ _).mp hsh |>.1
              have hstep2 := hcont v s1 hsh1 rfl hs1_code hWs1 hnt hfr
              have hstep2' := hstep2.with_locals_clock (r' := (evaluateHOLFiniteState s1 cont).1)
                (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 cont).2.locals (x, s.locals.lookup x))
                (evaluateHOLFiniteState s1 cont).2.clock
              exact WorldStepSc.trans hBvalid hgwSafe hs1_step hstep2'
            · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            have hstep := (hspec hres_ex).mono_bufs hB hgw
            exact hstep.from_entry

theorem wkSc_set_code :
    WorldKeepsSc WorldOK (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
      (ofString "set_code") := by
  have hB := validBufList_acctMutBufs
  have hgw := safeStepGlobals_acctMut_sc
  have hhl_264 : heapLimit < 2 ^ 64 := by decide
  refine ⟨[(ofString "addr", .one), (ofString "code", .one), (ofString "code_len", .one)],
    sourceFnBody Guest.Software.guestFn_set_code, .one, lookup_set_code, ?_⟩
  intro F s0 hc0 hW0 hex0 hnt0 hres0
  obtain ⟨vs0, hlk_s0⟩ := hex0
  obtain ⟨waddr, wcode, wcl, _, hwaddr_s0, hwcode_s0, hwcl_s0⟩ :=
    Fast_C08WkShard03.lookupCode_three_words (by decide) (by decide) (by decide) lookup_set_code hlk_s0
  have hfr0 : FlowingOrResumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_set_code)).1 :=
    Or.inr (Or.inr (Or.inr hres0))
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_set_code,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map] at hnt0 hfr0 ⊢
  refine progWStep_decCall_alloc_seq_acctMut hc0 hW0
    (fun wh m1 hm1_loc _ heff_m1 hwh_lo hwh_end _ hnt_k hcr_k => by
      have hwh_hi : wh.toNat + 32 ≤ heapLimit := by
        change wh.toNat + (32 + 7) / 8 * 8 = globN m1 "heap_ptr" at hwh_end; omega
      have hm1_h : m1.locals.lookup (ofString "h") = some (.val (.word wh)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hm1_code : m1.locals.lookup (ofString "code") = some (.val (.word wcode)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hwcode_s0,
          show ofString "h" ≠ ofString "code" by decide]
      have hm1_cl : m1.locals.lookup (ofString "code_len") = some (.val (.word wcl)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hwcl_s0,
          show ofString "h" ≠ ofString "code_len" by decide]
      have hkpad_m1 : Fast_C08WkShard03.globMapN m1.globals "keccak_pad" = globN s0 "keccak_pad" :=
        globN_eq_of_lookup (heff_m1.gw_kept (ofString "keccak_pad") (by decide))
      have hkst_m1 : Fast_C08WkShard03.globMapN m1.globals "keccak_st" = globN s0 "keccak_st" :=
        globN_eq_of_lookup (heff_m1.gw_kept (ofString "keccak_st") (by decide))
      exact worldEff_call0_funByteEff_sc heff_m1 Fast_C08WkShard03.funByteEff_keccak256 _
        [bufferRegion s0 ("keccak_st", 200), bufferRegion s0 ("keccak_pad", 136), (wh.toNat, 32)]
        (fun vals hargs i hi _ => by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact, evalHOLExact, hm1_code, hm1_cl, hm1_h] at hargs
          injection hargs with hargs_eq; subst hargs_eq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl
          · refine ⟨bufferRegion s0 ("keccak_st", 200), List.mem_cons_self, ?_, ?_⟩ <;>
              simp [Fast_C08WkShard03.globBufIvl, bufferRegion, hkst_m1]
          · refine ⟨bufferRegion s0 ("keccak_pad", 136), List.mem_cons_of_mem _ List.mem_cons_self, ?_, ?_⟩ <;>
              simp [Fast_C08WkShard03.globBufIvl, bufferRegion, hkpad_m1]
          · refine ⟨(wh.toNat, 32), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_, ?_⟩ <;>
              simp [Fast_C08WkShard03.valWordNat])
        (fun iv hiv _ => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
          rcases hiv with rfl | rfl | rfl
          · exact Or.inr (Or.inl ⟨("keccak_st", 200), by decide, le_rfl, le_rfl⟩)
          · exact Or.inr (Or.inl ⟨("keccak_pad", 136), by decide, le_rfl, le_rfl⟩)
          · exact Or.inr (Or.inr (Or.inr ⟨hwh_lo, hwh_hi⟩)))
        hnt_k hcr_k)
    (fun wh m2 _ _ hm2_loc hc2 hW2 hnt2 hfr2 => ?_)
    (fun m1 hnone => call0_none_locals_sc m1 (ofString "keccak256") _ hnone)
    hnt0 hfr0
  have hm2_h : m2.locals.lookup (ofString "h") = some (.val (.word wh)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_code : m2.locals.lookup (ofString "code") = some (.val (.word wcode)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hwcode_s0,
      show ofString "h" ≠ ofString "code" by decide]
  have hm2_cl : m2.locals.lookup (ofString "code_len") = some (.val (.word wcl)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hwcl_s0,
      show ofString "h" ≠ ofString "code_len" by decide]
  refine progWStep_decCall_keepLocals_sc hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsSc_of_readOnly Wave8Contracts.M15.«ro_memeq») hc2 hW2
    (fun veq m3 _ hm3_loc hc3 hW3 hnt3 hfr3 => ?_) hnt2 hfr2
  have hm3_h : m3.locals.lookup (ofString "h") = some (.val (.word wh)) := by
    rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_h,
      show ofString "eq" ≠ ofString "h" by decide]
  have hm3_code : m3.locals.lookup (ofString "code") = some (.val (.word wcode)) := by
    rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_code,
      show ofString "eq" ≠ ofString "code" by decide]
  have hm3_cl : m3.locals.lookup (ofString "code_len") = some (.val (.word wcl)) := by
    rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_cl,
      show ofString "eq" ≠ ofString "code_len" by decide]
  let pIte : ProgHOL 64 :=
    .ite (.cmp .equal (.var .local (ofString "eq")) (.const 0#64))
      (.decCall (ofString "sl") .one (ofString "alloc") [.const 16#64]
        (.seq (.store (.var .local (ofString "sl")) (.var .local (ofString "code")))
          (.seq (.store (.op .add [.var .local (ofString "sl"), .const 8#64]) (.var .local (ofString "code_len")))
            (.call (some (none, none)) (ofString "jset")
              [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]),
               .var .local (ofString "h"), .var .local (ofString "sl")]))))
      .skip
  have hIte_avoids : ∀ k : MlS, avoidsLocal k pIte = true := by
    intro k
    dsimp only [pIte, avoidsLocal]
    by_cases hk : k == ofString "sl"
    · simp [hk]
    · simp [hk]
  have hIte_step : ∀ (hnt_i : (evaluateHOLFiniteState m3 pIte).1 ≠ some .timeOut)
      (hfr_i : FlowingOrResumes (evaluateHOLFiniteState m3 pIte).1),
      WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
        m3 (evaluateHOLFiniteState m3 pIte).1 (evaluateHOLFiniteState m3 pIte).2 := by
    intro hnt_i hfr_i
    dsimp only [pIte] at hnt_i hfr_i ⊢
    rw [evaluateHOLFiniteState_ite] at hnt_i hfr_i ⊢
    rcases hev_c : @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
        (.cmp .equal (.var .local (ofString "eq")) (.const 0#64)) with _ | cv
    · simp [hev_c] at hfr_i; exact absurd hfr_i not_flowingOrResumes_error
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _
      · simp only [hev_c] at hnt_i hfr_i ⊢
        by_cases hcw : cw = 0
        · simp only [hcw, ↓reduceIte] at hnt_i hfr_i ⊢
          exact progWStep_skip acctMutBufs ["heap_ptr", "journal_n", "scratch_ptr"] m3 hc3 hW3 hnt_i hfr_i
        · simp only [hcw, ↓reduceIte] at hnt_i hfr_i ⊢
          have hassoc_br : ∀ (st : PanSemStateFiniteExact 64 F),
              evaluateHOLFiniteState st
                (.seq (.store (.var .local (ofString "sl")) (.var .local (ofString "code")))
                  (.seq (.store (.op .add [.var .local (ofString "sl"), .const 8#64]) (.var .local (ofString "code_len")))
                    (.call (some (none, none)) (ofString "jset")
                      [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]),
                       .var .local (ofString "h"), .var .local (ofString "sl")]))) =
              evaluateHOLFiniteState st
                (.seq
                  (.seq (.store (.var .local (ofString "sl")) (.var .local (ofString "code")))
                    (.store (.op .add [.var .local (ofString "sl"), .const 8#64]) (.var .local (ofString "code_len"))))
                  (.call (some (none, none)) (ofString "jset")
                    [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]),
                     .var .local (ofString "h"), .var .local (ofString "sl")])) := by
            intro st; simp only [evaluateHOLFiniteState_seq_line780]
            rcases evaluateHOLFiniteState st _ with ⟨r1, _⟩; cases r1 <;> rfl
          have hdec_assoc :
              evaluateHOLFiniteState m3
                (.decCall (ofString "sl") .one (ofString "alloc") [.const 16#64]
                  (.seq (.store (.var .local (ofString "sl")) (.var .local (ofString "code")))
                    (.seq (.store (.op .add [.var .local (ofString "sl"), .const 8#64]) (.var .local (ofString "code_len")))
                      (.call (some (none, none)) (ofString "jset")
                        [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]),
                         .var .local (ofString "h"), .var .local (ofString "sl")])))) =
              evaluateHOLFiniteState m3
                (.decCall (ofString "sl") .one (ofString "alloc") [.const 16#64]
                  (.seq
                    (.seq (.store (.var .local (ofString "sl")) (.var .local (ofString "code")))
                      (.store (.op .add [.var .local (ofString "sl"), .const 8#64]) (.var .local (ofString "code_len"))))
                    (.call (some (none, none)) (ofString "jset")
                      [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]),
                       .var .local (ofString "h"), .var .local (ofString "sl")]))) := by
            simp only [evaluateHOLFiniteState_decCall_fixClockRewrite]
            rcases evalListHOLFinite m3 (h := fun a => Classical.propDecidable (m3.memaddrs a)) [.const 16#64] with _ | vs_a; · rfl
            dsimp only
            rcases lookupCodeHOLFinite m3.code.lookup (ofString "alloc") vs_a with _ | ⟨ba, ca, ra⟩; · rfl
            dsimp only
            split; · rfl
            rcases evaluateHOLFiniteState (callEntryStateHOLFinite m3 ca) ba with ⟨ra0, pa0⟩
            cases ra0 with
            | none => rfl
            | some cra =>
              cases cra with
              | returned rva =>
                dsimp only
                by_cases hsh_a : (shapeEqHOL (shapeOfHOLExact rva) .one && shapeEqHOL (shapeOfHOLExact rva) ra) = true
                · rw [if_pos hsh_a, if_pos hsh_a, hassoc_br]
                · rw [if_neg hsh_a, if_neg hsh_a]
              | _ => rfl
          rw [hdec_assoc] at hnt_i hfr_i ⊢
          refine progWStep_decCall_alloc_seq_acctMut hc3 hW3
            (fun wsl ms1 hms1_loc _ heff_ms1 hwsl_lo hwsl_end _ hnt_st hcr_st => by
              have hwsl_hi : wsl.toNat + 16 ≤ heapLimit := by
                change wsl.toNat + (16 + 7) / 8 * 8 = globN ms1 "heap_ptr" at hwsl_end; omega
              have hms1_sl : ms1.locals.lookup (ofString "sl") = some (.val (.word wsl)) := by
                rw [hms1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
              have hms1_code : ms1.locals.lookup (ofString "code") = some (.val (.word wcode)) := by
                rw [hms1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm3_code,
                  show ofString "sl" ≠ ofString "code" by decide]
              have hms1_cl : ms1.locals.lookup (ofString "code_len") = some (.val (.word wcl)) := by
                rw [hms1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm3_cl,
                  show ofString "sl" ≠ ofString "code_len" by decide]
              refine worldEff_seq hnt_st hcr_st
                (fun _ _ => worldEff_store_word heff_ms1 _ _
                  (fun v hv => by simp [evalHOLExact, hms1_code] at hv; exact ⟨wcode, hv.symm⟩)
                  (fun x hx _ => by
                    simp [evalHOLExact, hms1_sl] at hx; subst hx
                    exact Or.inr (Or.inr (Or.inr ⟨hwsl_lo, by omega⟩))))
                (fun ms2 hms2 heff_ms2 _ _ => ?_)
              have hms2_loc : ms2.locals = ms1.locals := by
                have hk := fun k => evaluate_avoidsLocal_flowing k
                  (.store (.var .local (ofString "sl")) (.var .local (ofString "code")))
                  rfl ms1 (by rw [hms2]; exact Or.inl rfl)
                apply HolFiniteMapExact.ext; funext k; simpa [hms2] using hk k
              exact worldEff_store_word heff_ms2 _ _
                (fun v hv => by simp [evalHOLExact, hms2_loc, hms1_cl] at hv; exact ⟨wcl, hv.symm⟩)
                (fun x hx _ => by
                  simp [evalHOLExact, evalListHOLExact, hms2_loc, hms1_sl, panOpHOL, wordOpHOL, wordOp,
                    valueIsWord, valueWord] at hx
                  subst hx
                  have hx8 : (wsl + 8#64).toNat = wsl.toNat + 8 := by
                    apply BitVec.toNat_add_of_lt; change wsl.toNat + 8 < 2 ^ 64; omega
                  exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
            (fun wsl ms3 _ _ _ hcms3 hWms3 hnt_j hfr_j =>
              progWStep_call0_jset_ts48 (B := acctMutBufs) (gw := ["heap_ptr", "journal_n", "scratch_ptr"])
                (by simp) (by simp) _ _ ms3 hcms3 hWms3 hnt_j hfr_j)
            (fun ms1 hnone_st => by
              apply HolFiniteMapExact.ext; funext k
              exact evaluate_avoidsLocal_flowing k _ rfl ms1 (Or.inl hnone_st))
            hnt_i hfr_i
      · simp [hev_c] at hfr_i; exact absurd hfr_i not_flowingOrResumes_error
      · simp [hev_c] at hfr_i; exact absurd hfr_i not_flowingOrResumes_error
  change WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
    m3 (evaluateHOLFiniteState m3 (.seq pIte _)).1 (evaluateHOLFiniteState m3 (.seq pIte _)).2
  have hmeta_i := (PanRunBounded.evaluateHOLFiniteState_metadata m3 pIte).1
  rw [evaluateHOLFiniteState_seq_line780] at hnt3 hfr3 ⊢
  rcases hri : evaluateHOLFiniteState m3 pIte with ⟨ri, m4⟩
  have hri_def : evaluateHOLFiniteState m3
      (.ite (.cmp .equal (.var .local (ofString "eq")) (.const 0#64))
        (.decCall (ofString "sl") .one (ofString "alloc") [.const 16#64]
          (.seq (.store (.var .local (ofString "sl")) (.var .local (ofString "code")))
            (.seq (.store (.op .add [.var .local (ofString "sl"), .const 8#64]) (.var .local (ofString "code_len")))
              (.call (some (none, none)) (ofString "jset")
                [.load .one (.op .add [.var .global (ofString "ts"), .const 48#64]),
                 .var .local (ofString "h"), .var .local (ofString "sl")]))))
        .skip) = (ri, m4) := hri
  simp only [hri, hri_def] at hmeta_i hnt3 hfr3 ⊢
  cases ri with
  | some cri =>
    have hs_i := hIte_step (by rw [hri]; exact hnt3) (by rw [hri]; exact hfr3)
    rw [hri] at hs_i; exact hs_i
  | none =>
    dsimp only at hnt3 hfr3 ⊢
    have hs_i := hIte_step (by rw [hri]; simp) (by rw [hri]; exact Or.inl rfl)
    rw [hri] at hs_i; dsimp only at hs_i
    have hW4 : WorldOK m4 := hs_i.worldOK_bufs hB hW3
    have hc4 : m4.code = originalRuntimeCode := hmeta_i.trans hc3
    have hm4_loc : m4.locals = m3.locals := by
      apply HolFiniteMapExact.ext; funext k
      have hk := evaluate_avoidsLocal_flowing k pIte (hIte_avoids k) m3 (by rw [hri]; exact Or.inl rfl)
      simpa [hri] using hk
    have hm4_h : m4.locals.lookup (ofString "h") = some (.val (.word wh)) := by
      rw [hm4_loc]; exact hm3_h
    refine WorldStepSc.trans hB hgw hs_i ?_
    refine progWStep_decCall_keepLocals_sc hB hgw
      (by intro p hp; simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs])
      (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
      wkSc_get_account hc4 hW4
      (fun va m5 _ hm5_loc hc5 hW5 hnt5 hfr5 => ?_) hnt3 hfr3
    have hm5_h : m5.locals.lookup (ofString "h") = some (.val (.word wh)) := by
      rw [hm5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm4_h,
        show ofString "a" ≠ ofString "h" by decide]
    exact progWStep_acctCopy_mut_tail_at_sc hB hgw (by simp) _ _ hc5 hW5
      (fun s1_ac bw heff1 hs1_ac_loc hs1_ac_a hbw_lo hbw_hi _ _ =>
        worldEff_store_word heff1 _ _
          (fun v hv => by
            have hs1_h : s1_ac.locals.lookup (ofString "h") = some (.val (.word wh)) := by
              rw [hs1_ac_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm5_h,
                show ofString "a" ≠ ofString "h" by decide]
            simp [evalHOLExact, hs1_h] at hv
            exact ⟨wh, hv.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, hs1_ac_a, panOpHOL, wordOpHOL, wordOp,
              valueIsWord, valueWord] at hx
            subst hx
            have hx48 : (bw + 48#64).toNat = bw.toNat + 48 := by
              apply BitVec.toNat_add_of_lt; change bw.toNat + 48 < 2 ^ 64; omega
            exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
      (progWStep_seq hB hgw
        (progWStep_call0 (by intro p hp; simp at hp; subst hp; simp [acctMutBufs])
          (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp) wkSc_modify_state_commit)
        (progWStep_return _ _ _))
      hnt5 hfr5

end SetCode

section CreateFinish

open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Contracts.M08
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

def wordsOfCallees (f : MlS) : Bool :=
  f == ofString "ceil32" || f == ofString "add_sat"

theorem wordsOfCallees_good :
    ∀ f, wordsOfCallees f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs) →
      roProgR16 wordsOfCallees body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
  simp only [wordsOfCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with rfl | rfl
  · have hl := lookup_of_guestAst_getElem 442 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_ceil32) rfl
    change originalRuntimeCode.lookup (ofString "ceil32") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 441 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_add_sat) rfl
    change originalRuntimeCode.lookup (ofString "add_sat") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide

theorem ro_words_of : ReadOnlyFn (ofString "words_of") :=
  readOnlyFn_of_roProgR16 443 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_words_of rfl wordsOfCallees wordsOfCallees_good (by decide)

def createFinishAvoids : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl :=
  fun s => [
    (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
    (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
    (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
    (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)]

theorem evmStep_refl_gw {F : Type} {gw : List String} {s : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) : EvmStep gw s s :=
  ⟨hInv, le_rfl, fun _ _ => rfl, rfl⟩

theorem evmStep_with_locals_clock {F : Type} {gw : List String}
    {s post : PanSemStateFiniteExact 64 F}
    (h : EvmStep gw s post) (ls : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    EvmStep gw s { post with locals := ls, clock := k } :=
  ⟨localsFree_evmInv post ls k h.1, h.2.1, h.2.2.1,
    (evmChain_with_locals post ls k).trans h.2.2.2⟩

theorem evmStep_mono_gw {F : Type} {gw1 gw2 : List String}
    {s post : PanSemStateFiniteExact 64 F}
    (hsub : ∀ g, g ∈ gw1.map ofString → g ∈ gw2.map ofString)
    (h : EvmStep gw1 s post) : EvmStep gw2 s post :=
  ⟨h.1, h.2.1, fun g hg => h.2.2.1 g (fun hm => hg (hsub g hm)), h.2.2.2⟩

theorem evmStep_trans {F : Type} {gw : List String}
    {a b c : PanSemStateFiniteExact 64 F}
    (h1 : EvmStep gw a b) (h2 : EvmStep gw b c) : EvmStep gw a c :=
  ⟨h2.1, le_trans h1.2.1 h2.2.1,
    fun g hg => (h1.2.2.1 g hg).trans (h2.2.2.1 g hg),
    h2.2.2.2.trans h1.2.2.2⟩

private theorem lex_only_sc {a1 a2 b1 b2 : Nat} (h : a1 < a2 ∨ a1 = a2 ∧ b1 < b2) :
    Prod.Lex (· < ·) (· < ·) (a1, b1) (a2, b2) := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h

def onlyEvmOrTrapRaise (good : MlS → Bool) : ProgHOL 64 → Bool
  | .skip | .«break» | .«continue» | .annot _ _ | .«return» _
  | .assign _ _ _ | .store _ _ | .storeByte _ _ | .store32 _ _
  | .shMemStore _ _ _ | .extCall _ _ _ _ _ | .primitive _ _ _ => true
  | .raise name _ => name == ofString "TrapErr" || name == ofString "EvmErr"
  | .dec _ _ _ body | .«while» _ body => onlyEvmOrTrapRaise good body
  | .seq a b | .ite _ a b => onlyEvmOrTrapRaise good a && onlyEvmOrTrapRaise good b
  | .decCall _ _ fn _ cont => good fn && onlyEvmOrTrapRaise good cont
  | .call (some (_, none)) fn _ => good fn
  | .tick | .shMemLoad _ _ _ _ | .call none _ _ | .call (some (_, some _)) _ _ => false

theorem evaluate_onlyEvmOrTrapRaise {F : Type} (good : MlS → Bool)
    (hgood : ∀ f, good f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      onlyEvmOrTrapRaise good body = true)
    (p : ProgHOL 64) (hp : onlyEvmOrTrapRaise good p = true)
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode) :
    ∀ eid v, eid ≠ ofString "TrapErr" → eid ≠ ofString "EvmErr" →
      (evaluateHOLFiniteState s p).1 ≠ some (.exception eid v) := by
  cases shape : p with
  | tick => simp [shape, onlyEvmOrTrapRaise] at hp
  | skip => rw [evaluateHOLFiniteState_skip]; simp
  | «break» => rw [evaluateHOLFiniteState_break]; simp
  | «continue» => rw [evaluateHOLFiniteState_continue]; simp
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; simp
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]; split <;> [simp; (split <;> simp)]
  | assign _ _ _ =>
    rw [evaluateHOLFiniteState_assign]; split <;> [simp; (split <;> simp)]
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]; split <;> [(split <;> [(split <;> simp); simp]); simp]
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]; split <;> [(split <;> [(split <;> simp); simp]); simp]
  | store32 _ _ =>
    rw [evaluateHOLFiniteState_store32]; split <;> [(split <;> [(split <;> simp); simp]); simp]
  | shMemStore _ _ _ =>
    rw [evaluateHOLFiniteState_shMemStore_total]; dsimp only
    split
    · unfold shMemStoreHOLExact
      split <;> split
      all_goals simp [ofExact, toExact]
      all_goals split <;> simp
    · simp
  | shMemLoad _ _ _ _ => simp [shape, onlyEvmOrTrapRaise] at hp
  | extCall _ _ _ _ _ =>
    rw [evaluateHOLFiniteState_extCall_source]
    split <;> [ (split <;> [ (split <;> simp); simp ]); simp ]
  | primitive _ _ _ =>
    rw [evaluateHOLFiniteState_primitive]; split <;> [simp; (split <;> [simp; (split <;> simp)])]
  | raise name _ =>
    have hname : name = ofString "TrapErr" ∨ name = ofString "EvmErr" := by
      simpa [shape, onlyEvmOrTrapRaise, Bool.or_eq_true, beq_iff_eq] using hp
    intro eid v hneT hneE
    rw [evaluateHOLFiniteState_raise]
    rcases hname with rfl | rfl
    · split
      · dsimp only; split <;> [simp [hneT.symm]; simp]
      · simp
    · split
      · dsimp only; split <;> [simp [hneE.symm]; simp]
      · simp
  | dec name _ _ body =>
    have hb : onlyEvmOrTrapRaise good body = true := by simpa [shape, onlyEvmOrTrapRaise] using hp
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · simp
    · rename_i val _
      split
      · exact evaluate_onlyEvmOrTrapRaise good hgood body hb (setVarHOLFinite name val s) hcode
      · simp
  | seq a b =>
    have hab : onlyEvmOrTrapRaise good a = true ∧ onlyEvmOrTrapRaise good b = true := by
      simpa [shape, onlyEvmOrTrapRaise, Bool.and_eq_true] using hp
    have ih1 := evaluate_onlyEvmOrTrapRaise good hgood a hab.1 s hcode
    have rem := evaluateHOLFiniteState_clock_le s a
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata s a
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr : evaluateHOLFiniteState s a with ⟨r1, mid⟩
    rw [hr] at ih1 rem meta'
    dsimp only at ih1 rem meta' ⊢
    cases r1 with
    | none =>
      have mclock : mid.clock ≤ s.clock := rem
      exact evaluate_onlyEvmOrTrapRaise good hgood b hab.2 mid (meta'.1.trans hcode)
    | some _ => exact ih1
  | ite _ yes no =>
    have hy : onlyEvmOrTrapRaise good yes = true ∧ onlyEvmOrTrapRaise good no = true := by
      simpa [shape, onlyEvmOrTrapRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_onlyEvmOrTrapRaise good hgood no hy.2 s hcode
      · exact evaluate_onlyEvmOrTrapRaise good hgood yes hy.1 s hcode
    · simp
  | «while» cond body =>
    have hb : onlyEvmOrTrapRaise good body = true := by simpa [shape, onlyEvmOrTrapRaise] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_onlyEvmOrTrapRaise good hgood body hb (decClockHOLFinite s) hcode
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem meta'
          dsimp only at ih1 rem meta' ⊢
          have smaller : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
          have mCode : mid.code = originalRuntimeCode := meta'.1.trans hcode
          cases r1 with
          | none =>
            exact evaluate_onlyEvmOrTrapRaise good hgood (.while cond body) (by simpa [onlyEvmOrTrapRaise] using hb) mid mCode
          | some r =>
            cases r with
            | «continue» =>
              exact evaluate_onlyEvmOrTrapRaise good hgood (.while cond body) (by simpa [onlyEvmOrTrapRaise] using hb) mid mCode
            | «break» => simp
            | _ => exact ih1
      · simp
    · simp
  | decCall name _ fn args cont =>
    have hc : good fn = true ∧ onlyEvmOrTrapRaise good cont = true := by
      simpa [shape, onlyEvmOrTrapRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
    · simp
    · dsimp only
      rcases hl : lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨body, callee, rs⟩
      · simp
      · dsimp only
        have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fn values = some (body, callee, rs) := by rwa [← hcode]
        have bodyOk := hgood fn hc.1 values body callee rs hl'
        split
        · simp
        · have ih1 := evaluate_onlyEvmOrTrapRaise good hgood body bodyOk (callEntryStateHOLFinite s callee) hcode
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
          rw [hrun] at ih1 meta' cl
          dsimp only at ih1 meta' cl ⊢
          change st.clock ≤ s.clock - 1 at cl
          have small : st.clock < s.clock := by omega
          have stCode : st.code = originalRuntimeCode := meta'.1.trans hcode
          cases res with
          | none => simp
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · set resumed := setVarHOLFinite name v { st with locals := s.locals }
                have smallR : resumed.clock < s.clock := small
                have rCode : resumed.code = originalRuntimeCode := stCode
                exact evaluate_onlyEvmOrTrapRaise good hgood cont hc.2 resumed rCode
              · simp
            | «break» => simp
            | «continue» => simp
            | _ => exact ih1
  | call tail fn args =>
    cases tail with
    | none => simp [shape, onlyEvmOrTrapRaise] at hp
    | some th =>
      rcases th with ⟨dst, hdl⟩
      cases hdl with
      | some _ => simp [shape, onlyEvmOrTrapRaise] at hp
      | none =>
        have hf : good fn = true := by simpa [shape, onlyEvmOrTrapRaise] using hp
        rw [evaluateHOLFiniteState_call]
        rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
        · simp
        · dsimp only
          rcases hl : lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨body, callee, rs⟩
          · simp
          · dsimp only
            have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fn values = some (body, callee, rs) := by rwa [← hcode]
            have bodyOk := hgood fn hf values body callee rs hl'
            split
            · simp
            · have ih1 := evaluate_onlyEvmOrTrapRaise good hgood body bodyOk (callEntryStateHOLFinite s callee) hcode
              have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
              rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
              rw [hrun] at ih1 cl
              dsimp only at ih1 cl ⊢
              change st.clock ≤ s.clock - 1 at cl
              have small : st.clock < s.clock := by omega
              cases res with
              | none => simp
              | some r =>
                cases r with
                | returned v =>
                  dsimp only
                  split
                  · cases dst with
                    | none => simp
                    | some d =>
                      rcases d with ⟨k, x⟩
                      cases k <;> (dsimp only; split <;> simp)
                  · simp
                | «break» => simp
                | «continue» => simp
                | _ => exact ih1
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply lex_only_sc
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite, ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec,
      ProgHOL.call.sizeOf_spec]
    first
      | exact Or.inl small
      | exact Or.inl smaller
      | exact Or.inl smallR
      | exact Or.inl (by omega)
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · right; refine ⟨h, ?_⟩; simp +arith)
      | (right; refine ⟨rfl, ?_⟩; simp +arith)
      | (right; refine ⟨trivial, ?_⟩; simp +arith)

theorem addSatOnlyCallees_good :
    ∀ f, (f == ofString "add_sat") = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs) →
      onlyEvmOrTrapRaise (fun g => g == ofString "add_sat") body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
  simp only [beq_iff_eq] at hf; subst hf
  rw [lookup_add_sat] at hinst
  rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]
  decide

theorem evmStep_of_eps_call0 {F : Type} {gw : List String}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} (hf : EvmPreservingSpec (fun _ => True) Qc fname)
    (honly : ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, rs) →
      ∃ good, (∀ f, good f = true → ∀ vs b c r,
        lookupCodeHOLFinite originalRuntimeCode.lookup f vs = some (b, c, r) →
        onlyEvmOrTrapRaise good b = true) ∧ onlyEvmOrTrapRaise good body = true)
    (hg_ret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v post, Qc s v post → post.globals = s.globals)
    (hg_err : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) body,
      s.code = originalRuntimeCode → EvmInv s →
      (∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs = some (body, s.locals, .one)) →
      IsEvmErr (evaluateHOLFiniteState s body).1 →
      (evaluateHOLFiniteState s body).2.globals = s.globals)
    (hret1 : ∀ params body retShape,
      originalRuntimeCode.lookup fname = some (params, body, retShape) → retShape = .one)
    (args : List (ExpHOL 64))
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1) :
    EvmStep gw s (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2 ∧
    ((evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none →
      (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2.locals = s.locals ∧
      (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2.code = originalRuntimeCode) := by
  obtain ⟨params_f, body_f, ret_f, hlook_f, hspec_f⟩ := hf
  have hrf1 : ret_f = .one := hret1 params_f body_f ret_f hlook_f
  subst hrf1
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname vs = some (body', callee, ret') := by
          rwa [← hc]
        have hsame := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup fname
          params_f body_f body' .one ret' vs callee hlook_f hl_orig
        have hret_eq := lookupCodeHOLFinite_installed_return s fname
          params_f body_f body' .one ret' vs callee (by rw [hc]; exact hlook_f) hl
        subst hsame
        subst hret_eq
        let ent := callEntryStateHOLFinite s callee
        have hInv_ent : EvmInv ent := localsFree_evmInv s callee (s.clock - 1) hInv
        have hent_code : ent.code = originalRuntimeCode := hc
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata ent body').1
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨cres, cpost⟩
        simp only [ent] at hrun hmeta
        simp only [hrun] at hmeta hnt hfr ⊢
        have hnt_ent : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        have hsp := hspec_f ent hent_code hInv_ent trivial ⟨vs, hl_orig⟩ hnt_ent
        simp only [ent, hrun] at hsp
        cases cres with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some r =>
          cases r with
          | timeOut => simp at hnt
          | «break» | «continue» | error =>
            exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ =>
            exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) .one = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              obtain ⟨hInv_cp, hch_cp, _, hqc⟩ := hsp.1 v rfl
              have hg_cp : cpost.globals = s.globals := hg_ret ent v cpost hqc
              have hInv_out : EvmInv { cpost with locals := s.locals } :=
                localsFree_evmInv cpost s.locals cpost.clock hInv_cp
              have hhp_eq : globN { cpost with locals := s.locals } "heap_ptr" = globN s "heap_ptr" := by
                simp [globN, hg_cp]
              have hgk : GlobalsKept gw s { cpost with locals := s.locals } := by
                intro g _; simp [hg_cp]
              have hch_out : evmChain { cpost with locals := s.locals } = evmChain s := by
                rw [evmChain_with_locals cpost s.locals cpost.clock, hch_cp]
                exact evmChain_with_locals s callee (s.clock - 1)
              exact ⟨⟨hInv_out, le_of_eq hhp_eq.symm, hgk, hch_out⟩, fun _ => ⟨by simp, hmeta.trans hc⟩⟩
            · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hnt_trap : eid ≠ ofString "TrapErr" := by
              rcases hfr with h | h | h | (⟨_, hc'⟩ | ⟨e', v', hc', hnt_e⟩)
              · simp at h
              · simp at h
              · simp at h
              · simp at hc'
              · injection hc' with hc'; injection hc' with he _; subst he; exact hnt_e
            obtain ⟨good, hgood, hbody_only⟩ := honly vs body' callee .one hl_orig
            have hevm : eid = ofString "EvmErr" := by
              by_contra hneE
              have habs := evaluate_onlyEvmOrTrapRaise good hgood body' hbody_only ent hent_code eid ev hnt_trap hneE
              simp only [ent, hrun] at habs; exact habs rfl
            subst hevm
            obtain ⟨hInv_cp, hch_cp, _⟩ := hsp.2 ⟨ev, rfl⟩
            have hg_cp : cpost.globals = s.globals := by
              have hge := hg_err ent body' hent_code hInv_ent ⟨vs, hl_orig⟩ (by simp only [ent, hrun]; exact ⟨ev, rfl⟩)
              simp only [ent, hrun] at hge
              exact hge
            have hInv_out : EvmInv cpost.emptyLocalsHOLFinite :=
              localsFree_evmInv cpost cpost.emptyLocalsHOLFinite.locals cpost.clock hInv_cp
            have hhp_eq : globN cpost.emptyLocalsHOLFinite "heap_ptr" = globN s "heap_ptr" := by
              simp [emptyLocalsHOLFinite, globN, hg_cp]
            have hgk : GlobalsKept gw s cpost.emptyLocalsHOLFinite := by
              intro g _; simp [emptyLocalsHOLFinite, hg_cp]
            have hch_out : evmChain cpost.emptyLocalsHOLFinite = evmChain s := by
              change evmChain { cpost with locals := cpost.emptyLocalsHOLFinite.locals, clock := cpost.clock } = evmChain s
              rw [evmChain_with_locals cpost cpost.emptyLocalsHOLFinite.locals cpost.clock, hch_cp]
              exact evmChain_with_locals s callee (s.clock - 1)
            exact ⟨⟨hInv_out, le_of_eq hhp_eq.symm, hgk, hch_out⟩, fun h => by simp at h⟩

theorem evm_buffer_part_sc {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hi : EvmInvAt s S) (hw : WorldTypedWith s S Nd)
    (gn : String × Nat) (hg : gn ∈ globalBuffers)
    (hu : gn.1 ∉ typedRecords.map Prod.fst) (n : Nat) (hn : n ≤ gn.2) :
    ∀ j ∈ worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten,
      Disj (bufferRegion s (gn.1, n)) j := by
  intro j hj
  rcases List.mem_append.mp hj with hj | hj
  · exact bufferRegion_disj_le hw gn hg hu n hn j hj
  · obtain ⟨os, hos, hj⟩ := List.mem_flatten.mp hj
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.mp hos
    have hf : bufferRegion s gn ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨gn, hg, rfl⟩
    have hd := (hi.2.2.2.2.2.2.2.2.1 ec hec j hj).2 _ hf
    have hd := hd.flip
    by_cases hz : globN s gn.1 = 0
    · exact Or.inl (by simp [bufferRegion, hz])
    · simp only [bufferRegion, hz, ↓reduceIte] at hd ⊢
      unfold Disj at hd ⊢
      dsimp only at hd ⊢
      omega

theorem evm_createFinishAvoids {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    EvmAvoids createFinishAvoids s := by
  obtain ⟨ha, S, hi⟩ := h
  obtain ⟨Nd, hw⟩ := (worldTyped_iff_with s S).mp hi.1
  refine ⟨ha, S, hi, Nd, hw.2.2.2, ?_⟩
  intro i hm
  simp only [createFinishAvoids, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact evm_buffer_part_sc hi hw ("keccak_pad", 136) (by decide) (by decide) 136 (by decide)
  · exact evm_buffer_part_sc hi hw ("keccak_st", 200) (by decide) (by decide) 200 (by decide)
  · exact evm_buffer_part_sc hi hw ("mpt_nib_scratch", 64) (by decide) (by decide) 64 (by decide)
  · exact evm_buffer_part_sc hi hw ("sk_buf", 64) (by decide) (by decide) 52 (by decide)

theorem addSatOnly_keepsG_good (watched : MlS) :
    ∀ f, (f == ofString "add_sat") = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs) →
      keepsG watched (fun g => g == ofString "add_sat") body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
  simp only [beq_iff_eq] at hf; subst hf
  rw [lookup_add_sat] at hinst
  rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]
  rfl

theorem charge_gas_keeps_globals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_charge_gas)).2.globals = s.globals := by
  apply HolFiniteMapExact.ext; funext k
  exact evaluate_keepsG k (fun _ => false) (fun _ h => by simp at h)
    (sourceFnBody Guest.Software.guestFn_charge_gas) rfl s hc

theorem charge_state_gas_keeps_globals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_charge_state_gas)).2.globals = s.globals := by
  apply HolFiniteMapExact.ext; funext k
  exact evaluate_keepsG k (fun g => g == ofString "add_sat") (addSatOnly_keepsG_good k)
    (sourceFnBody Guest.Software.guestFn_charge_state_gas) rfl s hc

theorem evmStep_call0_charge_gas {F : Type} {gw : List String}
    (args : List (ExpHOL 64)) (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_gas") args)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_gas") args)).1) :
    EvmStep gw s (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_gas") args)).2 ∧
    ((evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_gas") args)).1 = none →
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_gas") args)).2.locals = s.locals ∧
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_gas") args)).2.code = originalRuntimeCode) :=
  evmStep_of_eps_call0 eps_charge_gas_any
    (fun values body callee rs hl => by
      obtain ⟨_, _, hinst⟩ := lookupCode_installed hl
      rw [M21.lookup_charge_gas] at hinst
      rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]
      exact ⟨fun _ => false, fun _ h => by simp at h, by decide⟩)
    (fun _ _ _ hq => hq)
    (fun st body hcs _ ⟨vs, hl⟩ _ => by
      obtain ⟨_, _, hinst⟩ := lookupCode_installed hl
      rw [M21.lookup_charge_gas] at hinst
      rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]
      exact charge_gas_keeps_globals st hcs)
    (fun _ _ _ hlk => by rw [M21.lookup_charge_gas] at hlk; exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hlk)).2).2.symm)
    args s hc hInv hnt hfr

theorem evmStep_call0_charge_state_gas {F : Type} {gw : List String}
    (args : List (ExpHOL 64)) (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_state_gas") args)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_state_gas") args)).1) :
    EvmStep gw s (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_state_gas") args)).2 ∧
    ((evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_state_gas") args)).1 = none →
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_state_gas") args)).2.locals = s.locals ∧
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_state_gas") args)).2.code = originalRuntimeCode) :=
  evmStep_of_eps_call0 eps_charge_state_gas
    (fun values body callee rs hl => by
      obtain ⟨_, _, hinst⟩ := lookupCode_installed hl
      rw [lookup_charge_state_gas_b] at hinst
      rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]
      exact ⟨fun g => g == ofString "add_sat", addSatOnlyCallees_good, by decide⟩)
    (fun _ _ _ hq => hq)
    (fun st body hcs _ ⟨vs, hl⟩ _ => by
      obtain ⟨_, _, hinst⟩ := lookupCode_installed hl
      rw [lookup_charge_state_gas_b] at hinst
      rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]
      exact charge_state_gas_keeps_globals st hcs)
    (fun _ _ _ hlk => by rw [lookup_charge_state_gas_b] at hlk; exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hlk)).2).2.symm)
    args s hc hInv hnt hfr

private theorem create_finish_tail_worldStepSc {F : Type}
    {s : PanSemStateFiniteExact 64 F} {nw codew msgw : BitVec 64}
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hn_le : nw.toNat ≤ 65536)
    (hs_n : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hs_code : s.locals.lookup (ofString "code") = some (.val (.word codew)))
    (hs_msg : s.locals.lookup (ofString "msg") = some (.val (.word msgw)))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "stored_code") .one (ofString "alloc")
        [.op .add [.var .local (ofString "n"), .const 8#64]]
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "stored_code"), .var .local (ofString "code"), .var .local (ofString "n")])
          (.seq
            (.call (some (none, none)) (ofString "set_code")
              [.load .one (.op .add [.var .local (ofString "msg"), .const 32#64]),
               .var .local (ofString "stored_code"), .var .local (ofString "n")])
            (.return (.const 0#64)))))).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.decCall (ofString "stored_code") .one (ofString "alloc")
        [.op .add [.var .local (ofString "n"), .const 8#64]]
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "stored_code"), .var .local (ofString "code"), .var .local (ofString "n")])
          (.seq
            (.call (some (none, none)) (ofString "set_code")
              [.load .one (.op .add [.var .local (ofString "msg"), .const 32#64]),
               .var .local (ofString "stored_code"), .var .local (ofString "n")])
            (.return (.const 0#64)))))).1) :
    WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
      s
      (evaluateHOLFiniteState s
        (.decCall (ofString "stored_code") .one (ofString "alloc")
          [.op .add [.var .local (ofString "n"), .const 8#64]]
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.var .local (ofString "stored_code"), .var .local (ofString "code"), .var .local (ofString "n")])
            (.seq
              (.call (some (none, none)) (ofString "set_code")
                [.load .one (.op .add [.var .local (ofString "msg"), .const 32#64]),
                 .var .local (ofString "stored_code"), .var .local (ofString "n")])
              (.return (.const 0#64)))))).1
      (evaluateHOLFiniteState s
        (.decCall (ofString "stored_code") .one (ofString "alloc")
          [.op .add [.var .local (ofString "n"), .const 8#64]]
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.var .local (ofString "stored_code"), .var .local (ofString "code"), .var .local (ofString "n")])
            (.seq
              (.call (some (none, none)) (ofString "set_code")
                [.load .one (.op .add [.var .local (ofString "msg"), .const 32#64]),
                 .var .local (ofString "stored_code"), .var .local (ofString "n")])
              (.return (.const 0#64)))))).2 := by
  let pRest : ProgHOL 64 :=
    .seq
      (.call (some (none, none)) (ofString "set_code")
        [.load .one (.op .add [.var .local (ofString "msg"), .const 32#64]),
         .var .local (ofString "stored_code"), .var .local (ofString "n")])
      (.return (.const 0#64))
  let pMc : ProgHOL 64 :=
    .call (some (none, none)) (ofString "memcpy")
      [.var .local (ofString "stored_code"), .var .local (ofString "code"), .var .local (ofString "n")]
  have heval_eq : ∀ (st : PanSemStateFiniteExact 64 F),
      st.locals.lookup (ofString "n") = some (.val (.word nw)) →
      evaluateHOLFiniteState st
        (.decCall (ofString "stored_code") .one (ofString "alloc")
          [.op .add [.var .local (ofString "n"), .const 8#64]] (.seq pMc pRest)) =
      evaluateHOLFiniteState st
        (.decCall (ofString "stored_code") .one (ofString "alloc")
          [.const (nw + 8#64)] (.seq pMc pRest)) := by
    intro st hst_n
    simp only [evaluateHOLFiniteState_decCall_fixClockRewrite]
    have ha1 : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
        [.op .add [.var .local (ofString "n"), .const 8#64]] = some [.val (.word (nw + 8#64))] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact, evalHOLExact, hst_n, wordOpHOL, wordOp, valueIsWord, valueWord]
    have ha2 : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
        [.const (nw + 8#64)] = some [.val (.word (nw + 8#64))] := rfl
    rw [ha1, ha2]
  change WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra s
    (evaluateHOLFiniteState s
      (.decCall (ofString "stored_code") .one (ofString "alloc")
        [.op .add [.var .local (ofString "n"), .const 8#64]] (.seq pMc pRest))).1
    (evaluateHOLFiniteState s
      (.decCall (ofString "stored_code") .one (ofString "alloc")
        [.op .add [.var .local (ofString "n"), .const 8#64]] (.seq pMc pRest))).2
  rw [heval_eq s hs_n] at hnt hfr ⊢
  refine progWStep_decCall_alloc_seq_acctMut hc hW
    (fun pw m1 hm1_loc _ heff_m1 hpw_lo hpw_end hhp_hi hnt_mc hcr_mc => by
      have hnw8 : (nw + 8#64).toNat = nw.toNat + 8 := create_finish_alloc_add_no_wrap nw hn_le
      have hpw_hi : pw.toNat + nw.toNat ≤ heapLimit := by
        rw [hnw8] at hpw_end; omega
      have hm1_sc : m1.locals.lookup (ofString "stored_code") = some (.val (.word pw)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hm1_code : m1.locals.lookup (ofString "code") = some (.val (.word codew)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs_code,
          show ofString "stored_code" ≠ ofString "code" by decide]
      have hm1_n : m1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs_n,
          show ofString "stored_code" ≠ ofString "n" by decide]
      exact worldEff_call0_memcpy_sc heff_m1 _ _ _ hnt_mc
        (call0_or_resumes_sc m1 (ofString "memcpy") _ hcr_mc)
        (fun dstw _ nw' hd _ hn' _ => by
          simp [evalHOLExact, hm1_sc, hm1_n] at hd hn'
          subst hd hn'
          exact Or.inr (Or.inr (Or.inr ⟨hpw_lo, hpw_hi⟩))))
    (fun pw m2 _ _ _ hc2 hW2 hnt2 hfr2 =>
      progWStep_seq validBufList_acctMutBufs safeStepGlobals_acctMut_sc
        (progWStep_call0 (fun _ h => h) (fun _ h => h) wkSc_set_code)
        (progWStep_return _ _ _)
        m2 hc2 hW2 hnt2 hfr2)
    (fun m1 hnone => call0_none_locals_sc m1 (ofString "memcpy") _ hnone)
    hnt hfr

private def cfMul6W : ExpHOL 64 :=
  FrontendCodecComputation.expToHOLStructural
    (Exp.panOp PanOp.mul [(Exp.const (BitVec.ofNat 64 6)), (Exp.var VarKind.local "w")])

private def cfMulN1530 : ExpHOL 64 :=
  FrontendCodecComputation.expToHOLStructural
    (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 1530))])

private def cfAllocTail : ProgHOL 64 :=
  .decCall (ofString "stored_code") .one (ofString "alloc")
    [.op .add [.var .local (ofString "n"), .const 8#64]]
    (.seq
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "stored_code"), .var .local (ofString "code"), .var .local (ofString "n")])
      (.seq
        (.call (some (none, none)) (ofString "set_code")
          [.load .one (.op .add [.var .local (ofString "msg"), .const 32#64]),
           .var .local (ofString "stored_code"), .var .local (ofString "n")])
        (.return (.const 0#64))))

private def cfChargesProg : ProgHOL 64 :=
  .seq
    (.call (some (none, none)) (ofString "charge_gas") [cfMul6W])
    (.seq
      (.call (some (none, none)) (ofString "charge_state_gas") [cfMulN1530])
      cfAllocTail)

private def cfGuardsProg : ProgHOL 64 :=
  .seq
    (.ite (.cmp .lower (.const 65536#64) (.var .local (ofString "n")))
      (.raise (ofString "EvmErr") (.const 4#64))
      .skip)
    (.decCall (ofString "w") .one (ofString "words_of") [.var .local (ofString "n")]
      cfChargesProg)

private def cfIte1Prog : ProgHOL 64 :=
  .ite (.cmp .lower (.const 0#64) (.var .local (ofString "n")))
    (.ite (.cmp .equal (.loadByte (.var .local (ofString "code"))) (.const 239#64))
      (.raise (ofString "EvmErr") (.const 11#64))
      .skip)
    .skip

private def cfBody2Prog : ProgHOL 64 :=
  .seq cfIte1Prog cfGuardsProg

private theorem cf_body_eq :
    sourceFnBody Guest.Software.guestFn_create_finish =
      .dec (ofString "code") .one (.load .one (.op .add [.var .local (ofString "child"), .const 120#64]))
        (.dec (ofString "n") .one (.load .one (.op .add [.var .local (ofString "child"), .const 128#64]))
          cfBody2Prog) := rfl

private theorem create_finish_after_charges {F : Type}
    {s4 : PanSemStateFiniteExact 64 F} {nw codew msgw : BitVec 64}
    (hc4 : s4.code = originalRuntimeCode) (hInv4 : EvmInv s4)
    (hn_le : nw.toNat ≤ 65536)
    (hs4_msg : s4.locals.lookup (ofString "msg") = some (.val (.word msgw)))
    (hs4_code : s4.locals.lookup (ofString "code") = some (.val (.word codew)))
    (hs4_n : s4.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnt : (evaluateHOLFiniteState s4 cfChargesProg).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s4 cfChargesProg).1) :
    EvmStep ["heap_ptr", "journal_n", "scratch_ptr"] s4
      (evaluateHOLFiniteState s4 cfChargesProg).2 := by
  dsimp only [cfChargesProg] at hnt hfr ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hcg : evaluateHOLFiniteState s4
      (.call (some (none, none)) (ofString "charge_gas") [cfMul6W]) with ⟨rcg, s5⟩
  simp only [hcg] at hnt hfr ⊢
  cases rcg with
  | some _ =>
    have hs_cg := (evmStep_call0_charge_gas (gw := ["heap_ptr", "journal_n", "scratch_ptr"])
      [cfMul6W] s4 hc4 hInv4 (by rw [hcg]; exact hnt) (by rw [hcg]; exact hfr)).1
    rw [hcg] at hs_cg; exact hs_cg
  | none =>
    dsimp only at hnt hfr ⊢
    obtain ⟨hs_cg, hnone_cg⟩ := evmStep_call0_charge_gas (gw := ["heap_ptr", "journal_n", "scratch_ptr"])
      [cfMul6W] s4 hc4 hInv4 (by rw [hcg]; simp) (by rw [hcg]; exact Or.inl rfl)
    rw [hcg] at hs_cg hnone_cg
    obtain ⟨hs5_loc, hc5⟩ := hnone_cg rfl
    have hInv5 : EvmInv s5 := hs_cg.1
    have hs5_msg : s5.locals.lookup (ofString "msg") = some (.val (.word msgw)) := by rw [hs5_loc]; exact hs4_msg
    have hs5_code : s5.locals.lookup (ofString "code") = some (.val (.word codew)) := by rw [hs5_loc]; exact hs4_code
    have hs5_n : s5.locals.lookup (ofString "n") = some (.val (.word nw)) := by rw [hs5_loc]; exact hs4_n
    refine evmStep_trans hs_cg ?_
    rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
    rcases hcsg : evaluateHOLFiniteState s5
        (.call (some (none, none)) (ofString "charge_state_gas") [cfMulN1530]) with ⟨rcsg, s6⟩
    simp only [hcsg] at hnt hfr ⊢
    cases rcsg with
    | some _ =>
      have hs_csg := (evmStep_call0_charge_state_gas (gw := ["heap_ptr", "journal_n", "scratch_ptr"])
        [cfMulN1530] s5 hc5 hInv5 (by rw [hcsg]; exact hnt) (by rw [hcsg]; exact hfr)).1
      rw [hcsg] at hs_csg; exact hs_csg
    | none =>
      dsimp only at hnt hfr ⊢
      obtain ⟨hs_csg, hnone_csg⟩ := evmStep_call0_charge_state_gas (gw := ["heap_ptr", "journal_n", "scratch_ptr"])
        [cfMulN1530] s5 hc5 hInv5 (by rw [hcsg]; simp) (by rw [hcsg]; exact Or.inl rfl)
      rw [hcsg] at hs_csg hnone_csg
      obtain ⟨hs6_loc, hc6⟩ := hnone_csg rfl
      have hInv6 : EvmInv s6 := hs_csg.1
      have hs6_msg : s6.locals.lookup (ofString "msg") = some (.val (.word msgw)) := by rw [hs6_loc]; exact hs5_msg
      have hs6_code : s6.locals.lookup (ofString "code") = some (.val (.word codew)) := by rw [hs6_loc]; exact hs5_code
      have hs6_n : s6.locals.lookup (ofString "n") = some (.val (.word nw)) := by rw [hs6_loc]; exact hs5_n
      refine evmStep_trans hs_csg ?_
      have hAv6 : EvmAvoids createFinishAvoids s6 := evm_createFinishAvoids s6 hInv6
      obtain ⟨hAs6, S6, hInvAt6, _⟩ := hAv6
      have hW6 : WorldOK s6 := ⟨hAs6, S6, hInvAt6.1⟩
      dsimp only [cfAllocTail] at hnt hfr ⊢
      have hws6 := create_finish_tail_worldStepSc hc6 hW6 hn_le hs6_n hs6_code hs6_msg hnt hfr
      exact evmStep_of_worldStepSc validBufList_acctMutBufs safeStepGlobals_acctMut_sc
        hAs6 ⟨S6, hInvAt6⟩ hws6

private theorem create_finish_after_guards {F : Type}
    {s3 : PanSemStateFiniteExact 64 F} {nw codew msgw : BitVec 64}
    (hc3 : s3.code = originalRuntimeCode) (hInv3 : EvmInv s3)
    (hs3_msg : s3.locals.lookup (ofString "msg") = some (.val (.word msgw)))
    (hs3_code : s3.locals.lookup (ofString "code") = some (.val (.word codew)))
    (hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnt0 : (evaluateHOLFiniteState s3 cfGuardsProg).1 ≠ some .timeOut)
    (hfr0 : FlowingOrResumes (evaluateHOLFiniteState s3 cfGuardsProg).1) :
    EvmStep ["heap_ptr", "journal_n", "scratch_ptr"] s3
      (evaluateHOLFiniteState s3 cfGuardsProg).2 := by
  dsimp only [cfGuardsProg] at hnt0 hfr0 ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt0 hfr0 ⊢
  rw [evaluateHOLFiniteState_ite] at hnt0 hfr0 ⊢
  have hcmp2 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
      (.cmp .lower (.const 65536#64) (.var .local (ofString "n"))) =
      some (.val (.word (if 65536#64 < nw then 1#64 else 0#64))) := by
    simp [evalHOLExact, hs3_n, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp2] at hnt0 hfr0 ⊢; dsimp only at hnt0 hfr0 ⊢
  by_cases hgt : 65536#64 < nw
  · have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
    simp only [hgt, ↓reduceIte, h10] at hnt0 hfr0 ⊢
    rw [evaluateHOLFiniteState_raise] at hnt0 hfr0 ⊢
    dsimp only [evalHOLExact] at hnt0 hfr0 ⊢
    cases s3.eshapes.lookup (ofString "EvmErr") with
    | none => dsimp only; exact evmStep_refl_gw hInv3
    | some sh =>
      by_cases hshape : shapeOfHOLExact (.val (.word 4#64) : ValueHOL 64) = sh ∧
          sizeOfShapeWithContextHOL s3.structs (shapeOfHOLExact (.val (.word 4#64) : ValueHOL 64)) ≤ 32
      · simp only [if_pos hshape] at hnt0 hfr0 ⊢
        exact evmStep_with_locals_clock (evmStep_refl_gw hInv3) _ s3.clock
      · simp only [if_neg hshape] at hnt0 hfr0 ⊢
        exact evmStep_refl_gw hInv3
  · have hn_le : nw.toNat ≤ 65536 := by
      rw [BitVec.lt_def] at hgt; change ¬ (65536 < nw.toNat) at hgt; omega
    have h00 : (0#64 : BitVec 64) = 0 := rfl
    simp only [hgt, ↓reduceIte, h00, evaluateHOLFiniteState_skip] at hnt0 hfr0 ⊢
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt0 hfr0 ⊢
    have hargs_w : evalListHOLFinite s3 (h := fun a => Classical.propDecidable (s3.memaddrs a))
        [.var .local (ofString "n")] = some [.val (.word nw)] := by
      rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hs3_n]
    rw [hargs_w] at hnt0 hfr0 ⊢; dsimp only at hnt0 hfr0 ⊢
    rcases hl_w : lookupCodeHOLFinite s3.code.lookup (ofString "words_of") [.val (.word nw)] with
      _ | ⟨body_w, callee_w, ret_w⟩
    · simp [hl_w] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
    · simp only [hl_w] at hnt0 hfr0 ⊢
      by_cases hz3 : s3.clock = 0
      · simp [hz3] at hnt0
      · rw [if_neg hz3] at hnt0 hfr0 ⊢
        have hlk_wo : originalRuntimeCode.lookup (ofString "words_of") =
            some ((sourceFunctionEntry Guest.Software.guestFn_words_of).2) :=
          lookup_of_guestAst_getElem 443 (by rw [guestAst_len]; decide)
            (extractFn Guest.Software.guestFn_words_of) rfl
        have hbw_eq := lookupCodeHOLFinite_installed_body s3.code.lookup (ofString "words_of")
          _ (sourceFnBody Guest.Software.guestFn_words_of) body_w _ ret_w [.val (.word nw)] callee_w
          (by rw [hc3]; exact hlk_wo) hl_w
        subst body_w
        let ent_w := callEntryStateHOLFinite s3 callee_w
        have hlfr_w : LocFrameR16 ent_w (evaluateHOLFiniteState ent_w (sourceFnBody Guest.Software.guestFn_words_of)).2 :=
          evaluate_roProgR16 wordsOfCallees wordsOfCallees_good
            (sourceFnBody Guest.Software.guestFn_words_of) (by decide) ent_w hc3
        rcases hrw : evaluateHOLFiniteState ent_w (sourceFnBody Guest.Software.guestFn_words_of) with ⟨rw0, pw0⟩
        dsimp only [ent_w] at hrw hlfr_w
        simp only [hrw] at hlfr_w hnt0 hfr0 ⊢
        cases rw0 with
        | none => exact absurd hfr0 not_flowingOrResumes_error
        | some crw =>
          cases crw with
          | timeOut => simp at hnt0
          | «break» | «continue» | error => exact absurd hfr0 not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr0 not_flowingOrResumes_finalFfi
          | exception _ _ =>
            dsimp only
            have hpw0_eq : pw0 = { s3 with locals := pw0.locals, clock := pw0.clock } := by
              unfold LocFrameR16 at hlfr_w; rw [hlfr_w]; rfl
            rw [hpw0_eq]
            exact evmStep_with_locals_clock (evmStep_refl_gw hInv3) _ pw0.clock
          | returned vw =>
            dsimp only at hnt0 hfr0 ⊢
            by_cases hsh_vw : (shapeEqHOL (shapeOfHOLExact vw) .one && shapeEqHOL (shapeOfHOLExact vw) ret_w) = true
            · simp only [hsh_vw, ↓reduceIte] at hnt0 hfr0 ⊢
              set s4 := setVarHOLFinite (ofString "w") vw { pw0 with locals := s3.locals }
              have hs4_eq : s4 = { s3 with locals := s3.locals.update (ofString "w", vw), clock := pw0.clock } := by
                dsimp only [s4, setVarHOLFinite]
                unfold LocFrameR16 at hlfr_w; rw [hlfr_w]; rfl
              have hInv4 : EvmInv s4 := by rw [hs4_eq]; exact localsFree_evmInv s3 (s3.locals.update (ofString "w", vw)) pw0.clock hInv3
              have hc4 : s4.code = originalRuntimeCode := by rw [hs4_eq]; exact hc3
              have hs4_msg : s4.locals.lookup (ofString "msg") = some (.val (.word msgw)) := by
                rw [hs4_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs3_msg,
                  show ofString "w" ≠ ofString "msg" by decide]
              have hs4_code : s4.locals.lookup (ofString "code") = some (.val (.word codew)) := by
                rw [hs4_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs3_code,
                  show ofString "w" ≠ ofString "code" by decide]
              have hs4_n : s4.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                rw [hs4_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs3_n,
                  show ofString "w" ≠ ofString "n" by decide]
              have hstep34 : EvmStep ["heap_ptr", "journal_n", "scratch_ptr"] s3 s4 := by
                rw [hs4_eq]; exact evmStep_with_locals_clock (evmStep_refl_gw hInv3) (s3.locals.update (ofString "w", vw)) pw0.clock
              have hbody4 := create_finish_after_charges hc4 hInv4 hn_le hs4_msg hs4_code hs4_n hnt0 hfr0
              rcases hr4 : evaluateHOLFiniteState s4 cfChargesProg with ⟨r4, p4⟩
              simp only [hr4] at hnt0 hfr0 hbody4 ⊢
              exact evmStep_trans hstep34 (evmStep_with_locals_clock hbody4 _ p4.clock)
            · simp [hsh_vw] at hfr0; exact absurd hfr0 not_flowingOrResumes_error

private theorem create_finish_body2 {F : Type}
    {s2 : PanSemStateFiniteExact 64 F} {nw codew msgw : BitVec 64}
    (hc2 : s2.code = originalRuntimeCode) (hInv2 : EvmInv s2)
    (hs2_msg : s2.locals.lookup (ofString "msg") = some (.val (.word msgw)))
    (hs2_code : s2.locals.lookup (ofString "code") = some (.val (.word codew)))
    (hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnt0 : (evaluateHOLFiniteState s2 cfBody2Prog).1 ≠ some .timeOut)
    (hfr0 : FlowingOrResumes (evaluateHOLFiniteState s2 cfBody2Prog).1) :
    EvmStep ["heap_ptr", "journal_n", "scratch_ptr"] s2
      (evaluateHOLFiniteState s2 cfBody2Prog).2 := by
  dsimp only [cfBody2Prog] at hnt0 hfr0 ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt0 hfr0 ⊢
  have hlfr1 : LocFrameR16 s2 (evaluateHOLFiniteState s2 cfIte1Prog).2 :=
    evaluate_roProgR16 (fun _ => false) (fun _ h => by simp at h) cfIte1Prog (by decide) s2 hc2
  have hav1 : ∀ k, avoidsLocal k cfIte1Prog = true := fun _ => rfl
  rcases hr_i1 : evaluateHOLFiniteState s2 cfIte1Prog with ⟨ri1, s3⟩
  have hflow1 : ri1 = none → ∀ k, s3.locals.lookup k = s2.locals.lookup k := by
    intro hri1 k
    have hk := evaluate_avoidsLocal_flowing k cfIte1Prog (hav1 k) s2 (by rw [hr_i1, hri1]; exact Or.inl rfl)
    rw [hr_i1] at hk; exact hk
  simp only [hr_i1] at hlfr1 hnt0 hfr0 ⊢
  cases ri1 with
  | some _ =>
    dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold LocFrameR16 at hlfr1; rw [hlfr1]; exact localsFree_evmInv s2 s3.locals s3.clock hInv2
    · unfold LocFrameR16 at hlfr1; rw [hlfr1]; exact le_rfl
    · intro g _; unfold LocFrameR16 at hlfr1; rw [hlfr1]
    · unfold LocFrameR16 at hlfr1; rw [hlfr1]; exact evmChain_with_locals s2 s3.locals s3.clock
  | none =>
    dsimp only at hnt0 hfr0 ⊢
    have hs3_loc : s3.locals = s2.locals := by
      apply HolFiniteMapExact.ext; funext k
      exact hflow1 rfl k
    have hs3_eq : s3 = { s2 with clock := s3.clock } := by
      unfold LocFrameR16 at hlfr1; rw [hlfr1, hs3_loc]
    have hInv3 : EvmInv s3 := by rw [hs3_eq]; exact localsFree_evmInv s2 s2.locals s3.clock hInv2
    have hc3 : s3.code = originalRuntimeCode := by rw [hs3_eq]; exact hc2
    have hs3_msg : s3.locals.lookup (ofString "msg") = some (.val (.word msgw)) := by rw [hs3_loc]; exact hs2_msg
    have hs3_code : s3.locals.lookup (ofString "code") = some (.val (.word codew)) := by rw [hs3_loc]; exact hs2_code
    have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word nw)) := by rw [hs3_loc]; exact hs2_n
    have hstep23 : EvmStep ["heap_ptr", "journal_n", "scratch_ptr"] s2 s3 := by
      rw [hs3_eq]; exact evmStep_with_locals_clock (evmStep_refl_gw hInv2) s2.locals s3.clock
    exact evmStep_trans hstep23 (create_finish_after_guards hc3 hInv3 hs3_msg hs3_code hs3_n hnt0 hfr0)

theorem ek_create_finish_proof :
    EvmKeeps (EvmAvoids createFinishAvoids)
      ["heap_ptr", "journal_n", "scratch_ptr"] (ofString "create_finish") := by
  have hlk_cf : originalRuntimeCode.lookup (ofString "create_finish") =
      some ([(ofString "msg", .one), (ofString "child", .one)],
        sourceFnBody Guest.Software.guestFn_create_finish, .one) :=
    lookup_create_finish
  refine ⟨[(ofString "msg", .one), (ofString "child", .one)],
    sourceFnBody Guest.Software.guestFn_create_finish, .one, hlk_cf, ?_⟩
  intro F s0 hc0 hAv0 hex0 hnt0 hres0
  have hInv0 : EvmInv s0 := ⟨hAv0.1, hAv0.2.elim fun S hS => ⟨S, hS.1⟩⟩
  obtain ⟨vs0, hlk0⟩ := hex0
  obtain ⟨msgw, childw, _, hs0_msg, hs0_child⟩ :=
    Fast_C08WkShard03.lookupCode_two_words (by decide) hlk_cf hlk0
  have hfr0 : FlowingOrResumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_create_finish)).1 :=
    Or.inr (Or.inr (Or.inr hres0))
  rw [cf_body_eq] at hnt0 hfr0 ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt0 hfr0 ⊢; dsimp only at hnt0 hfr0 ⊢
  rcases hcode_ev : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "child"), .const 120#64])) with _ | codev
  · simp [hcode_ev] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
  · simp only [hcode_ev] at hnt0 hfr0 ⊢
    rcases codev with ⟨⟨codew⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hfr0; exact absurd hfr0 not_flowingOrResumes_error)
    have hsh_code : shapeEqHOL .one (shapeOfHOLExact (.val (.word codew) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh_code] at hnt0 hfr0 ⊢; dsimp only at hnt0 hfr0 ⊢
    set s1 := setVarHOLFinite (ofString "code") (.val (.word codew)) s0
    have hInv1 : EvmInv s1 := localsFree_evmInv s0 s1.locals s0.clock hInv0
    have hc1 : s1.code = originalRuntimeCode := hc0
    have hs1_msg : s1.locals.lookup (ofString "msg") = some (.val (.word msgw)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs0_msg,
        show ofString "code" ≠ ofString "msg" by decide]
    have hs1_child : s1.locals.lookup (ofString "child") = some (.val (.word childw)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs0_child,
        show ofString "code" ≠ ofString "child" by decide]
    have hs1_code : s1.locals.lookup (ofString "code") = some (.val (.word codew)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rw [evaluateHOLFiniteState_dec_total] at hnt0 hfr0 ⊢; dsimp only at hnt0 hfr0 ⊢
    rcases hn_ev : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "child"), .const 128#64])) with _ | nv
    · simp [hn_ev] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
    · simp only [hn_ev] at hnt0 hfr0 ⊢
      rcases nv with ⟨⟨nw⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hfr0; exact absurd hfr0 not_flowingOrResumes_error)
      have hsh_n : shapeEqHOL .one (shapeOfHOLExact (.val (.word nw) : ValueHOL 64)) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      rw [if_pos hsh_n] at hnt0 hfr0 ⊢; dsimp only at hnt0 hfr0 ⊢
      set s2 := setVarHOLFinite (ofString "n") (.val (.word nw)) s1
      have hInv2 : EvmInv s2 := localsFree_evmInv s1 s2.locals s1.clock hInv1
      have hc2 : s2.code = originalRuntimeCode := hc1
      have hs2_msg : s2.locals.lookup (ofString "msg") = some (.val (.word msgw)) := by
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_msg,
          show ofString "n" ≠ ofString "msg" by decide]
      have hs2_code : s2.locals.lookup (ofString "code") = some (.val (.word codew)) := by
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_code,
          show ofString "n" ≠ ofString "code" by decide]
      have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hstep02 : EvmStep ["heap_ptr", "journal_n", "scratch_ptr"] s0 s2 :=
        ⟨hInv2, le_rfl, fun _ _ => rfl,
          (evmChain_with_locals s1 s2.locals s1.clock).trans (evmChain_with_locals s0 s1.locals s0.clock)⟩
      have hbody2 := create_finish_body2 hc2 hInv2 hs2_msg hs2_code hs2_n hnt0 hfr0
      rcases hr2 : evaluateHOLFiniteState s2 cfBody2Prog with ⟨r2, p2⟩
      simp only [hr2] at hnt0 hfr0 hbody2 ⊢
      exact evmStep_trans hstep02 (evmStep_with_locals_clock hbody2 _ p2.clock)

end CreateFinish

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish

namespace InitECandidate.Solver.Wave8GuestInv

open Flapjack.Basis.Pure.MlString

theorem «ek_create_finish» :
    EvmKeeps (EvmAvoids (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)]))
    ["heap_ptr", "journal_n", "scratch_ptr"] (ofString "create_finish") :=
  R16Shards.EvmEkFk.StorageCreateFinish.ek_create_finish_proof

end InitECandidate.Solver.Wave8GuestInv
