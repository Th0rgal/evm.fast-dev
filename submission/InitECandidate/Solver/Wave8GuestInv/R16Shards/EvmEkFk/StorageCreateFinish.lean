import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.EkWarmStorageKey
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkGetAccount
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.AccountWk
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.StateGasHelpers
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_stor_lookup
import InitECandidate.Solver.Wave8GuestInv.R14Shards.NodeFnHelpers
import InitECandidate.Solver.Wave8GuestInv.R14Shards.NfNodeNewLeaf
import InitECandidate.Solver.Wave8GuestInv.R14Shards.NfNodeNewExt
import InitECandidate.Solver.Wave8GuestInv.R16Shards.ResolveDecodeStep
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.DecodeStep
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyDecodeWitness
import InitECandidate.Solver.Wave8GuestInv.R13Shards.MptNibbleKey

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

def WitnessSliceOK {F : Type} (s : PanSemStateFiniteExact 64 F) (v : Nat) : Prop :=
  WordsOK s (v, 16) ∧ Inside (v, 16) sourceBase (globN s "heap_ptr") ∧
    memW s (v + 8) < 2 ^ 40 ∧
    Inside (memW s v, memW s (v + 8)) sourceBase (globN s "heap_ptr")

def WitnessDbAt {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : Prop :=
  globN s "ws" ≠ 0 →
    let db := memW s (globN s "ws")
    db ≠ 0 → HtabWF s db ∧ hdr s db 0 = 32 ∧
      (∀ i ∈ htabFootprint s db, Inside i sourceBase (globN s "heap_ptr")) ∧
      IvlsDisj (htabFootprint s db) (worldOwned s S Nd) ∧
      ∀ v ∈ htabValues s db, WitnessSliceOK s v ∧
        ∀ j ∈ worldOwned s S Nd, Disj (v, 16) j

def WitnessDbOK {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ S Nd, WorldTypedWith s S Nd ∧ WitnessDbAt s S Nd

def getStorageOriginalAvoids {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
   (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
   (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)]

theorem witnessSliceOK_of_preserved {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {v : Nat} (h : WitnessSliceOK s v)
    (hwords : WordsOK post (v, 16))
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hp : memW post v = memW s v)
    (hn : memW post (v + 8) = memW s (v + 8)) :
    WitnessSliceOK post v := by
  refine ⟨hwords, ⟨h.2.1.1, le_trans h.2.1.2 hhp⟩, ?_, ?_⟩
  · rw [hn]; exact h.2.2.1
  · rw [hp, hn]
    exact ⟨h.2.2.2.1, le_trans h.2.2.2.2 hhp⟩

theorem witnessSliceOK_with_locals_clock {F : Type} {s : PanSemStateFiniteExact 64 F}
    {v : Nat} (h : WitnessSliceOK s v)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    WitnessSliceOK { s with locals := L, clock := k } v := h

theorem witnessSliceOK_subslice {F : Type} {s : PanSemStateFiniteExact 64 F}
    {v p n : Nat} (h : WitnessSliceOK s v)
    (hp : memW s v ≤ p) (hn : p + n ≤ memW s v + memW s (v + 8)) :
    Inside (p, n) sourceBase (globN s "heap_ptr") ∧ n < 2 ^ 40 := by
  obtain ⟨_, _, hlen, hlo, hhi⟩ := h
  constructor
  · exact ⟨le_trans hlo hp, le_trans hn hhi⟩
  · omega

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

section StorageOriginal

open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.HeapPotential

def WitnessDbSlices {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  globN s "ws" ≠ 0 →
    let db := memW s (globN s "ws")
    db ≠ 0 → HtabWF s db ∧ hdr s db 0 = 32 ∧
      (∀ i ∈ htabFootprint s db, Inside i sourceBase (globN s "heap_ptr")) ∧
      ∀ v ∈ htabValues s db, WitnessSliceOK s v

theorem witnessDbSlices_of_ok {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : WitnessDbOK s) : WitnessDbSlices s := by
  obtain ⟨S, Nd, _, hdb⟩ := h
  intro hws
  dsimp only
  intro hdb_nz
  obtain ⟨hwf, hk, hfp, _, hvals⟩ := hdb hws hdb_nz
  exact ⟨hwf, hk, hfp, fun v hv => (hvals v hv).1⟩

theorem witnessDbSlices_with_locals_clock {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : WitnessDbSlices s) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    WitnessDbSlices { s with locals := L, clock := k } := by
  intro hws
  dsimp only
  intro hdb_nz
  obtain ⟨hwf, hk, hfp, hvals⟩ := h hws hdb_nz
  exact ⟨(htabWF_with_locals s L k _).2 hwf, hk, hfp,
    fun v hv => witnessSliceOK_with_locals_clock (hvals v hv) L k⟩

theorem witnessDbSlices_of_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hws_eq : globN post "ws" = globN s "ws")
    (hws0_eq : globN s "ws" ≠ 0 → memW post (globN s "ws") = memW s (globN s "ws"))
    (hfr : FrameOutside s post [freeGap s] (heapFree s))
    (h : WitnessDbSlices s) :
    WitnessDbSlices post := by
  intro hws_post
  rw [hws_eq] at hws_post
  dsimp only
  rw [hws_eq, hws0_eq hws_post]
  intro hdb_post
  set db := memW s (globN s "ws")
  obtain ⟨hwf, hk, hfp, hvals⟩ := h hws_post hdb_post
  have hu_heap : ∀ o : Ivl, Inside o sourceBase (globN s "heap_ptr") →
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post o := by
    intro o ho
    obtain ⟨hgap, hheap⟩ := allocated_disj_free_regions hAs.2 (Or.inl ho)
    exact aligned_cell_unhit_of_frameOutside hfr
      (fun j hj => by rw [List.mem_singleton.1 hj]; exact Or.inr (Or.inl hAs.2.2.2.2.2.2.2.1))
      (Or.inr (Or.inl hAs.2.2.2.2.2.2.1))
      (fun j hj => by rw [List.mem_singleton.1 hj]; exact hgap)
      hheap
  have hu_db : ∀ i ∈ htabFootprint s db, InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i :=
    fun i hi => hu_heap i (hfp i hi)
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have ht_fp : (db, 88) ∈ htabFootprint s db := by simp [htabFootprint]
  have hdb8 : db % 8 = 0 := (hwf.1 _ ht_fp).2.1
  have hhdr_hi : db + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; dsimp at this; omega
  obtain ⟨hhdr, hfp_eq⟩ := InitECandidate.Solver.Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit
    hdb8 hhdr_hi (hu_db _ ht_fp)
  have hvals_eq := InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit hwf hu_db
  refine ⟨InitECandidate.Solver.Wave8Contracts.M08.htabWF_congr_unhit hAs.1 hAp.1 hwf hu_db,
    by rw [hhdr 0 (by omega)]; exact hk,
    fun i hi => by rw [hfp_eq] at hi; exact ⟨(hfp i hi).1, le_trans (hfp i hi).2 hhp⟩,
    fun v hv => ?_⟩
  rw [hvals_eq] at hv
  have hv_ok := hvals v hv
  have hu_v := hu_heap (v, 16) hv_ok.2.1
  have hv_hi : v + 16 ≤ 2 ^ 64 := by
    have hhl : heapLimit ≤ 2 ^ 64 := by decide
    have := hAs.2.2.1; have := hv_ok.2.1.2; omega
  have hv8 : v % 8 = 0 := hv_ok.1.1
  refine witnessSliceOK_of_preserved hv_ok
    (InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hv_ok.1) hhp ?_ ?_
  · exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_v hv8 hv_hi ⟨by omega, by omega⟩
  · exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_v (by omega) hv_hi ⟨by omega, by omega⟩

theorem witnessDbOK_of_worldStepSc {F : Type}
    {B : R16WkAcctWs.BufList} {gw : List String}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hB : R16WkAcctWs.ValidBufList B)
    (hgw : R16WkAcctWs.SafeStepGlobals gw)
    (hAs : ArenaReady s)
    (hdb : WitnessDbOK s)
    (hstep : R16WkAcctWs.WorldStepSc (R16WkAcctWs.bufRegions B) gw EvmBase.stdKeep NoExtra s r post) :
    WitnessDbOK post := by
  obtain ⟨S, Nd, hWT, hdbAt⟩ := hdb
  obtain ⟨⟨hAp, hhp, hG, hK, hWS⟩, _⟩ := hstep
  obtain ⟨S', Nd', _, hWT', hOG, hfr, _⟩ :=
    hWS S Nd hWT (R16WkAcctWs.validBufList_disj hB hWT)
  refine ⟨S', Nd', hWT', ?_⟩
  have hws_eq : globN post "ws" = globN s "ws" :=
    InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup
      (hG (ofString "ws") (hgw.not_mem_map (by decide)))
  intro hws_post
  rw [hws_eq] at hws_post
  have hws0_eq : memW post (globN s "ws") = memW s (globN s "ws") := by
    have hno : ∀ i ∈ R16WkAcctWs.bufRegions B s, ¬ CellHits (globN s "ws" + 0) i := by
      intro i hi hhit
      have hws_mem : (globN s "ws", if globN s "ws" = 0 then 0 else 40) ∈ worldTypedIvls s S Nd := by
        unfold worldTypedIvls
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_right _
            (List.mem_map.2 ⟨("ws", 40), by simp [typedRecords], rfl⟩)))))
      have hdj := R16WkAcctWs.validBufList_disj hB hWT i hi _ hws_mem
      simp only [if_neg hws_post] at hdj
      obtain ⟨h1, h2⟩ := hhit
      rcases hdj with hz_i | hz_ws | hb | hb
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
        unfold bufferRegion at hz_i h1 h2
        by_cases hpz : globN s p.1 = 0
        · simp [hpz] at h1 h2
        · obtain ⟨sz, hgb, _⟩ := hB p hp
          have hfix : (globN s p.1, if globN s p.1 = 0 then 0 else sz) ∈ fixedObjects s := by
            unfold fixedObjects
            apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
            exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
          rcases hWT.2.2.1.1 _ hfix with h0 | ⟨_, hw⟩
          · simp [hpz] at h0; exact absurd h0 (globalBuffers_sz_pos (p.1, sz) hgb)
          · have hws_fix : (globN s "ws", if globN s "ws" = 0 then 0 else 40) ∈ fixedObjects s := by
              unfold fixedObjects
              apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
              exact List.mem_map.2 ⟨("ws", 40), by simp [globalBuffers], rfl⟩
            rcases hWT.2.2.1.1 _ hws_fix with h0_ws | ⟨_, hw_ws⟩
            · simp [hws_post] at h0_ws
            · have hp8 : globN s p.1 % 8 = 0 := hw.1
              have hws8 : globN s "ws" % 8 = 0 := hw_ws.1
              simp only [hpz, ↓reduceIte] at hz_i h1 h2
              omega
      · dsimp only at hz_ws; omega
      · dsimp only at hb; omega
      · dsimp only at hb; omega
    simpa using hK ("ws", [0, 8, 16, 24, 32]) (by simp [EvmBase.stdKeep]) hws_post 0 (by simp) hno
  dsimp only
  rw [hws_eq, hws0_eq]
  intro hdb_post
  set db := memW s (globN s "ws")
  obtain ⟨hwf, hk, hfp, hdisj_fp, hvals⟩ := hdbAt hws_post hdb_post
  have hkeep_shape : ∀ j ∈ worldOwned s S Nd ++ R16WkAcctWs.bufRegions B s ++ [freeGap s],
      j = (0, 0) ∨ j.1 % 8 = 0 ∨ j.2 ≠ 0 := by
    intro j hj
    rcases List.mem_append.1 hj with hj12 | hfg
    · rcases List.mem_append.1 hj12 with hj_ow | hj_R
      · exact worldOwned_well_shaped hWT j hj_ow
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj_R
        unfold bufferRegion
        by_cases hz : globN s p.1 = 0
        · exact Or.inl (by simp [hz])
        · by_cases hp2 : p.2 = 0
          · obtain ⟨sz, hgb, _⟩ := hB p hp
            have hfix : (globN s p.1, if globN s p.1 = 0 then 0 else sz) ∈ fixedObjects s := by
              unfold fixedObjects
              apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
              exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
            rcases hWT.2.2.1.1 _ hfix with h0 | ⟨_, hw⟩
            · simp [hz] at h0; exact absurd h0 (globalBuffers_sz_pos (p.1, sz) hgb)
            · exact Or.inr (Or.inl hw.1)
          · exact Or.inr (Or.inr (by simp [hz, hp2]))
    · rw [List.mem_singleton] at hfg; subst hfg
      exact Or.inr (Or.inl hAs.2.2.2.2.2.2.2.1)
  have hdisj_bufs_of_ow : ∀ b : Ivl, (∀ j ∈ worldOwned s S Nd, Disj b j) →
      ∀ j ∈ R16WkAcctWs.bufRegions B s, Disj b j := by
    intro b hbow j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
    obtain ⟨sz, hgb, _, hle⟩ := hB p hp
    have hfix : bufferRegion s (p.1, sz) ∈ worldOwned s S Nd := by
      unfold worldOwned
      apply List.mem_append_left; apply List.mem_append_right
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
    have hd := hbow _ hfix
    by_cases hz : globN s p.1 = 0
    · exact Or.inr (Or.inl (by simp [bufferRegion, hz]))
    · simp only [bufferRegion, hz, ↓reduceIte] at hd ⊢
      rcases hd with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by dsimp only at h ⊢; omega))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (by dsimp only at h ⊢; omega)))
  have hfp_surv : ∀ i ∈ htabFootprint s db,
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i ∧
      ∀ o ∈ worldOwned post S' Nd', Disj i o := by
    intro i hi
    exact allocated_survives_world_frame hAs.2 hAp.2 hhp (Or.inl (hfp i hi))
      (hdisj_fp i hi) (hdisj_bufs_of_ow i (hdisj_fp i hi)) hkeep_shape hfr hOG
  have hu_db : ∀ i ∈ htabFootprint s db, InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i :=
    fun i hi => (hfp_surv i hi).1
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have ht_fp : (db, 88) ∈ htabFootprint s db := by simp [htabFootprint]
  have hdb8 : db % 8 = 0 := (hwf.1 _ ht_fp).2.1
  have hhdr_hi : db + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; dsimp at this; omega
  obtain ⟨hhdr, hfp_eq⟩ := InitECandidate.Solver.Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit
    hdb8 hhdr_hi (hu_db _ ht_fp)
  have hvals_eq := InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit hwf hu_db
  refine ⟨InitECandidate.Solver.Wave8Contracts.M08.htabWF_congr_unhit hAs.1 hAp.1 hwf hu_db,
    by rw [hhdr 0 (by omega)]; exact hk,
    fun i hi => by rw [hfp_eq] at hi; exact ⟨(hfp i hi).1, le_trans (hfp i hi).2 hhp⟩,
    fun i hi o ho => by rw [hfp_eq] at hi; exact (hfp_surv i hi).2 o ho,
    fun v hv => ?_⟩
  rw [hvals_eq] at hv
  obtain ⟨hv_ok, hv_disj⟩ := hvals v hv
  obtain ⟨hu_v, hv_disj'⟩ := allocated_survives_world_frame hAs.2 hAp.2 hhp (Or.inl hv_ok.2.1)
    hv_disj (hdisj_bufs_of_ow (v, 16) hv_disj) hkeep_shape hfr hOG
  have hv_hi : v + 16 ≤ 2 ^ 64 := by
    have hhl : heapLimit ≤ 2 ^ 64 := by decide
    have := hAs.2.2.1; have := hv_ok.2.1.2; omega
  have hv8 : v % 8 = 0 := hv_ok.1.1
  refine ⟨witnessSliceOK_of_preserved hv_ok
    (InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hv_ok.1) hhp ?_ ?_,
    hv_disj'⟩
  · exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_v hv8 hv_hi ⟨by omega, by omega⟩
  · exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_v (by omega) hv_hi ⟨by omega, by omega⟩

structure DecoderNodeStep {F : Type} (s post : PanSemStateFiniteExact 64 F) (Nd Nd' : List Nat) : Prop where
  step : R14Shards.NodeStep s post Nd Nd'
  old_path : ∀ n ∈ Nd, nodePath post n = nodePath s n
  fresh_path : ∀ x ∈ Nd', x ∉ Nd →
    nodePath post x = (0, 0) ∨
      Inside (nodePath post x) (globN s "heap_ptr") (globN post "heap_ptr")

theorem DecoderNodeStep.refl {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (ha : ArenaReady s) (hn : NodeHeap s Nd) : DecoderNodeStep s s Nd Nd :=
  ⟨R14Shards.NodeStep.refl ha hn, fun _ _ => rfl, fun _ hx hnx => absurd hx hnx⟩

theorem DecoderNodeStep.with_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat} (h : DecoderNodeStep s post Nd Nd')
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (C : Nat) :
    DecoderNodeStep s { post with locals := L, clock := C } Nd Nd' :=
  ⟨h.step.with_locals_clock L C, h.old_path, h.fresh_path⟩

theorem DecoderNodeStep.from_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {C : Nat}
    (h : DecoderNodeStep { s with locals := L, clock := C } post Nd Nd') :
    DecoderNodeStep s post Nd Nd' :=
  ⟨h.step.from_locals_clock, h.old_path, h.fresh_path⟩

theorem DecoderNodeStep.trans {F : Type} {a b c : PanSemStateFiniteExact 64 F}
    {Nd1 Nd2 Nd3 : List Nat} (ha : ArenaReady a)
    (h1 : DecoderNodeStep a b Nd1 Nd2) (h2 : DecoderNodeStep b c Nd2 Nd3) :
    DecoderNodeStep a c Nd1 Nd3 := by
  refine ⟨R14Shards.NodeStep.trans ha h1.step h2.step,
    fun n hn1 => (h2.old_path n (h1.step.sub n hn1)).trans (h1.old_path n hn1),
    fun x hx3 hnx1 => ?_⟩
  by_cases hx2 : x ∈ Nd2
  · rw [h2.old_path x hx2]
    rcases h1.fresh_path x hx2 hnx1 with hz | hin
    · exact Or.inl hz
    · exact Or.inr ⟨hin.1, le_trans hin.2 h2.step.hp_le⟩
  · rcases h2.fresh_path x hx3 hx2 with hz | hin
    · exact Or.inl hz
    · exact Or.inr ⟨le_trans h1.step.hp_le hin.1, hin.2⟩

theorem decoderNodeStep_of_heap_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (ha : ArenaReady s) (hn : NodeHeap s Nd)
    (hst : R14Shards.NodeStep s post Nd Nd)
    (hfr0 : FrameOutside s post [freeGap s] (heapFree s)) :
    DecoderNodeStep s post Nd Nd := by
  refine ⟨hst, fun n hn_mem => ?_, fun _ hx hnx => absurd hx hnx⟩
  by_cases h12 : memW s n = 1 ∨ memW s n = 2
  · have hp := hn.1 n hn_mem
    have hsz56 : 56 ≤ nodeSize (memW s n) := by
      unfold nodeSize
      rcases h12 with h | h <;> simp [h]
    have hlo : sourceBase ≤ n := hp.2.2.1.1
    have hhi_hp : n + nodeSize (memW s n) ≤ globN s "heap_ptr" := by
      rcases hp.2.1 with ⟨_, hhi⟩ | ⟨hscr, _⟩
      · exact hhi
      · have hsep : heapLimit ≤ scratchStart := by decide
        have := hp.2.2.1.2
        dsimp [nodeIvl, Inside] at this
        dsimp [nodeIvl] at hscr
        have hfmp := ha.2.2.2.1
        have hfmp_sp := ha.2.2.2.2.1
        omega
    obtain ⟨hgap, hheap⟩ := allocated_disj_free_regions (o := (n, nodeSize (memW s n))) ha.2 (Or.inl ⟨hlo, hhi_hp⟩)
    have hu : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (n, nodeSize (memW s n)) :=
      aligned_cell_unhit_of_frameOutside hfr0
        (fun j hj => by rw [List.mem_singleton.1 hj]; exact Or.inr (Or.inl ha.2.2.2.2.2.2.2.1))
        (Or.inr (Or.inl ha.2.2.2.2.2.2.1))
        (fun j hj => by rw [List.mem_singleton.1 hj]; exact hgap)
        hheap
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    have hn_hi : n + nodeSize (memW s n) ≤ 2 ^ 64 := by
      have := hp.2.2.1.2; dsimp [nodeIvl] at this; omega
    have hn8 : n % 8 = 0 := hp.2.2.2.1.1
    have hw32 : memW post (n + 32) = memW s (n + 32) :=
      InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu (by omega) hn_hi ⟨by omega, by omega⟩
    have hw40 : memW post (n + 40) = memW s (n + 40) :=
      InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu (by omega) hn_hi ⟨by omega, by omega⟩
    unfold nodePath
    rw [hst.kinds n hn_mem, hw32, hw40]
  · unfold nodePath
    rw [hst.kinds n hn_mem]
    simp [h12]

def RetRootIn : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun _ r _ _ Nd' => ∀ w : BitVec 64, r = some (.returned (.val (.word w))) → RootIn Nd' w.toNat

theorem worldStepSc_of_decoderNodeStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hWOK : WorldOK s)
    (hstep : ∀ Nd, NodeHeap s Nd → ∃ Nd', DecoderNodeStep s post Nd Nd' ∧
      RetRootIn s r post [] Nd') :
    R16WkAcctWs.WorldStepSc (R16WkAcctWs.bufRegions []) ["heap_ptr", "scratch_ptr"]
      EvmBase.stdKeep RetRootIn s r post := by
  have hAs : ArenaReady s := hWOK.1
  have hNh0 : NodeHeap s [] := ⟨fun _ h => False.elim (List.not_mem_nil h),
    fun _ h => False.elim (List.not_mem_nil h)⟩
  obtain ⟨Nd0', hds0, _⟩ := hstep [] hNh0
  have hst0 := hds0.step
  have hAp := hst0.arena
  have hhp := hst0.hp_le
  have hsp := hst0.sp_le
  have hG : GlobalsKept ["heap_ptr", "scratch_ptr"] s post := hst0.globals
  have hfr0 : FrameOutside s post [freeGap s] (heapFree s) := hst0.frame
  have hu_alloc : ∀ o : Ivl, Allocated s o →
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post o := by
    intro o ho
    obtain ⟨hgap, hheap⟩ := allocated_disj_free_regions hAs.2 ho
    exact aligned_cell_unhit_of_frameOutside hfr0
      (fun j hj => by rw [List.mem_singleton.1 hj]; exact Or.inr (Or.inl hAs.2.2.2.2.2.2.2.1))
      (Or.inr (Or.inl hAs.2.2.2.2.2.2.1))
      (fun j hj => by rw [List.mem_singleton.1 hj]; exact hgap)
      hheap
  have hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW post a = memW s a := fun a ha => by
      have hsb_ss : sourceBase ≤ scratchStart := by decide
      have hsb_lt : sourceBase < 2 ^ 64 := by decide
      have ha_lt : a < 2 ^ 64 := lt_of_le_of_lt (by omega) hsb_lt
      have hm := hfr0 (BitVec.ofNat 64 a)
        (fun j hj hcj => by
          rw [List.mem_singleton.1 hj] at hcj
          obtain ⟨h1, _⟩ := hcj
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have := hAs.2.2.2.1
          unfold freeGap at h1; dsimp only at h1; omega)
        (fun hcf => by
          obtain ⟨h1, _⟩ := hcf
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have := hAs.2.1
          unfold heapFree at h1; dsimp only at h1; omega)
      unfold memW; rw [hm]
    exact ⟨hlow 0 (by decide), hlow 8 (by decide), hlow 16 (by decide)⟩
  have hag : AllocatorGrows s post := ⟨hhp, hsp⟩
  have hgs : InitECandidate.Solver.Wave8Contracts.M08.WorldGlobalsSame s post :=
    InitECandidate.Solver.Wave8Contracts.M08.worldGlobalsSame_of_kept hG
      (fun g hg => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        exact hg)
  have hK : RecordsKept (R16WkAcctWs.bufRegions []) EvmBase.stdKeep s post :=
    InitECandidate.Solver.Wave8Contracts.M08.recordsKept_of_free_writes hWOK
      (by simpa [R16WkAcctWs.bufRegions, freeGap, heapFree,
            InitECandidate.Solver.Wave8Contracts.M08.freeGap,
            InitECandidate.Solver.Wave8Contracts.M08.heapFree] using hfr0)
  refine ⟨⟨hAp, hhp, hG, hK, fun S Nd hWT _ => ?_⟩, hsp⟩
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  have hu_fix : ∀ i ∈ fixedObjects s, i.2 ≠ 0 →
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i := fun i hi hipos => by
    rcases hF.1 i hi with h0 | ⟨hal, _⟩
    · exact absurd h0 hipos
    · exact hu_alloc i hal
  have hu_ws : globN s "ws" ≠ 0 → InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (globN s "ws", 40) :=
    fun hnz => by
      have hm := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s
        (r := ("ws", 40)) (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords])
      simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_bs : globN s "bs" ≠ 0 → InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (globN s "bs", 80) :=
    fun hnz => by
      have hm := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s
        (r := ("bs", 80)) (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords])
      simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_ts : globN s "ts" ≠ 0 → InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (globN s "ts", 72) :=
    fun hnz => by
      have hm := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s
        (r := ("ts", 72)) (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords])
      simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_bo : globN s "bo" ≠ 0 → InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (globN s "bo", 88) :=
    fun hnz => by
      have hm := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s
        (r := ("bo", 88)) (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords])
      simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_jr : globN s "journal_cap" ≠ 0 →
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") :=
    fun hnz => by
      apply hu_fix _ _ (by dsimp only; omega)
      unfold fixedObjects
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
      simp [hnz]
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 →
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i := fun i hi h24 =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hi)))) (by omega)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 →
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i := fun i hi hipos =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)) hipos
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t,
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i :=
    fun t ht i hi => hu_alloc i (((hT.2.1 t ht).2 i hi).1)
  have hu_nd_rec : ∀ n ∈ Nd, InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (nodeIvl s n) :=
    fun n hn => hu_alloc _ (hTr.1.1 n hn).2.1
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen k hk
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
    · exact absurd h0 hlen
    · have hhl : heapLimit < 2 ^ 64 := by decide
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by
        dsimp [Inside] at hin_p; omega
      let c := panByteAlignHOL (BitVec.ofNat 64 (memW s (n + 32) + k))
      have hc_nat : c.toNat = (memW s (n + 32) + k) / 8 * 8 := R14Shards.byteCell_toNat ha_lt
      have hp_lo_hi : sourceBase ≤ memW s (n + 32) ∧ memW s (n + 32) + memW s (n + 40) ≤ globN s "heap_ptr" := by
        rcases hal_p with ⟨h1, h2⟩ | ⟨h1, _⟩
        · exact ⟨h1, h2⟩
        · have hsep : heapLimit ≤ scratchStart := by decide
          have := hAs.2.2.2.1; have := hAs.2.2.2.2.1
          dsimp [Inside] at hin_p h1; omega
      have hmem : post.memory c = s.memory c := hfr0 c
        (fun j hj hcj => by
          rw [List.mem_singleton.1 hj] at hcj
          obtain ⟨h1, _⟩ := hcj
          rw [hc_nat] at h1
          have hsep : heapLimit ≤ scratchStart := by decide
          have hfmp8 := hAs.2.2.2.2.2.2.2.1
          have := hAs.2.2.2.1; have := hAs.2.1
          dsimp [Inside] at hin_p
          unfold freeGap at h1; dsimp only at h1; omega)
        (fun hcf => by
          obtain ⟨h1, _⟩ := hcf
          rw [hc_nat] at h1
          have hhp8 := hAs.2.2.2.2.2.2.1
          unfold heapFree at h1; dsimp only at h1; omega)
      unfold memB
      change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v post.be).toNat) =
             (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v s.be).toNat)
      rw [hmem, hst0.be_eq]
  obtain ⟨⟨hT_post, hJ_post, hF_post, hTr_old⟩, _, _, hfix_eq, htab_fp_eq⟩ :=
    InitECandidate.Solver.Wave8Contracts.M08.worldTypedWith_congr_parts
      hAs hAp hag hgs ⟨hT, hJ, hF, hTr⟩
      hu_tab hu_ws hu_bs hu_ts hu_bo hu_jr hu_bo_lst hu_bal hu_nd_rec hu_nd_byte hm0
  obtain ⟨Nd', hds, hQ⟩ := hstep Nd hTr.1
  have hst := hds.step
  have hOG_nd : OwnedGrows s post (nodeExtents s Nd) (nodeExtents post Nd') :=
    ownedGrows_nodeExtents_of_fresh
      (fun n hn => ⟨hst.sub n hn, by simp [nodeIvl, hst.kinds n hn], hds.old_path n hn⟩)
      (fun x hx hnx =>
        ⟨(hst.fresh x hx).resolve_left hnx, hds.fresh_path x hx hnx⟩)
  have hgrow_nd : ∀ j ∈ nodeExtents post Nd', j ≠ (0, 0) →
      (∃ i ∈ nodeExtents s Nd, Inside j i.1 (i.1 + i.2)) ∨
        Inside j (globN s "heap_ptr") (globN post "heap_ptr") := by
    intro j hj hjnz
    rcases hOG_nd j hj with h0 | hold | hfr_j
    · exact absurd h0 hjnz
    · exact Or.inl hold
    · exact Or.inr hfr_j
  have hTr_post : TriesTypedWith post S Nd' := by
    refine ⟨hst.heap, fun o ho => ?_, fun hnz => ?_⟩
    · by_cases ho0 : o = (0, 0)
      · subst ho0
        exact ⟨fun _ _ _ _ => Or.inl rfl, fun _ _ => Or.inl rfl⟩
      · refine ⟨fun t ht i hi => ?_, fun j hj => ?_⟩
        · rw [htab_fp_eq t ht] at hi
          have hal_i : Allocated s i := ((hT.2.1 t ht).2 i hi).1
          exact (allocated_disj_old_or_fresh_extent hAs.2 hAp.2 hhp hal_i
            (fun i' hi' => ((hTr.2.1 i' hi').1 t ht i hi).flip)
            (hgrow_nd o ho ho0)).flip
        · rw [hfix_eq] at hj
          rcases hF.1 j hj with hjz | ⟨hal_j, _⟩
          · exact Or.inr (Or.inl hjz)
          · exact (allocated_disj_old_or_fresh_extent hAs.2 hAp.2 hhp hal_j
              (fun i' hi' => ((hTr.2.1 i' hi').2 j hj).flip)
              (hgrow_nd o ho ho0)).flip
    · obtain ⟨hr24, hr32⟩ := hTr_old.2.2 hnz
      exact ⟨hst.rootIn hr24, fun hm i hi => hst.rootIn (hr32 hm i hi)⟩
  have hOG_world : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd') := by
    intro o ho
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with h12 | hnd
    · rcases List.mem_append.1 h12 with htab | hfix
      · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 htab
        rw [htab_fp_eq t ht] at hfp
        refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
        unfold worldOwned
        exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨t, ht, hfp⟩))))
      · rw [hfix_eq] at hfix
        refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
        unfold worldOwned
        exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
    · rcases hOG_nd o hnd with h0 | ⟨j, hj, hin⟩ | hfr_o
      · exact Or.inl h0
      · refine Or.inr (Or.inl ⟨j, ?_, hin⟩)
        unfold worldOwned
        exact List.mem_append.2 (Or.inr hj)
      · exact Or.inr (Or.inr hfr_o)
  have hFO_world : FrameOutside s post
      (worldOwned s S Nd ++ R16WkAcctWs.bufRegions [] s ++ [freeGap s]) (heapFree s) := by
    intro a hnot_list hnot_hf
    exact hfr0 a
      (fun j hj hcj => hnot_list j (by simp [List.mem_singleton.1 hj]) hcj)
      hnot_hf
  exact ⟨S, Nd', fun _ h => h, ⟨hT_post, hJ_post, hF_post, hTr_post⟩, hOG_world, hFO_world, hQ⟩

/-- Forget a decoder's returned-root refinement while retaining its world frame. -/
theorem worldStepSc_forget_extra {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (h : R16WkAcctWs.WorldStepSc R gw keep Q s r post) :
    R16WkAcctWs.WorldStepSc R gw keep NoExtra s r post := by
  obtain ⟨⟨hA, hhp, hG, hK, hW⟩, hsp⟩ := h
  refine ⟨⟨hA, hhp, hG, hK, fun S Nd hWT hD => ?_⟩, hsp⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hfr, _⟩ := hW S Nd hWT hD
  exact ⟨S', Nd', hsub, hWT', hOG, hfr, trivial⟩

/-- A decoder which only adds fresh nodes preserves the EVM frame chain and the
witness database, as well as exposing its returned root to its caller. -/
theorem decoderNodeStep_evm_and_witness {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hInv : EvmInv s) (hdb : WitnessDbOK s)
    (hstep : ∀ Nd, NodeHeap s Nd → ∃ Nd', DecoderNodeStep s post Nd Nd' ∧
      RetRootIn s r post [] Nd') :
    EvmStep ["heap_ptr", "scratch_ptr"] s post ∧ WitnessDbOK post ∧
      R16WkAcctWs.WorldStepSc (R16WkAcctWs.bufRegions []) ["heap_ptr", "scratch_ptr"]
        EvmBase.stdKeep RetRootIn s r post := by
  have hW : WorldOK s := ⟨hInv.1, hInv.2.elim fun S hS => ⟨S, hS.1⟩⟩
  have hfull := worldStepSc_of_decoderNodeStep hW hstep
  have hplain := worldStepSc_forget_extra hfull
  have hB : R16WkAcctWs.ValidBufList [] := by intro p hp; cases hp
  have hgw : R16WkAcctWs.SafeStepGlobals ["heap_ptr", "scratch_ptr"] := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp
  exact ⟨evmStep_of_worldStepSc hB hgw hInv.1 hInv.2 hplain,
    witnessDbOK_of_worldStepSc hB hgw hInv.1 hdb hplain, hfull⟩

theorem nodeStep_of_stepFrame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (ha : ArenaReady s) (hNd : NodeHeap s Nd)
    (hbe : post.be = s.be)
    (hsf : ResolveDecodeStep.StepFrame s post) :
    R14Shards.NodeStep s post Nd Nd ∧ FrameOutside s post [freeGap s] (heapFree s) := by
  obtain ⟨hapost, hgrow, hfmp_eq, hsp_le, hfo, hglob⟩ := hsf
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hhe_ge : heapLimit ≤ heapEnd := by decide
  have hsep : heapLimit ≤ scratchStart := by decide
  have hhp_hi_s : globN s "heap_ptr" ≤ heapLimit := ha.2.2.1
  have hfmp_lo_s : scratchStart ≤ globN s "frame_mem_ptr" := ha.2.2.2.1
  have hmem_lt : ∀ a : BitVec 64, a.toNat + 8 ≤ globN s "heap_ptr" → post.memory a = s.memory a := by
    intro a ha_lt
    apply hfo a
    · intro i hi hch
      simp only [List.mem_singleton] at hi; subst hi
      dsimp [CellHits] at hch
      omega
    · intro hch
      dsimp [CellHits] at hch
      omega
  have halloc_heap : ∀ {n : Nat}, n ∈ Nd → Inside (nodeIvl s n) sourceBase (globN s "heap_ptr") := by
    intro n hn
    have hp := hNd.1 n hn
    rcases hp.2.1 with h1 | h2
    · exact h1
    · have := hp.2.2.1.2; have := ha.2.2.2.2.1
      obtain ⟨hsz, _, _⟩ := R14Shards.nodeSize_bounds (memW s n)
      dsimp [nodeIvl, Inside] at *; omega
  have hold_word_eq : ∀ n ∈ Nd, ∀ off, off + 8 ≤ nodeSize (memW s n) →
      memW post (n + off) = memW s (n + off) := by
    intro n hn off hoff
    have hins := halloc_heap hn
    dsimp [nodeIvl, Inside] at hins
    have hlt : n + off < globN s "heap_ptr" := by omega
    have hlt64 : n + off < 2 ^ 64 := by omega
    unfold memW
    rw [hmem_lt (BitVec.ofNat 64 (n + off)) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]; omega)]
  have hkinds : ∀ n ∈ Nd, memW post n = memW s n := by
    intro n hn
    obtain ⟨hsz, _, _⟩ := R14Shards.nodeSize_bounds (memW s n)
    simpa using hold_word_eq n hn 0 (by omega)
  have hivl_eq : ∀ n ∈ Nd, nodeIvl post n = nodeIvl s n := by
    intro n hn; simp [nodeIvl, hkinds n hn]
  have hNd_post : NodeHeap post Nd := by
    refine ⟨?_, ?_⟩
    · intro x hx
      have hp := hNd.1 x hx
      have hx_in := halloc_heap hx
      rw [hkinds x hx, hivl_eq x hx]
      refine ⟨hp.1, Or.inl ⟨hx_in.1, Nat.le_trans hx_in.2 hgrow⟩, hp.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · obtain ⟨ha1, ha2, _⟩ := hp.2.2.2.1
        exact Wave8Contracts.M26.wordsOK_of_guestInv post hapost.1 x (nodeSize (memW s x))
          ha1 ha2 hp.2.2.1.1 (Nat.le_trans hp.2.2.1.2 hhe_ge)
      · intro hk2
        have hsz2 : nodeSize (memW s x) = 56 := by simp [nodeSize, hk2]
        rw [hold_word_eq x hx 48 (by omega)]
        exact hp.2.2.2.2.1 hk2
      · intro hk3 i hi
        have hsz3 : nodeSize (memW s x) = 176 := by simp [nodeSize, hk3]
        have heq : x + 32 + 8 * i = x + (32 + 8 * i) := by omega
        rw [heq, hold_word_eq x hx (32 + 8 * i) (by omega), ← heq]
        exact hp.2.2.2.2.2.1 hk3 i hi
      · intro hk12
        have hsz12 : 56 ≤ nodeSize (memW s x) := by
          rcases hk12 with hk1 | hk2
          · simp [nodeSize, hk1]
          · simp [nodeSize, hk2]
        rw [hold_word_eq x hx 32 (by omega), hold_word_eq x hx 40 (by omega)]
        have hk := hp.2.2.2.2.2.2.1 hk12
        by_cases hz : memW s (x + 40) = 0
        · exact Or.inl hz
        obtain ⟨hplo, hheap, hphi⟩ := R14Shards.keyIn_heap ha hk hz
        obtain ⟨hnib, _, hi, hd⟩ := hk.resolve_left hz
        refine Or.inr ⟨?_, Or.inl ⟨hi.1, by omega⟩, hi, ?_⟩
        · intro k hkl
          have ha64 : memW s (x + 32) + k < 2 ^ 64 := by omega
          let c := panByteAlignHOL (BitVec.ofNat 64 (memW s (x + 32) + k))
          have hc : c.toNat = (memW s (x + 32) + k) / 8 * 8 := R14Shards.byteCell_toNat ha64
          have hptr8 : globN s "heap_ptr" % 8 = 0 := ha.2.2.2.2.2.2.1
          have heq := hmem_lt c (by omega)
          have hb : memB post (memW s (x + 32) + k) = memB s (memW s (x + 32) + k) := by
            unfold memB
            change (match post.memory c with | .word v => (panGetByteHOL _ v post.be).toNat) =
              (match s.memory c with | .word v => (panGetByteHOL _ v s.be).toNat)
            rw [heq, hbe]
          rw [hb]
          exact hnib k hkl
        · intro n hn
          simpa only [nodeIvl, hkinds n hn] using hd n hn
      · obtain ⟨hsz32, _, _⟩ := R14Shards.nodeSize_bounds (memW s x)
        rw [hold_word_eq x hx 16 (by omega)]
        exact hp.2.2.2.2.2.2.2.1
      · intro hk1
        have hsz1 : nodeSize (memW s x) = 64 := by simp [nodeSize, hk1]
        rw [hold_word_eq x hx 56 (by omega)]
        exact hp.2.2.2.2.2.2.2.2.1 hk1
      · intro hk3
        have hsz3 : nodeSize (memW s x) = 176 := by simp [nodeSize, hk3]
        rw [hold_word_eq x hx 168 (by omega)]
        exact hp.2.2.2.2.2.2.2.2.2 hk3
    · intro x hx y hy hxy
      rw [hivl_eq x hx, hivl_eq y hy]
      exact hNd.2 x hx y hy hxy
  have hfr_node : FrameOutside s post
      ((Nd.map fun n => nodeIvl s n) ++
        [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") := by
    intro a hnot hfresh
    exact hfo a
      (fun j hj hcj => hnot j (List.mem_append.2 (Or.inr hj)) hcj)
      hfresh
  have hfr0 : FrameOutside s post [freeGap s] (heapFree s) := by
    simpa only [freeGap, heapFree, List.nil_append] using hfo
  exact ⟨⟨hapost, hgrow, hsp_le, hbe, hNd_post, fun _ h => h, hkinds, fun _ h => Or.inl h, hfr_node, hglob⟩, hfr0⟩

theorem decoderNodeStep_of_stepFrame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (ha : ArenaReady s) (hNd : NodeHeap s Nd)
    (hbe : post.be = s.be)
    (hsf : ResolveDecodeStep.StepFrame s post) :
    DecoderNodeStep s post Nd Nd := by
  obtain ⟨hst, hfr0⟩ := nodeStep_of_stepFrame ha hNd hbe hsf
  exact decoderNodeStep_of_heap_frame ha hNd hst hfr0

theorem stepFrame_of_worldEff {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (heff : R16Shards.WorldEff s post [] [] R16Shards.wsGw) :
    ResolveDecodeStep.StepFrame s post := by
  refine ⟨heff.arena, heff.hp_lo, heff.fmp_eq, heff.sp_hi, ?_, ?_⟩
  · intro a hkeep hfresh
    by_contra hne
    rcases heff.cell_frame a hne with ⟨_, h, _⟩ | ⟨_, h, _⟩ | hfg | hhf
    · cases h
    · cases h
    · exact hkeep _ (List.mem_singleton.2 rfl)
        (by exact hfg.2)
    · exact hfresh
        (by exact hhf.2)
  · intro k hk
    exact heff.gw_kept k hk

theorem decoderNodeStep_of_worldEff {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (ha : ArenaReady s) (hNd : NodeHeap s Nd)
    (heff : R16Shards.WorldEff s post [] [] R16Shards.wsGw) :
    DecoderNodeStep s post Nd Nd :=
  decoderNodeStep_of_stepFrame ha hNd heff.be (stepFrame_of_worldEff heff)

theorem memB_kept_below_hp_of_stepFrame {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (ha : ArenaReady s) (hbe : post.be = s.be)
    (hsf : ResolveDecodeStep.StepFrame s post)
    {b : Nat} (hb : b < globN s "heap_ptr") :
    memB post b = memB s b := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hsep : heapLimit ≤ scratchStart := by decide
  have hhp_hi : globN s "heap_ptr" ≤ heapLimit := ha.2.2.1
  have hfmp_lo : scratchStart ≤ globN s "frame_mem_ptr" := ha.2.2.2.1
  have hhp8 : globN s "heap_ptr" % 8 = 0 := ha.2.2.2.2.2.2.1
  have hb64 : b < 2 ^ 64 := by omega
  let c := panByteAlignHOL (BitVec.ofNat 64 b)
  have hc : c.toNat = b / 8 * 8 := R14Shards.byteCell_toNat hb64
  have hc_lt : c.toNat < globN s "heap_ptr" := by omega
  have hmem_c : post.memory c = s.memory c := by
    apply hsf.2.2.2.2.1 c
    · intro i hi hch; simp only [List.mem_singleton] at hi; subst hi
      unfold CellHits at hch; omega
    · intro hch; unfold CellHits at hch; omega
  unfold memB
  change (match post.memory c with | .word v => (panGetByteHOL _ v post.be).toNat) =
    (match s.memory c with | .word v => (panGetByteHOL _ v s.be).toNat)
  rw [hmem_c, hbe]

theorem memW_kept_below_hp_of_stepFrame {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (ha : ArenaReady s) (hsf : ResolveDecodeStep.StepFrame s post)
    {a : Nat} (ha_lt : a + 8 ≤ globN s "heap_ptr") :
    memW post a = memW s a := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hsep : heapLimit ≤ scratchStart := by decide
  have hhp_hi : globN s "heap_ptr" ≤ heapLimit := ha.2.2.1
  have hfmp_lo : scratchStart ≤ globN s "frame_mem_ptr" := ha.2.2.2.1
  have ha64 : a < 2 ^ 64 := by omega
  have hmem : post.memory (BitVec.ofNat 64 a) = s.memory (BitVec.ofNat 64 a) := by
    apply hsf.2.2.2.2.1
    · intro i hi hch; simp only [List.mem_singleton] at hi; subst hi
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64] at hch
      unfold CellHits at hch; omega
    · intro hch
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64] at hch
      unfold CellHits at hch; omega
  unfold memW
  rw [hmem]

def RetOK (Q : ValueHOL 64 → Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) : Prop :=
  ∀ v, (evaluateHOLFiniteState s p).1 = some (.returned v) → Q v

theorem RetOK.seq {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (ha : RetOK Q s a) (hb : ∀ mid, evaluateHOLFiniteState s a = (none, mid) → RetOK Q mid b) :
    RetOK Q s (.seq a b) := by
  intro v hv
  rw [evaluateHOLFiniteState_seq_line780] at hv
  rcases hr : evaluateHOLFiniteState s a with ⟨r, mid⟩
  rw [hr] at hv
  cases r with
  | none => exact hb mid hr v hv
  | some _ => apply ha v; rw [hr]; simpa using hv

theorem RetOK.ite {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {yes no : ProgHOL 64}
    (h : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → (w ≠ 0 → RetOK Q s yes) ∧ (w = 0 → RetOK Q s no)) :
    RetOK Q s (.ite c yes no) := by
  intro v hv
  rw [evaluateHOLFiniteState_ite] at hv
  split at hv
  · rename_i w hw
    split at hv
    · exact (h w hw).2 (by assumption) v hv
    · exact (h w hw).1 (by assumption) v hv
  · simp at hv

theorem RetOK.dec {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS}
    {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (h : ∀ v, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) init =
      some v → shapeEqHOL sh (shapeOfHOLExact v) = true → RetOK Q (setVarHOLFinite n v s) body) :
    RetOK Q s (.dec n sh init body) := by
  intro v hv
  rw [evaluateHOLFiniteState_dec_total] at hv
  dsimp only at hv
  split at hv
  · simp at hv
  · rename_i val hval
    split at hv
    · rename_i hsh; exact h val hval hsh v hv
    · simp at hv

theorem RetOK.ret {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    (h : ∀ v, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e =
      some v → Q v) :
    RetOK Q s (.return e) := by
  intro v hv
  rw [evaluateHOLFiniteState_return] at hv
  split at hv
  · simp at hv
  · rename_i val hval
    split at hv
    · simp at hv; subst hv; exact h val hval
    · simp at hv

theorem RetOK.skip {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} :
    RetOK Q s .skip := by
  intro v hv; rw [evaluateHOLFiniteState_skip] at hv; simp at hv

def abruptProg : ProgHOL 64 → Bool
  | .return _ => true
  | .raise _ _ => true
  | .seq _ b => abruptProg b
  | .dec _ _ _ b => abruptProg b
  | .decCall _ _ _ _ c => abruptProg c
  | .ite _ y n => abruptProg y && abruptProg n
  | _ => false

theorem abruptProg_nonone {F : Type} (p : ProgHOL 64) (h : abruptProg p = true) (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ none := by
  match p, h with
  | .return e, _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | .raise n e, _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  | .seq a b, h =>
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr : evaluateHOLFiniteState s a with ⟨r, mid⟩
    cases r with
    | none => exact abruptProg_nonone b (by simpa [abruptProg] using h) mid
    | some _ => simp
  | .dec n sh e b, h =>
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact abruptProg_nonone b (by simpa [abruptProg] using h) _
      · simp
  | .decCall n sh f args c, h =>
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · simp
    · split
      · simp
      · rename_i body callee rs _
        split
        · simp
        · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, st⟩
          simp only [hrun]
          rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> try simp
          split
          · exact abruptProg_nonone c (by simpa [abruptProg] using h) _
          · simp
  | .ite c y n, h =>
    have hh : abruptProg y = true ∧ abruptProg n = true := by simpa [abruptProg] using h
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact abruptProg_nonone n hh.2 s
      · exact abruptProg_nonone y hh.1 s
    · simp

theorem lookup_rlp_fail_so : originalRuntimeCode.lookup (ofString "rlp_fail") =
    some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_rlp_fail, .one) :=
  lookup_of_guestAst_getElem 105 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_fail) rfl

theorem rlp_fail_noret_so {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_fail)).1 ≠ some (.returned v) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_fail =
      .seq (.raise (ofString "RlpErr") (.var .local (ofString "code"))) (.return (.const 0)) := rfl
  have hraise : ∀ w, (evaluateHOLFiniteState s (.raise (ofString "RlpErr") (.var .local (ofString "code")) :
        ProgHOL 64)).1 ≠ some (.returned w) ∧
      (evaluateHOLFiniteState s (.raise (ofString "RlpErr") (.var .local (ofString "code")) :
        ProgHOL 64)).1 ≠ none := by
    intro w
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  rw [hb, evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s (.raise (ofString "RlpErr") (.var .local (ofString "code")) :
    ProgHOL 64) with ⟨r, mid⟩
  rw [hr] at hraise
  cases r with
  | none => exact absurd rfl (hraise v).2
  | some _ => dsimp only; exact (hraise v).1

theorem call0_noret_so {F : Type} (s : PanSemStateFiniteExact 64 F) (f : MlS) (args : List (ExpHOL 64))
    (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) f args)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨r, st⟩
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> (repeat' split) <;> simp

theorem call0_rlp_fail_nonone_so {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "rlp_fail") args)).1 ≠ none := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · rename_i values _
    split
    · simp
    · rename_i body callee rs hl
      have hb := lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ body _ rs values callee
        (by rw [hcode]; exact lookup_rlp_fail_so) hl
      subst hb
      split
      · simp
      · have hnr := fun w => rlp_fail_noret_so (callEntryStateHOLFinite s callee) w
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_rlp_fail) with ⟨r, st⟩
        rw [hrun] at hnr
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
        exact absurd rfl (hnr w)

theorem call0_flow_locals_so {F : Type} (s : PanSemStateFiniteExact 64 F) (f : MlS) (args : List (ExpHOL 64))
    (mid : PanSemStateFiniteExact 64 F)
    (h : evaluateHOLFiniteState s (.call (some (none, none)) f args) = (none, mid)) :
    mid.locals = s.locals ∧ mid.code = s.code := by
  have hmeta := (evaluateHOLFiniteState_metadata s (.call (some (none, none)) f args)).1
  rw [h] at hmeta
  refine ⟨?_, hmeta⟩
  revert h
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨r, st⟩
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
        intro h; rw [← h]

theorem RetOK.guard {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hcode : s.code = originalRuntimeCode) {c : ExpHOL 64} {args : List (ExpHOL 64)} {rest : ProgHOL 64}
    (h : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → w = 0 → RetOK Q s rest) :
    RetOK Q s (.seq (.ite c (.call (some (none, none)) (ofString "rlp_fail") args) .skip) rest) := by
  apply RetOK.seq
  · apply RetOK.ite
    intro w _
    exact ⟨fun _ v hv => absurd hv (call0_noret_so s _ args v), fun _ => RetOK.skip⟩
  · intro mid hmid
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · rename_i w hw
      split at hmid
      · rename_i hw0
        rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        obtain ⟨-, rfl⟩ := hmid
        exact h w hw hw0
      · exact absurd (by rw [hmid]) (call0_rlp_fail_nonone_so s hcode args)
    · simp at hmid

theorem RetOK.check2 {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hcode : s.code = originalRuntimeCode) {c c' : ExpHOL 64} {args : List (ExpHOL 64)} {rest : ProgHOL 64}
    (hr : RetOK Q s rest) :
    RetOK Q s (.seq (.ite c (.ite c' (.call (some (none, none)) (ofString "rlp_fail") args) .skip) .skip) rest) := by
  apply RetOK.seq
  · apply RetOK.ite
    intro w _
    refine ⟨fun _ => ?_, fun _ => RetOK.skip⟩
    apply RetOK.ite
    intro w' _
    exact ⟨fun _ v hv => absurd hv (call0_noret_so s _ args v), fun _ => RetOK.skip⟩
  · intro mid hmid
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · split at hmid
      · rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        obtain ⟨-, rfl⟩ := hmid
        exact hr
      · rw [evaluateHOLFiniteState_ite] at hmid
        split at hmid
        · split at hmid
          · rw [evaluateHOLFiniteState_skip] at hmid
            simp only [Prod.mk.injEq] at hmid
            obtain ⟨-, rfl⟩ := hmid
            exact hr
          · exact absurd (by rw [hmid]) (call0_rlp_fail_nonone_so s hcode args)
        · simp at hmid
    · simp at hmid

theorem RetOK.branch {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {yes rest : ProgHOL 64} (hab : abruptProg yes = true)
    (hy : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → w ≠ 0 → RetOK Q s yes)
    (hr : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → w = 0 → RetOK Q s rest) :
    RetOK Q s (.seq (.ite c yes .skip) rest) := by
  apply RetOK.seq
  · apply RetOK.ite
    intro w hw
    exact ⟨hy w hw, fun _ => RetOK.skip⟩
  · intro mid hmid
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · rename_i w hw
      split at hmid
      · rename_i hw0
        rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        obtain ⟨-, rfl⟩ := hmid
        exact hr w hw hw0
      · exact absurd (by rw [hmid]) (abruptProg_nonone yes hab s)
    · simp at hmid

theorem RetOK.decCall {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS}
    {sh : ShapeHOL} {f : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (h : ∀ (u : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), shapeEqHOL (shapeOfHOLExact v) sh = true →
      u.code = s.code → (∀ k, k ≠ n → u.locals.lookup k = s.locals.lookup k) →
      u.locals.lookup n = some v → RetOK Q u cont) :
    RetOK Q s (.decCall n sh f args cont) := by
  intro v hv
  rw [evaluateHOLFiniteState_decCall_total] at hv
  split at hv
  · simp at hv
  · split at hv
    · simp at hv
    · rename_i body callee rs _
      split at hv
      · simp at hv
      · have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, st⟩
        rw [hrun] at hmeta
        change st.code = s.code at hmeta
        simp only [hrun] at hv
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only at hv <;> try simp at hv
        split at hv
        · rename_i hsh
          try simp only [Bool.and_eq_true] at hsh
          refine h _ w hsh.1 (by simp [setVarHOLFinite, fixClockHOLFinite, hmeta]) ?_ ?_ v hv
          · intro k hk
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · simp at hv

theorem RetOK.call0 {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F}
    {f : MlS} {args : List (ExpHOL 64)} {rest : ProgHOL 64}
    (h : ∀ mid : PanSemStateFiniteExact 64 F, mid.locals = s.locals → mid.code = s.code → RetOK Q mid rest) :
    RetOK Q s (.seq (.call (some (none, none)) f args) rest) := by
  apply RetOK.seq
  · intro v hv; exact absurd hv (call0_noret_so s f args v)
  · intro mid hmid
    obtain ⟨hloc, hcode⟩ := call0_flow_locals_so s f args mid hmid
    exact h mid hloc hcode

def RlpItemQ (P L : BitVec 64) (v : ValueHOL 64) : Prop :=
  ∃ tag p' n' tot : BitVec 64,
    v = .rStruct [.val (.word tag), .val (.word p'), .val (.word n'), .val (.word tot)] ∧
    (tag = 0#64 ∨ tag = 1#64) ∧
    1 ≤ tot.toNat ∧ tot.toNat ≤ L.toNat ∧
    P.toNat ≤ p'.toNat ∧ p'.toNat + n'.toNat ≤ P.toNat + tot.toNat

theorem lk_set_so {F : Type} (st : PanSemStateFiniteExact 64 F) (k : MlS) (x : ValueHOL 64) (k' : MlS)
    (hk : k ≠ k') : (setVarHOLFinite k x st).locals.lookup k' = st.locals.lookup k' := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk]

theorem lk_set_same_so {F : Type} (st : PanSemStateFiniteExact 64 F) (k : MlS) (x : ValueHOL 64) :
    (setVarHOLFinite k x st).locals.lookup k = some x := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem toNat_sub_one_so (L : BitVec 64) (hL : L ≠ 0#64) : (L - 1#64).toNat = L.toNat - 1 := by
  have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
  rw [BitVec.toNat_sub]; simp; omega

theorem rlp_item_long_branch_ret {F : Type} (st : PanSemStateFiniteExact 64 F)
    (hcode : st.code = originalRuntimeCode)
    (P L B off tag : BitVec 64) (hPL : P.toNat + L.toNat < 2 ^ 64) (hL : L ≠ 0#64)
    (htag : tag = 0#64 ∨ tag = 1#64)
    (hp : st.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : st.locals.lookup (ofString "len") = some (.val (.word L)))
    (hb : st.locals.lookup (ofString "b") = some (.val (.word B)))
    (tailProg : ProgHOL 64)
    (htail : ∀ u : PanSemStateFiniteExact 64 F, ∀ N : BitVec 64,
      u.code = originalRuntimeCode →
      u.locals.lookup (ofString "p") = some (.val (.word P)) →
      u.locals.lookup (ofString "ll") = some (.val (.word (B - off))) →
      u.locals.lookup (ofString "n") = some (.val (.word N)) →
      (B - off).toNat ≤ L.toNat - 1 →
      N.toNat ≤ L.toNat - 1 - (B - off).toNat →
      RetOK (RlpItemQ P L) u tailProg) :
    RetOK (RlpItemQ P L) st
      (.dec (ofString "ll") .one (.op .sub [.var .local (ofString "b"), .const off])
        (.seq (.ite (.cmp .lower (.op .sub [.var .local (ofString "len"), .const 1#64]) (.var .local (ofString "ll")))
            (.call (some (none, none)) (ofString "rlp_fail") [.const 3#64]) .skip)
          (.decCall (ofString "n") .one (ofString "rlp_read_length")
            [.op .add [.var .local (ofString "p"), .const 1#64], .var .local (ofString "ll")]
            (.seq (.ite (.cmp .notLower (.const 55#64) (.var .local (ofString "n")))
                (.call (some (none, none)) (ofString "rlp_fail") [.const 5#64]) .skip)
              (.seq (.ite (.cmp .lower (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64], .var .local (ofString "ll")])
                    (.var .local (ofString "n")))
                  (.call (some (none, none)) (ofString "rlp_fail") [.const 3#64]) .skip)
                tailProg))))) := by
  have hL1 := toNat_sub_one_so L hL
  refine RetOK.dec (fun v hv _ => ?_)
  simp [evalHOLExact, evalListHOLExact, hb, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  set s1 := setVarHOLFinite (ofString "ll") (.val (.word (B - off))) st
  have hc1 : s1.code = originalRuntimeCode := hcode
  have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word P)) := by
    rw [lk_set_so _ _ _ _ (by decide)]; exact hp
  have hl1 : s1.locals.lookup (ofString "len") = some (.val (.word L)) := by
    rw [lk_set_so _ _ _ _ (by decide)]; exact hl
  have hll1 : s1.locals.lookup (ofString "ll") = some (.val (.word (B - off))) := lk_set_same_so _ _ _
  refine RetOK.guard hc1 (fun w hw hw0 => ?_)
  have hll_le : (B - off).toNat ≤ L.toNat - 1 := by
    simp [evalHOLExact, evalListHOLExact, hl1, hll1, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
    subst hw0
    by_contra hc
    have : L - 1#64 < B - off := by rw [BitVec.lt_def, hL1]; omega
    simp [this] at hw
  refine RetOK.decCall (fun u v hsh hcu hloc hn => ?_)
  have hvw : ∃ N : BitVec 64, v = .val (.word N) := by
    rcases v with ⟨⟨N⟩⟩ | fs | ⟨nm, fs⟩ <;> simp_all [shapeEqHOL, shapeOfHOLExact]
  obtain ⟨N, rfl⟩ := hvw
  have hcu' : u.code = originalRuntimeCode := hcu.trans hc1
  have hpu : u.locals.lookup (ofString "p") = some (.val (.word P)) := by
    rw [hloc _ (by decide)]; exact hp1
  have hlu : u.locals.lookup (ofString "len") = some (.val (.word L)) := by
    rw [hloc _ (by decide)]; exact hl1
  have hllu : u.locals.lookup (ofString "ll") = some (.val (.word (B - off))) := by
    rw [hloc _ (by decide)]; exact hll1
  refine RetOK.guard hcu' (fun _ _ _ => ?_)
  refine RetOK.guard hcu' (fun w hw hw0 => ?_)
  have hsub : (L - 1#64 - (B - off)).toNat = L.toNat - 1 - (B - off).toNat := by
    rw [BitVec.toNat_sub, hL1]; have := (B - off).isLt; omega
  have hN_le : N.toNat ≤ L.toNat - 1 - (B - off).toNat := by
    simp [evalHOLExact, evalListHOLExact, hlu, hllu, hn, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
    subst hw0
    by_contra hc
    have : L - 1#64 - (B - off) < N := by rw [BitVec.lt_def, hsub]; omega
    simp [this] at hw
  exact htail u N hcu' hpu hllu hn hll_le hN_le

theorem rlp_item_ret_spec {F : Type} (e : PanSemStateFiniteExact 64 F)
    (hcode : e.code = originalRuntimeCode)
    (P L : BitVec 64) (hPL : P.toNat + L.toNat < 2 ^ 64)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : e.locals.lookup (ofString "len") = some (.val (.word L)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState e (sourceFnBody Guest.Software.guestFn_rlp_item)).1 =
      some (.returned v)) :
    RlpItemQ P L v := by
  revert v hret
  change RetOK (RlpItemQ P L) e (sourceFnBody Guest.Software.guestFn_rlp_item)
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine RetOK.guard hcode (fun w hw hw0 => ?_)
  have hL : L ≠ 0#64 := by
    simp [evalHOLExact, evalListHOLExact, hl, Compiler.Encoders.Asm.wordCmpHOL] at hw
    subst hw0; intro h0; subst h0; simp at hw
  have hL_pos : 0 < L.toNat := by
    by_contra hc; exact hL (BitVec.eq_of_toNat_eq (by simp; omega))
  have hL1 := toNat_sub_one_so L hL
  refine RetOK.dec (fun vb hvb _ => ?_)
  have hvb_w : ∃ B : BitVec 64, vb = .val (.word B) := by
    simp only [evalHOLExact] at hvb
    split at hvb
    · dsimp only [panMemLoadByteHOL] at hvb
      split at hvb
      · simp only [Option.map_some, Option.some.injEq] at hvb
        exact ⟨_, hvb.symm⟩
      · simp at hvb
    · simp at hvb
  obtain ⟨B, rfl⟩ := hvb_w
  set e1 := setVarHOLFinite (ofString "b") (.val (.word B)) e
  have hc1 : e1.code = originalRuntimeCode := hcode
  have hp1 : e1.locals.lookup (ofString "p") = some (.val (.word P)) := by
    rw [lk_set_so _ _ _ _ (by decide)]; exact hp
  have hl1 : e1.locals.lookup (ofString "len") = some (.val (.word L)) := by
    rw [lk_set_so _ _ _ _ (by decide)]; exact hl
  have hb1 : e1.locals.lookup (ofString "b") = some (.val (.word B)) := lk_set_same_so _ _ _
  refine RetOK.branch (by rfl) (fun _ _ _ => RetOK.ret (fun v hv => ?_)) (fun _ _ _ => ?_)
  · simp [evalHOLExact, evalListHOLExact, hp1] at hv
    subst hv
    exact ⟨0#64, P, 1#64, 1#64, rfl, Or.inl rfl, by decide, hL_pos, le_rfl, le_rfl⟩
  refine RetOK.branch (by rfl) (fun _ _ _ => RetOK.dec (fun v hv _ => ?_)) (fun _ _ _ => ?_)
  · simp [evalHOLExact, evalListHOLExact, hb1, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
    subst hv
    set e2 := setVarHOLFinite (ofString "n") (.val (.word (B - 128#64))) e1
    have hc2 : e2.code = originalRuntimeCode := hcode
    have hp2 : e2.locals.lookup (ofString "p") = some (.val (.word P)) := by
      rw [lk_set_so _ _ _ _ (by decide)]; exact hp1
    have hl2 : e2.locals.lookup (ofString "len") = some (.val (.word L)) := by
      rw [lk_set_so _ _ _ _ (by decide)]; exact hl1
    have hn2 : e2.locals.lookup (ofString "n") = some (.val (.word (B - 128#64))) := lk_set_same_so _ _ _
    refine RetOK.guard hc2 (fun w hw hw0 => ?_)
    have hN : (B - 128#64).toNat ≤ L.toNat - 1 := by
      simp [evalHOLExact, evalListHOLExact, hl2, hn2, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
      subst hw0; by_contra hc
      have : L - 1#64 < B - 128#64 := by rw [BitVec.lt_def, hL1]; omega
      simp [this] at hw
    refine RetOK.check2 hc2 (RetOK.ret (fun v hv => ?_))
    simp [evalHOLExact, evalListHOLExact, hp2, hn2, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
    subst hv
    have hp_add : (P + 1#64).toNat = P.toNat + 1 := BitVec.toNat_add_of_lt (by change P.toNat + 1 < 2 ^ 64; omega)
    have ht_add : (1#64 + (B - 128#64)).toNat = 1 + (B - 128#64).toNat :=
      BitVec.toNat_add_of_lt (by change 1 + (B - 128#64).toNat < 2 ^ 64; omega)
    exact ⟨0#64, P + 1#64, B - 128#64, 1#64 + (B - 128#64), rfl, Or.inl rfl,
      by omega, by omega, by omega, by omega⟩
  refine RetOK.branch (by rfl) (fun _ _ _ => ?_) (fun _ _ _ => ?_)
  · refine rlp_item_long_branch_ret e1 hc1 P L B 183#64 0#64 hPL hL (Or.inl rfl) hp1 hl1 hb1 _
      (fun u N _ hpu hllu hnu hll_le hN_le => RetOK.ret (fun v hv => ?_))
    simp [evalHOLExact, evalListHOLExact, hpu, hllu, hnu, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
    subst hv
    have hll_n_le : (B - 183#64).toNat + N.toNat + 1 ≤ L.toNat := by omega
    have h1ll : (1#64 + (B - 183#64)).toNat = 1 + (B - 183#64).toNat :=
      BitVec.toNat_add_of_lt (by change 1 + (B - 183#64).toNat < 2 ^ 64; omega)
    have hp_add : (P + (1#64 + (B - 183#64))).toNat = P.toNat + 1 + (B - 183#64).toNat := by
      rw [BitVec.toNat_add_of_lt (by rw [h1ll]; omega), h1ll]; omega
    have hllN : (B - 183#64 + N).toNat = (B - 183#64).toNat + N.toNat :=
      BitVec.toNat_add_of_lt (by omega)
    have ht_lt : (1#64 : BitVec 64).toNat + (B - 183#64 + N).toNat < 2 ^ 64 := by
      have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
      rw [h1, hllN]; omega
    have ht_add : (1#64 + (B - 183#64 + N)).toNat = 1 + (B - 183#64).toNat + N.toNat := by
      rw [BitVec.toNat_add_of_lt ht_lt, hllN]
      have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
      rw [h1]; omega
    exact ⟨0#64, P + (1#64 + (B - 183#64)), N, 1#64 + (B - 183#64 + N), rfl, Or.inl rfl,
      by rw [ht_add]; omega, by rw [ht_add]; omega, by rw [hp_add]; omega, by rw [hp_add, ht_add]; omega⟩
  refine RetOK.branch (by rfl) (fun _ _ _ => RetOK.dec (fun v hv _ => ?_)) (fun _ _ _ => ?_)
  · simp [evalHOLExact, evalListHOLExact, hb1, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
    subst hv
    set e2 := setVarHOLFinite (ofString "n") (.val (.word (B - 192#64))) e1
    have hc2 : e2.code = originalRuntimeCode := hcode
    have hp2 : e2.locals.lookup (ofString "p") = some (.val (.word P)) := by
      rw [lk_set_so _ _ _ _ (by decide)]; exact hp1
    have hl2 : e2.locals.lookup (ofString "len") = some (.val (.word L)) := by
      rw [lk_set_so _ _ _ _ (by decide)]; exact hl1
    have hn2 : e2.locals.lookup (ofString "n") = some (.val (.word (B - 192#64))) := lk_set_same_so _ _ _
    refine RetOK.guard hc2 (fun w hw hw0 => ?_)
    have hN : (B - 192#64).toNat ≤ L.toNat - 1 := by
      simp [evalHOLExact, evalListHOLExact, hl2, hn2, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
      subst hw0; by_contra hc
      have : L - 1#64 < B - 192#64 := by rw [BitVec.lt_def, hL1]; omega
      simp [this] at hw
    refine RetOK.call0 (fun mid hloc _ => RetOK.ret (fun v hv => ?_))
    have hpm : mid.locals.lookup (ofString "p") = some (.val (.word P)) := by rw [hloc]; exact hp2
    have hnm : mid.locals.lookup (ofString "n") = some (.val (.word (B - 192#64))) := by rw [hloc]; exact hn2
    simp [evalHOLExact, evalListHOLExact, hpm, hnm, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
    subst hv
    have hp_add : (P + 1#64).toNat = P.toNat + 1 := BitVec.toNat_add_of_lt (by change P.toNat + 1 < 2 ^ 64; omega)
    have ht_add : (1#64 + (B - 192#64)).toNat = 1 + (B - 192#64).toNat :=
      BitVec.toNat_add_of_lt (by change 1 + (B - 192#64).toNat < 2 ^ 64; omega)
    exact ⟨1#64, P + 1#64, B - 192#64, 1#64 + (B - 192#64), rfl, Or.inr rfl,
      by omega, by omega, by omega, by omega⟩
  · refine rlp_item_long_branch_ret e1 hc1 P L B 247#64 1#64 hPL hL (Or.inr rfl) hp1 hl1 hb1 _
      (fun u N _ hpu hllu hnu hll_le hN_le => RetOK.call0 (fun mid hloc _ => RetOK.ret (fun v hv => ?_)))
    have hpm : mid.locals.lookup (ofString "p") = some (.val (.word P)) := by rw [hloc]; exact hpu
    have hllm : mid.locals.lookup (ofString "ll") = some (.val (.word (B - 247#64))) := by rw [hloc]; exact hllu
    have hnm : mid.locals.lookup (ofString "n") = some (.val (.word N)) := by rw [hloc]; exact hnu
    simp [evalHOLExact, evalListHOLExact, hpm, hllm, hnm, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
    subst hv
    have hll_n_le : (B - 247#64).toNat + N.toNat + 1 ≤ L.toNat := by omega
    have h1ll : (1#64 + (B - 247#64)).toNat = 1 + (B - 247#64).toNat :=
      BitVec.toNat_add_of_lt (by change 1 + (B - 247#64).toNat < 2 ^ 64; omega)
    have hp_add : (P + (1#64 + (B - 247#64))).toNat = P.toNat + 1 + (B - 247#64).toNat := by
      rw [BitVec.toNat_add_of_lt (by rw [h1ll]; omega), h1ll]; omega
    have hllN : (B - 247#64 + N).toNat = (B - 247#64).toNat + N.toNat :=
      BitVec.toNat_add_of_lt (by omega)
    have ht_lt : (1#64 : BitVec 64).toNat + (B - 247#64 + N).toNat < 2 ^ 64 := by
      have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
      rw [h1, hllN]; omega
    have ht_add : (1#64 + (B - 247#64 + N)).toNat = 1 + (B - 247#64).toNat + N.toNat := by
      rw [BitVec.toNat_add_of_lt ht_lt, hllN]
      have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
      rw [h1]; omega
    exact ⟨1#64, P + (1#64 + (B - 247#64)), N, 1#64 + (B - 247#64 + N), rfl, Or.inr rfl,
      by rw [ht_add]; omega, by rw [ht_add]; omega, by rw [hp_add]; omega, by rw [hp_add, ht_add]; omega⟩

theorem lookup_rlp_item_so :
    originalRuntimeCode.lookup (ofString "rlp_item") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_item, .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 107 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item) rfl

theorem lookup_rlp_decode_fully_so :
    originalRuntimeCode.lookup (ofString "rlp_decode_fully") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_decode_fully, .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 108 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_decode_fully) rfl

theorem sf_rlp_decode_fully_so :
    WritesWithin (fun _s => []) ["heap_ptr", "scratch_ptr"] (ofString "rlp_decode_fully") := by
  refine ⟨_, _, _, lookup_rlp_decode_fully_so, ?_⟩
  intro F s hcode hAR _hlookup hnt hres
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_decode_fully =
      .decCall (ofString "it") (.comb [.one, .one, .one, .one]) (ofString "rlp_item")
        [.var .local (ofString "p"), .var .local (ofString "len")]
        (.seq
          (.ite (.cmp .notEqual (.rfield 3 (.var .local (ofString "it"))) (.var .local (ofString "len")))
            (.call (some (none, none)) (ofString "rlp_fail") [.const 6#64])
            .skip)
          (.return (.var .local (ofString "it")))) := rfl
  have hprog : ResolveDecodeStep.StepFlowProg (sourceFnBody Guest.Software.guestFn_rlp_decode_fully) := by
    rw [hbody]
    exact ResolveDecodeStep.StepFlowProg.decCall_ww
      (by intro x hx; simp at hx; subst hx; simp)
      R10Shards.P02.ww_rlp_item _ _ _
      (ResolveDecodeStep.StepFlowProg.seq
        (ResolveDecodeStep.StepFlowProg.ite _
          (ResolveDecodeStep.StepFlowProg.call0_ro R13.ro_rlp_fail _)
          ResolveDecodeStep.StepFlowProg.skip)
        (ResolveDecodeStep.StepFlowProg.ret _))
  exact ResolveDecodeStep.stepFrame_to_ww (hprog s hcode hAR hnt (Or.inr (Or.inr (Or.inr hres))))

theorem rlp_decode_fully_ret_spec {F : Type} (e : PanSemStateFiniteExact 64 F)
    (hcode : e.code = originalRuntimeCode)
    (P L : BitVec 64) (hPL : P.toNat + L.toNat < 2 ^ 64)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : e.locals.lookup (ofString "len") = some (.val (.word L)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState e (sourceFnBody Guest.Software.guestFn_rlp_decode_fully)).1 =
      some (.returned v)) :
    RlpItemQ P L v := by
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_decode_fully =
      .decCall (ofString "it") (.comb [.one, .one, .one, .one]) (ofString "rlp_item")
        [.var .local (ofString "p"), .var .local (ofString "len")]
        (.seq
          (.ite (.cmp .notEqual (.rfield 3 (.var .local (ofString "it"))) (.var .local (ofString "len")))
            (.call (some (none, none)) (ofString "rlp_fail") [.const 6#64])
            .skip)
          (.return (.var .local (ofString "it")))) := rfl
  rw [hbody, evaluateHOLFiniteState_decCall_total] at hret
  have hargs : evalListHOLFinite e (h := fun a => Classical.propDecidable (e.memaddrs a))
      [.var .local (ofString "p"), .var .local (ofString "len")] =
      some [.val (.word P), .val (.word L)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hl]
  rcases hl_i : lookupCodeHOLFinite e.code.lookup (ofString "rlp_item") [.val (.word P), .val (.word L)] with
    _ | ⟨body_i, callee_i, ret_i⟩
  · rw [hargs] at hret; dsimp only at hret; rw [hl_i] at hret; simp at hret
  · rw [hargs] at hret; dsimp only at hret; rw [hl_i] at hret; dsimp only at hret
    have hsame_i := lookupCodeHOLFinite_installed_body e.code.lookup _
      [(ofString "p", .one), (ofString "len", .one)] (sourceFnBody Guest.Software.guestFn_rlp_item) body_i
      (.comb [.one, .one, .one, .one]) ret_i [.val (.word P), .val (.word L)] callee_i
      (by rw [hcode]; exact lookup_rlp_item_so) hl_i
    subst hsame_i
    have hret_i := lookupCodeHOLFinite_installed_return e _
      [(ofString "p", .one), (ofString "len", .one)] (sourceFnBody Guest.Software.guestFn_rlp_item)
      (sourceFnBody Guest.Software.guestFn_rlp_item)
      (.comb [.one, .one, .one, .one]) ret_i [.val (.word P), .val (.word L)] callee_i
      (by rw [hcode]; exact lookup_rlp_item_so) hl_i
    subst hret_i
    have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup _ [.val (.word P), .val (.word L)]
      _ callee_i _ (by rwa [← hcode])
    simp only [lookupCodeHOLExact, lookup_rlp_item_so, shapeOfHOLExact, shapeEqHOL] at hx
    simp [show ofString "p" ≠ ofString "len" by decide] at hx
    obtain ⟨_, hclk_eq⟩ := hx
    by_cases hz : e.clock = 0
    · simp [hz] at hret
    · simp only [hz, ↓reduceIte] at hret
      try dsimp only at hret
      rw [fixClockHOLFinite_evaluateState] at hret
      let ent := callEntryStateHOLFinite e callee_i
      have hp_ent : ent.locals.lookup (ofString "p") = some (.val (.word P)) := by
        dsimp only [ent, callEntryStateHOLFinite]; rw [← hclk_eq]
        simp [show ofString "p" ≠ ofString "len" by decide]
      have hl_ent : ent.locals.lookup (ofString "len") = some (.val (.word L)) := by
        dsimp only [ent, callEntryStateHOLFinite]; rw [← hclk_eq]
        simp
      rcases hrun_i : evaluateHOLFiniteState (callEntryStateHOLFinite e callee_i)
          (sourceFnBody Guest.Software.guestFn_rlp_item) with ⟨res_i, post_i⟩
      rw [hrun_i] at hret
      rcases res_i with _ | (_ | _ | _ | _ | v_i | _ | _) <;> dsimp only at hret <;> try simp at hret
      split at hret
      · have hqi := rlp_item_ret_spec ent hcode P L hPL hp_ent hl_ent v_i (by dsimp only [ent]; rw [hrun_i])
        let cstate := setVarHOLFinite (ofString "it") v_i { post_i with locals := e.locals }
        have hc_c : cstate.code = originalRuntimeCode := by
          have hm := (evaluateHOLFiniteState_metadata ent (sourceFnBody Guest.Software.guestFn_rlp_item)).1
          dsimp only [ent] at hm; rw [hrun_i] at hm
          exact hm.trans hcode
        have hit_c : cstate.locals.lookup (ofString "it") = some v_i := lk_set_same_so _ _ _
        have hok : RetOK (RlpItemQ P L) cstate
            (.seq
              (.ite (.cmp .notEqual (.rfield 3 (.var .local (ofString "it"))) (.var .local (ofString "len")))
                (.call (some (none, none)) (ofString "rlp_fail") [.const 6#64])
                .skip)
              (.return (.var .local (ofString "it")))) := by
          refine RetOK.guard hc_c (fun _ _ _ => RetOK.ret (fun v' hv' => ?_))
          simp [evalHOLExact, hit_c] at hv'
          subst hv'
          exact hqi
        exact hok v hret
      · simp at hret

/-! ### Section 2c: `rlp_read_length` Byte-Invariance and `rlp_item_total_unchecked` Agreement -/

theorem memW_store_word_exact_so {F : Type}
    {cur post : PanSemStateFiniteExact 64 F}
    {dstExp valExp : ExpHOL 64} {dst w : BitVec 64}
    (hdst : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp =
      some (.val (.word dst)))
    (hval : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp =
      some (.val (.word w)))
    (hflow : evaluateHOLFiniteState cur (.store dstExp valExp) = (none, post)) :
    memW post dst.toNat = w.toNat ∧
    post.locals = cur.locals ∧
    post.globals = cur.globals ∧
    (∀ a : Nat, a < 2 ^ 64 → a ≠ dst.toNat → memW post a = memW cur a) := by
  rw [evaluateHOLFiniteState_store] at hflow
  simp only [hdst, hval, flattenHOL, panMemStoresHOL, panMemStoreHOL] at hflow
  by_cases hd : cur.memaddrs dst
  · simp only [hd, ↓reduceIte, Prod.mk.injEq] at hflow
    obtain ⟨-, rfl⟩ := hflow
    refine ⟨?_, rfl, rfl, ?_⟩
    · unfold memW
      have hbv : BitVec.ofNat 64 dst.toNat = dst := by simp
      rw [hbv]; simp
    · intro a ha64 hne
      unfold memW
      have hbne : BitVec.ofNat 64 a ≠ dst := by
        intro heq
        apply hne
        have h := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64] at h
        exact h
      simp [hbne]
  · simp [hd] at hflow

theorem lookup_rlp_read_length_so :
    originalRuntimeCode.lookup (ofString "rlp_read_length") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_read_length, .one) :=
  lookup_of_guestAst_getElem 106 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_read_length) rfl

theorem lookup_rlp_item_header_so :
    originalRuntimeCode.lookup (ofString "rlp_item_header") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_item_header, .comb [.one, .one, .one]) :=
  lookup_of_guestAst_getElem 109 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item_header) rfl

theorem lookup_rlp_item_total_so :
    originalRuntimeCode.lookup (ofString "rlp_item_total") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_item_total, .one) :=
  lookup_of_guestAst_getElem 112 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item_total) rfl

theorem lookup_rlp_list_count_so :
    originalRuntimeCode.lookup (ofString "rlp_list_count") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_list_count, .one) :=
  lookup_of_guestAst_getElem 113 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_list_count) rfl

theorem lookup_rlp_item_total_unchecked_so :
    originalRuntimeCode.lookup (ofString "rlp_item_total_unchecked") =
      some ([(ofString "p", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked, .one) :=
  lookup_of_guestAst_getElem 114 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item_total_unchecked) rfl

theorem lookup_rlp_list_to_slices_so :
    originalRuntimeCode.lookup (ofString "rlp_list_to_slices") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_list_to_slices, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 115 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_list_to_slices) rfl

theorem RetOK.decCall' {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS}
    {sh : ShapeHOL} {f : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (h : ∀ (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (v : ValueHOL 64),
      evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address)) args =
        some values →
      lookupCodeHOLFinite s.code.lookup f values = some (body, callee, rs) →
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 = some (.returned v) →
      shapeEqHOL (shapeOfHOLExact v) sh = true →
      ∀ (u : PanSemStateFiniteExact 64 F), u.code = s.code →
        (∀ k, k ≠ n → u.locals.lookup k = s.locals.lookup k) → u.locals.lookup n = some v →
        RetOK Q u cont) :
    RetOK Q s (.decCall n sh f args cont) := by
  intro v hv
  rw [evaluateHOLFiniteState_decCall_total] at hv
  split at hv
  · simp at hv
  · rename_i values hargs
    split at hv
    · simp at hv
    · rename_i body callee rs hl
      split at hv
      · simp at hv
      · have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, st⟩
        rw [hrun] at hmeta
        change st.code = s.code at hmeta
        simp only [hrun] at hv
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only at hv <;> try simp at hv
        split at hv
        · rename_i hsh
          try simp only [Bool.and_eq_true] at hsh
          refine h values body callee rs w hargs hl (by rw [hrun]) hsh.1 _
            (by simp [setVarHOLFinite, fixClockHOLFinite, hmeta]) ?_ ?_ v hv
          · intro k hk
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · simp at hv

theorem callee_p_n_so {fname : MlS} {body0 : ProgHOL 64} {rs0 : ShapeHOL}
    (hlook : originalRuntimeCode.lookup fname =
      some ([(ofString "p", .one), (ofString "n", .one)], body0, rs0))
    (v1 v2 : ValueHOL 64) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (rs : ShapeHOL)
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup fname [v1, v2] =
      some (body, callee, rs)) :
    body = body0 ∧ callee.lookup (ofString "p") = some v1 ∧ callee.lookup (ofString "n") = some v2 := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
  split at hl
  · simp at hl
  · rename_i b cl r heq
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    simp only [lookupCodeHOLExact, hlook] at heq
    split at heq
    · simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      refine ⟨rfl, ?_, by simp⟩
      simp [List.zip, List.foldl, show ofString "p" ≠ ofString "n" by decide]
    · simp at heq

theorem callee_p_len_so {fname : MlS} {body0 : ProgHOL 64} {rs0 : ShapeHOL}
    (hlook : originalRuntimeCode.lookup fname =
      some ([(ofString "p", .one), (ofString "len", .one)], body0, rs0))
    (v1 v2 : ValueHOL 64) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (rs : ShapeHOL)
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup fname [v1, v2] =
      some (body, callee, rs)) :
    body = body0 ∧ callee.lookup (ofString "p") = some v1 ∧ callee.lookup (ofString "len") = some v2 := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
  split at hl
  · simp at hl
  · rename_i b cl r heq
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    simp only [lookupCodeHOLExact, hlook] at heq
    split at heq
    · simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      refine ⟨rfl, ?_, by simp⟩
      simp [List.zip, List.foldl, show ofString "p" ≠ ofString "len" by decide]
    · simp at heq

theorem callee_one_p_so {fname : MlS} {body0 : ProgHOL 64} {rs0 : ShapeHOL}
    (hlook : originalRuntimeCode.lookup fname =
      some ([(ofString "p", .one)], body0, rs0))
    (v1 : ValueHOL 64) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (rs : ShapeHOL)
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup fname [v1] =
      some (body, callee, rs)) :
    body = body0 ∧ callee.lookup (ofString "p") = some v1 := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
  split at hl
  · simp at hl
  · rename_i b cl r heq
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    simp only [lookupCodeHOLExact, hlook] at heq
    split at heq
    · simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact ⟨rfl, by simp [List.zip, List.foldl]⟩
    · simp at heq

theorem loadByte_eq_memB_so {F : Type}
    (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.loadByte e) =
      some v) :
    ∃ a : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e =
        some (.val (.word a)) ∧
      s.memaddrs (panByteAlignHOL (width := 64) a) ∧
      v = .val (.word (BitVec.ofNat 64 (memB s a.toNat))) := by
  simp only [evalHOLExact] at hv
  split at hv
  · rename_i a ha
    dsimp only [panMemLoadByteHOL] at hv
    split at hv
    · rename_i hdom
      simp only [Option.map_some, Option.some.injEq] at hv
      refine ⟨a, ha, hdom, ?_⟩
      rw [← hv]
      unfold memB
      have ha_bv : BitVec.ofNat 64 a.toNat = a := by simp
      rw [ha_bv]
    · simp at hv
  · simp at hv

def rlpReadLenAcc_so (f : Nat → Nat) : Nat → Nat → BitVec 64 → BitVec 64
  | 0, _, acc => acc
  | k + 1, idx, acc => rlpReadLenAcc_so f k (idx + 1) ((acc <<< 8) ||| BitVec.ofNat 64 (f idx))

theorem rlpReadLenAcc_congr_so {f g : Nat → Nat} :
    ∀ (k idx : Nat) (acc : BitVec 64),
      (∀ j, idx ≤ j → j < idx + k → f j = g j) →
      rlpReadLenAcc_so f k idx acc = rlpReadLenAcc_so g k idx acc
  | 0, _, _, _ => rfl
  | k + 1, idx, acc, hfg => by
    unfold rlpReadLenAcc_so
    rw [hfg idx le_rfl (by omega)]
    exact rlpReadLenAcc_congr_so k (idx + 1) _ (fun j hj1 hj2 => hfg j (by omega) (by omega))

def rrlCond_so : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))

def rrlBody_so : ProgHOL 64 :=
  .seq
    (.assign .local (ofString "v")
      (.op .or [.shift .lsl (.var .local (ofString "v")) (.const 8#64),
        .loadByte (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])]))
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))

theorem rrlBody_no_bc_ret_so {F : Type} (st : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState st rrlBody_so).1 ≠ some .break ∧
    (evaluateHOLFiniteState st rrlBody_so).1 ≠ some .continue ∧
    (∀ rv, (evaluateHOLFiniteState st rrlBody_so).1 ≠ some (.returned rv)) := by
  unfold rrlBody_so
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
  split
  · simp
  · split
    · dsimp only
      rw [evaluateHOLFiniteState_assign]
      split <;> [simp; (split <;> simp)]
    · simp

theorem while_rrl_no_return_so {F : Type} (rv : ValueHOL 64) :
    ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock ≤ k →
      (evaluateHOLFiniteState st (.while rrlCond_so rrlBody_so)).1 ≠ some (.returned rv) := by
  intro k
  induction k with
  | zero =>
    intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) rrlCond_so with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]; rw [if_pos (by omega : st.clock = 0)]; simp
  | succ k ih =>
    intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) rrlCond_so with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]
        by_cases hk0 : st.clock = 0
        · rw [if_pos hk0]; simp
        · rw [if_neg hk0]
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) rrlBody_so
          have hb_nr := (rrlBody_no_bc_ret_so (decClockHOLFinite st)).2.2 rv
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) rrlBody_so with ⟨r1, m1⟩
          simp only [hbr] at rem hb_nr ⊢
          cases r1 with
          | none => exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
          | some r1 =>
            cases r1 with
            | «continue» => exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
            | «break» => simp
            | returned v' =>
              intro heq; injection heq with heq'; injection heq' with heq''; subst heq''
              exact hb_nr rfl
            | _ => simp

def RrlInv_so {F : Type} (s0 : PanSemStateFiniteExact 64 F) (P N : BitVec 64)
    (st : PanSemStateFiniteExact 64 F) : Prop :=
  st.memory = s0.memory ∧ st.memaddrs = s0.memaddrs ∧ st.be = s0.be ∧
  ∃ (wi wv : BitVec 64),
    st.locals.lookup (ofString "p") = some (.val (.word P)) ∧
    st.locals.lookup (ofString "n") = some (.val (.word N)) ∧
    st.locals.lookup (ofString "i") = some (.val (.word wi)) ∧
    st.locals.lookup (ofString "v") = some (.val (.word wv)) ∧
    wi.toNat ≤ N.toNat ∧
    rlpReadLenAcc_so (fun k => memB s0 (P.toNat + k)) (N.toNat - wi.toNat) wi.toNat wv =
      rlpReadLenAcc_so (fun k => memB s0 (P.toNat + k)) N.toNat 0 0#64

theorem while_rrlInv_so {F : Type} (s0 : PanSemStateFiniteExact 64 F) (P N : BitVec 64)
    (hfit : P.toNat + N.toNat ≤ 2 ^ 64)
    (k : Nat) (st post : PanSemStateFiniteExact 64 F)
    (hclk : st.clock ≤ k) (hinv : RrlInv_so s0 P N st)
    (hrun : evaluateHOLFiniteState st (.while rrlCond_so rrlBody_so) = (none, post)) :
    post.locals.lookup (ofString "v") =
      some (.val (.word (rlpReadLenAcc_so (fun j => memB s0 (P.toNat + j)) N.toNat 0 0#64))) := by
  induction k generalizing st with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun <;> [simp at hrun; omega]
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun
        obtain ⟨_, _, _, wi, wv, _, hn, hi, hv, hle, hacc⟩ := hinv
        have hge : N.toNat ≤ wi.toNat := by
          simp [evalHOLFinite, rrlCond_so, evalHOLExact, hi, hn, Compiler.Encoders.Asm.wordCmpHOL] at hcond
          omega
        have heq : N.toNat - wi.toNat = 0 := by omega
        rw [heq] at hacc
        dsimp [rlpReadLenAcc_so] at hacc
        rw [hv, hacc]
    · simp at hrun
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) rrlBody_so
          have hbc := rrlBody_no_bc_ret_so (decClockHOLFinite st)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) rrlBody_so with ⟨r1, mid⟩
          rw [hbr] at hrun rem hbc
          cases r1 with
          | none =>
            obtain ⟨hmem, hdom, hbe, wi, wv, hp, hn, hi, hv, hle, hacc⟩ := hinv
            have hlt : wi.toNat < N.toNat := by
              simp [evalHOLFinite, rrlCond_so, evalHOLExact, hi, hn, Compiler.Encoders.Asm.wordCmpHOL] at hcond
              by_contra hge
              have hge' : ¬ (wi < N) := by rw [BitVec.lt_def]; omega
              simp [hge'] at hcond
              exact hnz hcond.symm
            let sd := decClockHOLFinite st
            have hbr' := hbr
            unfold rrlBody_so at hbr'
            rw [evaluateHOLFiniteState_seq_line780] at hbr'
            rcases ha1 : evaluateHOLFiniteState sd
                (.assign .local (ofString "v")
                  (.op .or [.shift .lsl (.var .local (ofString "v")) (.const 8#64),
                    .loadByte (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])])) with ⟨ra1, u1⟩
            rw [ha1] at hbr'
            cases ra1 with
            | some _ => simp at hbr'
            | none =>
              dsimp only at hbr'
              rw [evaluateHOLFiniteState_assign] at ha1
              rcases he1 : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
                  (.op .or [.shift .lsl (.var .local (ofString "v")) (.const 8#64),
                    .loadByte (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])]) with _ | ve1
              · simp [he1] at ha1
              · rw [he1] at ha1
                dsimp only at ha1
                split at ha1
                · simp only [Prod.mk.injEq] at ha1
                  obtain ⟨-, rfl⟩ := ha1
                  have hsd_p : sd.locals.lookup (ofString "p") = some (.val (.word P)) := hp
                  have hsd_i : sd.locals.lookup (ofString "i") = some (.val (.word wi)) := hi
                  have hsd_v : sd.locals.lookup (ofString "v") = some (.val (.word wv)) := hv
                  rcases hlb : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
                      (.loadByte (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])) with _ | vlb
                  · simp [evalHOLExact, evalListHOLExact, hsd_p, hsd_i, hsd_v, wordShiftHOL, wordOpHOL, wordOp,
                      valueIsWord, valueWord] at hlb he1
                    rw [hlb] at he1
                    simp at he1
                  · obtain ⟨addr, haddr, _, rfl⟩ := loadByte_eq_memB_so sd _ vlb hlb
                    simp [evalHOLExact, evalListHOLExact, hsd_p, hsd_i, wordOpHOL, wordOp, valueIsWord, valueWord] at haddr
                    subst haddr
                    have hpwi_nat : (P + wi).toNat = P.toNat + wi.toNat :=
                      BitVec.toNat_add_of_lt (by omega)
                    have hmemB_sd : memB sd (P + wi).toNat = memB s0 (P.toNat + wi.toNat) := by
                      rw [hpwi_nat]; unfold memB
                      have hsd_mem : sd.memory = s0.memory := hmem
                      have hsd_be : sd.be = s0.be := hbe
                      rw [hsd_mem, hsd_be]
                    have hve1 : ve1 = .val (.word ((wv <<< 8) ||| BitVec.ofNat 64 (memB s0 (P.toNat + wi.toNat)))) := by
                      rw [← hmemB_sd]
                      simp [evalHOLExact, evalListHOLExact, hsd_p, hsd_i, hsd_v, wordShiftHOL, wordOpHOL, wordOp,
                        valueIsWord, valueWord] at hlb he1
                      obtain ⟨b8, hb8, hb8_eq⟩ := hlb
                      rw [hb8] at he1
                      simp [wordOpHOL, wordOp, valueIsWord, valueWord] at he1
                      rw [← he1, hb8_eq, ← BitVec.toNat_add, hpwi_nat]
                      congr 2
                      change (wv <<< 8) ||| (BitVec.ofNat 64 (memB sd (P.toNat + wi.toNat)) ||| 0#64) = _
                      simp
                    subst hve1
                    let wv' := (wv <<< 8) ||| BitVec.ofNat 64 (memB s0 (P.toNat + wi.toNat))
                    let u1' := setKvarHOLFinite .local (ofString "v") (.val (.word wv')) sd
                    change evaluateHOLFiniteState u1' _ = (none, mid) at hbr'
                    have hu1_i : u1'.locals.lookup (ofString "i") = some (.val (.word wi)) := by
                      simp [u1', setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsd_i,
                        show ofString "v" ≠ ofString "i" by decide]
                    rw [evaluateHOLFiniteState_assign] at hbr'
                    simp [evalHOLExact, evalListHOLExact, hu1_i, wordOpHOL, wordOp, valueIsWord, valueWord,
                      isValidValueHOLFinite, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL] at hbr'
                    subst hbr'
                    have h1_nat : (1#64 : BitVec 64).toNat = 1 := rfl
                    have hwi1 : (wi + 1#64).toNat = wi.toNat + 1 := by
                      rw [BitVec.toNat_add_of_lt (by rw [h1_nat]; have := N.isLt; omega), h1_nat]
                    have hrem_eq : N.toNat - wi.toNat = (N.toNat - (wi.toNat + 1)) + 1 := by omega
                    rw [hrem_eq] at hacc
                    dsimp [rlpReadLenAcc_so] at hacc
                    have hclk_next :
                        (setKvarHOLFinite .local (ofString "i") (.val (.word (wi + 1#64))) u1').clock ≤ k := by
                      have hsd_clk : sd.clock = st.clock - 1 := rfl
                      have hu2_clk :
                          (setKvarHOLFinite .local (ofString "i") (.val (.word (wi + 1#64))) u1').clock ≤ sd.clock := rem
                      omega
                    refine ih _ hclk_next ?_ hrun
                    refine ⟨hmem, hdom, hbe, wi + 1#64, wv', ?_, ?_, ?_, ?_, by omega, by rw [hwi1]; exact hacc⟩
                    · simp [u1', setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsd_p,
                        show ofString "i" ≠ ofString "p" by decide, show ofString "v" ≠ ofString "p" by decide]
                    · simp [u1', setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                        show sd.locals.lookup (ofString "n") = some (.val (.word N)) from hn,
                        show ofString "i" ≠ ofString "n" by decide, show ofString "v" ≠ ofString "n" by decide]
                    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                    · simp [u1', setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                        show ofString "i" ≠ ofString "v" by decide]
                · simp at ha1
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl hbc.2.1
            | «break» => exact absurd rfl hbc.1
            | _ => simp at hrun
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun
        obtain ⟨_, _, _, wi, wv, _, hn, hi, hv, hle, hacc⟩ := hinv
        have hge : N.toNat ≤ wi.toNat := by
          simp [evalHOLFinite, rrlCond_so, evalHOLExact, hi, hn, Compiler.Encoders.Asm.wordCmpHOL] at hcond
          omega
        have heq : N.toNat - wi.toNat = 0 := by omega
        rw [heq] at hacc
        dsimp [rlpReadLenAcc_so] at hacc
        rw [hv, hacc]
    · simp at hrun

theorem rlp_read_length_ret_eq_acc_so {F : Type}
    (e : PanSemStateFiniteExact 64 F) (hcode : e.code = originalRuntimeCode)
    (P N : BitVec 64) (hfit : P.toNat + N.toNat ≤ 2 ^ 64)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word P)))
    (hn : e.locals.lookup (ofString "n") = some (.val (.word N)))
    (rv : ValueHOL 64)
    (hret : (evaluateHOLFiniteState e (sourceFnBody Guest.Software.guestFn_rlp_read_length)).1 =
      some (.returned rv)) :
    rv = .val (.word (rlpReadLenAcc_so (fun j => memB e (P.toNat + j)) N.toNat 0 0#64)) := by
  revert rv hret
  change RetOK (fun rv => rv = .val (.word (rlpReadLenAcc_so (fun j => memB e (P.toNat + j)) N.toNat 0 0#64))) e
    (sourceFnBody Guest.Software.guestFn_rlp_read_length)
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_read_length =
      .seq
        (.ite (.op .and
            [.cmp .notEqual (.const 0#64) (.cmp .lower (.const 1#64) (.var .local (ofString "n"))),
             .cmp .notEqual (.const 0#64) (.cmp .equal (.loadByte (.var .local (ofString "p"))) (.const 0#64))])
          (.call (some (none, none)) (ofString "rlp_fail") [.const 2#64]) .skip)
        (.dec (ofString "v") .one (.const 0#64)
          (.dec (ofString "i") .one (.const 0#64)
            (.seq (.while rrlCond_so rrlBody_so)
              (.return (.var .local (ofString "v")))))) := rfl
  rw [hbody]
  refine RetOK.guard hcode (fun _ _ _ => ?_)
  refine RetOK.dec (fun vv hvv _ => ?_)
  have hvv_eq : vv = .val (.word 0#64) := by simp [evalHOLExact] at hvv; exact hvv.symm
  subst hvv_eq
  refine RetOK.dec (fun vi hvi _ => ?_)
  have hvi_eq : vi = .val (.word 0#64) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi_eq
  let e2 := setVarHOLFinite (ofString "i") (.val (.word 0#64))
    (setVarHOLFinite (ofString "v") (.val (.word 0#64)) e)
  refine RetOK.seq (fun rv hw => absurd hw (while_rrl_no_return_so rv e2.clock e2 le_rfl))
    (fun mid hmid => ?_)
  have hinv2 : RrlInv_so e P N e2 := by
    refine ⟨rfl, rfl, rfl, 0#64, 0#64, ?_, ?_, ?_, ?_, by simp, by simp⟩
    · simp [e2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
        show ofString "i" ≠ ofString "p" by decide, show ofString "v" ≠ ofString "p" by decide]
    · simp [e2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
        show ofString "i" ≠ ofString "n" by decide, show ofString "v" ≠ ofString "n" by decide]
    · simp [e2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [e2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "i" ≠ ofString "v" by decide]
  have hm_v := while_rrlInv_so e P N hfit e2.clock e2 mid le_rfl hinv2 hmid
  refine RetOK.ret (fun v hv => ?_)
  simp [evalHOLExact, hm_v] at hv
  exact hv.symm

def hval_so (hl pl flag : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word hl), .val (.word pl), .val (.word flag)]

def HdrTotalSpec_so {F : Type} (s0 : PanSemStateFiniteExact 64 F) (P L : BitVec 64) (v : ValueHOL 64) : Prop :=
  ∃ hl pl flag : BitVec 64,
    v = hval_so hl pl flag ∧
    1 ≤ hl.toNat + pl.toNat ∧
    hl.toNat + pl.toNat ≤ L.toNat ∧
    ∀ e2 : PanSemStateFiniteExact 64 F,
      e2.code = originalRuntimeCode →
      e2.locals.lookup (ofString "p") = some (.val (.word P)) →
      (∀ j < L.toNat, memB e2 (P.toNat + j) = memB s0 (P.toNat + j)) →
      ∀ rv2 : ValueHOL 64,
        (evaluateHOLFiniteState e2 (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)).1 =
          some (.returned rv2) →
        rv2 = .val (.word (hl + pl))

theorem rlp_item_header_agree_unchecked_so {F : Type}
    (e1 : PanSemStateFiniteExact 64 F) (hcode1 : e1.code = originalRuntimeCode)
    (P L : BitVec 64) (hfit : P.toNat + L.toNat ≤ 2 ^ 64)
    (hp1 : e1.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl1 : e1.locals.lookup (ofString "len") = some (.val (.word L))) :
    RetOK (HdrTotalSpec_so e1 P L) e1 (sourceFnBody Guest.Software.guestFn_rlp_item_header) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_header,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine RetOK.guard hcode1 (fun w hw hw0 => ?_)
  have hL : L ≠ 0 := by
    intro h; subst h; simp [evalHOLExact, hl1, Compiler.Encoders.Asm.wordCmpHOL] at hw; subst hw0; simp at hw
  have hL_pos : 0 < L.toNat := by
    have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  have hL1 := toNat_sub_one_so L hL
  refine RetOK.dec (fun vb hvb _ => ?_)
  obtain ⟨P', ha1, _, rfl⟩ := loadByte_eq_memB_so e1 _ vb hvb
  simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hp1, Option.some.injEq, ValueHOL.val.injEq,
    HolWordLab.word.injEq] at ha1
  subst ha1
  let B : BitVec 64 := BitVec.ofNat 64 (memB e1 P.toNat)
  set s1 := setVarHOLFinite (ofString "b") (.val (.word B)) e1 with hs1
  have hs1_b : s1.locals.lookup (ofString "b") = some (.val (.word B)) := by
    simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_p : s1.locals.lookup (ofString "p") = some (.val (.word P)) := by
    simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp1,
      show ofString "b" ≠ ofString "p" by decide]
  have hs1_l : s1.locals.lookup (ofString "len") = some (.val (.word L)) := by
    simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl1,
      show ofString "b" ≠ ofString "len" by decide]
  have hc_s1 : s1.code = originalRuntimeCode := hcode1
  refine RetOK.branch (by rfl) (fun w1 hw1 hw1_nz => RetOK.ret (fun v hv => ?_)) (fun w1 hw1 hw1_0 => ?_)
  · have hB_lt128 : B < 128#64 := by
      simp [evalHOLExact, hs1_b, Compiler.Encoders.Asm.wordCmpHOL] at hw1
      by_contra hge; simp [hge] at hw1; exact hw1_nz hw1.symm
    simp [evalHOLExact, evalListHOLExact] at hv; subst hv
    refine ⟨0#64, 1#64, 0#64, rfl, by simp, by simp; omega, ?_⟩
    intro e2 hc2 hp2 hbytes rv2 hret2
    revert rv2 hret2
    change RetOK (fun rv2 => rv2 = .val (.word (0#64 + 1#64))) e2
      (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total_unchecked,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    refine RetOK.dec (fun vb2 hvb2 _ => ?_)
    obtain ⟨P2', ha2, _, rfl⟩ := loadByte_eq_memB_so e2 _ vb2 hvb2
    simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hp2, Option.some.injEq, ValueHOL.val.injEq,
      HolWordLab.word.injEq] at ha2; subst ha2
    have hb2_eq : BitVec.ofNat 64 (memB e2 P.toNat) = B := by
      have h0 := hbytes 0 hL_pos; simp at h0; rw [h0]
    rw [hb2_eq]
    refine RetOK.branch (by rfl) (fun _ _ _ => RetOK.ret (fun v2 hv2 => ?_)) (fun w2' hw2' hw2'_0 => ?_)
    · simp [evalHOLExact] at hv2; exact hv2.symm
    · simp [evalHOLExact, lk_set_same_so, Compiler.Encoders.Asm.wordCmpHOL, hB_lt128] at hw2'
      subst hw2'_0; simp at hw2'
  have hB_ge128 : ¬ (B < 128#64) := by
    simp [evalHOLExact, hs1_b, Compiler.Encoders.Asm.wordCmpHOL] at hw1
    subst hw1_0; intro hlt; simp [hlt] at hw1
  refine RetOK.branch (by rfl) (fun w2 hw2 hw2_nz => RetOK.dec (fun vn hvn _ => ?_)) (fun w2 hw2 hw2_0 => ?_)
  · have hB_le183 : B ≤ 183#64 := by
      simp [evalHOLExact, hs1_b, Compiler.Encoders.Asm.wordCmpHOL] at hw2
      by_contra hgt
      have hnot : ¬ (B ≤ 183#64) := hgt
      simp [hnot] at hw2
      exact hw2_nz hw2.symm
    simp [evalHOLExact, evalListHOLExact, hs1_b, wordOpHOL, wordOp, valueIsWord, valueWord] at hvn; subst hvn
    set s2 := setVarHOLFinite (ofString "n") (.val (.word (B - 128#64))) s1 with hs2
    have hc_s2 : s2.code = originalRuntimeCode := hcode1
    refine RetOK.guard hc_s2 (fun wg hwg hwg0 => ?_)
    have hN : (B - 128#64).toNat ≤ L.toNat - 1 := by
      simp [evalHOLExact, evalListHOLExact, hs2, lk_set_so, lk_set_same_so,
        show ofString "n" ≠ ofString "len" by decide, hs1_l, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hwg
      subst hwg0; by_contra hc
      have : L - 1#64 < B - 128#64 := by rw [BitVec.lt_def, hL1]; omega
      simp [this] at hwg
    refine RetOK.check2 hc_s2 (RetOK.ret (fun v hv => ?_))
    simp [evalHOLExact, evalListHOLExact, hs2, lk_set_so, lk_set_same_so] at hv; subst hv
    have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
    refine ⟨1#64, B - 128#64, 0#64, rfl, by rw [h1]; omega, by rw [h1]; omega, ?_⟩
    intro e2 hc2 hp2 hbytes rv2 hret2
    revert rv2 hret2
    change RetOK (fun rv2 => rv2 = .val (.word (1#64 + (B - 128#64)))) e2
      (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total_unchecked,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    refine RetOK.dec (fun vb2 hvb2 _ => ?_)
    obtain ⟨P2', ha2, _, rfl⟩ := loadByte_eq_memB_so e2 _ vb2 hvb2
    simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hp2, Option.some.injEq, ValueHOL.val.injEq,
      HolWordLab.word.injEq] at ha2; subst ha2
    have hb2_eq : BitVec.ofNat 64 (memB e2 P.toNat) = B := by
      have h0 := hbytes 0 hL_pos; simp at h0; rw [h0]
    rw [hb2_eq]
    refine RetOK.branch (by rfl) (fun w2' hw2' hw2'_nz => ?_) (fun _ _ _ => ?_)
    · simp [evalHOLExact, lk_set_same_so, Compiler.Encoders.Asm.wordCmpHOL, hB_ge128] at hw2'
      exact absurd hw2'.symm hw2'_nz
    refine RetOK.branch (by rfl) (fun _ _ _ => RetOK.ret (fun v2 hv2 => ?_)) (fun w2' hw2' hw2'_0 => ?_)
    · simp [evalHOLExact, evalListHOLExact, lk_set_same_so, wordOpHOL, wordOp, valueIsWord, valueWord] at hv2
      rw [← hv2]; congr 2; bv_omega
    · simp [evalHOLExact, lk_set_same_so, Compiler.Encoders.Asm.wordCmpHOL, hB_le183] at hw2'
      subst hw2'_0; simp at hw2'
  have hB_notle183 : ¬ (B ≤ 183#64) := by
    simp [evalHOLExact, hs1_b, Compiler.Encoders.Asm.wordCmpHOL] at hw2
    subst hw2_0; intro hle; simp [hle] at hw2
  refine RetOK.branch (by rfl) (fun w3 hw3 hw3_nz => ?_) (fun w3 hw3 hw3_0 => ?_)
  · have hB_le191 : B ≤ 191#64 := by
      simp [evalHOLExact, hs1_b, Compiler.Encoders.Asm.wordCmpHOL] at hw3
      by_contra hgt; simp [hgt] at hw3; exact hw3_nz hw3.symm
    refine RetOK.dec (fun vll hvll _ => ?_)
    simp [evalHOLExact, evalListHOLExact, hs1_b, wordOpHOL, wordOp, valueIsWord, valueWord] at hvll; subst hvll
    set LL := B - 183#64
    refine RetOK.guard (by exact hcode1) (fun wg hwg hwg0 => ?_)
    have hLL : LL.toNat ≤ L.toNat - 1 := by
      simp [evalHOLExact, evalListHOLExact, lk_set_so, lk_set_same_so,
        show ofString "ll" ≠ ofString "len" by decide, hs1_l, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hwg
      subst hwg0; by_contra hc
      have hlt_ll : L - 1#64 < LL := by rw [BitVec.lt_def, hL1]; omega
      simp [hlt_ll] at hwg
    refine RetOK.decCall' (fun cvals cbody callee crs vn hargs hlk hret_n _ u hcu hloc hun => ?_)
    have hs_p : (setVarHOLFinite (ofString "ll") (.val (.word LL)) s1).locals.lookup (ofString "p") =
        some (.val (.word P)) := by
      rw [lk_set_so _ _ _ _ (by decide)]; exact hs1_p
    have hs_ll : (setVarHOLFinite (ofString "ll") (.val (.word LL)) s1).locals.lookup (ofString "ll") =
        some (.val (.word LL)) := lk_set_same_so _ _ _
    simp [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hs_p, hs_ll,
      wordOpHOL, wordOp, valueIsWord, valueWord] at hargs
    subst hargs
    have hlk' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_read_length")
        [.val (.word (P + 1#64)), .val (.word LL)] = some (cbody, callee, crs) := by
      simpa [setVarHOLFinite, hc_s1] using hlk
    obtain ⟨rfl, hcp_n, hcn_n⟩ := callee_p_n_so lookup_rlp_read_length_so _ _ cbody callee crs hlk'
    have h1_nat : (1#64 : BitVec 64).toNat = 1 := rfl
    have hLL0 : 0 < LL.toNat := by
      have hgt183 : 183 < B.toNat := by
        by_contra hle; exact hB_notle183 (by rw [BitVec.le_def]; exact Nat.not_lt.mp hle)
      have h183_nat : (183#64 : BitVec 64).toNat = 183 := rfl
      have hLL_sub : LL.toNat = B.toNat - 183 := by
        change (B - 183#64).toNat = B.toNat - 183
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h183_nat]; omega), h183_nat]
      omega
    have hp1_nat : (P + 1#64).toNat = P.toNat + 1 := by
      have hPlt : P.toNat + 1 < 2 ^ 64 := by omega
      exact BitVec.toNat_add_of_lt (by simpa [h1_nat] using hPlt)
    have hfit_ll : (P + 1#64).toNat + LL.toNat ≤ 2 ^ 64 := by
      rw [hp1_nat]; omega
    have hvn_eq := rlp_read_length_ret_eq_acc_so
      (callEntryStateHOLFinite (setVarHOLFinite (ofString "ll") (.val (.word LL)) s1) callee)
      hc_s1 (P + 1#64) LL hfit_ll hcp_n hcn_n vn hret_n
    let N := rlpReadLenAcc_so (fun j => memB e1 ((P + 1#64).toNat + j)) LL.toNat 0 0#64
    have hvn_eq' : vn = .val (.word N) := hvn_eq
    subst hvn_eq'
    have hul : u.locals.lookup (ofString "len") = some (.val (.word L)) := by
      rw [hloc _ (by decide), lk_set_so _ _ _ _ (by decide)]; exact hs1_l
    have hull : u.locals.lookup (ofString "ll") = some (.val (.word LL)) := by
      rw [hloc _ (by decide), lk_set_same_so]
    have hcu' : u.code = originalRuntimeCode := hcu.trans hc_s1
    refine RetOK.guard hcu' (fun _ _ _ => ?_)
    refine RetOK.guard hcu' (fun wg2 hwg2 hwg2_0 => RetOK.ret (fun v hv => ?_))
    have hsub : (L - 1#64 - LL).toNat = L.toNat - 1 - LL.toNat := by
      rw [BitVec.toNat_sub, hL1]; omega
    have hNle : N.toNat ≤ L.toNat - 1 - LL.toNat := by
      simp [evalHOLExact, evalListHOLExact, hul, hull, hun, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hwg2
      subst hwg2_0; by_contra hc
      have : L - 1#64 - LL < N := by rw [BitVec.lt_def, hsub]; omega
      simp [this] at hwg2
    simp [evalHOLExact, evalListHOLExact, hull, hun, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
    subst hv
    have hadd_hl : (1#64 + LL).toNat = 1 + LL.toNat := by
      rw [BitVec.toNat_add_of_lt (by rw [h1_nat]; omega), h1_nat]
    refine ⟨1#64 + LL, N, 0#64, rfl, by rw [hadd_hl]; omega, by rw [hadd_hl]; omega, ?_⟩
    intro e2 hc2 hp2 hbytes rv2 hret2
    revert rv2 hret2
    change RetOK (fun rv2 => rv2 = .val (.word ((1#64 + LL) + N))) e2
      (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total_unchecked,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    refine RetOK.dec (fun vb2 hvb2 _ => ?_)
    obtain ⟨P2', ha2, _, rfl⟩ := loadByte_eq_memB_so e2 _ vb2 hvb2
    simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hp2, Option.some.injEq, ValueHOL.val.injEq,
      HolWordLab.word.injEq] at ha2; subst ha2
    have hb2_eq : BitVec.ofNat 64 (memB e2 P.toNat) = B := by
      have h0 := hbytes 0 hL_pos; simp at h0; rw [h0]
    rw [hb2_eq]
    refine RetOK.branch (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
    · simp [evalHOLExact, lk_set_same_so, Compiler.Encoders.Asm.wordCmpHOL, hB_ge128] at hw'
      exact absurd hw'.symm hw'_nz
    refine RetOK.branch (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
    · simp [evalHOLExact, lk_set_same_so, Compiler.Encoders.Asm.wordCmpHOL, hB_notle183] at hw'
      exact absurd hw'.symm hw'_nz
    refine RetOK.branch (by rfl) (fun _ _ _ => ?_) (fun w' hw' hw'_0 => ?_)
    · refine RetOK.dec (fun vll2 hvll2 _ => ?_)
      simp [evalHOLExact, evalListHOLExact, lk_set_same_so, wordOpHOL, wordOp, valueIsWord, valueWord] at hvll2
      subst hvll2
      refine RetOK.decCall' (fun cvals2 cbody2 callee2 crs2 vn2 hargs2 hlk2 hret_n2 _ u2 _ hloc2 hun2 => ?_)
      have hup2 : (setVarHOLFinite (ofString "ll") (.val (.word (B - 183#64)))
          (setVarHOLFinite (ofString "b") (.val (.word B)) e2)).locals.lookup (ofString "p") =
          some (.val (.word P)) := by
        rw [lk_set_so _ _ _ _ (by decide), lk_set_so _ _ _ _ (by decide)]; exact hp2
      have hull2 : (setVarHOLFinite (ofString "ll") (.val (.word (B - 183#64)))
          (setVarHOLFinite (ofString "b") (.val (.word B)) e2)).locals.lookup (ofString "ll") =
          some (.val (.word LL)) := lk_set_same_so _ _ _
      simp [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hup2, hull2,
        wordOpHOL, wordOp, valueIsWord, valueWord] at hargs2
      subst hargs2
      have hlk2' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_read_length")
          [.val (.word (P + 1#64)), .val (.word LL)] = some (cbody2, callee2, crs2) := by
        simpa [setVarHOLFinite, hc2] using hlk2
      obtain ⟨rfl, hcp2, hcn2⟩ := callee_p_n_so lookup_rlp_read_length_so _ _ cbody2 callee2 crs2 hlk2'
      have hvn2_eq := rlp_read_length_ret_eq_acc_so
        (callEntryStateHOLFinite _ callee2) hc2 (P + 1#64) LL hfit_ll hcp2 hcn2 vn2 hret_n2
      have hacc_eq : rlpReadLenAcc_so (fun j => memB e2 ((P + 1#64).toNat + j)) LL.toNat 0 0#64 = N := by
        apply rlpReadLenAcc_congr_so
        intro j _ hj2
        rw [hp1_nat, Nat.add_assoc]
        exact hbytes (1 + j) (by omega)
      change vn2 = .val (.word (rlpReadLenAcc_so (fun j => memB e2 ((P + 1#64).toNat + j)) LL.toNat 0 0#64)) at hvn2_eq
      rw [hacc_eq] at hvn2_eq
      subst hvn2_eq
      have hu2_ll : u2.locals.lookup (ofString "ll") = some (.val (.word LL)) := by
        rw [hloc2 _ (by decide), lk_set_same_so]
      refine RetOK.ret (fun v2 hv2 => ?_)
      simp [evalHOLExact, evalListHOLExact, hu2_ll, hun2, wordOpHOL, wordOp, valueIsWord, valueWord] at hv2
      rw [← hv2]; congr 2; bv_omega
    · simp [evalHOLExact, lk_set_same_so, Compiler.Encoders.Asm.wordCmpHOL, hB_le191] at hw'
      subst hw'_0; simp at hw'
  have hB_notle191 : ¬ (B ≤ 191#64) := by
    simp [evalHOLExact, hs1_b, Compiler.Encoders.Asm.wordCmpHOL] at hw3
    subst hw3_0; intro hle; simp [hle] at hw3
  refine RetOK.branch (by rfl) (fun w4 hw4 hw4_nz => ?_) (fun w4 hw4 hw4_0 => ?_)
  · have hB_le247 : B ≤ 247#64 := by
      simp [evalHOLExact, hs1_b, Compiler.Encoders.Asm.wordCmpHOL] at hw4
      by_contra hgt; simp [hgt] at hw4; exact hw4_nz hw4.symm
    refine RetOK.dec (fun vn hvn _ => ?_)
    simp [evalHOLExact, evalListHOLExact, hs1_b, wordOpHOL, wordOp, valueIsWord, valueWord] at hvn; subst hvn
    refine RetOK.guard (by exact hcode1) (fun wg hwg hwg0 => RetOK.ret (fun v hv => ?_))
    have hN : (B - 192#64).toNat ≤ L.toNat - 1 := by
      simp [evalHOLExact, evalListHOLExact, lk_set_so, lk_set_same_so,
        show ofString "n" ≠ ofString "len" by decide, hs1_l, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hwg
      subst hwg0; by_contra hc
      have : L - 1#64 < B - 192#64 := by rw [BitVec.lt_def, hL1]; omega
      simp [this] at hwg
    simp [evalHOLExact, evalListHOLExact, lk_set_so, lk_set_same_so] at hv; subst hv
    have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
    refine ⟨1#64, B - 192#64, 1#64, rfl, by rw [h1]; omega, by rw [h1]; omega, ?_⟩
    intro e2 hc2 hp2 hbytes rv2 hret2
    revert rv2 hret2
    change RetOK (fun rv2 => rv2 = .val (.word (1#64 + (B - 192#64)))) e2
      (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total_unchecked,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    refine RetOK.dec (fun vb2 hvb2 _ => ?_)
    obtain ⟨P2', ha2, _, rfl⟩ := loadByte_eq_memB_so e2 _ vb2 hvb2
    simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hp2, Option.some.injEq, ValueHOL.val.injEq,
      HolWordLab.word.injEq] at ha2; subst ha2
    have hb2_eq : BitVec.ofNat 64 (memB e2 P.toNat) = B := by
      have h0 := hbytes 0 hL_pos; simp at h0; rw [h0]
    rw [hb2_eq]
    refine RetOK.branch (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
    · simp [evalHOLExact, lk_set_same_so, Compiler.Encoders.Asm.wordCmpHOL, hB_ge128] at hw'
      exact absurd hw'.symm hw'_nz
    refine RetOK.branch (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
    · simp [evalHOLExact, lk_set_same_so, Compiler.Encoders.Asm.wordCmpHOL, hB_notle183] at hw'
      exact absurd hw'.symm hw'_nz
    refine RetOK.branch (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
    · simp [evalHOLExact, lk_set_same_so, Compiler.Encoders.Asm.wordCmpHOL, hB_notle191] at hw'
      exact absurd hw'.symm hw'_nz
    refine RetOK.branch (by rfl) (fun _ _ _ => RetOK.ret (fun v2 hv2 => ?_)) (fun w' hw' hw'_0 => ?_)
    · simp [evalHOLExact, evalListHOLExact, lk_set_same_so, wordOpHOL, wordOp, valueIsWord, valueWord] at hv2
      rw [← hv2]; congr 2; bv_omega
    · simp [evalHOLExact, lk_set_same_so, Compiler.Encoders.Asm.wordCmpHOL, hB_le247] at hw'
      subst hw'_0; simp at hw'
  have hB_notle247 : ¬ (B ≤ 247#64) := by
    simp [evalHOLExact, hs1_b, Compiler.Encoders.Asm.wordCmpHOL] at hw4
    subst hw4_0; intro hle; simp [hle] at hw4
  refine RetOK.dec (fun vll hvll _ => ?_)
  simp [evalHOLExact, evalListHOLExact, hs1_b, wordOpHOL, wordOp, valueIsWord, valueWord] at hvll; subst hvll
  set LL := B - 247#64
  refine RetOK.guard (by exact hcode1) (fun wg hwg hwg0 => ?_)
  have hLL : LL.toNat ≤ L.toNat - 1 := by
    simp [evalHOLExact, evalListHOLExact, lk_set_so, lk_set_same_so,
      show ofString "ll" ≠ ofString "len" by decide, hs1_l, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hwg
    subst hwg0; by_contra hc
    have hlt_ll : L - 1#64 < LL := by rw [BitVec.lt_def, hL1]; omega
    simp [hlt_ll] at hwg
  refine RetOK.decCall' (fun cvals cbody callee crs vn hargs hlk hret_n _ u hcu hloc hun => ?_)
  have hs_p : (setVarHOLFinite (ofString "ll") (.val (.word LL)) s1).locals.lookup (ofString "p") =
      some (.val (.word P)) := by
    rw [lk_set_so _ _ _ _ (by decide)]; exact hs1_p
  have hs_ll : (setVarHOLFinite (ofString "ll") (.val (.word LL)) s1).locals.lookup (ofString "ll") =
      some (.val (.word LL)) := lk_set_same_so _ _ _
  simp [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hs_p, hs_ll,
    wordOpHOL, wordOp, valueIsWord, valueWord] at hargs
  subst hargs
  have hlk' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_read_length")
      [.val (.word (P + 1#64)), .val (.word LL)] = some (cbody, callee, crs) := by
    simpa [setVarHOLFinite, hc_s1] using hlk
  obtain ⟨rfl, hcp_n, hcn_n⟩ := callee_p_n_so lookup_rlp_read_length_so _ _ cbody callee crs hlk'
  have h1_nat : (1#64 : BitVec 64).toNat = 1 := rfl
  have hLL0 : 0 < LL.toNat := by
    have hgt247 : 247 < B.toNat := by
      by_contra hle; exact hB_notle247 (by rw [BitVec.le_def]; exact Nat.not_lt.mp hle)
    have hlt256 : B.toNat < 256 := by
      have hm : memB e1 P.toNat < 256 := by
        unfold memB; rcases e1.memory _ with ⟨w⟩; exact (panGetByteHOL _ w e1.be).toNat_lt
      change (BitVec.ofNat 64 (memB e1 P.toNat)).toNat < 256
      rw [BitVec.toNat_ofNat]; omega
    have h247_nat : (247#64 : BitVec 64).toNat = 247 := rfl
    have hLL_sub : LL.toNat = B.toNat - 247 := by
      change (B - 247#64).toNat = B.toNat - 247
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h247_nat]; omega), h247_nat]
    omega
  have hp1_nat : (P + 1#64).toNat = P.toNat + 1 := by
    have hPlt : P.toNat + 1 < 2 ^ 64 := by omega
    exact BitVec.toNat_add_of_lt (by simpa [h1_nat] using hPlt)
  have hfit_ll : (P + 1#64).toNat + LL.toNat ≤ 2 ^ 64 := by
    rw [hp1_nat]; omega
  have hvn_eq := rlp_read_length_ret_eq_acc_so
    (callEntryStateHOLFinite (setVarHOLFinite (ofString "ll") (.val (.word LL)) s1) callee)
    hc_s1 (P + 1#64) LL hfit_ll hcp_n hcn_n vn hret_n
  let N := rlpReadLenAcc_so (fun j => memB e1 ((P + 1#64).toNat + j)) LL.toNat 0 0#64
  have hvn_eq' : vn = .val (.word N) := hvn_eq
  subst hvn_eq'
  have hul : u.locals.lookup (ofString "len") = some (.val (.word L)) := by
    rw [hloc _ (by decide), lk_set_so _ _ _ _ (by decide)]; exact hs1_l
  have hull : u.locals.lookup (ofString "ll") = some (.val (.word LL)) := by
    rw [hloc _ (by decide), lk_set_same_so]
  have hcu' : u.code = originalRuntimeCode := hcu.trans hc_s1
  refine RetOK.guard hcu' (fun _ _ _ => ?_)
  refine RetOK.guard hcu' (fun wg2 hwg2 hwg2_0 => RetOK.ret (fun v hv => ?_))
  have hsub : (L - 1#64 - LL).toNat = L.toNat - 1 - LL.toNat := by
    rw [BitVec.toNat_sub, hL1]; omega
  have hNle : N.toNat ≤ L.toNat - 1 - LL.toNat := by
    simp [evalHOLExact, evalListHOLExact, hul, hull, hun, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hwg2
    subst hwg2_0; by_contra hc
    have : L - 1#64 - LL < N := by rw [BitVec.lt_def, hsub]; omega
    simp [this] at hwg2
  simp [evalHOLExact, evalListHOLExact, hull, hun, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  have hadd_hl : (1#64 + LL).toNat = 1 + LL.toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [h1_nat]; omega), h1_nat]
  refine ⟨1#64 + LL, N, 1#64, rfl, by rw [hadd_hl]; omega, by rw [hadd_hl]; omega, ?_⟩
  intro e2 hc2 hp2 hbytes rv2 hret2
  revert rv2 hret2
  change RetOK (fun rv2 => rv2 = .val (.word ((1#64 + LL) + N))) e2
    (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total_unchecked,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine RetOK.dec (fun vb2 hvb2 _ => ?_)
  obtain ⟨P2', ha2, _, rfl⟩ := loadByte_eq_memB_so e2 _ vb2 hvb2
  simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hp2, Option.some.injEq, ValueHOL.val.injEq,
    HolWordLab.word.injEq] at ha2; subst ha2
  have hb2_eq : BitVec.ofNat 64 (memB e2 P.toNat) = B := by
    have h0 := hbytes 0 hL_pos; simp at h0; rw [h0]
  rw [hb2_eq]
  refine RetOK.branch (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
  · simp [evalHOLExact, lk_set_same_so, Compiler.Encoders.Asm.wordCmpHOL, hB_ge128] at hw'
    exact absurd hw'.symm hw'_nz
  refine RetOK.branch (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
  · simp [evalHOLExact, lk_set_same_so, Compiler.Encoders.Asm.wordCmpHOL, hB_notle183] at hw'
    exact absurd hw'.symm hw'_nz
  refine RetOK.branch (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
  · simp [evalHOLExact, lk_set_same_so, Compiler.Encoders.Asm.wordCmpHOL, hB_notle191] at hw'
    exact absurd hw'.symm hw'_nz
  refine RetOK.branch (by rfl) (fun w' hw' hw'_nz => ?_) (fun _ _ _ => ?_)
  · simp [evalHOLExact, lk_set_same_so, Compiler.Encoders.Asm.wordCmpHOL, hB_notle247] at hw'
    exact absurd hw'.symm hw'_nz
  refine RetOK.dec (fun vll2 hvll2 _ => ?_)
  simp [evalHOLExact, evalListHOLExact, lk_set_same_so, wordOpHOL, wordOp, valueIsWord, valueWord] at hvll2
  subst hvll2
  refine RetOK.decCall' (fun cvals2 cbody2 callee2 crs2 vn2 hargs2 hlk2 hret_n2 _ u2 _ hloc2 hun2 => ?_)
  have hup2 : (setVarHOLFinite (ofString "ll2") (.val (.word (B - 247#64)))
      (setVarHOLFinite (ofString "b") (.val (.word B)) e2)).locals.lookup (ofString "p") =
      some (.val (.word P)) := by
    rw [lk_set_so _ _ _ _ (by decide), lk_set_so _ _ _ _ (by decide)]; exact hp2
  have hull2 : (setVarHOLFinite (ofString "ll2") (.val (.word (B - 247#64)))
      (setVarHOLFinite (ofString "b") (.val (.word B)) e2)).locals.lookup (ofString "ll2") =
      some (.val (.word LL)) := lk_set_same_so _ _ _
  simp [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hup2, hull2,
    wordOpHOL, wordOp, valueIsWord, valueWord] at hargs2
  subst hargs2
  have hlk2' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_read_length")
      [.val (.word (P + 1#64)), .val (.word LL)] = some (cbody2, callee2, crs2) := by
    simpa [setVarHOLFinite, hc2] using hlk2
  obtain ⟨rfl, hcp2, hcn2⟩ := callee_p_n_so lookup_rlp_read_length_so _ _ cbody2 callee2 crs2 hlk2'
  have hvn2_eq := rlp_read_length_ret_eq_acc_so
    (callEntryStateHOLFinite _ callee2) hc2 (P + 1#64) LL hfit_ll hcp2 hcn2 vn2 hret_n2
  have hacc_eq : rlpReadLenAcc_so (fun j => memB e2 ((P + 1#64).toNat + j)) LL.toNat 0 0#64 = N := by
    apply rlpReadLenAcc_congr_so
    intro j _ hj2
    rw [hp1_nat, Nat.add_assoc]
    exact hbytes (1 + j) (by omega)
  change vn2 = .val (.word (rlpReadLenAcc_so (fun j => memB e2 ((P + 1#64).toNat + j)) LL.toNat 0 0#64)) at hvn2_eq
  rw [hacc_eq] at hvn2_eq
  subst hvn2_eq
  have hu2_ll : u2.locals.lookup (ofString "ll2") = some (.val (.word LL)) := by
    rw [hloc2 _ (by decide), lk_set_same_so]
  refine RetOK.ret (fun v2 hv2 => ?_)
  simp [evalHOLExact, evalListHOLExact, hu2_ll, hun2, wordOpHOL, wordOp, valueIsWord, valueWord] at hv2
  rw [← hv2]; congr 2; bv_omega

theorem rlp_item_total_agree_unchecked_so {F : Type}
    (e1 : PanSemStateFiniteExact 64 F) (hcode1 : e1.code = originalRuntimeCode)
    (P L : BitVec 64) (hfit : P.toNat + L.toNat ≤ 2 ^ 64)
    (hp1 : e1.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl1 : e1.locals.lookup (ofString "len") = some (.val (.word L))) :
    RetOK (fun v =>
      ∃ T : BitVec 64, v = .val (.word T) ∧ 1 ≤ T.toNat ∧ T.toNat ≤ L.toNat ∧
        ∀ e2 : PanSemStateFiniteExact 64 F,
          e2.code = originalRuntimeCode →
          e2.locals.lookup (ofString "p") = some (.val (.word P)) →
          (∀ j < L.toNat, memB e2 (P.toNat + j) = memB e1 (P.toNat + j)) →
          ∀ rv2 : ValueHOL 64,
            (evaluateHOLFiniteState e2 (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)).1 =
              some (.returned rv2) →
            rv2 = .val (.word T))
      e1 (sourceFnBody Guest.Software.guestFn_rlp_item_total) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine RetOK.decCall' (fun values body callee rs v hargs hlk hret _ u _ _ hu => ?_)
  simp only [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hp1, hl1, Option.some.injEq] at hargs
  subst hargs
  rw [hcode1] at hlk
  obtain ⟨rfl, hcp, hcl⟩ := callee_p_len_so lookup_rlp_item_header_so _ _ body callee rs hlk
  obtain ⟨a, b, c, rfl, h1, h2, hagree⟩ :=
    rlp_item_header_agree_unchecked_so (callEntryStateHOLFinite e1 callee) hcode1 P L hfit hcp hcl v hret
  refine RetOK.seq (RetOK.ite (fun _ _ => ⟨fun _ v hv => absurd hv (call0_noret_so u _ _ v), fun _ => RetOK.skip⟩))
    (fun mid hmid => ?_)
  have hmid_h : mid.locals.lookup (ofString "h") = some (hval_so a b c) := by
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · split at hmid
      · rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        rw [← hmid.2]; exact hu
      · rw [(call0_flow_locals_so u _ _ mid hmid).1]; exact hu
    · simp at hmid
  refine RetOK.ret (fun v hv => ?_)
  simp [evalHOLExact, evalListHOLExact, hmid_h, hval_so, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  have hab_nat : (a + b).toNat = a.toNat + b.toNat :=
    BitVec.toNat_add_of_lt (by have := L.isLt; omega)
  refine ⟨a + b, rfl, by rw [hab_nat]; omega, by rw [hab_nat]; omega, ?_⟩
  intro e2 hc2 hp2 hbytes rv2 hret2
  exact hagree e2 hc2 hp2 hbytes rv2 hret2

/-! ### Section 2d: `rlp_list_count` Item-List Spec and `rlp_list_to_slices` Slice-Bounds Spec -/

def rlpNoAllocGood_so (f : MlS) : Bool :=
  f == ofString "trap_with" ||
  f == ofString "rlp_fail" ||
  f == ofString "rlp_read_length" ||
  f == ofString "rlp_item_header" ||
  f == ofString "scratch_mark" ||
  f == ofString "scratch_alloc" ||
  f == ofString "scratch_release" ||
  f == ofString "_rlp_validate_items_body" ||
  f == ofString "rlp_validate_items" ||
  f == ofString "rlp_item_total" ||
  f == ofString "rlp_list_count"

theorem rlpNoAllocGood_keeps_hp_so :
    ∀ f, rlpNoAllocGood_so f = true →
      ∀ values body callee rs,
        PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
          some (body, callee, rs) →
        GuestGlobalKeep.keepsG (ofString "heap_ptr") rlpNoAllocGood_so body = true := by
  have hl_tw : originalRuntimeCode.lookup (ofString "trap_with") =
      some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_trap_with, .one) :=
    lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_trap_with) rfl
  have hl_fail : originalRuntimeCode.lookup (ofString "rlp_fail") =
      some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_rlp_fail, .one) :=
    lookup_of_guestAst_getElem 105 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_rlp_fail) rfl
  have hl_sm : originalRuntimeCode.lookup (ofString "scratch_mark") =
      some ([], sourceFnBody Guest.Software.guestFn_scratch_mark, .one) :=
    lookup_of_guestAst_getElem 14 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_scratch_mark) rfl
  have hl_sa : originalRuntimeCode.lookup (ofString "scratch_alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_scratch_alloc, .one) :=
    lookup_of_guestAst_getElem 13 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_scratch_alloc) rfl
  have hl_sr : originalRuntimeCode.lookup (ofString "scratch_release") =
      some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_scratch_release, .one) :=
    lookup_of_guestAst_getElem 15 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_scratch_release) rfl
  have hl_vib : originalRuntimeCode.lookup (ofString "_rlp_validate_items_body") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn__rlp_validate_items_body, .one) :=
    lookup_of_guestAst_getElem 110 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn__rlp_validate_items_body) rfl
  have hl_vi : originalRuntimeCode.lookup (ofString "rlp_validate_items") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_validate_items, .one) :=
    lookup_of_guestAst_getElem 111 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_rlp_validate_items) rfl
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hcode_f⟩ := GuestGlobalKeep.lookupCode_installed hfound
  unfold rlpNoAllocGood_so at hf
  simp only [Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with ((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
  · rw [hl_tw] at hcode_f; injection hcode_f with h; obtain ⟨_, rfl, _⟩ := Prod.mk.injEq .. ▸ h; decide
  · rw [hl_fail] at hcode_f; injection hcode_f with h; obtain ⟨_, rfl, _⟩ := Prod.mk.injEq .. ▸ h; decide
  · rw [lookup_rlp_read_length_so] at hcode_f; injection hcode_f with h; obtain ⟨_, rfl, _⟩ := Prod.mk.injEq .. ▸ h; decide
  · rw [lookup_rlp_item_header_so] at hcode_f; injection hcode_f with h; obtain ⟨_, rfl, _⟩ := Prod.mk.injEq .. ▸ h; decide
  · rw [hl_sm] at hcode_f; injection hcode_f with h; obtain ⟨_, rfl, _⟩ := Prod.mk.injEq .. ▸ h; decide
  · rw [hl_sa] at hcode_f; injection hcode_f with h; obtain ⟨_, rfl, _⟩ := Prod.mk.injEq .. ▸ h; decide
  · rw [hl_sr] at hcode_f; injection hcode_f with h; obtain ⟨_, rfl, _⟩ := Prod.mk.injEq .. ▸ h; decide
  · rw [hl_vib] at hcode_f; injection hcode_f with h; obtain ⟨_, rfl, _⟩ := Prod.mk.injEq .. ▸ h; decide
  · rw [hl_vi] at hcode_f; injection hcode_f with h; obtain ⟨_, rfl, _⟩ := Prod.mk.injEq .. ▸ h; decide
  · rw [lookup_rlp_item_total_so] at hcode_f; injection hcode_f with h; obtain ⟨_, rfl, _⟩ := Prod.mk.injEq .. ▸ h; decide
  · rw [lookup_rlp_list_count_so] at hcode_f; injection hcode_f with h; obtain ⟨_, rfl, _⟩ := Prod.mk.injEq .. ▸ h; decide

theorem rlp_item_total_keeps_hp_so {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) :
    globN (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item_total)).2 "heap_ptr" =
      globN s "heap_ptr" :=
  InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup
    (GuestGlobalKeep.evaluate_keepsG (ofString "heap_ptr") rlpNoAllocGood_so rlpNoAllocGood_keeps_hp_so
      (sourceFnBody Guest.Software.guestFn_rlp_item_total) (by decide) s hc).symm

theorem rlp_list_count_keeps_hp_so {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) :
    globN (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).2 "heap_ptr" =
      globN s "heap_ptr" :=
  InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup
    (GuestGlobalKeep.evaluate_keepsG (ofString "heap_ptr") rlpNoAllocGood_so rlpNoAllocGood_keeps_hp_so
      (sourceFnBody Guest.Software.guestFn_rlp_list_count) (by decide) s hc).symm

private theorem lookup__rlp_validate_items_body_so :
    originalRuntimeCode.lookup (ofString "_rlp_validate_items_body") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn__rlp_validate_items_body, .one) :=
  lookup_of_guestAst_getElem 110 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__rlp_validate_items_body) rfl

private theorem lookup_rlp_validate_items_so :
    originalRuntimeCode.lookup (ofString "rlp_validate_items") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_validate_items, .one) :=
  lookup_of_guestAst_getElem 111 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_validate_items) rfl

private theorem lookupCode_two_words_so {fname p1 p2 : MlS} {body : ProgHOL 64} {retShape : ShapeHOL}
    {vals : List (ValueHOL 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, retShape))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, retShape)) :
    ∃ w1 w2 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L retShape hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, rfl, ?_, ?_⟩ <;> (rw [← hL]; simp [hne, Ne.symm hne])
  · simp at hx

private def vibPushProg_so : ProgHOL 64 :=
  .decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24]
    (.seq (.store (.var .local (ofString "rec")) (.var .local (ofString "after")))
      (.seq (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end")))
        (.seq (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top")))
          (.seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
            (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
              (.assign .local (ofString "end") (.var .local (ofString "after"))))))))

private theorem worldEff_vibPush_so {F : Type}
    {s t3 : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (heff_t3 : R16Shards.WorldEff s t3 [] [] R16Shards.wsGw)
    (w_top w_end w_aft : BitVec 64)
    (ht3_aft : t3.locals.lookup (ofString "after") = some (.val (.word w_aft)))
    (ht3_end : t3.locals.lookup (ofString "end") = some (.val (.word w_end)))
    (ht3_top : t3.locals.lookup (ofString "top") = some (.val (.word w_top)))
    (hnt_push : (evaluateHOLFiniteState t3 vibPushProg_so).1 ≠ some .timeOut)
    (hcr_push : R16Shards.ContOrRes (evaluateHOLFiniteState t3 vibPushProg_so).1) :
    R16Shards.WorldEff s (evaluateHOLFiniteState t3 vibPushProg_so).2 [] [] R16Shards.wsGw := by
  dsimp only [vibPushProg_so] at hnt_push hcr_push ⊢
  refine R16Shards.worldEff_decCall_scratch_alloc heff_t3 (by decide) _ _ hnt_push hcr_push
    (fun qw nw mid hsz_ev _ hmid_loc _ heff_mid _ hqw_lo hqw_add hsp_le _ _ hnt_ps hcr_ps => ?_)
  have hnw_eq : nw = 24 := by simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
  subst hnw_eq
  have h24 : ((24 : BitVec 64).toNat + 7) / 8 * 8 = 24 := by decide
  rw [h24] at hqw_add
  have hse_lt : scratchEnd < 2 ^ 64 := by decide
  have hsp_s_hi : globN s "scratch_ptr" ≤ scratchEnd := hAR.2.2.2.2.2.1
  have hqw8 : (qw + 8#64).toNat = qw.toNat + 8 := BitVec.toNat_add_of_lt (by change qw.toNat + 8 < 2 ^ 64; omega)
  have hqw16 : (qw + 16#64).toNat = qw.toNat + 16 := BitVec.toNat_add_of_lt (by change qw.toNat + 16 < 2 ^ 64; omega)
  have hmid_rec : mid.locals.lookup (ofString "rec") = some (.val (.word qw)) := by
    rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hmid_aft : mid.locals.lookup (ofString "after") = some (.val (.word w_aft)) := by
    rw [hmid_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, ht3_aft, show ofString "rec" ≠ ofString "after" by decide]
  have hmid_end : mid.locals.lookup (ofString "end") = some (.val (.word w_end)) := by
    rw [hmid_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, ht3_end, show ofString "rec" ≠ ofString "end" by decide]
  have hmid_top : mid.locals.lookup (ofString "top") = some (.val (.word w_top)) := by
    rw [hmid_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, ht3_top, show ofString "rec" ≠ ofString "top" by decide]
  refine R16Shards.worldEff_seq hnt_ps hcr_ps
    (fun _ _ => R16Shards.worldEff_store_word heff_mid _ _
      (fun v hv => by simp [evalHOLExact, hmid_aft] at hv; exact ⟨_, hv.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, hmid_rec] at hx; subst hx
        exact Or.inr (Or.inr (Or.inl ⟨hqw_lo, by omega⟩))))
    (fun u1 hu1 heff_u1 hnt_u1 hcr_u1 => ?_)
  have hu1_loc : u1.locals = mid.locals := by
    have hcf := (evaluate_store_control_frame mid (.var .local (ofString "rec")) (.var .local (ofString "after"))).2.1
    rwa [hu1] at hcf
  refine R16Shards.worldEff_seq hnt_u1 hcr_u1
    (fun _ _ => R16Shards.worldEff_store_word heff_u1 _ _
      (fun v hv => by simp [evalHOLExact, hu1_loc, hmid_end] at hv; exact ⟨_, hv.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, evalListHOLExact, hu1_loc, hmid_rec, valueIsWord, valueWord, wordOpHOL, wordOp] at hx
        subst hx
        exact Or.inr (Or.inr (Or.inl ⟨by rw [hqw8]; omega, by rw [hqw8]; omega⟩))))
    (fun u2 hu2 heff_u2 hnt_u2 hcr_u2 => ?_)
  have hu2_loc : u2.locals = mid.locals := by
    have hcf := (evaluate_store_control_frame u1 (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end"))).2.1
    rw [hu2] at hcf; exact hcf.trans hu1_loc
  refine R16Shards.worldEff_seq hnt_u2 hcr_u2
    (fun _ _ => R16Shards.worldEff_store_word heff_u2 _ _
      (fun v hv => by simp [evalHOLExact, hu2_loc, hmid_top] at hv; exact ⟨_, hv.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, evalListHOLExact, hu2_loc, hmid_rec, valueIsWord, valueWord, wordOpHOL, wordOp] at hx
        subst hx
        exact Or.inr (Or.inr (Or.inl ⟨by rw [hqw16]; omega, by rw [hqw16]; omega⟩))))
    (fun u3 _ heff_u3 hnt_u3 hcr_u3 =>
      R16Shards.worldEff_seq hnt_u3 hcr_u3
        (fun _ _ => R16Shards.worldEff_assign_local heff_u3 _ _)
        (fun u4 _ heff_u4 hnt_u4 hcr_u4 =>
          R16Shards.worldEff_seq hnt_u4 hcr_u4
            (fun _ _ => R16Shards.worldEff_assign_local heff_u4 _ _)
            (fun u5 _ heff_u5 _ _ => R16Shards.worldEff_assign_local heff_u5 _ _)))

private def vibLoopBody_so : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "pos")) (.var .local (ofString "end")))
    (.ite (.cmp .equal (.var .local (ofString "top")) (.const 0))
      (.assign .local (ofString "go") (.const 0))
      (.seq
        (.assign .local (ofString "pos") (.load .one (.op .add [.var .local (ofString "top"), .const 0])))
        (.seq
          (.assign .local (ofString "end") (.load .one (.op .add [.var .local (ofString "top"), .const 8])))
          (.assign .local (ofString "top") (.load .one (.op .add [.var .local (ofString "top"), .const 16]))))))
    (.decCall (ofString "h") (.comb [.one, .one, .one]) (ofString "rlp_item_header")
      [.var .local (ofString "pos"), .op .sub [.var .local (ofString "end"), .var .local (ofString "pos")]]
      (.dec (ofString "payload") .one (.op .add [.var .local (ofString "pos"), .rfield 0 (.var .local (ofString "h"))])
        (.dec (ofString "after") .one (.op .add [.var .local (ofString "payload"), .rfield 1 (.var .local (ofString "h"))])
          (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0))
            vibPushProg_so
            (.assign .local (ofString "pos") (.var .local (ofString "after")))))))

private theorem worldEff_vibLoopBody_so {F : Type}
    {s t : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (heff_t : R16Shards.WorldEff s t [] [] R16Shards.wsGw)
    (hinv_t : R16Shards.WordLocals ["top", "pos", "end", "go"] t)
    (hnt_b : (evaluateHOLFiniteState t vibLoopBody_so).1 ≠ some .timeOut)
    (hcr_b : R16Shards.ContOrRes (evaluateHOLFiniteState t vibLoopBody_so).1) :
    R16Shards.WorldEff s (evaluateHOLFiniteState t vibLoopBody_so).2 [] [] R16Shards.wsGw := by
  dsimp only [vibLoopBody_so] at hnt_b hcr_b ⊢
  refine R16Shards.worldEff_ite heff_t _ hnt_b hcr_b
    (fun _ _ _ hnt_eq hcr_eq =>
      R16Shards.worldEff_ite heff_t _ hnt_eq hcr_eq
        (fun _ _ _ _ _ => R16Shards.worldEff_assign_local heff_t _ _)
        (fun _ hnt_pop hcr_pop =>
          R16Shards.worldEff_seq hnt_pop hcr_pop
            (fun _ _ => R16Shards.worldEff_assign_local heff_t _ _)
            (fun m1 _ heff_m1 hnt_p2 hcr_p2 =>
              R16Shards.worldEff_seq hnt_p2 hcr_p2
                (fun _ _ => R16Shards.worldEff_assign_local heff_m1 _ _)
                (fun m2 _ heff_m2 _ _ => R16Shards.worldEff_assign_local heff_m2 _ _))))
    (fun _ hnt_neq hcr_neq => ?_)
  refine R16Shards.worldEff_decCall_ro heff_t R13.ro_rlp_item_header
    (ofString "h") (.comb [.one, .one, .one]) _ hnt_neq hcr_neq (fun rvh cpost _ hcpost hnt_c1 hcr_c1 => ?_)
  let t1 := setVarHOLFinite (ofString "h") rvh { cpost with locals := t.locals }
  have heff_t1 : R16Shards.WorldEff s t1 [] [] R16Shards.wsGw := (heff_t.of_readOnly hcpost).locals_clock _ _
  obtain ⟨w_top, htop_t⟩ := hinv_t "top" (by simp)
  obtain ⟨w_end, hend_t⟩ := hinv_t "end" (by simp)
  refine R16Shards.worldEff_dec heff_t1 _ _ _ hnt_c1 hcr_c1 (fun vpay _ hsh_pay hnt_c2 hcr_c2 => ?_)
  rcases vpay with ⟨⟨wpay⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_pay
  let t2 := setVarHOLFinite (ofString "payload") (.val (.word wpay)) t1
  have heff_t2 : R16Shards.WorldEff s t2 [] [] R16Shards.wsGw := heff_t1.locals_clock _ _
  refine R16Shards.worldEff_dec heff_t2 _ _ _ hnt_c2 hcr_c2 (fun vaft _ hsh_aft hnt_c3 hcr_c3 => ?_)
  rcases vaft with ⟨⟨waft⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_aft
  let t3 := setVarHOLFinite (ofString "after") (.val (.word waft)) t2
  have heff_t3 : R16Shards.WorldEff s t3 [] [] R16Shards.wsGw := heff_t2.locals_clock _ _
  refine R16Shards.worldEff_ite heff_t3 _ hnt_c3 hcr_c3
    (fun _ _ _ hnt_push hcr_push =>
      worldEff_vibPush_so hAR heff_t3 w_top w_end waft
        (by simp [t3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        (by simp [t3, t2, t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hend_t,
              show ofString "after" ≠ ofString "end" by decide,
              show ofString "payload" ≠ ofString "end" by decide,
              show ofString "h" ≠ ofString "end" by decide])
        (by simp [t3, t2, t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, htop_t,
              show ofString "after" ≠ ofString "top" by decide,
              show ofString "payload" ≠ ofString "top" by decide,
              show ofString "h" ≠ ofString "top" by decide])
        hnt_push hcr_push)
    (fun _ _ _ => R16Shards.worldEff_assign_local heff_t3 _ _)

private theorem worldEff__rlp_validate_items_body_so {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "_rlp_validate_items_body") vals =
      some (sourceFnBody Guest.Software.guestFn__rlp_validate_items_body, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__rlp_validate_items_body)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__rlp_validate_items_body)).1) :
    R16Shards.WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__rlp_validate_items_body)).2
      [] [] R16Shards.wsGw := by
  obtain ⟨wp, wlen, rfl, hp_lk, hlen_lk⟩ :=
    lookupCode_two_words_so (by decide) lookup__rlp_validate_items_body_so hl
  have heff0 : R16Shards.WorldEff s s [] [] R16Shards.wsGw := R16Shards.WorldEff.refl s [] [] R16Shards.wsGw hAR hc
  have hbody : sourceFnBody Guest.Software.guestFn__rlp_validate_items_body =
      .dec (ofString "top") .one (.const 0)
        (.dec (ofString "pos") .one (.var .local (ofString "p"))
          (.dec (ofString "end") .one (.op .add [.var .local (ofString "p"), .var .local (ofString "len")])
            (.dec (ofString "go") .one (.const 1)
              (.seq
                (.while (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) vibLoopBody_so)
                (.return (.const 0)))))) := rfl
  rw [hbody] at hnt hres ⊢
  refine R16Shards.worldEff_dec heff0 _ _ _ hnt (Or.inr (Or.inr (Or.inr hres))) (fun vtop hvtop _ hnt1 hcr1 => ?_)
  have hvtop_eq : vtop = .val (.word 0) := by simp [evalHOLExact] at hvtop; exact hvtop.symm
  subst hvtop_eq
  let s1 := setVarHOLFinite (ofString "top") (.val (.word 0)) s
  have heff1 : R16Shards.WorldEff s s1 [] [] R16Shards.wsGw := heff0.locals_clock _ _
  refine R16Shards.worldEff_dec heff1 _ _ _ hnt1 hcr1 (fun vpos hvpos _ hnt2 hcr2 => ?_)
  have hvpos_eq : vpos = .val (.word wp) := by
    simp [s1, setVarHOLFinite, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, hp_lk,
      show ofString "top" ≠ ofString "p" by decide] at hvpos
    exact hvpos.symm
  subst hvpos_eq
  let s2 := setVarHOLFinite (ofString "pos") (.val (.word wp)) s1
  have heff2 : R16Shards.WorldEff s s2 [] [] R16Shards.wsGw := heff1.locals_clock _ _
  refine R16Shards.worldEff_dec heff2 _ _ _ hnt2 hcr2 (fun vend hvend _ hnt3 hcr3 => ?_)
  have hvend_eq : vend = .val (.word (wp + wlen)) := by
    simp [s2, s1, setVarHOLFinite, evalHOLExact, evalListHOLExact, HolFiniteMapExact.lookup_update, FUPDATE,
      hp_lk, hlen_lk, valueIsWord, valueWord, wordOpHOL, wordOp,
      show ofString "pos" ≠ ofString "p" by decide, show ofString "top" ≠ ofString "p" by decide,
      show ofString "pos" ≠ ofString "len" by decide, show ofString "top" ≠ ofString "len" by decide] at hvend
    exact hvend.symm
  subst hvend_eq
  let s3 := setVarHOLFinite (ofString "end") (.val (.word (wp + wlen))) s2
  have heff3 : R16Shards.WorldEff s s3 [] [] R16Shards.wsGw := heff2.locals_clock _ _
  refine R16Shards.worldEff_dec heff3 _ _ _ hnt3 hcr3 (fun vgo hvgo _ hnt4 hcr4 => ?_)
  have hvgo_eq : vgo = .val (.word 1) := by simp [evalHOLExact] at hvgo; exact hvgo.symm
  subst hvgo_eq
  let s4 := setVarHOLFinite (ofString "go") (.val (.word 1)) s3
  have heff4 : R16Shards.WorldEff s s4 [] [] R16Shards.wsGw := heff3.locals_clock _ _
  have hw4 : R16Shards.WordLocals ["top", "pos", "end", "go"] s4 := by
    intro nm hnm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
    rcases hnm with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [s4, s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "go" ≠ ofString "top" by decide, show ofString "end" ≠ ofString "top" by decide,
        show ofString "pos" ≠ ofString "top" by decide]⟩
    · exact ⟨wp, by simp [s4, s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "go" ≠ ofString "pos" by decide, show ofString "end" ≠ ofString "pos" by decide]⟩
    · exact ⟨wp + wlen, by simp [s4, s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "go" ≠ ofString "end" by decide]⟩
    · exact ⟨1, by simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
  have hws_vib : R16Shards.wsafe vibLoopBody_so = true := by decide
  refine R16Shards.worldEff_seq hnt4 hcr4
    (fun hnt_w hcr_w =>
      R16Shards.worldEff_while _ (R16Shards.WordLocals ["top", "pos", "end", "go"])
        (fun _ hinv => hinv)
        (fun t heff_t hinv_t hnt_b hcr_b =>
          ⟨worldEff_vibLoopBody_so hAR heff_t hinv_t hnt_b hcr_b,
           fun hf => R16Shards.wordLocals_flowing hws_vib hinv_t
             (by rcases hf with h | h; exact Or.inl h; exact Or.inr (Or.inr h))⟩)
        s4.clock s4 rfl heff4 hw4 hnt_w hcr_w)
    (fun mid _ heff_mid _ _ => R16Shards.worldEff_return heff_mid _)

private theorem handledCall_raise_keeps_local_so {F : Type}
    (cur mid : PanSemStateFiniteExact 64 F)
    (eid evar fname : MlS) (preProg : ProgHOL 64) (rexp : ExpHOL 64) (args : List (ExpHOL 64))
    (key : MlS) (hrun : evaluateHOLFiniteState cur
      (.call (some (none, some (eid, evar, .seq preProg (.raise eid rexp)))) fname args) = (none, mid)) :
    mid.locals.lookup key = cur.locals.lookup key := by
  rw [evaluateHOLFiniteState_call] at hrun
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vs
  · rw [hargs] at hrun; cases hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hlk : lookupCodeHOLFinite cur.code.lookup fname vs with _ | ⟨b', c', r'⟩
    · rw [hlk] at hrun; cases hrun
    · rw [hlk] at hrun; dsimp only at hrun
      split at hrun
      · cases hrun
      · rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite cur c') b' with ⟨rc, st⟩
        rw [hcal] at hrun
        cases rc with
        | none => cases hrun
        | some r =>
          cases r with
          | returned rv =>
            dsimp only at hrun
            split at hrun
            · injection hrun with _ hm; rw [← hm]
            · cases hrun
          | exception exId exVal =>
            dsimp only at hrun
            split at hrun
            · split at hrun
              · split at hrun
                · rw [evaluateHOLFiniteState_seq_line780] at hrun
                  rcases hpre : evaluateHOLFiniteState _ preProg with ⟨rp, sp0⟩
                  rw [hpre] at hrun
                  cases rp with
                  | none =>
                    dsimp only at hrun
                    rw [evaluateHOLFiniteState_raise] at hrun
                    split at hrun
                    · dsimp only at hrun
                      split at hrun; cases hrun; cases hrun
                    · cases hrun
                  | some r_pre =>
                    dsimp only at hrun
                    cases hrun
                · cases hrun
              · cases hrun
            · cases hrun
          | _ => dsimp only at hrun; (repeat' split at hrun) <;> cases hrun

private theorem empty_B_sub_so : ∀ gs ∈ ([] : List (String × Nat)), gs ∈ globalBuffers :=
  fun _ h => nomatch h

private theorem ws_no_gb_so : ∀ gs ∈ globalBuffers, ofString gs.1 ∉ R16Shards.wsGw.map ofString := by
  decide

private theorem worldEff_rlp_validate_items_so {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_validate_items") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_validate_items, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_validate_items)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_validate_items)).1) :
    R16Shards.WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_validate_items)).2
      [] [] R16Shards.wsGw := by
  have _ := hl
  have heff0 : R16Shards.WorldEff s s [] [] R16Shards.wsGw := R16Shards.WorldEff.refl s [] [] R16Shards.wsGw hAR hc
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_validate_items =
      .decCall (ofString "mark") .one (ofString "scratch_mark") []
        (.dec (ofString "e") .one (.const 0)
          (.seq
            (.call (some (none, some (ofString "RlpErr", ofString "e",
                .seq
                  (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "mark")])
                  (.raise (ofString "RlpErr") (.var .local (ofString "e"))))))
              (ofString "_rlp_validate_items_body") [.var .local (ofString "p"), .var .local (ofString "len")])
            (.seq
              (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "mark")])
              (.return (.const 0))))) := rfl
  rw [hbody] at hnt hres ⊢
  refine R16Shards.worldEff_decCall_scratch_mark heff0 _ hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun sp mid1 _ _ hsp_al hsp_lo hsp_hi hmid1_eq heff1 hnt1 hcr1 => ?_)
  refine R16Shards.worldEff_dec heff1 _ _ _ hnt1 hcr1 (fun ve hve _ hnt2 hcr2 => ?_)
  have hve_eq : ve = .val (.word (0 : BitVec 64)) := by simp [evalHOLExact] at hve; exact hve.symm
  subst hve_eq
  let mid2 := setVarHOLFinite (ofString "e") (.val (.word (0 : BitVec 64))) mid1
  have heff2 : R16Shards.WorldEff s mid2 [] [] R16Shards.wsGw := heff1.locals_clock _ _
  have hmark_m2 : mid2.locals.lookup (ofString "mark") = some (.val (.word sp)) := by
    simp [mid2, setVarHOLFinite, hmid1_eq, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "e" ≠ ofString "mark" by decide]
  refine R16Shards.worldEff_seq hnt2 hcr2
    (fun hnt_c hcr_c =>
      R16Shards.worldEff_handledCall heff2 none (ofString "RlpErr") (ofString "e") _
        (ofString "_rlp_validate_items_body") _
        (fun _ _ h => by cases h) (by decide) _ _ _ lookup__rlp_validate_items_body_so
        (fun callee cvals _ hlc hnt_cb hres_cb =>
          heff2.trans_noBuf
            (R16Shards.WorldEff.from_locals_clock
              (worldEff__rlp_validate_items_body_so (callEntryStateHOLFinite mid2 callee) cvals
                heff2.code (localsFree_arenaReady mid2 callee _ heff2.arena)
                (by simpa [heff2.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
            empty_B_sub_so ws_no_gb_so)
        (fun exVal cpost heff_cp hnt_h hcr_h => by
          let hst := setVarHOLFinite (ofString "e") exVal { cpost with locals := mid2.locals }
          have heff_hst : R16Shards.WorldEff s hst [] [] R16Shards.wsGw := heff_cp.locals_clock _ _
          have hmark_hst : @evalHOLExact 64 F _ hst.toExact (fun a => Classical.propDecidable (hst.memaddrs a))
              (.var .local (ofString "mark")) = some (.val (.word sp)) := by
            simp [hst, setVarHOLFinite, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, hmark_m2,
              show ofString "e" ≠ ofString "mark" by decide]
          exact R16Shards.worldEff_seq hnt_h hcr_h
            (fun hnt_sr _ => (R16Shards.worldEff_call0_scratch_release hAR.2 heff_hst (by decide) _ sp hmark_hst hsp_lo hsp_hi hsp_al hnt_sr).2.choose_spec.2)
            (fun m_sr _ heff_sr _ _ => R16Shards.worldEff_raise heff_sr _ _))
        hnt_c hcr_c)
    (fun mid3 hmid3 heff3 hnt3 hcr3 => ?_)
  have hmark_m3 : mid3.locals.lookup (ofString "mark") = some (.val (.word sp)) := by
    rw [handledCall_raise_keeps_local_so mid2 mid3 _ _ _ _ _ _ _ hmid3]
    exact hmark_m2
  have hmark_ev3 : @evalHOLExact 64 F _ mid3.toExact (fun a => Classical.propDecidable (mid3.memaddrs a))
      (.var .local (ofString "mark")) = some (.val (.word sp)) := hmark_m3
  exact R16Shards.worldEff_seq hnt3 hcr3
    (fun hnt_sr _ => (R16Shards.worldEff_call0_scratch_release hAR.2 heff3 (by decide) _ sp hmark_ev3 hsp_lo hsp_hi hsp_al hnt_sr).2.choose_spec.2)
    (fun m_sr _ heff_sr _ _ => R16Shards.worldEff_return heff_sr _)

theorem worldEff_rlp_item_total_so {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_item_total") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_item_total, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item_total)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item_total)).1) :
    R16Shards.WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item_total)).2
      [] [] R16Shards.wsGw := by
  have _ := hl
  have heff0 : R16Shards.WorldEff s s [] [] R16Shards.wsGw := R16Shards.WorldEff.refl s [] [] R16Shards.wsGw hAR hc
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine R16Shards.worldEff_decCall_ro heff0 R13.ro_rlp_item_header
    _ _ _ hnt (Or.inr (Or.inr (Or.inr hres))) (fun rvh cpost _ hcpost hnt1 hcr1 => ?_)
  let s1 := setVarHOLFinite (ofString "h") rvh { cpost with locals := s.locals }
  have heff1 : R16Shards.WorldEff s s1 [] [] R16Shards.wsGw := (heff0.of_readOnly hcpost).locals_clock _ _
  refine R16Shards.worldEff_seq hnt1 hcr1
    (fun hnt_i hcr_i =>
      R16Shards.worldEff_ite heff1 _ hnt_i hcr_i
        (fun _ _ _ hnt_c hcr_c =>
          R16Shards.worldEff_call0_eff heff1 (ofString "rlp_validate_items") _ _ _ _ lookup_rlp_validate_items_so
            (fun callee cvals _ hlc hnt_cb hres_cb =>
              heff1.trans_noBuf
                (R16Shards.WorldEff.from_locals_clock
                  (worldEff_rlp_validate_items_so (callEntryStateHOLFinite s1 callee) cvals
                    heff1.code (localsFree_arenaReady s1 callee _ heff1.arena)
                    (by simpa [heff1.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                empty_B_sub_so ws_no_gb_so)
            hnt_c hcr_c)
        (fun _ _ _ => R16Shards.worldEff_skip heff1))
    (fun mid _ heff_mid _ _ => R16Shards.worldEff_return heff_mid _)

theorem worldEff_rlp_list_count_so {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_list_count") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_list_count, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).1) :
    R16Shards.WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).2
      [] [] R16Shards.wsGw := by
  have _ := hl
  have heff0 : R16Shards.WorldEff s s [] [] R16Shards.wsGw := R16Shards.WorldEff.refl s [] [] R16Shards.wsGw hAR hc
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_list_count,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine R16Shards.worldEff_dec heff0 _ _ _ hnt (Or.inr (Or.inr (Or.inr hres))) (fun vcnt _ _ hnt1 hcr1 => ?_)
  let s1 := setVarHOLFinite (ofString "count") vcnt s
  have heff1 : R16Shards.WorldEff s s1 [] [] R16Shards.wsGw := heff0.locals_clock _ _
  refine R16Shards.worldEff_dec heff1 _ _ _ hnt1 hcr1 (fun voff _ _ hnt2 hcr2 => ?_)
  let s2 := setVarHOLFinite (ofString "off") voff s1
  have heff2 : R16Shards.WorldEff s s2 [] [] R16Shards.wsGw := heff1.locals_clock _ _
  refine R16Shards.worldEff_seq hnt2 hcr2
    (fun hnt_w hcr_w =>
      R16Shards.worldEff_while _ (fun _ => True) (fun _ _ => trivial)
        (fun t heff_t _ hnt_b hcr_b =>
          ⟨R16Shards.worldEff_decCall_eff heff_t (ofString "total") .one (ofString "rlp_item_total") _ _ _ _ lookup_rlp_item_total_so
            (fun callee cvals _ hlc hnt_cb hres_cb =>
              heff_t.trans_noBuf
                (R16Shards.WorldEff.from_locals_clock
                  (worldEff_rlp_item_total_so (callEntryStateHOLFinite t callee) cvals
                    heff_t.code (localsFree_arenaReady t callee _ heff_t.arena)
                    (by simpa [heff_t.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                empty_B_sub_so ws_no_gb_so)
            (fun _ _ rv cpost _ _ _ _ heff_cp hnt_k hcr_k =>
              R16Shards.worldEff_seq hnt_k hcr_k
                (fun _ _ => R16Shards.worldEff_assign_local (heff_cp.locals_clock _ _) _ _)
                (fun m2 _ heff_m2 _ _ => R16Shards.worldEff_assign_local heff_m2 _ _))
            hnt_b hcr_b,
           fun _ => trivial⟩)
        s2.clock s2 rfl heff2 trivial hnt_w hcr_w)
    (fun mid _ heff_mid _ _ => R16Shards.worldEff_return heff_mid _)

private def countCond_so : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "off")) (.var .local (ofString "len"))

private def countBody_so : ProgHOL 64 :=
  .decCall (ofString "total") .one (ofString "rlp_item_total")
    [.op .add [.var .local (ofString "p"), .var .local (ofString "off")],
      .op .sub [.var .local (ofString "len"), .var .local (ofString "off")]]
    (.seq (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))
      (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const 1#64])))

private theorem countBody_no_bc_so {F : Type} (t : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState t countBody_so).1 ≠ some .break ∧
    (evaluateHOLFiniteState t countBody_so).1 ≠ some .continue := by
  unfold countBody_so
  rw [evaluateHOLFiniteState_decCall_total]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rename_i body callee _ _ _
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨r, st⟩
        simp only [hrun]
        cases r with
        | none => simp
        | some r =>
          cases r with
          | returned w =>
            dsimp only
            split
            · dsimp only
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
              split
              · simp
              · split
                · dsimp only
                  rw [evaluateHOLFiniteState_assign]
                  split <;> [simp; (split <;> simp)]
                · simp
            · simp
          | _ => simp

private def RlpItemEntry_so {F : Type} (s : PanSemStateFiniteExact 64 F) (P L : BitVec 64)
    (off T : BitVec 64) : Prop :=
  1 ≤ T.toNat ∧ off.toNat + T.toNat ≤ L.toNat ∧
  ∀ e2 : PanSemStateFiniteExact 64 F,
    e2.code = originalRuntimeCode →
    e2.locals.lookup (ofString "p") = some (.val (.word (P + off))) →
    (∀ j < L.toNat, memB e2 (P.toNat + j) = memB s (P.toNat + j)) →
    ∀ rv2 : ValueHOL 64,
      (evaluateHOLFiniteState e2 (sourceFnBody Guest.Software.guestFn_rlp_item_total_unchecked)).1 =
        some (.returned rv2) →
      rv2 = .val (.word T)

private def CountLoopInv_so {F : Type} (s0 : PanSemStateFiniteExact 64 F) (P L : BitVec 64)
    (t : PanSemStateFiniteExact 64 F) : Prop :=
  R16Shards.WorldEff s0 t [] [] R16Shards.wsGw ∧
  globN t "heap_ptr" = globN s0 "heap_ptr" ∧
  ∃ (items : List (BitVec 64 × BitVec 64)) (y c : BitVec 64),
    t.locals.lookup (ofString "p") = some (.val (.word P)) ∧
    t.locals.lookup (ofString "off") = some (.val (.word y)) ∧
    t.locals.lookup (ofString "len") = some (.val (.word L)) ∧
    t.locals.lookup (ofString "count") = some (.val (.word c)) ∧
    items.length = c.toNat ∧
    c.toNat ≤ y.toNat ∧
    y.toNat ≤ L.toNat ∧
    ((items.map (fun x => x.2.toNat)).sum = y.toNat) ∧
    (∀ k (hk : k < items.length),
      (items[k].1).toNat = ((items.take k).map (fun x => x.2.toNat)).sum ∧
      RlpItemEntry_so s0 P L items[k].1 items[k].2)

private theorem countBody_step_so {F : Type}
    {s0 t mid : PanSemStateFiniteExact 64 F} {P L : BitVec 64}
    (hAR0 : ArenaReady s0)
    (hPL : P.toNat + L.toNat ≤ globN s0 "heap_ptr")
    (hinv : CountLoopInv_so s0 P L t)
    (hlt_cond : ∃ cw : BitVec 64,
      @evalHOLExact 64 F _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) countCond_so =
        some (.val (.word cw)) ∧ cw ≠ 0)
    (hbr : evaluateHOLFiniteState (decClockHOLFinite t) countBody_so = (none, mid)) :
    CountLoopInv_so s0 P L mid := by
  obtain ⟨heff_t, hhp_t, items, y, c, hp_t, hy_t, hl_t, hc_t, hlen_it, hc_le_y, hy_le_L, hsum_it, hitems⟩ := hinv
  obtain ⟨cw, hcond, hnz⟩ := hlt_cond
  have hlt : y.toNat < L.toNat := by
    simp [countCond_so, evalHOLExact, hy_t, hl_t, Compiler.Encoders.Asm.wordCmpHOL] at hcond
    by_contra hge
    have hge' : ¬ (y < L) := by rw [BitVec.lt_def]; omega
    simp [hge'] at hcond
    exact hnz hcond.symm
  let td := decClockHOLFinite t
  have heff_td : R16Shards.WorldEff s0 td [] [] R16Shards.wsGw := heff_t.locals_clock t.locals (t.clock - 1)
  have hhp_td : globN td "heap_ptr" = globN s0 "heap_ptr" := hhp_t
  unfold countBody_so at hbr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hbr
  have hargs_td : evalListHOLFinite td (h := fun a => Classical.propDecidable (td.memaddrs a))
      [.op .add [.var .local (ofString "p"), .var .local (ofString "off")],
       .op .sub [.var .local (ofString "len"), .var .local (ofString "off")]] =
      some [.val (.word (P + y)), .val (.word (L - y))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [td, decClockHOLFinite, evalListHOLExact, evalHOLExact, hp_t, hy_t, hl_t,
      wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hargs_td] at hbr; dsimp only at hbr
  rcases hl_call : lookupCodeHOLFinite td.code.lookup (ofString "rlp_item_total")
      [.val (.word (P + y)), .val (.word (L - y))] with _ | ⟨body', callee, ret'⟩
  · rw [hl_call] at hbr; simp at hbr
  · rw [hl_call] at hbr; dsimp only at hbr
    by_cases hz : td.clock = 0
    · rw [if_pos hz] at hbr; simp at hbr
    · rw [if_neg hz] at hbr
      have hsame_b := lookupCodeHOLFinite_installed_body td.code.lookup _ _ _ body' _ ret' _ callee
        (by rw [heff_td.code]; exact lookup_rlp_item_total_so) hl_call
      subst hsame_b
      have hsame_r := lookupCodeHOLFinite_installed_return td _ _ _ _ _ ret' _ callee
        (by rw [heff_td.code]; exact lookup_rlp_item_total_so) hl_call
      subst hsame_r
      obtain ⟨_, hcp, hcl⟩ := callee_p_len_so lookup_rlp_item_total_so _ _ _ callee _
        (by simpa [heff_td.code] using hl_call)
      let ent := callEntryStateHOLFinite td callee
      rcases hrun_c : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_item_total) with ⟨rc, cpost⟩
      rw [hrun_c] at hbr
      cases rc with
      | none => simp at hbr
      | some r1 =>
        cases r1 with
        | returned rv =>
          dsimp only at hbr
          split at hbr <;> [skip; simp at hbr]
          have hhl_lt : heapLimit < 2 ^ 64 := by decide
          have hhp0_hi : globN s0 "heap_ptr" ≤ heapLimit := hAR0.2.2.1
          have hPy_add : (P + y).toNat = P.toNat + y.toNat :=
            BitVec.toNat_add_of_lt (by omega)
          have hLy_sub : (L - y).toNat = L.toNat - y.toNat := by
            rw [BitVec.toNat_sub]; omega
          have hfit_ent : (P + y).toNat + (L - y).toNat ≤ 2 ^ 64 := by omega
          obtain ⟨T, rfl, hT1, hT_le, hagree_ent⟩ :=
            rlp_item_total_agree_unchecked_so ent heff_td.code (P + y) (L - y) hfit_ent hcp hcl rv
              (by rw [hrun_c])
          rw [hLy_sub] at hT_le
          have heff_cpost_raw := worldEff_rlp_item_total_so ent [.val (.word (P + y)), .val (.word (L - y))]
            heff_td.code (localsFree_arenaReady td callee _ heff_td.arena)
            (by simpa [heff_td.code, ent, callEntryStateHOLFinite] using hl_call)
            (by rw [hrun_c]; simp) (by rw [hrun_c]; exact Or.inl ⟨_, rfl⟩)
          rw [hrun_c] at heff_cpost_raw; dsimp only at heff_cpost_raw
          have heff_cpost : R16Shards.WorldEff s0 cpost [] [] R16Shards.wsGw :=
            heff_td.trans_noBuf (R16Shards.WorldEff.from_locals_clock heff_cpost_raw) empty_B_sub_so ws_no_gb_so
          have hhp_cpost : globN cpost "heap_ptr" = globN s0 "heap_ptr" := by
            have hk := rlp_item_total_keeps_hp_so ent heff_td.code
            rw [hrun_c] at hk; dsimp only at hk
            exact hk.trans hhp_td
          let u0 := setVarHOLFinite (ofString "total") (.val (.word T)) { cpost with locals := td.locals }
          have hu0_off : u0.locals.lookup (ofString "off") = some (.val (.word y)) := by
            simp [u0, td, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy_t,
              show ofString "total" ≠ ofString "off" by decide]
          have hu0_cnt : u0.locals.lookup (ofString "count") = some (.val (.word c)) := by
            simp [u0, td, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hc_t,
              show ofString "total" ≠ ofString "count" by decide]
          have hu0_p : u0.locals.lookup (ofString "p") = some (.val (.word P)) := by
            simp [u0, td, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_t,
              show ofString "total" ≠ ofString "p" by decide]
          have hu0_len : u0.locals.lookup (ofString "len") = some (.val (.word L)) := by
            simp [u0, td, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_t,
              show ofString "total" ≠ ofString "len" by decide]
          have hu0_tot : u0.locals.lookup (ofString "total") = some (.val (.word T)) := by
            simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have ha1 : evaluateHOLFiniteState u0
              (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")])) =
              (none, setKvarHOLFinite .local (ofString "off") (.val (.word (y + T))) u0) := by
            rw [evaluateHOLFiniteState_assign]
            simp [evalHOLExact, evalListHOLExact, hu0_off, hu0_tot, wordOpHOL, wordOp, valueIsWord, valueWord,
              isValidValueHOLFinite, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL]
          let u1 := setKvarHOLFinite .local (ofString "off") (.val (.word (y + T))) u0
          have hu1_cnt : u1.locals.lookup (ofString "count") = some (.val (.word c)) := by
            simp [u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu0_cnt,
              show ofString "off" ≠ ofString "count" by decide]
          have ha2 : evaluateHOLFiniteState u1
              (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const 1#64])) =
              (none, setKvarHOLFinite .local (ofString "count") (.val (.word (c + 1#64))) u1) := by
            rw [evaluateHOLFiniteState_assign]
            simp [evalHOLExact, evalListHOLExact, hu1_cnt, wordOpHOL, wordOp, valueIsWord, valueWord,
              isValidValueHOLFinite, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL]
          let u2 := setKvarHOLFinite .local (ofString "count") (.val (.word (c + 1#64))) u1
          have hseq_eval : evaluateHOLFiniteState u0
              (.seq (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))
                (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const 1#64]))) =
              (none, u2) := by
            rw [evaluateHOLFiniteState_seq_line780, ha1]; dsimp only; exact ha2
          change (let r := evaluateHOLFiniteState u0 _;
            (r.1, { r.2 with locals := HolFiniteMapExact.resVarEq r.2.locals (ofString "total", td.locals.lookup (ofString "total")) })) =
            (none, mid) at hbr
          rw [hseq_eval] at hbr
          simp only [Prod.mk.injEq] at hbr
          obtain ⟨-, hmid_eq⟩ := hbr
          subst hmid_eq
          have heff_mid : R16Shards.WorldEff s0
              { u2 with locals := HolFiniteMapExact.resVarEq u2.locals (ofString "total", td.locals.lookup (ofString "total")) }
              [] [] R16Shards.wsGw :=
            heff_cpost.locals_clock _ u2.clock
          have hhp_mid : globN
              { u2 with locals := HolFiniteMapExact.resVarEq u2.locals (ofString "total", td.locals.lookup (ofString "total")) }
              "heap_ptr" = globN s0 "heap_ptr" := hhp_cpost
          have hyT_nat : (y + T).toNat = y.toNat + T.toNat :=
            BitVec.toNat_add_of_lt (by omega)
          have hc1_nat : (c + 1#64).toNat = c.toNat + 1 :=
            BitVec.toNat_add_of_lt (by change c.toNat + 1 < 2 ^ 64; omega)
          have hent_memB : ∀ j < (L - y).toNat, memB ent ((P + y).toNat + j) = memB s0 ((P + y).toNat + j) := by
            intro j hj
            have hmem_t : memB t ((P + y).toNat + j) = memB s0 ((P + y).toNat + j) :=
              memB_kept_below_hp_of_stepFrame hAR0 heff_t.be (stepFrame_of_worldEff heff_t) (by omega)
            exact hmem_t
          have hentry_new : RlpItemEntry_so s0 P L y T := by
            refine ⟨hT1, by omega, ?_⟩
            intro e2 hc2 hp2 hbytes2 rv2 hret2
            apply hagree_ent e2 hc2 hp2 _ rv2 hret2
            intro j hj
            rw [hLy_sub] at hj
            rw [hPy_add, Nat.add_assoc, hbytes2 (y.toNat + j) (by omega),
              ← Nat.add_assoc, ← hPy_add, ← hent_memB j (by rw [hLy_sub]; exact hj)]
          refine ⟨heff_mid, hhp_mid, items ++ [(y, T)], y + T, c + 1#64, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · dsimp only
            rw [R16Shards.resVarEq_lookup_local, if_neg (by decide : ofString "p" ≠ ofString "total")]
            simp [u2, u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu0_p,
              show ofString "count" ≠ ofString "p" by decide, show ofString "off" ≠ ofString "p" by decide]
          · dsimp only
            rw [R16Shards.resVarEq_lookup_local, if_neg (by decide : ofString "off" ≠ ofString "total")]
            simp [u2, u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "count" ≠ ofString "off" by decide]
          · dsimp only
            rw [R16Shards.resVarEq_lookup_local, if_neg (by decide : ofString "len" ≠ ofString "total")]
            simp [u2, u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu0_len,
              show ofString "count" ≠ ofString "len" by decide, show ofString "off" ≠ ofString "len" by decide]
          · dsimp only
            rw [R16Shards.resVarEq_lookup_local, if_neg (by decide : ofString "count" ≠ ofString "total")]
            simp [u2, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          · simp [hlen_it, hc1_nat]
          · rw [hc1_nat, hyT_nat]; omega
          · rw [hyT_nat]; omega
          · simp [List.map_append, List.sum_append, hsum_it, hyT_nat]
          · intro k hk
            rw [List.length_append, List.length_singleton] at hk
            by_cases hk_lt : k < items.length
            · rw [List.getElem_append_left hk_lt, List.take_append_of_le_length (Nat.le_of_lt hk_lt)]
              exact hitems k hk_lt
            · have hk_eq : k = items.length := by omega
              subst hk_eq
              simp [List.take_append_of_le_length (le_refl items.length), hsum_it, hentry_new]
        | _ => simp at hbr

private theorem countBody_no_return_so {F : Type} (st : PanSemStateFiniteExact 64 F) (rv : ValueHOL 64) :
    (evaluateHOLFiniteState st countBody_so).1 ≠ some (.returned rv) := by
  unfold countBody_so
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
      [.op .add [.var .local (ofString "p"), .var .local (ofString "off")],
       .op .sub [.var .local (ofString "len"), .var .local (ofString "off")]] with _ | vs
  · simp
  · simp only [hargs]
    rcases hlk : lookupCodeHOLFinite st.code.lookup (ofString "rlp_item_total") vs with _ | ⟨b', c', r'⟩
    · simp
    · simp only [hlk]
      by_cases hz : st.clock = 0
      · simp [hz]
      · simp only [hz, ↓reduceIte]
        rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite st c') b' with ⟨rc, cst⟩
        simp only [hcal]
        rcases rc with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> try simp
        split
        · dsimp only
          let u0 := setVarHOLFinite (ofString "total") w { cst with locals := st.locals }
          change (evaluateHOLFiniteState u0 _).1 ≠ some (.returned rv)
          rw [evaluateHOLFiniteState_seq_line780]
          have ha1 : ∀ x : Option (PanSemResultExact 64),
              (evaluateHOLFiniteState u0 (.assign .local (ofString "off")
                (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))).1 = x →
              x = none ∨ x = some .error := by
            intro x hx; rw [← hx, evaluateHOLFiniteState_assign]
            rcases @evalHOLExact 64 F _ u0.toExact (fun a => Classical.propDecidable (u0.memaddrs a))
                (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]) with _ | v1
            · exact Or.inr rfl
            · dsimp only
              by_cases hv : isValidValueHOLFinite u0 .local (ofString "off") v1 = true
              · rw [if_pos hv]; exact Or.inl rfl
              · rw [if_neg hv]; exact Or.inr rfl
          rcases h1 : evaluateHOLFiniteState u0 (.assign .local (ofString "off")
              (.op .add [.var .local (ofString "off"), .var .local (ofString "total")])) with ⟨r1, u1⟩
          rcases ha1 r1 (by rw [h1]) with rfl | rfl
          · dsimp only
            rw [evaluateHOLFiniteState_assign]
            rcases @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
                (.op .add [.var .local (ofString "count"), .const 1#64]) with _ | v2
            · simp
            · dsimp only
              by_cases hv2 : isValidValueHOLFinite u1 .local (ofString "count") v2 = true
              · rw [if_pos hv2]; simp
              · rw [if_neg hv2]; simp
          · simp
        · simp

private theorem while_count_no_return_so {F : Type} (rv : ValueHOL 64) :
    ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock ≤ k →
      (evaluateHOLFiniteState st (.while countCond_so countBody_so)).1 ≠ some (.returned rv) := by
  intro k
  induction k with
  | zero =>
    intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) countCond_so with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]
        have hk0 : st.clock = 0 := by omega
        rw [if_pos hk0]; simp
  | succ k ih =>
    intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) countCond_so with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]
        by_cases hk0 : st.clock = 0
        · rw [if_pos hk0]; simp
        · rw [if_neg hk0]
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) countBody_so
          have hb_nr := countBody_no_return_so (decClockHOLFinite st) rv
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) countBody_so with ⟨r1, m1⟩
          simp only [hbr] at rem hb_nr ⊢
          cases r1 with
          | none => exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
          | some r1 =>
            cases r1 with
            | «continue» => exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
            | «break» => simp
            | returned v' =>
              intro heq; injection heq with heq'; injection heq' with heq''; subst heq''
              exact hb_nr rfl
            | _ => simp

private theorem while_countLoopInv_so {F : Type}
    {s0 : PanSemStateFiniteExact 64 F} {P L : BitVec 64}
    (hAR0 : ArenaReady s0) (hPL : P.toNat + L.toNat ≤ globN s0 "heap_ptr") :
    ∀ (k : Nat) (t post : PanSemStateFiniteExact 64 F),
      t.clock ≤ k →
      CountLoopInv_so s0 P L t →
      evaluateHOLFiniteState t (.while countCond_so countBody_so) = (none, post) →
      CountLoopInv_so s0 P L post ∧
        ∃ cw : BitVec 64,
          @evalHOLExact 64 F _ post.toExact (fun x => Classical.propDecidable (post.memaddrs x)) countCond_so =
            some (.val (.word cw)) ∧ cw = 0 := by
  intro k
  induction k with
  | zero =>
    intro t post hclk hinv hrun
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun <;> [simp at hrun; omega]
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun
        exact ⟨hinv, 0, hcond, rfl⟩
    · simp at hrun
  | succ k ih =>
    intro t post hclk hinv hrun
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite t) countBody_so
          have hbc := countBody_no_bc_so (decClockHOLFinite t)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite t) countBody_so with ⟨r1, mid⟩
          rw [hbr] at hrun rem hbc
          cases r1 with
          | none =>
            have hinv_mid := countBody_step_so hAR0 hPL hinv ⟨cw, hcond, hnz⟩ hbr
            exact ih mid post (by change mid.clock ≤ t.clock - 1 at rem; omega) hinv_mid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl hbc.2
            | «break» => exact absurd rfl hbc.1
            | _ => simp at hrun
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun
        exact ⟨hinv, 0, hcond, rfl⟩
    · simp at hrun

theorem rlp_list_count_ret_spec_so {F : Type}
    (s cpost : PanSemStateFiniteExact 64 F) (P L : BitVec 64) (rv : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hPL : P.toNat + L.toNat ≤ globN s "heap_ptr")
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : s.locals.lookup (ofString "len") = some (.val (.word L)))
    (hret : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count) =
      (some (.returned rv), cpost)) :
    ∃ (wcnt : BitVec 64) (items : List (BitVec 64 × BitVec 64)),
      rv = .val (.word wcnt) ∧
      R16Shards.WorldEff s cpost [] [] R16Shards.wsGw ∧
      globN cpost "heap_ptr" = globN s "heap_ptr" ∧
      items.length = wcnt.toNat ∧
      wcnt.toNat ≤ L.toNat ∧
      ((items.map (fun x => x.2.toNat)).sum = L.toNat) ∧
      (∀ k (hk : k < items.length),
        (items[k].1).toNat = ((items.take k).map (fun x => x.2.toNat)).sum ∧
        RlpItemEntry_so s P L items[k].1 items[k].2) := by
  have heff_cp : R16Shards.WorldEff s cpost [] [] R16Shards.wsGw := by
    have heff0 : R16Shards.WorldEff s s [] [] R16Shards.wsGw := R16Shards.WorldEff.refl s [] [] R16Shards.wsGw hAR hc
    have hbody : sourceFnBody Guest.Software.guestFn_rlp_list_count =
        .dec (ofString "count") .one (.const 0#64)
          (.dec (ofString "off") .one (.const 0#64)
            (.seq (.while countCond_so countBody_so)
              (.return (.var .local (ofString "count"))))) := rfl
    have hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).1 ≠ some .timeOut := by
      rw [hret]; simp
    have hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).1 := by
      rw [hret]; exact Or.inl ⟨rv, rfl⟩
    have hw := worldEff_rlp_list_count_so (callEntryStateHOLFinite s
      (HolFiniteMapExact.update (HolFiniteMapExact.update HolFiniteMapExact.empty (ofString "p", .val (.word P)))
        (ofString "len", .val (.word L)))) [.val (.word P), .val (.word L)]
    clear hw
    rw [hbody] at hnt hres
    have heff_run : R16Shards.WorldEff s (evaluateHOLFiniteState s
        (.dec (ofString "count") .one (.const 0#64)
          (.dec (ofString "off") .one (.const 0#64)
            (.seq (.while countCond_so countBody_so)
              (.return (.var .local (ofString "count"))))))).2 [] [] R16Shards.wsGw := by
      refine R16Shards.worldEff_dec heff0 _ _ _ hnt (Or.inr (Or.inr (Or.inr hres))) (fun vcnt _ _ hnt1 hcr1 => ?_)
      let s1 := setVarHOLFinite (ofString "count") vcnt s
      have heff1 : R16Shards.WorldEff s s1 [] [] R16Shards.wsGw := heff0.locals_clock _ _
      refine R16Shards.worldEff_dec heff1 _ _ _ hnt1 hcr1 (fun voff _ _ hnt2 hcr2 => ?_)
      let s2 := setVarHOLFinite (ofString "off") voff s1
      have heff2 : R16Shards.WorldEff s s2 [] [] R16Shards.wsGw := heff1.locals_clock _ _
      refine R16Shards.worldEff_seq hnt2 hcr2
        (fun hnt_w hcr_w =>
          R16Shards.worldEff_while _ (fun _ => True) (fun _ _ => trivial)
            (fun t heff_t _ hnt_b hcr_b =>
              ⟨R16Shards.worldEff_decCall_eff heff_t (ofString "total") .one (ofString "rlp_item_total") _ _ _ _ lookup_rlp_item_total_so
                (fun callee cvals _ hlc hnt_cb hres_cb =>
                  heff_t.trans_noBuf
                    (R16Shards.WorldEff.from_locals_clock
                      (worldEff_rlp_item_total_so (callEntryStateHOLFinite t callee) cvals
                        heff_t.code (localsFree_arenaReady t callee _ heff_t.arena)
                        (by simpa [heff_t.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                    empty_B_sub_so ws_no_gb_so)
                (fun _ _ _ cp _ _ _ _ heff_c hnt_k hcr_k =>
                  R16Shards.worldEff_seq hnt_k hcr_k
                    (fun _ _ => R16Shards.worldEff_assign_local (heff_c.locals_clock _ _) _ _)
                    (fun m2 _ heff_m2 _ _ => R16Shards.worldEff_assign_local heff_m2 _ _))
                hnt_b hcr_b,
               fun _ => trivial⟩)
            s2.clock s2 rfl heff2 trivial hnt_w hcr_w)
        (fun mid _ heff_mid _ _ => R16Shards.worldEff_return heff_mid _)
    change R16Shards.WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).2
      [] [] R16Shards.wsGw at heff_run
    rwa [hret] at heff_run
  have hhp_cp : globN cpost "heap_ptr" = globN s "heap_ptr" := by
    have hk := rlp_list_count_keeps_hp_so s hc
    rwa [hret] at hk
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_list_count =
      .dec (ofString "count") .one (.const 0#64)
        (.dec (ofString "off") .one (.const 0#64)
          (.seq (.while countCond_so countBody_so)
            (.return (.var .local (ofString "count"))))) := rfl
  have hret1 : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).1 =
      some (.returned rv) := by rw [hret]
  clear hret
  rw [hbody] at hret1
  revert rv hret1
  change RetOK (fun rv =>
    ∃ (wcnt : BitVec 64) (items : List (BitVec 64 × BitVec 64)),
      rv = .val (.word wcnt) ∧
      R16Shards.WorldEff s cpost [] [] R16Shards.wsGw ∧
      globN cpost "heap_ptr" = globN s "heap_ptr" ∧
      items.length = wcnt.toNat ∧
      wcnt.toNat ≤ L.toNat ∧
      ((items.map (fun x => x.2.toNat)).sum = L.toNat) ∧
      (∀ k (hk : k < items.length),
        (items[k].1).toNat = ((items.take k).map (fun x => x.2.toNat)).sum ∧
        RlpItemEntry_so s P L items[k].1 items[k].2)) s _
  refine RetOK.dec (fun vcnt hvcnt _ => ?_)
  have hvcnt_eq : vcnt = .val (.word 0#64) := by simp [evalHOLExact] at hvcnt; exact hvcnt.symm
  subst hvcnt_eq
  refine RetOK.dec (fun voff hvoff _ => ?_)
  have hvoff_eq : voff = .val (.word 0#64) := by simp [evalHOLExact] at hvoff; exact hvoff.symm
  subst hvoff_eq
  let s2 := setVarHOLFinite (ofString "off") (.val (.word 0#64))
    (setVarHOLFinite (ofString "count") (.val (.word 0#64)) s)
  have heff0 : R16Shards.WorldEff s s [] [] R16Shards.wsGw := R16Shards.WorldEff.refl s [] [] R16Shards.wsGw hAR hc
  have hinv2 : CountLoopInv_so s P L s2 := by
    refine ⟨(heff0.locals_clock _ _).locals_clock _ _, rfl, [], 0#64, 0#64, ?_, ?_, ?_, ?_,
      rfl, Nat.zero_le _, Nat.zero_le _, rfl, fun k hk => by simp at hk⟩
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
        show ofString "off" ≠ ofString "p" by decide, show ofString "count" ≠ ofString "p" by decide]
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl,
        show ofString "off" ≠ ofString "len" by decide, show ofString "count" ≠ ofString "len" by decide]
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "off" ≠ ofString "count" by decide]
  refine RetOK.seq (fun v hv => absurd hv (while_count_no_return_so v s2.clock s2 le_rfl)) (fun mid hmid => ?_)
  obtain ⟨⟨_, _, items, y, c, _, hy_m, hl_m, hc_m, hlen_it, hc_le_y, hy_le_L, hsum_it, hitems⟩, cw, hcond_m, hcw0⟩ :=
    while_countLoopInv_so hAR hPL s2.clock s2 mid le_rfl hinv2 hmid
  have hy_eq_L : y.toNat = L.toNat := by
    subst hcw0
    simp only [countCond_so, evalHOLExact, hy_m, hl_m, Compiler.Encoders.Asm.wordCmpHOL] at hcond_m
    by_contra hne
    have hlt : y < L := by rw [BitVec.lt_def]; omega
    simp [hlt] at hcond_m
  refine RetOK.ret (fun v hv => ?_)
  simp [evalHOLExact, hc_m] at hv
  subst hv
  exact ⟨c, items, rfl, heff_cp, hhp_cp, hlen_it, by omega, by omega, hitems⟩

theorem sf_rlp_list_to_slices_so {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_list_to_slices") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices, s.locals, .comb [.one, .one]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices)).1) :
    ResolveDecodeStep.StepFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices)).2 := by
  obtain ⟨params, body0, ret0, hlook, hspec⟩ := R16Shards.MptC10C12.«ww_rlp_list_to_slices»
  have hsame_b := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "rlp_list_to_slices")
    params body0 (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices) ret0 (.comb [.one, .one]) vals s.locals hlook hl
  subst hsame_b
  have hsame_r := lookupCodeHOLFinite_installed_return s (ofString "rlp_list_to_slices")
    params _ _ ret0 (.comb [.one, .one]) vals s.locals (by rw [hc]; exact hlook) (by rwa [hc])
  subst hsame_r
  obtain ⟨hAR_p, hhp, hsp, hfo, hgl⟩ := hspec s hc hAR ⟨vals, hl⟩ hnt hres
  exact ResolveDecodeStep.stepFrame_of_ww_sub (fun _ hx => hx) hAR_p hhp hsp hfo hgl

private def ltsCond_so : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "count"))

private def ltsBody_so : ProgHOL 64 :=
  .decCall (ofString "total") .one (ofString "rlp_item_total_unchecked")
    [.op .add [.var .local (ofString "p"), .var .local (ofString "off")]]
    (.seq
      (.store (.op .add [.var .local (ofString "arr"),
          .panop .mul [.var .local (ofString "i"), .const 16#64]])
        (.op .add [.var .local (ofString "p"), .var .local (ofString "off")]))
      (.seq
        (.store (.op .add [.var .local (ofString "arr"),
            .panop .mul [.var .local (ofString "i"), .const 16#64], .const 8#64])
          (.var .local (ofString "total")))
        (.seq
          (.assign .local (ofString "off")
            (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const 1#64])))))

private theorem ltsBody_no_bc_so {F : Type} (st : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState st ltsBody_so).1 ≠ some .break ∧
    (evaluateHOLFiniteState st ltsBody_so).1 ≠ some .continue ∧
    ∀ rv, (evaluateHOLFiniteState st ltsBody_so).1 ≠ some (.returned rv) := by
  unfold ltsBody_so
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
      [.op .add [.var .local (ofString "p"), .var .local (ofString "off")]] with _ | vs
  · simp
  · simp only [hargs]
    rcases hlk : lookupCodeHOLFinite st.code.lookup (ofString "rlp_item_total_unchecked") vs with _ | ⟨b', c', r'⟩
    · simp
    · simp only [hlk]
      by_cases hz : st.clock = 0
      · simp [hz]
      · simp only [hz, ↓reduceIte]
        rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite st c') b' with ⟨rc, cst⟩
        simp only [hcal]
        rcases rc with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> try simp
        split
        · dsimp only
          let u0 := setVarHOLFinite (ofString "total") w { cst with locals := st.locals }
          have hst_res : ∀ (x : PanSemStateFiniteExact 64 F) (de ve : ExpHOL 64) (ro : Option (PanSemResultExact 64)),
              (evaluateHOLFiniteState x (.store de ve)).1 = ro → ro = none ∨ ro = some .error := by
            intro x de ve ro hro; rw [← hro, evaluateHOLFiniteState_store]
            rcases @evalHOLExact 64 F _ x.toExact (fun a => Classical.propDecidable (x.memaddrs a)) de with _ | dv
            · exact Or.inr rfl
            · rcases dv with ⟨⟨dw⟩⟩ | _ | _ <;> try exact Or.inr rfl
              rcases @evalHOLExact 64 F _ x.toExact (fun a => Classical.propDecidable (x.memaddrs a)) ve with _ | vv
              · exact Or.inr rfl
              · dsimp only
                rcases @panMemStoresHOL 64 _ dw (flattenHOL vv) x.memaddrs (fun a => Classical.propDecidable (x.memaddrs a)) x.memory with _ | m'
                · exact Or.inr rfl
                · exact Or.inl rfl
          have has_res : ∀ (x : PanSemStateFiniteExact 64 F) (nm : MlS) (ve : ExpHOL 64) (ro : Option (PanSemResultExact 64)),
              (evaluateHOLFiniteState x (.assign .local nm ve)).1 = ro → ro = none ∨ ro = some .error := by
            intro x nm ve ro hro; rw [← hro, evaluateHOLFiniteState_assign]
            rcases @evalHOLExact 64 F _ x.toExact (fun a => Classical.propDecidable (x.memaddrs a)) ve with _ | vv
            · exact Or.inr rfl
            · dsimp only
              by_cases hv : isValidValueHOLFinite x .local nm vv = true
              · rw [if_pos hv]; exact Or.inl rfl
              · rw [if_neg hv]; exact Or.inr rfl
          change (let r := evaluateHOLFiniteState u0 _;
            (r.1, { r.2 with locals := HolFiniteMapExact.resVarEq r.2.locals (ofString "total", st.locals.lookup (ofString "total")) })).1 ≠ _ ∧ _
          dsimp only
          rw [evaluateHOLFiniteState_seq_line780]
          rcases h1 : evaluateHOLFiniteState u0 (.store _ _) with ⟨r1, u1⟩
          rcases hst_res u0 _ _ r1 (by rw [h1]) with rfl | rfl
          · dsimp only; rw [evaluateHOLFiniteState_seq_line780]
            rcases h2 : evaluateHOLFiniteState u1 (.store _ _) with ⟨r2, u2⟩
            rcases hst_res u1 _ _ r2 (by rw [h2]) with rfl | rfl
            · dsimp only; rw [evaluateHOLFiniteState_seq_line780]
              rcases h3 : evaluateHOLFiniteState u2 (.assign .local (ofString "off") _) with ⟨r3, u3⟩
              rcases has_res u2 _ _ r3 (by rw [h3]) with rfl | rfl
              · dsimp only
                rcases h4 : evaluateHOLFiniteState u3 (.assign .local (ofString "i") _) with ⟨r4, u4⟩
                rcases has_res u3 _ _ r4 (by rw [h4]) with rfl | rfl <;> simp
              · simp
            · simp
          · simp
        · simp

private theorem while_lts_no_return_so {F : Type} (rv : ValueHOL 64) :
    ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock ≤ k →
      (evaluateHOLFiniteState st (.while ltsCond_so ltsBody_so)).1 ≠ some (.returned rv) := by
  intro k
  induction k with
  | zero =>
    intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) ltsCond_so with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]; rw [if_pos (by omega : st.clock = 0)]; simp
  | succ k ih =>
    intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) ltsCond_so with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]
        by_cases hk0 : st.clock = 0
        · rw [if_pos hk0]; simp
        · rw [if_neg hk0]
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) ltsBody_so
          have hbc := ltsBody_no_bc_so (decClockHOLFinite st)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) ltsBody_so with ⟨r1, m1⟩
          simp only [hbr] at rem hbc ⊢
          cases r1 with
          | none => exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
          | some r1 =>
            cases r1 with
            | «continue» => exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
            | «break» => simp
            | returned v' => exact absurd rfl (hbc.2.2 v')
            | _ => simp

private def LtsLoopInv_so {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (P pw wcnt : BitVec 64) (hp2 : Nat)
    (items : List (BitVec 64 × BitVec 64)) (t : PanSemStateFiniteExact 64 F) : Prop :=
  R16Shards.WorldEff s0 t [] [] R16Shards.wsGw ∧
  globN t "heap_ptr" = hp2 ∧
  ∃ (wi woff : BitVec 64) (_ : items.length = wcnt.toNat),
    t.locals.lookup (ofString "p") = some (.val (.word P)) ∧
    t.locals.lookup (ofString "arr") = some (.val (.word pw)) ∧
    t.locals.lookup (ofString "count") = some (.val (.word wcnt)) ∧
    t.locals.lookup (ofString "i") = some (.val (.word wi)) ∧
    t.locals.lookup (ofString "off") = some (.val (.word woff)) ∧
    wi.toNat ≤ wcnt.toNat ∧
    woff.toNat = ((items.take wi.toNat).map (fun x => x.2.toNat)).sum ∧
    (∀ k (_ : k < wi.toNat) (hk_len : k < items.length),
      memW t (pw.toNat + 16 * k) = (P + (items[k]'hk_len).1).toNat ∧
      memW t (pw.toNat + 16 * k + 8) = (items[k]'hk_len).2.toNat)

private theorem list_take_succ_sum_so (items : List (BitVec 64 × BitVec 64)) (i : Nat) (hi : i < items.length) :
    ((items.take (i + 1)).map (fun x => x.2.toNat)).sum =
      ((items.take i).map (fun x => x.2.toNat)).sum + (items[i]'hi).2.toNat := by
  have ht : items.take (i + 1) = items.take i ++ [items[i]] := by
    exact List.take_succ_eq_append_getElem hi
  rw [ht, List.map_append, List.sum_append]
  simp

private def ltsTailProg_so : ProgHOL 64 :=
  .seq
    (.store (.op .add [.var .local (ofString "arr"),
        .panop .mul [.var .local (ofString "i"), .const 16#64]])
      (.op .add [.var .local (ofString "p"), .var .local (ofString "off")]))
    (.seq
      (.store (.op .add [.var .local (ofString "arr"),
          .panop .mul [.var .local (ofString "i"), .const 16#64], .const 8#64])
        (.var .local (ofString "total")))
      (.seq
        (.assign .local (ofString "off")
          (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const 1#64]))))

private theorem ltsTail_step_so {F : Type}
    {s0 u0 useq : PanSemStateFiniteExact 64 F}
    {P pw wcnt wi woff T : BitVec 64} {hp2 : Nat}
    (heff_u0 : R16Shards.WorldEff s0 u0 [] [] R16Shards.wsGw)
    (hhp_u0 : globN u0 "heap_ptr" = hp2)
    (hpw_lo : globN s0 "heap_ptr" ≤ pw.toNat)
    (hpw_hi : pw.toNat + 16 * wcnt.toNat ≤ hp2)
    (hhp2_hi : hp2 ≤ heapLimit)
    (hlt_i : wi.toNat < wcnt.toNat)
    (hu0_p : u0.locals.lookup (ofString "p") = some (.val (.word P)))
    (hu0_arr : u0.locals.lookup (ofString "arr") = some (.val (.word pw)))
    (hu0_cnt : u0.locals.lookup (ofString "count") = some (.val (.word wcnt)))
    (hu0_i : u0.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hu0_off : u0.locals.lookup (ofString "off") = some (.val (.word woff)))
    (hu0_tot : u0.locals.lookup (ofString "total") = some (.val (.word T)))
    (hflow : evaluateHOLFiniteState u0 ltsTailProg_so = (none, useq)) :
    R16Shards.WorldEff s0 useq [] [] R16Shards.wsGw ∧
    globN useq "heap_ptr" = hp2 ∧
    useq.locals.lookup (ofString "p") = some (.val (.word P)) ∧
    useq.locals.lookup (ofString "arr") = some (.val (.word pw)) ∧
    useq.locals.lookup (ofString "count") = some (.val (.word wcnt)) ∧
    useq.locals.lookup (ofString "i") = some (.val (.word (wi + 1#64))) ∧
    useq.locals.lookup (ofString "off") = some (.val (.word (woff + T))) ∧
    memW useq (pw.toNat + 16 * wi.toNat) = (P + woff).toNat ∧
    memW useq (pw.toNat + 16 * wi.toNat + 8) = T.toNat ∧
    (∀ k < wi.toNat,
      memW useq (pw.toNat + 16 * k) = memW u0 (pw.toNat + 16 * k) ∧
      memW useq (pw.toNat + 16 * k + 8) = memW u0 (pw.toNat + 16 * k + 8)) := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hwi16 : (wi * 16#64).toNat = wi.toNat * 16 :=
    BitVec.toNat_mul_of_lt (by change wi.toNat * 16 < 2 ^ 64; omega)
  have hdst1_nat : (pw + wi * 16#64).toNat = pw.toNat + 16 * wi.toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [hwi16]; omega), hwi16]; omega
  have hdst2_nat : (pw + (wi * 16#64 + 8#64)).toNat = pw.toNat + 16 * wi.toNat + 8 := by
    have hadd8 : (wi * 16#64 + 8#64).toNat = wi.toNat * 16 + 8 := by
      rw [BitVec.toNat_add_of_lt (by rw [hwi16]; change wi.toNat * 16 + 8 < 2 ^ 64; omega), hwi16]; rfl
    rw [BitVec.toNat_add_of_lt (by rw [hadd8]; omega), hadd8]; omega
  unfold ltsTailProg_so at hflow
  rw [evaluateHOLFiniteState_seq_line780] at hflow
  rcases hst1 : evaluateHOLFiniteState u0
      (.store (.op .add [.var .local (ofString "arr"), .panop .mul [.var .local (ofString "i"), .const 16#64]])
        (.op .add [.var .local (ofString "p"), .var .local (ofString "off")])) with ⟨r_s1, u1⟩
  rw [hst1] at hflow
  cases r_s1 with
  | some _ => simp at hflow
  | none =>
    dsimp only at hflow
    have hdst1_ev : @evalHOLExact 64 F _ u0.toExact (fun a => Classical.propDecidable (u0.memaddrs a))
        (.op .add [.var .local (ofString "arr"), .panop .mul [.var .local (ofString "i"), .const 16#64]]) =
        some (.val (.word (pw + wi * 16#64))) := by
      simp [evalHOLExact, evalListHOLExact, hu0_arr, hu0_i, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hval1_ev : @evalHOLExact 64 F _ u0.toExact (fun a => Classical.propDecidable (u0.memaddrs a))
        (.op .add [.var .local (ofString "p"), .var .local (ofString "off")]) =
        some (.val (.word (P + woff))) := by
      simp [evalHOLExact, evalListHOLExact, hu0_p, hu0_off, wordOpHOL, wordOp, valueIsWord, valueWord]
    obtain ⟨hu1_w0, hu1_loc, hu1_glob, hu1_wother⟩ := memW_store_word_exact_so hdst1_ev hval1_ev hst1
    have heff_u1 : R16Shards.WorldEff s0 u1 [] [] R16Shards.wsGw := by
      have hw1 := R16Shards.worldEff_store_word heff_u0
        (.op .add [.var .local (ofString "arr"), .panop .mul [.var .local (ofString "i"), .const 16#64]])
        (.op .add [.var .local (ofString "p"), .var .local (ofString "off")])
        (fun v hv => by rw [hval1_ev] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
        (fun x hx _ => by
          rw [hdst1_ev] at hx; simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hx; subst hx
          exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
      rwa [hst1] at hw1
    have hhp_u1 : globN u1 "heap_ptr" = hp2 := by unfold globN; rw [hu1_glob]; exact hhp_u0
    rw [evaluateHOLFiniteState_seq_line780] at hflow
    rcases hst2 : evaluateHOLFiniteState u1
        (.store (.op .add [.var .local (ofString "arr"),
            .panop .mul [.var .local (ofString "i"), .const 16#64], .const 8#64])
          (.var .local (ofString "total"))) with ⟨r_s2, u2⟩
    rw [hst2] at hflow
    cases r_s2 with
    | some _ => simp at hflow
    | none =>
      dsimp only at hflow
      have hdst2_ev : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
          (.op .add [.var .local (ofString "arr"),
            .panop .mul [.var .local (ofString "i"), .const 16#64], .const 8#64]) =
          some (.val (.word (pw + (wi * 16#64 + 8#64)))) := by
        simp [evalHOLExact, evalListHOLExact, hu1_loc, hu0_arr, hu0_i, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
      have hval2_ev : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
          (.var .local (ofString "total")) = some (.val (.word T)) := by
        simp [evalHOLExact, hu1_loc, hu0_tot]
      obtain ⟨hu2_w8, hu2_loc_step, hu2_glob, hu2_wother⟩ := memW_store_word_exact_so hdst2_ev hval2_ev hst2
      have heff_u2 : R16Shards.WorldEff s0 u2 [] [] R16Shards.wsGw := by
        have hw2 := R16Shards.worldEff_store_word heff_u1
          (.op .add [.var .local (ofString "arr"),
            .panop .mul [.var .local (ofString "i"), .const 16#64], .const 8#64])
          (.var .local (ofString "total"))
          (fun v hv => by rw [hval2_ev] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
          (fun x hx _ => by
            rw [hdst2_ev] at hx; simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hx; subst hx
            exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
        rwa [hst2] at hw2
      have hu2_loc : u2.locals = u0.locals := hu2_loc_step.trans hu1_loc
      have hhp_u2 : globN u2 "heap_ptr" = hp2 := by unfold globN; rw [hu2_glob]; exact hhp_u1
      have ha1 : evaluateHOLFiniteState u2
          (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")])) =
          (none, setKvarHOLFinite .local (ofString "off") (.val (.word (woff + T))) u2) := by
        rw [evaluateHOLFiniteState_assign]
        simp [evalHOLExact, evalListHOLExact, hu2_loc, hu0_off, hu0_tot, wordOpHOL, wordOp, valueIsWord, valueWord,
          isValidValueHOLFinite, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL]
      let u3 := setKvarHOLFinite .local (ofString "off") (.val (.word (woff + T))) u2
      have hu3_i : u3.locals.lookup (ofString "i") = some (.val (.word wi)) := by
        simp [u3, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2_loc, hu0_i,
          show ofString "off" ≠ ofString "i" by decide]
      have ha2 : evaluateHOLFiniteState u3
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])) =
          (none, setKvarHOLFinite .local (ofString "i") (.val (.word (wi + 1#64))) u3) := by
        rw [evaluateHOLFiniteState_assign]
        simp [evalHOLExact, evalListHOLExact, hu3_i, wordOpHOL, wordOp, valueIsWord, valueWord,
          isValidValueHOLFinite, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL]
      let u4 := setKvarHOLFinite .local (ofString "i") (.val (.word (wi + 1#64))) u3
      rw [evaluateHOLFiniteState_seq_line780, ha1] at hflow
      dsimp only at hflow
      rw [ha2] at hflow
      simp only [Prod.mk.injEq] at hflow
      obtain ⟨-, rfl⟩ := hflow
      refine ⟨heff_u2.locals_clock _ _, hhp_u2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [u4, u3, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2_loc, hu0_p,
          show ofString "i" ≠ ofString "p" by decide, show ofString "off" ≠ ofString "p" by decide]
      · simp [u4, u3, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2_loc, hu0_arr,
          show ofString "i" ≠ ofString "arr" by decide, show ofString "off" ≠ ofString "arr" by decide]
      · simp [u4, u3, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2_loc, hu0_cnt,
          show ofString "i" ≠ ofString "count" by decide, show ofString "off" ≠ ofString "count" by decide]
      · simp [u4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      · simp [u4, u3, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "off" by decide]
      · change memW u2 _ = _; rw [hu2_wother _ (by omega) (by omega), ← hdst1_nat, hu1_w0]
      · change memW u2 _ = _; rw [← hdst2_nat, hu2_w8]
      · intro k hk
        refine ⟨?_, ?_⟩
        · change memW u2 _ = _; rw [hu2_wother _ (by omega) (by omega), hu1_wother _ (by omega) (by omega)]
        · change memW u2 _ = _; rw [hu2_wother _ (by omega) (by omega), hu1_wother _ (by omega) (by omega)]

private theorem ltsBody_step_so {F : Type}
    {s0 t mid : PanSemStateFiniteExact 64 F}
    {P L pw wcnt : BitVec 64} {hp2 : Nat} {items : List (BitVec 64 × BitVec 64)}
    (hAR0 : ArenaReady s0)
    (hPL : P.toNat + L.toNat ≤ globN s0 "heap_ptr")
    (hpw_lo : globN s0 "heap_ptr" ≤ pw.toNat)
    (hpw_hi : pw.toNat + 16 * wcnt.toNat ≤ hp2)
    (hhp2_hi : hp2 ≤ heapLimit)
    (hlen_it : items.length = wcnt.toNat)
    (hsum_it : (items.map (fun x => x.2.toNat)).sum = L.toNat)
    (hitems : ∀ k (hk : k < items.length),
      (items[k].1).toNat = ((items.take k).map (fun x => x.2.toNat)).sum ∧
      RlpItemEntry_so s0 P L items[k].1 items[k].2)
    (hinv : LtsLoopInv_so s0 P pw wcnt hp2 items t)
    (hlt_cond : ∃ cw : BitVec 64,
      @evalHOLExact 64 F _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) ltsCond_so =
        some (.val (.word cw)) ∧ cw ≠ 0)
    (hbr : evaluateHOLFiniteState (decClockHOLFinite t) ltsBody_so = (none, mid)) :
    LtsLoopInv_so s0 P pw wcnt hp2 items mid := by
  obtain ⟨heff_t, hhp_t, wi, woff, _, hp_t, harr_t, hcnt_t, hi_t, hoff_t, hwi_le, hwoff_sum, hmemW_prev⟩ := hinv
  obtain ⟨cw, hcond, hnz⟩ := hlt_cond
  have hlt_i : wi.toNat < wcnt.toNat := by
    simp only [ltsCond_so, evalHOLExact, hi_t, hcnt_t, Compiler.Encoders.Asm.wordCmpHOL] at hcond
    by_contra hge
    have hge' : ¬ (wi < wcnt) := by rw [BitVec.lt_def]; omega
    simp [hge'] at hcond
    exact hnz hcond.symm
  have hlt_len : wi.toNat < items.length := by omega
  obtain ⟨hk_off_sum, hentry_i⟩ := hitems wi.toNat hlt_len
  obtain ⟨h1_le_t, hoff_t_le_L, hagree_u⟩ := hentry_i
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hhp0_hi : globN s0 "heap_ptr" ≤ heapLimit := hAR0.2.2.1
  have hwoff_eq_item : woff = (items[wi.toNat]'hlt_len).1 := by
    apply BitVec.eq_of_toNat_eq
    rw [hwoff_sum, hk_off_sum]
  let T := (items[wi.toNat]'hlt_len).2
  let td := decClockHOLFinite t
  have heff_td : R16Shards.WorldEff s0 td [] [] R16Shards.wsGw := heff_t.locals_clock t.locals (t.clock - 1)
  have hbody_eq : ltsBody_so =
      .decCall (ofString "total") .one (ofString "rlp_item_total_unchecked")
        [.op .add [.var .local (ofString "p"), .var .local (ofString "off")]] ltsTailProg_so := rfl
  rw [hbody_eq, evaluateHOLFiniteState_decCall_fixClockRewrite] at hbr
  have hargs_td : evalListHOLFinite td (h := fun a => Classical.propDecidable (td.memaddrs a))
      [.op .add [.var .local (ofString "p"), .var .local (ofString "off")]] =
      some [.val (.word (P + woff))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [td, decClockHOLFinite, evalListHOLExact, evalHOLExact, hp_t, hoff_t,
      wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hargs_td] at hbr; dsimp only at hbr
  rcases hl_call : lookupCodeHOLFinite td.code.lookup (ofString "rlp_item_total_unchecked")
      [.val (.word (P + woff))] with _ | ⟨body', callee, ret'⟩
  · rw [hl_call] at hbr; simp at hbr
  · rw [hl_call] at hbr; dsimp only at hbr
    by_cases hz : td.clock = 0
    · rw [if_pos hz] at hbr; simp at hbr
    · rw [if_neg hz] at hbr
      obtain ⟨p_ro, b_ro, r_ro, hlook_ro, hspec_ro⟩ := InitECandidate.Solver.Wave8GuestInv.R13.ro_rlp_item_total_unchecked
      have hsame_b := lookupCodeHOLFinite_installed_body td.code.lookup _ _ _ body' _ ret' _ callee
        (by rw [heff_td.code]; exact lookup_rlp_item_total_unchecked_so) hl_call
      have hsame_r := lookupCodeHOLFinite_installed_return td _ _ _ _ _ ret' _ callee
        (by rw [heff_td.code]; exact lookup_rlp_item_total_unchecked_so) hl_call
      subst hsame_r
      have hsame_ro := lookupCodeHOLFinite_installed_body td.code.lookup _ p_ro b_ro body' r_ro .one
        [.val (.word (P + woff))] callee (by rw [heff_td.code]; exact hlook_ro) hl_call
      have hret_ro := lookupCodeHOLFinite_installed_return td _ p_ro _ body' r_ro .one
        [.val (.word (P + woff))] callee (by rw [heff_td.code]; exact hlook_ro) hl_call
      subst hret_ro
      have hhl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_item_total_unchecked")
          [.val (.word (P + woff))] = some (body', callee, .one) := by
        rw [← heff_td.code]; exact hl_call
      obtain ⟨_, hcp_u⟩ := callee_one_p_so lookup_rlp_item_total_unchecked_so _ body' callee .one hhl_orig
      let ent := callEntryStateHOLFinite td callee
      rcases hrun_u : evaluateHOLFiniteState ent body' with ⟨rc, cpost⟩
      rw [hrun_u] at hbr
      cases rc with
      | none => simp at hbr
      | some r1 =>
        cases r1 with
        | returned rv =>
          dsimp only at hbr
          split at hbr <;> [skip; simp at hbr]
          have hcpost_ro := hspec_ro ent heff_td.code (guestInv_callEntry td callee heff_td.arena.1)
            ⟨[.val (.word (P + woff))], by rw [← hsame_ro]; exact hhl_orig⟩
            (by rw [← hsame_ro, hrun_u]; simp) (by rw [← hsame_ro, hrun_u]; exact Or.inl ⟨rv, rfl⟩)
          rw [← hsame_ro, hrun_u] at hcpost_ro; dsimp only at hcpost_ro
          have hcpost_frame : cpost = { td with locals := cpost.locals, clock := cpost.clock } := by
            have h1 : ent.globals = td.globals ∧ ent.structs = td.structs ∧ ent.code = td.code ∧
                ent.eshapes = td.eshapes ∧ ent.memory = td.memory ∧ ent.memaddrs = td.memaddrs ∧
                ent.shMemaddrs = td.shMemaddrs ∧ ent.be = td.be ∧ ent.ffi = td.ffi ∧
                ent.baseAddr = td.baseAddr ∧ ent.topAddr = td.topAddr := by
              dsimp only [ent, callEntryStateHOLFinite]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            rw [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1,
              h1.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.1,
              h1.2.2.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.2.2] at hcpost_ro
            exact hcpost_ro
          have hent_bytes : ∀ j < L.toNat,
              memB ent (P.toNat + j) = memB s0 (P.toNat + j) := by
            intro j hj
            exact memB_kept_below_hp_of_stepFrame hAR0 heff_t.be (stepFrame_of_worldEff heff_t) (by omega)
          have hrv_eq : rv = .val (.word T) :=
            hagree_u ent heff_td.code (by rw [← hwoff_eq_item]; exact hcp_u) hent_bytes rv
              (by rw [← hsame_b, hrun_u])
          subst hrv_eq
          let u0 := setVarHOLFinite (ofString "total") (.val (.word T)) { cpost with locals := td.locals }
          have heff_u0 : R16Shards.WorldEff s0 u0 [] [] R16Shards.wsGw :=
            (heff_td.of_readOnly hcpost_frame).locals_clock _ _
          have hhp_u0 : globN u0 "heap_ptr" = hp2 := by
            unfold globN; dsimp only [u0, setVarHOLFinite]; rw [hcpost_frame]; exact hhp_t
          have hu0_memW : ∀ a, memW u0 a = memW t a := by
            intro a; unfold memW; dsimp only [u0, setVarHOLFinite]; rw [hcpost_frame]; rfl
          change (let r := evaluateHOLFiniteState u0 ltsTailProg_so;
            (r.1, { r.2 with locals := HolFiniteMapExact.resVarEq r.2.locals (ofString "total", td.locals.lookup (ofString "total")) })) =
            (none, mid) at hbr
          rcases hrun_tail : evaluateHOLFiniteState u0 ltsTailProg_so with ⟨rtail, useq⟩
          rw [hrun_tail] at hbr
          simp only [Prod.mk.injEq] at hbr
          obtain ⟨rfl, hmid_eq⟩ := hbr
          subst hmid_eq
          obtain ⟨heff_useq, hhp_useq, hp_u, harr_u, hcnt_u, hi_u, hoff_u, hw_cur0, hw_cur8, hw_keep⟩ :=
            @ltsTail_step_so F s0 u0 useq P pw wcnt wi woff T hp2
              heff_u0 hhp_u0 hpw_lo hpw_hi hhp2_hi hlt_i
              (by simp [u0, td, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_t,
                show ofString "total" ≠ ofString "p" by decide])
              (by simp [u0, td, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, harr_t,
                show ofString "total" ≠ ofString "arr" by decide])
              (by simp [u0, td, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hcnt_t,
                show ofString "total" ≠ ofString "count" by decide])
              (by simp [u0, td, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi_t,
                show ofString "total" ≠ ofString "i" by decide])
              (by simp [u0, td, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hoff_t,
                show ofString "total" ≠ ofString "off" by decide])
              (by simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
              hrun_tail
          have hwi1_nat : (wi + 1#64).toNat = wi.toNat + 1 :=
            BitVec.toNat_add_of_lt (by change wi.toNat + 1 < 2 ^ 64; omega)
          have hwoffT_nat : (woff + T).toNat = woff.toNat + T.toNat := by
            have : woff.toNat + T.toNat ≤ L.toNat := by rw [hwoff_eq_item]; exact hoff_t_le_L
            exact BitVec.toNat_add_of_lt (by omega)
          refine ⟨heff_useq.locals_clock _ useq.clock, hhp_useq, wi + 1#64, woff + T, hlen_it,
            ?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_⟩
          · rw [R16Shards.resVarEq_lookup_local, if_neg (by decide)]; exact hp_u
          · rw [R16Shards.resVarEq_lookup_local, if_neg (by decide)]; exact harr_u
          · rw [R16Shards.resVarEq_lookup_local, if_neg (by decide)]; exact hcnt_u
          · rw [R16Shards.resVarEq_lookup_local, if_neg (by decide)]; exact hi_u
          · rw [R16Shards.resVarEq_lookup_local, if_neg (by decide)]; exact hoff_u
          · rw [hwi1_nat, list_take_succ_sum_so items wi.toNat hlt_len, ← hwoff_sum, hwoffT_nat]
          · intro k hk hk_len
            rw [hwi1_nat] at hk
            change memW useq _ = _ ∧ memW useq _ = _
            by_cases hk_lt : k < wi.toNat
            · obtain ⟨hk0, hk8⟩ := hw_keep k hk_lt
              obtain ⟨hp0, hp8⟩ := hmemW_prev k hk_lt hk_len
              exact ⟨by rw [hk0, hu0_memW]; exact hp0, by rw [hk8, hu0_memW]; exact hp8⟩
            · have hk_eq : k = wi.toNat := by omega
              subst hk_eq
              exact ⟨by rw [hw_cur0, hwoff_eq_item], hw_cur8⟩
        | _ => simp at hbr

private theorem while_ltsLoopInv_so {F : Type}
    {s0 : PanSemStateFiniteExact 64 F}
    {P L pw wcnt : BitVec 64} {hp2 : Nat} {items : List (BitVec 64 × BitVec 64)}
    (hAR0 : ArenaReady s0)
    (hPL : P.toNat + L.toNat ≤ globN s0 "heap_ptr")
    (hpw_lo : globN s0 "heap_ptr" ≤ pw.toNat)
    (hpw_hi : pw.toNat + 16 * wcnt.toNat ≤ hp2)
    (hhp2_hi : hp2 ≤ heapLimit)
    (hlen_it : items.length = wcnt.toNat)
    (hsum_it : (items.map (fun x => x.2.toNat)).sum = L.toNat)
    (hitems : ∀ k (hk : k < items.length),
      (items[k].1).toNat = ((items.take k).map (fun x => x.2.toNat)).sum ∧
      RlpItemEntry_so s0 P L items[k].1 items[k].2) :
    ∀ (k : Nat) (t post : PanSemStateFiniteExact 64 F),
      t.clock ≤ k →
      LtsLoopInv_so s0 P pw wcnt hp2 items t →
      evaluateHOLFiniteState t (.while ltsCond_so ltsBody_so) = (none, post) →
      LtsLoopInv_so s0 P pw wcnt hp2 items post ∧
        ∃ cw : BitVec 64,
          @evalHOLExact 64 F _ post.toExact (fun x => Classical.propDecidable (post.memaddrs x)) ltsCond_so =
            some (.val (.word cw)) ∧ cw = 0 := by
  intro k
  induction k with
  | zero =>
    intro t post hclk hinv hrun
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun <;> [simp at hrun; omega]
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun
        exact ⟨hinv, 0, hcond, rfl⟩
    · simp at hrun
  | succ k ih =>
    intro t post hclk hinv hrun
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite t) ltsBody_so
          have hbc := ltsBody_no_bc_so (decClockHOLFinite t)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite t) ltsBody_so with ⟨r1, mid⟩
          rw [hbr] at hrun rem hbc
          cases r1 with
          | none =>
            have hinv_mid := ltsBody_step_so hAR0 hPL hpw_lo hpw_hi hhp2_hi hlen_it hsum_it hitems
              hinv ⟨cw, hcond, hnz⟩ hbr
            exact ih mid post (by change mid.clock ≤ t.clock - 1 at rem; omega) hinv_mid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl hbc.2.1
            | «break» => exact absurd rfl hbc.1
            | _ => simp at hrun
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun
        exact ⟨hinv, 0, hcond, rfl⟩
    · simp at hrun

theorem rlp_list_to_slices_ret_spec_so {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (P L : BitVec 64) (rv : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hin : Inside (P.toNat, L.toNat) sourceBase (globN s "heap_ptr"))
    (hL40 : L.toNat < 2 ^ 40)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : s.locals.lookup (ofString "len") = some (.val (.word L)))
    (hret : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices) =
      (some (.returned rv), post)) :
    ∃ (pw wcnt : BitVec 64),
      rv = .rStruct [.val (.word pw), .val (.word wcnt)] ∧
      R16Shards.WorldEff s post [] [] R16Shards.wsGw ∧
      WordsOK post (pw.toNat, 16 * wcnt.toNat) ∧
      Inside (pw.toNat, 16 * wcnt.toNat) (globN s "heap_ptr") (globN post "heap_ptr") ∧
      wcnt.toNat ≤ L.toNat ∧
      (∀ k < wcnt.toNat,
        Inside (memW post (pw.toNat + 16 * k), memW post (pw.toNat + 16 * k + 8)) sourceBase (globN s "heap_ptr") ∧
        1 ≤ memW post (pw.toNat + 16 * k + 8) ∧
        memW post (pw.toNat + 16 * k + 8) ≤ L.toNat) := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hhp0_hi : globN s "heap_ptr" ≤ heapLimit := hAR.2.2.1
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_list_to_slices =
      .decCall (ofString "count") .one (ofString "rlp_list_count")
        [.var .local (ofString "p"), .var .local (ofString "len")]
        (.decCall (ofString "arr") .one (ofString "alloc")
          [.panop .mul [.var .local (ofString "count"), .const 16#64]]
          (.dec (ofString "i") .one (.const 0#64)
            (.dec (ofString "off") .one (.const 0#64)
              (.seq (.while ltsCond_so ltsBody_so)
                (.return (.rstruct [.var .local (ofString "arr"), .var .local (ofString "count")])))))) := rfl
  rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  have hargs_c : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "p"), .var .local (ofString "len")] =
      some [.val (.word P), .val (.word L)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hp, hl]
  rw [hargs_c] at hret; dsimp only at hret
  rcases hlc : lookupCodeHOLFinite s.code.lookup (ofString "rlp_list_count")
      [.val (.word P), .val (.word L)] with _ | ⟨bc, calleec, retc⟩
  · rw [hlc] at hret; simp at hret
  · rw [hlc] at hret; dsimp only at hret
    by_cases hzc : s.clock = 0
    · rw [if_pos hzc] at hret; simp at hret
    · rw [if_neg hzc] at hret
      have hsame_bc := lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ bc _ retc _ calleec
        (by rw [hc]; exact lookup_rlp_list_count_so) hlc
      have hsame_rc := lookupCodeHOLFinite_installed_return s _ _ _ _ _ retc _ calleec
        (by rw [hc]; exact lookup_rlp_list_count_so) hlc
      subst hsame_rc
      obtain ⟨_, hcp_c, hcl_c⟩ := callee_p_len_so lookup_rlp_list_count_so _ _ bc calleec .one (by rwa [← hc])
      let entc := callEntryStateHOLFinite s calleec
      let k1Prog : ProgHOL 64 :=
        .decCall (ofString "arr") .one (ofString "alloc")
          [.panop .mul [.var .local (ofString "count"), .const 16#64]]
          (.dec (ofString "i") .one (.const 0#64)
            (.dec (ofString "off") .one (.const 0#64)
              (.seq (.while ltsCond_so ltsBody_so)
                (.return (.rstruct [.var .local (ofString "arr"), .var .local (ofString "count")])))))
      rcases hrunc : evaluateHOLFiniteState entc bc with ⟨rcc, cpost⟩
      rw [hrunc] at hret
      cases rcc with
      | none => simp at hret
      | some r1 =>
        cases r1 with
        | returned rvc =>
          dsimp only at hret
          split at hret <;> [skip; simp at hret]
          have hAR_entc : ArenaReady entc :=
            ⟨guestInv_callEntry s calleec hAR.1, hAR.2⟩
          obtain ⟨wcnt, items, rfl, heff_entc_cp, hhp_cp, hlen_it, hcnt_le_L, hsum_it, hitems⟩ :=
            rlp_list_count_ret_spec_so entc cpost P L rvc hc hAR_entc hin.2 hcp_c hcl_c
              (by rw [← hsame_bc]; exact hrunc)
          let m1 := setVarHOLFinite (ofString "count") (.val (.word wcnt)) { cpost with locals := s.locals }
          have heff_m1 : R16Shards.WorldEff s m1 [] [] R16Shards.wsGw := by
            have heff0 : R16Shards.WorldEff s entc [] [] R16Shards.wsGw :=
              (R16Shards.WorldEff.refl s [] [] R16Shards.wsGw hAR hc).locals_clock _ _
            exact (heff0.trans_noBuf heff_entc_cp (by decide) (by decide)).locals_clock _ _
          have hm1_cnt : m1.locals.lookup (ofString "count") = some (.val (.word wcnt)) := by
            simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hm1_p : m1.locals.lookup (ofString "p") = some (.val (.word P)) := by
            simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
              show ofString "count" ≠ ofString "p" by decide]
          have hhp_m1 : globN m1 "heap_ptr" = globN s "heap_ptr" := by
            change globN cpost "heap_ptr" = _; exact hhp_cp
          rcases hrun_k1 : evaluateHOLFiniteState m1 k1Prog with ⟨rk1, pk1⟩
          have hret' : (rk1, { pk1 with locals := HolFiniteMapExact.resVarEq pk1.locals (ofString "count", s.locals.lookup (ofString "count")) }) =
              (some (.returned rv), post) := by
            dsimp only [m1, k1Prog] at hrun_k1
            rw [hrun_k1] at hret; exact hret
          simp only [Prod.mk.injEq] at hret'
          obtain ⟨hrk1_eq, hpost_eq1⟩ := hret'
          subst hrk1_eq
          unfold k1Prog at hrun_k1
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun_k1
          have hargs_a : evalListHOLFinite m1 (h := fun a => Classical.propDecidable (m1.memaddrs a))
              [.panop .mul [.var .local (ofString "count"), .const 16#64]] =
              some [.val (.word (wcnt * 16#64))] := by
            rw [evalListHOLFinite_eq_toExact]
            simp [evalListHOLExact, evalHOLExact, hm1_cnt, panOpHOL, valueIsWord, valueWord]
          have hla := pan_one_word_lookup m1.code.lookup (ofString "alloc") (ofString "n")
            (sourceFnBody Guest.Software.guestFn_alloc) (wcnt * 16#64) (by rw [heff_m1.code]; exact lookup_alloc_r16)
          rw [hargs_a] at hrun_k1; dsimp only at hrun_k1; rw [hla] at hrun_k1; dsimp only at hrun_k1
          by_cases hza : m1.clock = 0
          · rw [if_pos hza] at hrun_k1; simp at hrun_k1
          · rw [if_neg hza] at hrun_k1
            obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, m1.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
              globalWord_of_globN_pos m1 "heap_ptr"
                (by have := heff_m1.arena.2.1; have : sourceBase = 2701131776 := rfl; omega)
            let cala := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word (wcnt * 16#64)))
            let enta := callEntryStateHOLFinite m1 cala
            rcases hruna : evaluateHOLFiniteState enta (sourceFnBody Guest.Software.guestFn_alloc) with ⟨rca, pa⟩
            dsimp only [enta, cala] at hruna
            rw [hruna] at hrun_k1
            cases rca with
            | none => simp at hrun_k1
            | some r2 =>
              cases r2 with
              | returned rva =>
                dsimp only at hrun_k1
                split at hrun_k1 <;> [skip; simp at hrun_k1]
                have hal := InitECandidate.Solver.Wave8GuestInv.R13.alloc_body_resumes enta pw heff_m1.code hpw_lk
                  (by dsimp only [enta, cala]; rw [hruna]; exact Or.inl ⟨rva, rfl⟩)
                dsimp only [enta, cala] at hal; rw [hruna] at hal
                obtain ⟨nw', hnw'_lk, hrva_eq, hcmp1, hcmp2, hpa_eq⟩ := hal
                have hnw_eq : wcnt * 16#64 = nw' := by
                  have : enta.locals.lookup (ofString "n") = some (.val (.word (wcnt * 16#64))) := by
                    simp [enta, cala, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  rw [this] at hnw'_lk; simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hnw'_lk
                  exact hnw'_lk
                subst hnw_eq
                dsimp only at hrva_eq hpa_eq
                simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hrva_eq
                subst hrva_eq
                let m2 := setVarHOLFinite (ofString "arr") (.val (.word pw)) { pa with locals := m1.locals }
                have hm2_next : m2 = { m1 with
                    globals := m1.globals.update (ofString "heap_ptr",
                      .val (.word ((pw + (wcnt * 16#64 + 7)) &&& ((0 : BitVec 64) - 8)))),
                    locals := m2.locals, clock := m2.clock } := by
                  dsimp only [m2, setVarHOLFinite]; rw [hpa_eq]; rfl
                obtain ⟨heff_m2, _, hpw_al, _, _, hpw_add, hhp_m2_hi, hwok_m2⟩ :=
                  R16Shards.worldEff_alloc_step heff_m1 (by decide) hpw_lk hcmp1 hcmp2 hm2_next
                have hpw_eq_hp0 : pw.toNat = globN s "heap_ptr" := by
                  have : globN m1 "heap_ptr" = pw.toNat := by simp [globN, hpw_lk]
                  omega
                have hwcnt16 : (wcnt * 16#64).toNat = 16 * wcnt.toNat := by
                  have h16 : (16#64 : BitVec 64).toNat = 16 := rfl
                  rw [BitVec.toNat_mul_of_lt (by rw [h16]; change wcnt.toNat * 16 < 18446744073709551616; omega), h16]; omega
                have halign16 : ((wcnt * 16#64).toNat + 7) / 8 * 8 = 16 * wcnt.toNat := by omega
                let hp2 := globN m2 "heap_ptr"
                have hhp2_eq : hp2 = pw.toNat + 16 * wcnt.toNat := by change globN m2 "heap_ptr" = _; omega
                let k4Prog : ProgHOL 64 :=
                  .seq (.while ltsCond_so ltsBody_so)
                    (.return (.rstruct [.var .local (ofString "arr"), .var .local (ofString "count")]))
                let k3Prog : ProgHOL 64 := .dec (ofString "off") .one (.const 0#64) k4Prog
                let k2Prog : ProgHOL 64 := .dec (ofString "i") .one (.const 0#64) k3Prog
                rcases hrun_k2 : evaluateHOLFiniteState m2 k2Prog with ⟨rk2, pk2⟩
                have hk2' : (rk2, { pk2 with locals := HolFiniteMapExact.resVarEq pk2.locals (ofString "arr", m1.locals.lookup (ofString "arr")) }) =
                    (some (.returned rv), pk1) := by
                  dsimp only [m2, k2Prog, k3Prog, k4Prog] at hrun_k2
                  rw [hrun_k2] at hrun_k1; exact hrun_k1
                simp only [Prod.mk.injEq] at hk2'
                obtain ⟨hrk2_eq, hpk1_eq⟩ := hk2'
                subst hrk2_eq
                unfold k2Prog at hrun_k2
                rw [evaluateHOLFiniteState_dec_total] at hrun_k2
                dsimp only at hrun_k2
                have hev0_2 : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a))
                    (.const 0#64) = some (.val (.word 0#64)) := rfl
                have hsh0 : shapeEqHOL .one (shapeOfHOLExact (ValueHOL.val (.word 0#64))) = true := by
                  simp [shapeOfHOLExact, shapeEqHOL]
                rw [hev0_2] at hrun_k2; dsimp only at hrun_k2; rw [if_pos hsh0] at hrun_k2
                let m3 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m2
                rcases hrun_k3 : evaluateHOLFiniteState m3 k3Prog with ⟨rk3, pk3⟩
                have hk3' : (rk3, { pk3 with locals := HolFiniteMapExact.resVarEq pk3.locals (ofString "i", m2.locals.lookup (ofString "i")) }) =
                    (some (.returned rv), pk2) := by
                  dsimp only [m3, k3Prog, k4Prog] at hrun_k3
                  rw [hrun_k3] at hrun_k2; exact hrun_k2
                simp only [Prod.mk.injEq] at hk3'
                obtain ⟨hrk3_eq, hpk2_eq⟩ := hk3'
                subst hrk3_eq
                unfold k3Prog at hrun_k3
                rw [evaluateHOLFiniteState_dec_total] at hrun_k3
                dsimp only at hrun_k3
                have hev0_3 : @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
                    (.const 0#64) = some (.val (.word 0#64)) := rfl
                rw [hev0_3] at hrun_k3; dsimp only at hrun_k3; rw [if_pos hsh0] at hrun_k3
                let m4 := setVarHOLFinite (ofString "off") (.val (.word 0#64)) m3
                rcases hrun_k4 : evaluateHOLFiniteState m4 k4Prog with ⟨rk4, pk4⟩
                have hk4' : (rk4, { pk4 with locals := HolFiniteMapExact.resVarEq pk4.locals (ofString "off", m3.locals.lookup (ofString "off")) }) =
                    (some (.returned rv), pk3) := by
                  dsimp only [m4, k4Prog] at hrun_k4
                  rw [hrun_k4] at hrun_k3; exact hrun_k3
                simp only [Prod.mk.injEq] at hk4'
                obtain ⟨hrk4_eq, hpk3_eq⟩ := hk4'
                subst hrk4_eq
                unfold k4Prog at hrun_k4
                rw [evaluateHOLFiniteState_seq_line780] at hrun_k4
                rcases hw_lts : evaluateHOLFiniteState m4 (.while ltsCond_so ltsBody_so) with ⟨rw_l, wpost⟩
                rw [hw_lts] at hrun_k4
                cases rw_l with
                | some rw1 =>
                  cases rw1 with
                  | returned rv' =>
                    have hwnr := while_lts_no_return_so rv' m4.clock m4 le_rfl
                    rw [hw_lts] at hwnr
                    exact absurd rfl hwnr
                  | _ => simp at hrun_k4
                | none =>
                  dsimp only at hrun_k4
                  have hinv_m4 : LtsLoopInv_so s P pw wcnt hp2 items m4 := by
                    refine ⟨heff_m2.locals_clock _ _, rfl, 0#64, 0#64, hlen_it,
                      ?_, ?_, ?_, ?_, ?_, Nat.zero_le _, rfl, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
                    · simp [m4, m3, m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_p,
                        show ofString "off" ≠ ofString "p" by decide,
                        show ofString "i" ≠ ofString "p" by decide,
                        show ofString "arr" ≠ ofString "p" by decide]
                    · simp [m4, m3, m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                        show ofString "off" ≠ ofString "arr" by decide,
                        show ofString "i" ≠ ofString "arr" by decide]
                    · simp [m4, m3, m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm1_cnt,
                        show ofString "off" ≠ ofString "count" by decide,
                        show ofString "i" ≠ ofString "count" by decide,
                        show ofString "arr" ≠ ofString "count" by decide]
                    · simp [m4, m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                        show ofString "off" ≠ ofString "i" by decide]
                    · simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  have hitems_s : ∀ k (hk : k < items.length),
                      (items[k].1).toNat = ((items.take k).map (fun x => x.2.toNat)).sum ∧
                      RlpItemEntry_so s P L items[k].1 items[k].2 := hitems
                  obtain ⟨hinv_wp, cw_end, hcond_end, hcw0⟩ :=
                    while_ltsLoopInv_so hAR hin.2 (by omega) (by omega) hhp_m2_hi hlen_it hsum_it hitems_s
                      m4.clock m4 wpost le_rfl hinv_m4 hw_lts
                  obtain ⟨heff_wp, hhp_wp, wi_end, woff_end, _, hp_wp, harr_wp, hcnt_wp, hi_wp, hoff_wp,
                    hwi_le_end, _, hmemW_wp⟩ := hinv_wp
                  have hwi_eq_cnt : wi_end.toNat = wcnt.toNat := by
                    subst hcw0
                    simp only [ltsCond_so, evalHOLExact, hi_wp, hcnt_wp, Compiler.Encoders.Asm.wordCmpHOL] at hcond_end
                    by_contra hne
                    have hlt : wi_end < wcnt := by rw [BitVec.lt_def]; omega
                    simp [hlt] at hcond_end
                  rw [evaluateHOLFiniteState_return] at hrun_k4
                  have hret_ev : @evalHOLExact 64 F _ wpost.toExact (fun a => Classical.propDecidable (wpost.memaddrs a))
                      (.rstruct [.var .local (ofString "arr"), .var .local (ofString "count")]) =
                      some (.rStruct [.val (.word pw), .val (.word wcnt)]) := by
                    simp [evalHOLExact, evalListHOLExact, harr_wp, hcnt_wp]
                  rw [hret_ev] at hrun_k4
                  dsimp only at hrun_k4
                  split at hrun_k4 <;> [skip; simp at hrun_k4]
                  simp only [Prod.mk.injEq, Option.some.injEq, PanSemResultExact.returned.injEq] at hrun_k4
                  obtain ⟨hrv_eq, hpk4_eq⟩ := hrun_k4
                  subst hrv_eq
                  have hpost_frame : post = { wpost with locals := post.locals, clock := post.clock } := by
                    rw [← hpost_eq1, ← hpk1_eq, ← hpk2_eq, ← hpk3_eq, ← hpk4_eq]; rfl
                  have heff_post : R16Shards.WorldEff s post [] [] R16Shards.wsGw :=
                    heff_wp.of_readOnly hpost_frame
                  have hhp_post : globN post "heap_ptr" = hp2 := by
                    unfold globN; rw [hpost_frame]; exact hhp_wp
                  have hmemW_post : ∀ a, memW post a = memW wpost a := by
                    intro a; unfold memW; rw [hpost_frame]
                  have hhp2_le_hl : hp2 ≤ heapLimit := hhp_m2_hi
                  have hpw16_le_he : pw.toNat + 16 * wcnt.toNat ≤ heapEnd := by
                    have hhl_le_he : heapLimit ≤ heapEnd := by decide
                    omega
                  have hwok_post : WordsOK post (pw.toNat, 16 * wcnt.toNat) :=
                    Wave8Contracts.M26.wordsOK_of_guestInv post heff_post.arena.1 pw.toNat (16 * wcnt.toNat)
                      hpw_al (by omega) (by have := hAR.2.1; omega) hpw16_le_he
                  refine ⟨pw, wcnt, rfl, heff_post, hwok_post,
                    ⟨hpw_eq_hp0.symm.le, by rw [hhp_post, hhp2_eq]⟩, hcnt_le_L, ?_⟩
                  intro k hk
                  have hk_wi : k < wi_end.toNat := by omega
                  have hk_len : k < items.length := by omega
                  obtain ⟨hw0, hw8⟩ := hmemW_wp k hk_wi hk_len
                  obtain ⟨hoff_eq_sum, h1_le_tk, hoff_tk_le_L, _⟩ := hitems_s k hk_len
                  obtain ⟨hP_lo, hPL_hi⟩ := hin
                  have hhp_lt64 : globN s "heap_ptr" < 18446744073709551616 := by
                    have : heapLimit < 18446744073709551616 := by decide
                    omega
                  have hadd_pk : (P + (items[k]'hk_len).1).toNat = P.toNat + (items[k]'hk_len).1.toNat :=
                    BitVec.toNat_add_of_lt (by change P.toNat + (items[k]'hk_len).1.toNat < 18446744073709551616; omega)
                  rw [hmemW_post, hmemW_post, hw0, hw8, hadd_pk]
                  exact ⟨⟨by omega, by omega⟩, h1_le_tk, by omega⟩
              | _ => simp at hrun_k1
        | _ => simp at hret

/-- Each returned pair is itself a well-formed witness slice.  This packages the
array-level RLP bounds in the form consumed by the node insertion loop. -/
theorem rlp_list_to_slices_witness_slices_so {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (P L : BitVec 64) (rv : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hin : Inside (P.toNat, L.toNat) sourceBase (globN s "heap_ptr"))
    (hL40 : L.toNat < 2 ^ 40)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : s.locals.lookup (ofString "len") = some (.val (.word L)))
    (hret : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices) =
      (some (.returned rv), post)) :
    ∃ (pw wcnt : BitVec 64),
      rv = .rStruct [.val (.word pw), .val (.word wcnt)] ∧
      R16Shards.WorldEff s post [] [] R16Shards.wsGw ∧
      Inside (pw.toNat, 16 * wcnt.toNat) (globN s "heap_ptr") (globN post "heap_ptr") ∧
      wcnt.toNat ≤ L.toNat ∧
      ∀ k < wcnt.toNat, WitnessSliceOK post (pw.toNat + 16 * k) := by
  obtain ⟨pw, wcnt, hrv, heff, hw, hfresh, hcnt, hitems⟩ :=
    rlp_list_to_slices_ret_spec_so s post P L rv hc hAR hin hL40 hp hl hret
  refine ⟨pw, wcnt, hrv, heff, hfresh, hcnt, fun k hk => ?_⟩
  obtain ⟨hi, _, hlen⟩ := hitems k hk
  have hwords : WordsOK post (pw.toNat + 16 * k, 16) := by
    refine ⟨by have := hw.1; omega, by norm_num, fun j hj => ?_⟩
    have hj' : 2 * k + j < 16 * wcnt.toNat / 8 := by omega
    have hjw := hw.2.2 (2 * k + j) hj'
    have heq : pw.toNat + 16 * k + 8 * j = pw.toNat + 8 * (2 * k + j) := by omega
    change WordAt post (pw.toNat + 16 * k + 8 * j)
    rw [heq]
    exact hjw
  refine ⟨hwords, ⟨?_, ?_⟩, lt_of_le_of_lt hlen hL40, hi.1,
    le_trans hi.2 heff.hp_lo⟩
  · have := hAR.2.1; have := hfresh.1; omega
  · have := hfresh.2; omega

/-- The concrete RLP slice allocator preserves the caller's EVM and witness
database while supplying typed, bounded input records for node decoding. -/
theorem rlp_list_to_slices_evm_and_witness_so {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (P L : BitVec 64) (rv : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hInv : EvmInv s) (hdb : WitnessDbOK s)
    (hin : Inside (P.toNat, L.toNat) sourceBase (globN s "heap_ptr"))
    (hL40 : L.toNat < 2 ^ 40)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : s.locals.lookup (ofString "len") = some (.val (.word L)))
    (hret : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices) =
      (some (.returned rv), post)) :
    EvmStep ["heap_ptr", "scratch_ptr"] s post ∧ WitnessDbOK post ∧
    ∃ (pw wcnt : BitVec 64),
      rv = .rStruct [.val (.word pw), .val (.word wcnt)] ∧
      Inside (pw.toNat, 16 * wcnt.toNat) (globN s "heap_ptr") (globN post "heap_ptr") ∧
      wcnt.toNat ≤ L.toNat ∧
      ∀ k < wcnt.toNat, WitnessSliceOK post (pw.toNat + 16 * k) := by
  obtain ⟨pw, wcnt, hrv, heff, hfresh, hcnt, hslices⟩ :=
    rlp_list_to_slices_witness_slices_so s post P L rv hc hInv.1 hin hL40 hp hl hret
  have hsteps : ∀ Nd, NodeHeap s Nd → ∃ Nd', DecoderNodeStep s post Nd Nd' ∧
      RetRootIn s (some (.returned rv)) post [] Nd' := by
    intro Nd hNd
    refine ⟨Nd, decoderNodeStep_of_worldEff hInv.1 hNd heff, ?_⟩
    intro w hw
    rw [hrv] at hw
    cases hw
  obtain ⟨hE, hdb', _⟩ := decoderNodeStep_evm_and_witness hInv hdb hsteps
  exact ⟨hE, hdb', pw, wcnt, hrv, hfresh, hcnt, hslices⟩

/-- A decoder step cannot overwrite an already allocated slice record which
is separate from the input node records.  Payload bytes need no extra frame:
the slice invariant only requires their heap containment. -/
theorem witnessSliceOK_of_decoderNodeStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd Nd' : List Nat} {v : Nat}
    (hAR : ArenaReady s) (hNd : NodeHeap s Nd)
    (hstep : DecoderNodeStep s post Nd Nd')
    (hv : WitnessSliceOK s v)
    (hdisj : ∀ n ∈ Nd, Disj (v, 16) (nodeIvl s n)) :
    WitnessSliceOK post v := by
  have hal : Allocated s (v, 16) := Or.inl hv.2.1
  obtain ⟨hgap, hheap⟩ := allocated_disj_free_regions hAR.2 hal
  have hu : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (v, 16) := by
    apply aligned_cell_unhit_of_frameOutside hstep.step.frame
    · intro j hj
      rcases List.mem_append.1 hj with hj | hj
      · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hj
        exact Or.inr (Or.inl ((hNd.1 n hn).2.2.2.1.1))
      · rw [List.mem_singleton.1 hj]
        exact Or.inr (Or.inl hAR.2.2.2.2.2.2.2.1)
    · exact Or.inr (Or.inl hAR.2.2.2.2.2.2.1)
    · intro j hj
      rcases List.mem_append.1 hj with hj | hj
      · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hj
        exact hdisj n hn
      · rw [List.mem_singleton.1 hj]
        exact hgap
    · exact hheap
  have hhi : v + 16 ≤ 2 ^ 64 := by
    have := hv.2.1.2
    have := hAR.2.2.1
    have : heapLimit ≤ 2 ^ 64 := by decide
    omega
  refine witnessSliceOK_of_preserved hv
    (InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAR.1 hstep.step.arena.1 hv.1)
    hstep.step.hp_le ?_ ?_
  · exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu hv.1.1 hhi
      ⟨by omega, by omega⟩
  · exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu (by have := hv.1.1; omega) hhi
      ⟨by omega, by omega⟩

/-- Fully decoding the payload of a witness slice keeps the returned RLP
payload inside the original heap and below the decoder's length bound. -/
theorem rlp_decode_fully_witness_payload_so {F : Type}
    (s : PanSemStateFiniteExact 64 F) (v : Nat) (P L : BitVec 64) (rv : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hv : WitnessSliceOK s v)
    (hP : P.toNat = memW s v) (hL : L.toNat = memW s (v + 8))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : s.locals.lookup (ofString "len") = some (.val (.word L)))
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_decode_fully)).1 =
      some (.returned rv)) :
    ∃ tag p' n' tot : BitVec 64,
      rv = .rStruct [.val (.word tag), .val (.word p'), .val (.word n'), .val (.word tot)] ∧
      (tag = 0#64 ∨ tag = 1#64) ∧
      Inside (p'.toNat, n'.toNat) sourceBase (globN s "heap_ptr") ∧ n'.toNat < 2 ^ 40 := by
  have hPL : P.toNat + L.toNat < 2 ^ 64 := by
    have := hv.2.2.2.2
    have := hAR.2.2.1
    have : heapLimit < 2 ^ 64 := by decide
    omega
  obtain ⟨tag, p', n', tot, hrv, htag, htotpos, htot, hp', hn'⟩ :=
    rlp_decode_fully_ret_spec s hc P L hPL hp hl rv hret
  refine ⟨tag, p', n', tot, hrv, htag, ⟨?_, ?_⟩, ?_⟩
  · have := hv.2.2.2.1; omega
  · have := hv.2.2.2.2; omega
  · have := hv.2.2.1; omega

/-- Slice records remain separated from all decoded nodes and their nibble
paths, so the insertion-loop invariant can be used again at its next iteration. -/
theorem witnessSliceOK_separated_of_decoderNodeStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd Nd' : List Nat} {v : Nat}
    (hAR : ArenaReady s) (hNd : NodeHeap s Nd)
    (hstep : DecoderNodeStep s post Nd Nd')
    (hv : WitnessSliceOK s v)
    (hdisj : ∀ j ∈ nodeExtents s Nd, Disj (v, 16) j) :
    WitnessSliceOK post v ∧ ∀ j ∈ nodeExtents post Nd', Disj (v, 16) j := by
  have hgrow : OwnedGrows s post (nodeExtents s Nd) (nodeExtents post Nd') := by
    apply ownedGrows_nodeExtents_of_fresh
    · intro n hn
      refine ⟨hstep.step.sub n hn, ?_, hstep.old_path n hn⟩
      simp only [nodeIvl, hstep.step.kinds n hn]
    · intro x hx hnx
      exact ⟨(hstep.step.fresh x hx).resolve_left hnx, hstep.fresh_path x hx hnx⟩
  refine ⟨witnessSliceOK_of_decoderNodeStep hAR hNd hstep hv ?_,
    allocated_disj_ownedGrows hAR.2 hstep.step.arena.2 hstep.step.hp_le
      (Or.inl hv.2.1) hdisj hgrow⟩
  intro n hn
  apply hdisj
  exact List.mem_flatMap.2 ⟨n, hn, List.mem_cons_self ..⟩

/-- A successful witness-table lookup supplies a slice satisfying the decoder's
memory and size preconditions, rather than merely an untyped table value. -/
theorem witness_htab_get_ret_slice_so {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw kw : BitVec 64) (rv : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hdb : WitnessDbSlices s)
    (hws : globN s "ws" ≠ 0) (htw : tw.toNat = memW s (globN s "ws"))
    (htnz : tw.toNat ≠ 0)
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hk : s.locals.lookup (ofString "key") = some (.val (.word kw)))
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_get)).1 =
      some (.returned rv)) :
    ∃ found ptr : BitVec 64,
      rv = .rStruct [.val (.word found), .val (.word ptr)] ∧
      (found ≠ 0 → WitnessSliceOK s ptr.toNat) := by
  obtain ⟨hwf, _, _, hvals⟩ := hdb hws (htw ▸ htnz)
  obtain ⟨found, ptr, hrv, hptr⟩ := WkBal.htab_get_ret_in_values s tw kw hc ht hk
    (htw ▸ hwf) rv hret
  refine ⟨found, ptr, hrv, fun hf => ?_⟩
  apply hvals
  rw [← htw]
  exact hptr hf

end StorageOriginal

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack.Basis.Pure.MlString

/-- Primitive-shaped export (statement identical to `Primitives.lean`'s `ek_create_finish`),
namespaced to avoid clashing with the `ContractParts.C08` placeholder. -/
theorem «ek_create_finish» :
    EvmKeeps (EvmAvoids (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)]))
    ["heap_ptr", "journal_n", "scratch_ptr"] (ofString "create_finish") :=
  StorageCreateFinish.ek_create_finish_proof

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
