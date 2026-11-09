import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4c2d0EvmBridgeCore
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4c2c2AcctMutCallees
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4c1GasWarmRo

/-!
# Scratch Rung B4c2d: `WorldStepCodeSc` → `EvmMsgReadyMsgBounded` + `EvmStepCC` Bridge & Callee Wrappers

Bridges any `WorldStepCodeSc B gw s r post` (`PosBufList B`, `SafeStepGlobals gw`) directly to
`EvmMsgReadyMsgBounded post ∧ EvmStepCC gw_out s post ∧ memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112)`,
and lifts `WorldKeepsCodeSc` and bounded-return (`get_code`, `ext_code_of`) callees to `FunSpec`
and `Hoare` wrappers on `D0PreB` and `EvmMsgReadyMsgBounded`.
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8M19.Htab
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
  (IvlUnhit not_cellHits_of_disj memW_eq_of_ivlUnhit worldOwned_zero_or_allocated
   worldOwned_zero_aligned worldTypedWith_erase_local adjoin_local_table
   htabValues_eq_of_unhit ivl_allocated_bound zero_not_mem_S worldTypedIvls_sub_worldOwned
   fixedObjects_zero_len_eq)
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-! ## 1. Non-trie payload transfer -/

/-- Non-trie owned intervals are zero-or-8-aligned: table footprints are `WordsOK` and fixed objects
are 8-aligned when nonzero. -/
theorem nonTrieOwned_zero_aligned_b4d {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hT : TablesTyped s S) (_hF : FixedTyped s) :
    ∀ j ∈ nonTrieOwned s S, j.2 = 0 → j.1 % 8 = 0 := by
  intro j hj hz
  unfold nonTrieOwned at hj
  rcases List.mem_append.1 hj with htab | hfix
  · obtain ⟨t, ht, hit⟩ := List.mem_flatMap.1 htab
    exact absurd hz (Nat.ne_of_gt (htabFootprint_len_pos_b4d (hT.2.1 t ht).1 j hit))
  · rw [fixedObjects_zero_len_eq s j hfix hz]; rfl

/-- A live code-DB payload record is disjoint from every non-trie owned interval. -/
theorem codeDbPayload_disj_nonTrieOwned {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat} {db p : Nat}
    (hC : CodeDbPayloadBounded s S db) (hp : p ∈ htabValues s db)
    {j : Ivl} (hj : j ∈ nonTrieOwned s S) :
    Disj (p, 16) j := by
  obtain ⟨_, _, ht, hf⟩ := hC.2 p hp
  unfold nonTrieOwned at hj
  rcases List.mem_append.1 hj with htab | hfix
  · obtain ⟨t, ht', hj'⟩ := List.mem_flatMap.1 htab
    exact ht t ht' j hj'
  · exact hf j hfix

/-- Step buffers are disjoint from a live code-DB payload record: a live buffer is a fixed object. -/
theorem bufRegions_disj_codeDbPayload {F : Type}
    {s : PanSemStateFiniteExact 64 F} {B : BufList} {S : List Nat} {db p : Nat}
    (hB : ValidBufList B)
    (hC : CodeDbPayloadBounded s S db) (hp : p ∈ htabValues s db) :
    ∀ j ∈ bufRegions B s, Disj (p, 16) j := by
  intro j hj
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hj
  obtain ⟨sz, hgb, _, _⟩ := hB b hb
  by_cases hz : globN s b.1 = 0
  · exact Or.inr (Or.inl (by simp [Wave8GuestInv.bufferRegion, hz]))
  · have hfix : Wave8GuestInv.bufferRegion s (b.1, sz) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨(b.1, sz), hgb, rfl⟩
    obtain ⟨_, _, _, hf⟩ := hC.2 p hp
    have hd := hf _ hfix
    have hin : Inside (Wave8GuestInv.bufferRegion s b)
        (Wave8GuestInv.bufferRegion s (b.1, sz)).1
        ((Wave8GuestInv.bufferRegion s (b.1, sz)).1 +
          (Wave8GuestInv.bufferRegion s (b.1, sz)).2) := by
      simp only [Wave8GuestInv.bufferRegion, hz, ↓reduceIte, Inside]
      exact ⟨le_rfl, by omega⟩
    exact disj_of_inside_right hin hd

/-- Payload length words of a live code-DB entry are untouched by a `NonTrieStep` frame. -/
theorem codeDbPayload_words_kept_of_nonTrieStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {B : BufList} {S : List Nat} {db p : Nat}
    (hAs : ArenaOK s)
    (hC : CodeDbPayloadBounded s S db) (hp : p ∈ htabValues s db)
    (hfr : FrameOutside s post (nonTrieOwned s S ++ bufRegions B s ++ [freeGap s]) (heapFree s))
    (hold_z : ∀ j ∈ nonTrieOwned s S, j.2 = 0 → j.1 % 8 = 0)
    (hR_z : ∀ j ∈ bufRegions B s, j.2 = 0 → j.1 % 8 = 0)
    (hB : ValidBufList B) :
    memW post (p + 8) = memW s (p + 8) := by
  obtain ⟨hin, hb, _, _⟩ := hC.2 p hp
  have hwords : WordsOK s (p, 16) := (hC.1 p hp).1
  have hp8 : p % 8 = 0 := hwords.1
  have hunhit : IvlUnhit s post (p, 16) :=
    ivlUnhit_of_worldStep_frameOutside_b4d hAs hfr hold_z hR_z hp8 hwords.2.1
      (Or.inr (Or.inl hin)) (fun j hj => codeDbPayload_disj_nonTrieOwned hC hp hj)
      (bufRegions_disj_codeDbPayload hB hC hp)
  exact memW_eq_of_ivlUnhit hunhit (by omega) hb ⟨by omega, by omega⟩

/-- `CodeDbPayloadBounded` is contravariant in the table list. -/
theorem codeDbPayloadBounded_sub {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S1 S2 : List Nat} {db : Nat}
    (hsub : ∀ t ∈ S1, t ∈ S2) (hC : CodeDbPayloadBounded s S2 db) :
    CodeDbPayloadBounded s S1 db := by
  refine ⟨hC.1, fun p hp => ?_⟩
  obtain ⟨hin, hb, ht, hf⟩ := hC.2 p hp
  exact ⟨hin, hb, fun t ht2 i hi => ht t (hsub t ht2) i hi, hf⟩

/-- `CodeDbPayloadBoundedNz` is contravariant in the table list. -/
theorem codeDbPayloadBoundedNz_sub {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S1 S2 : List Nat}
    (hsub : ∀ t ∈ S1, t ∈ S2) (hC : CodeDbPayloadBoundedNz s S2) :
    CodeDbPayloadBoundedNz s S1 :=
  fun g k hgk hgnz hdb => codeDbPayloadBounded_sub hsub (hC g k hgk hgnz hdb)

/-- `CodeDbPayloadBounded` transfers along a permutation of the table list. -/
theorem codeDbPayloadBounded_perm {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S1 S2 : List Nat} {db : Nat}
    (hperm : S1.Perm S2) (hC : CodeDbPayloadBounded s S1 db) :
    CodeDbPayloadBounded s S2 db :=
  codeDbPayloadBounded_sub (fun _ ht => hperm.symm.subset ht) hC

/-- `CodeDbPayloadBoundedNz` transfers along a permutation of the table list. -/
theorem codeDbPayloadBoundedNz_perm {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S1 S2 : List Nat}
    (hperm : S1.Perm S2) (hC : CodeDbPayloadBoundedNz s S1) :
    CodeDbPayloadBoundedNz s S2 :=
  fun g k hgk hgnz hdb => codeDbPayloadBounded_perm hperm (hC g k hgk hgnz hdb)

/-- A post non-trie owned interval sits inside a pre non-trie owned interval or in fresh heap. -/
theorem nonTrieOwned_post_loc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {i : Ivl}
    (hg : OwnedGrows s post (nonTrieOwned s S) (nonTrieOwned post S))
    (hi : i ∈ nonTrieOwned post S) :
    i = (0, 0) ∨
      (∃ j, j ∈ nonTrieOwned s S ∧ Inside i j.1 (j.1 + j.2)) ∨
      Inside i (globN s "heap_ptr") (globN post "heap_ptr") := by
  rcases hg i hi with h0 | ⟨j, hj, hlo, hhi⟩ | hnew
  · exact Or.inl h0
  · exact Or.inr (Or.inl ⟨j, hj, hlo, hhi⟩)
  · exact Or.inr (Or.inr hnew)

/-- `CodeDbPayloadBounded` survives a `NonTrieStep` on the same table set: values are preserved by
`CodeRootsValsEq`, payload words by the non-trie frame, and post intervals grow inside the pre
non-trie owned set or fresh heap. -/
theorem codeDbPayloadBounded_of_nonTrieStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {B : BufList} {S : List Nat} {db : Nat}
    (hB : ValidBufList B)
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hT : TablesTyped s S) (hF : FixedTyped s)
    (hC : CodeDbPayloadBounded s S db)
    (hv : htabValues post db = htabValues s db)
    (hgrow : OwnedGrows s post (nonTrieOwned s S) (nonTrieOwned post S))
    (hfr : FrameOutside s post (nonTrieOwned s S ++ bufRegions B s ++ [freeGap s]) (heapFree s)) :
    CodeDbPayloadBounded post S db := by
  have hold_z : ∀ j ∈ nonTrieOwned s S, j.2 = 0 → j.1 % 8 = 0 :=
    nonTrieOwned_zero_aligned_b4d hT hF
  have hR_z : ∀ j ∈ bufRegions B s, j.2 = 0 → j.1 % 8 = 0 :=
    bufRegions_zero_aligned_b4d hB hF
  have hw : ∀ p ∈ htabValues s db, memW post (p + 8) = memW s (p + 8) :=
    fun p hp => codeDbPayload_words_kept_of_nonTrieStep hAs.2 hC hp hfr hold_z hR_z hB
  refine codeDbPayloadBounded_of_owned_growth hC hAs hAp hhp hv hw ?_
  intro i hi
  have hi_nt : i ∈ nonTrieOwned post S := by
    unfold nonTrieOwned
    rcases hi with ⟨t, ht, hit⟩ | hfix
    · exact List.mem_append_left _ (List.mem_flatMap.2 ⟨t, ht, hit⟩)
    · exact List.mem_append_right _ hfix
  rcases nonTrieOwned_post_loc hgrow hi_nt with h0 | ⟨j, hj, hlo, hhi⟩ | hnew
  · exact Or.inl h0
  · exact Or.inr (Or.inl ⟨j, by
      unfold nonTrieOwned at hj
      rcases List.mem_append.1 hj with htab | hfix
      · obtain ⟨t, ht, hit⟩ := List.mem_flatMap.1 htab
        exact Or.inl ⟨t, ht, hit⟩
      · exact Or.inr hfix, hlo, hhi⟩)
  · exact Or.inr (Or.inr hnew)

/-- `CodeDbPayloadBoundedNz` survives a `NonTrieStep` on the same table set. -/
theorem codeDbPayloadBoundedNz_of_nonTrieStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {B : BufList} {S : List Nat}
    (hB : ValidBufList B)
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hT : TablesTyped s S) (hF : FixedTyped s)
    (hC : CodeDbPayloadBoundedNz s S)
    (hv : ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
      globN s g ≠ 0 → memW s (globN s g + k) ≠ 0 →
      htabValues post (memW s (globN s g + k)) = htabValues s (memW s (globN s g + k)))
    (hgrow : OwnedGrows s post (nonTrieOwned s S) (nonTrieOwned post S))
    (hfr : FrameOutside s post (nonTrieOwned s S ++ bufRegions B s ++ [freeGap s]) (heapFree s))
    (hglob : ∀ g ∈ (["ws", "bs", "ts"] : List String), globN post g = globN s g)
    (hroot : ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
      globN s g ≠ 0 → memW post (globN s g + k) = memW s (globN s g + k)) :
    CodeDbPayloadBoundedNz post S := by
  intro g k hgk hgnz_p hdb_p
  have hgg : globN post g = globN s g := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
    rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hglob "ws" (by decide)
    · exact hglob "bs" (by decide)
    · exact hglob "ts" (by decide)
  have hgnz_s : globN s g ≠ 0 := by rwa [← hgg]
  have hroot_eq : memW post (globN s g + k) = memW s (globN s g + k) := hroot g k hgk hgnz_s
  rw [hgg, hroot_eq] at hdb_p ⊢
  exact codeDbPayloadBounded_of_nonTrieStep hB hAs hAp hhp hT hF
    (hC g k hgk hgnz_s hdb_p) (hv g k hgk hgnz_s hdb_p) hgrow hfr

/-! ## 2. Master bridge: `WorldStepCodeSc` → `EvmMsgReadyMsgBounded` + `EvmStepCC` -/

/-- `MsgDisjCodeStrong` survives a step that keeps the code-DB roots, their `htabValues`, the
`ev` global, and the word at `ev+112`. -/
theorem msgDisjCodeStrong_of_roots_kept {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hM : MsgDisjCodeStrong s)
    (hglob : ∀ g ∈ (["ws", "bs", "ts", "ev"] : List String), globN post g = globN s g)
    (h112 : memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112))
    (hroot : ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
      globN s g ≠ 0 → memW post (globN s g + k) = memW s (globN s g + k))
    (hv : ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
      globN s g ≠ 0 → memW s (globN s g + k) ≠ 0 →
      htabValues post (memW s (globN s g + k)) = htabValues s (memW s (globN s g + k))) :
    MsgDisjCodeStrong post := by
  intro g k hgk hgnz_p hdb_p p hp
  have hgg : globN post g = globN s g := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
    rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hglob "ws" (by decide)
    · exact hglob "bs" (by decide)
    · exact hglob "ts" (by decide)
  have hgnz_s : globN s g ≠ 0 := by rwa [← hgg]
  have hroot_eq : memW post (globN s g + k) = memW s (globN s g + k) := hroot g k hgk hgnz_s
  rw [hgg, hroot_eq] at hdb_p hp
  rw [hv g k hgk hgnz_s hdb_p] at hp
  have hgev : globN post "ev" = globN s "ev" := hglob "ev" (by decide)
  rw [hgev, h112]
  exact hM g k hgk hgnz_s hdb_p p hp

/-- A live code-DB payload record sits in old heap, avoids persistent trie extents, and is
disjoint from `worldOwned s S_w Nd`. Consequently it remains disjoint from every post table
footprint in `S_w' ++ F_rem` and every post fixed object across a `WorldStepSc` step. -/
theorem codeDbPayloadBounded_lift_join {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S_w F_rem S_w' Nd Nd' : List Nat} {db : Nat}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (_hWT_Sw : WorldTypedWith s S_w Nd)
    (hC_s : CodeDbPayloadBounded s (S_w ++ F_rem) db)
    (hC_nt : CodeDbPayloadBounded post S_w db)
    (hv : htabValues post db = htabValues s db)
    (hgrow : OwnedGrows s post (worldOwned s S_w Nd) (worldOwned post S_w' Nd'))
    (hF_fp : ∀ t ∈ F_rem, htabFootprint post t = htabFootprint s t)
    (hdb_disj_nd : ∀ p ∈ htabValues s db, ∀ o ∈ nodeExtents s Nd, Disj (p, 16) o) :
    CodeDbPayloadBounded post (S_w' ++ F_rem) db := by
  refine ⟨hC_nt.1, fun p hp_post => ?_⟩
  have hp_s : p ∈ htabValues s db := by rwa [hv] at hp_post
  obtain ⟨hin_post, hb_post, _, hfix_post⟩ := hC_nt.2 p hp_post
  obtain ⟨hin_s, _, ht_s, hfix_s⟩ := hC_s.2 p hp_s
  have halloc : (p, 16).2 = 0 ∨ AllocatedEvmB4d s (p, 16) := Or.inr (Or.inl hin_s)
  have hold_disj : ∀ j ∈ worldOwned s S_w Nd, Disj (p, 16) j := by
    intro j hj
    unfold worldOwned at hj
    rcases List.mem_append.1 hj with hj1 | hj_nd
    · rcases List.mem_append.1 hj1 with hj_tab | hj_fix
      · obtain ⟨t, ht, hjt⟩ := List.mem_flatMap.1 hj_tab
        exact ht_s t (List.mem_append_left _ ht) j hjt
      · exact hfix_s j hj_fix
    · exact hdb_disj_nd p hp_s j hj_nd
  have hnew_disj : ∀ j ∈ worldOwned post S_w' Nd', Disj (p, 16) j :=
    allocatedEvm_disj_ownedGrows_b4d hAs hAp hhp halloc hold_disj hgrow
  refine ⟨hin_post, hb_post, ?_, hfix_post⟩
  intro t ht i hi
  rcases List.mem_append.1 ht with htw | htf
  · apply hnew_disj i
    unfold worldOwned
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, htw, hi⟩))
  · rw [hF_fp t htf] at hi
    exact ht_s t (List.mem_append_right _ htf) i hi

/-- Construct `CodeBoundedCtxNz0` on `(s, S, Nd)` from `EvmMsgReadyMsgBounded s` by extracting the
typed world witness from `EvmInvAt`. -/
theorem codeBoundedCtxNz0_of_msgBounded {F : Type}
    {s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (h : EvmMsgReadyMsgBounded s) :
    ∃ S Nd, CodeBoundedCtxNz0 s S Nd := by
  obtain ⟨hA, _, S, hInvAt, _, hC⟩ := h
  obtain ⟨hT, hJ, hF, ⟨Nd, hTr⟩⟩ := hInvAt.1
  exact ⟨S, Nd, hA, ⟨hT, hJ, hF, hTr⟩, hC, hc⟩

/-! ## 3. Shrinking `EvmInvAt` and `MsgOwned` across `S ⊆ S'` -/

private theorem triesTypedWith_sub_b4d {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S S' Nd : List Nat}
    (hsub : ∀ t ∈ S, t ∈ S') (hTr : TriesTypedWith s S' Nd) :
    TriesTypedWith s S Nd := by
  obtain ⟨hNH, hDisj, hWs⟩ := hTr
  refine ⟨hNH, fun o ho => ⟨fun t ht => (hDisj o ho).1 t (hsub t ht), (hDisj o ho).2⟩, ?_⟩
  intro hws
  obtain ⟨hR24, hR32⟩ := hWs hws
  exact ⟨hR24, fun h32 => hR32 (hsub _ h32)⟩

theorem avoidsTries_sub_b4d {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S S' : List Nat} {os : List Ivl}
    (hsub : ∀ t ∈ S, t ∈ S') (hAT : AvoidsTries s S' os) :
    AvoidsTries s S os := by
  obtain ⟨Nd, hTr, hd⟩ := hAT
  exact ⟨Nd, triesTypedWith_sub_b4d hsub hTr, hd⟩

theorem msgOwned_sub_b4d {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S S' : List Nat} {m : Nat}
    (hsub : ∀ t ∈ S, t ∈ S') (hMO : MsgOwned s S' m) :
    MsgOwned s S m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hMO
  exact ⟨h1, h2, fun t ht => h3 t (hsub t ht), h4, h5, avoidsTries_sub_b4d hsub h6⟩

private theorem worldTableRefs_sub_b4d {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S S' : List Nat} {t0 : Nat}
    (hsub : ∀ t ∈ S, t ∈ S') (hm : t0 ∈ worldTableRefs s S) :
    t0 ∈ worldTableRefs s S' := by
  unfold worldTableRefs at hm ⊢
  dsimp only at hm ⊢
  have hnest : ∀ g : String,
      t0 ∈ (if globN s g ≠ 0 ∧ memW s (globN s g + 32) ∈ S then htabValues s (memW s (globN s g + 32)) else []) →
      t0 ∈ (if globN s g ≠ 0 ∧ memW s (globN s g + 32) ∈ S' then htabValues s (memW s (globN s g + 32)) else []) := by
    intro g hg
    split at hg
    · rename_i hc
      rw [if_pos ⟨hc.1, hsub _ hc.2⟩]
      exact hg
    · cases hg
  rcases List.mem_append.1 hm with h1 | hr
  · rcases List.mem_append.1 h1 with h2 | hb
    · rcases List.mem_append.1 h2 with h3 | hts
      · rcases List.mem_append.1 h3 with h4 | hbs
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h4)))
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (hnest "bs" hbs))))
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (hnest "ts" hts)))
    · exact List.mem_append_left _ (List.mem_append_right _ hb)
  · exact List.mem_append_right _ hr

theorem delExclusive_sub_b4d {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S S' : List Nat} {ch : List Ivl} {i u : Nat}
    (hsub : ∀ t ∈ S, t ∈ S') (hDE : DelExclusive s S' ch i u) :
    DelExclusive s S ch i u :=
  ⟨fun hm => hDE.1 (worldTableRefs_sub_b4d hsub hm), hDE.2⟩

private theorem frameWF_sub_b4d {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S S' : List Nat} {ec : Ivl}
    (hsub : ∀ t ∈ S, t ∈ S')
    (h136 : memW s (ec.1 + 136) ∈ S)
    (h168 : memW s (ec.1 + 168) ∈ S)
    (h176 : memW s (ec.1 + 176) ∈ S)
    (hFW : FrameWF s S' ec) :
    FrameWF s S ec := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, _, _, _, f11, f12, f13, f14, f15, f16, f17⟩ := hFW
  exact ⟨f1, f2, f3, f4, f5, f6, f7, h136, h168, h176, f11, f12, f13, f14, f15, f16,
    msgOwned_sub_b4d hsub f17⟩

private theorem evmInvAt_sub_b4d {F : Type}
    {post : PanSemStateFiniteExact 64 F} {S S' : List Nat}
    (hW : WorldTyped post S)
    (hsub : ∀ t ∈ S, t ∈ S')
    (hInv' : EvmInvAt post S')
    (hslots : ∀ ec ∈ evmChain post,
      memW post (ec.1 + 136) ∈ S ∧ memW post (ec.1 + 168) ∈ S ∧ memW post (ec.1 + 176) ∈ S) :
    EvmInvAt post S := by
  obtain ⟨_, hne, hlen, hlast, hFW', hFR, hRW, hPW, hFO', hAT', hMarks', hRoles', hGas⟩ := hInv'
  refine ⟨hW, hne, hlen, hlast, ?_, hFR, hRW, hPW, ?_, avoidsTries_sub_b4d hsub hAT', ?_, ?_, hGas⟩
  · intro ec hec
    obtain ⟨h1, h2, h3⟩ := hslots ec hec
    exact frameWF_sub_b4d hsub h1 h2 h3 (hFW' ec hec)
  · intro ec hec o ho
    exact ⟨fun t ht => (hFO' ec hec o ho).1 t (hsub t ht), (hFO' ec hec o ho).2⟩
  · intro i hi
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hMarks' i hi
    refine ⟨m1, m2, m3, m4, m5, m6, m7, ?_, m9⟩
    intro t ht
    rcases m8 t (hsub t ht) with ⟨htake, hdel⟩ | hloc
    · exact Or.inl ⟨htake, delExclusive_sub_b4d hsub hdel⟩
    · exact Or.inr hloc
  · refine ⟨?_, hRoles'.2.1, hRoles'.2.2⟩
    intro a ha
    have hhdr := (hRoles'.1 a ha).2
    refine ⟨?_, hhdr⟩
    rcases List.mem_append.1 ha with hwf | hjr
    · rcases List.mem_append.1 hwf with hw | hf
      · exact (hW.1.2.2.2.2.2.2.2.2.2.2.2.1 a (List.mem_append_left _ hw)).1
      · obtain ⟨ec, hec, ha_ec⟩ := List.mem_flatMap.1 hf
        obtain ⟨h136, h168, h176⟩ := hslots ec hec
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha_ec
        rcases ha_ec with rfl | rfl | rfl
        · exact h136
        · exact h168
        · exact h176
    · exact (hW.1.2.2.2.2.2.2.2.2.2.2.2.1 a (List.mem_append_right _ hjr)).1

/-! ## 4. Master Theorem & `FunSpec` / `D0PreB` Wrappers -/

/-- Master bridge: any `WorldStepCodeSc B gw s r post` (`PosBufList B`, `SafeStepGlobals gw`,
`gw ⊆ gw_out`) preserves `EvmMsgReadyMsgBounded`, establishes `EvmStepCC gw_out s post`, and
preserves `memW _ (globN s "ev" + 112)`. -/
theorem msgBounded_stepCC_of_worldStepCodeSc {F : Type}
    {B : BufList} {gw gw_out : List String}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hB : PosBufList B)
    (hgw : SafeStepGlobals gw)
    (hgw_sub : ∀ g ∈ gw, g ∈ gw_out)
    (h : EvmMsgReadyMsgBounded s)
    (hstep : WorldStepCodeSc B gw s r post) :
    EvmMsgReadyMsgBounded post ∧
    EvmStepCC gw_out s post ∧
    memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) := by
  obtain ⟨hAs, hM, S, hInvAt, hMO, hC⟩ := h
  have hNT := hstep.2
  obtain ⟨⟨hAp, hhp, hG, hR, htyped⟩, hsc⟩ := hstep.1
  obtain ⟨hT, hJ, hF, ⟨Nd0, hTr0⟩⟩ := hInvAt.1
  have hWT_S0 : WorldTypedWith s S Nd0 := ⟨hT, hJ, hF, hTr0⟩
  have hR_disj0 : IvlsDisj (bufRegions B s) (worldTypedIvls s S Nd0) :=
    validBufList_disj hB.1 hWT_S0
  obtain ⟨⟨Nd_nt, hWT_S_post⟩, hgrow_nt, hfr_nt⟩ := hNT S Nd0 hWT_S0 hR_disj0
  obtain ⟨_, _, _, _, _, _, hv⟩ := htyped S Nd0 hWT_S0 hR_disj0
  have hroots := code_roots_kept_of_safeGlobals hWT_S0 hB hgw hR hG
  have hglob_wbt : ∀ g ∈ (["ws", "bs", "ts"] : List String), globN post g = globN s g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact (hroots "ws" 16 (by decide)).1
    · exact (hroots "bs" 48 (by decide)).1
    · exact (hroots "ts" 48 (by decide)).1
  have hroot_eq : ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
      globN s g ≠ 0 → memW post (globN s g + k) = memW s (globN s g + k) := by
    intro g k hgk hgnz
    have hk_in : (g, k) ∈ ([("ws", 16), ("ts", 40), ("ts", 48), ("bs", 48)] : List (String × Nat)) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk ⊢
      rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    obtain ⟨hg_eq, hr_eq⟩ := hroots g k hk_in
    have hhr := hr_eq hgnz
    rwa [hg_eq] at hhr
  have hC_post : CodeDbPayloadBoundedNz post S :=
    codeDbPayloadBoundedNz_of_nonTrieStep hB.1 hAs hAp hhp hT hF hC hv hgrow_nt hfr_nt hglob_wbt hroot_eq
  obtain ⟨S_w, F_rem, S_w', _, _, _, hperm_S, hSw_sub_Sw', _, _, _, _, _, _, _, _,
    hInvAt', hMO', hStepCC, h112_eq, _⟩ :=
    evmStepCC_full_of_worldStepSc hB.1 hgw hgw_sub hAs hInvAt hMO hstep.1
  have hS_sub_S' : ∀ t ∈ S, t ∈ S_w' ++ F_rem := by
    intro t ht
    rcases List.mem_append.1 (hperm_S.subset ht) with htw | htf
    · exact List.mem_append_left _ (hSw_sub_Sw' t htw)
    · exact List.mem_append_right _ htf
  have hev_eq : globN post "ev" = globN s "ev" :=
    globN_eq_of_lookup (hG (ofString "ev") (hgw.not_mem_map (by decide)))
  have hglob_wbte : ∀ g ∈ (["ws", "bs", "ts", "ev"] : List String), globN post g = globN s g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact hglob_wbt "ws" (by decide)
    · exact hglob_wbt "bs" (by decide)
    · exact hglob_wbt "ts" (by decide)
    · exact hev_eq
  have hM_post : MsgDisjCodeStrong post :=
    msgDisjCodeStrong_of_roots_kept hM hglob_wbte h112_eq hroot_eq hv
  have hold_z : ∀ j ∈ nonTrieOwned s S, j.2 = 0 → j.1 % 8 = 0 :=
    nonTrieOwned_zero_aligned_b4d hT hF
  have hR_z : ∀ j ∈ bufRegions B s, j.2 = 0 → j.1 % 8 = 0 :=
    bufRegions_zero_aligned_b4d hB.1 hF
  have hslots : ∀ ec ∈ evmChain post,
      memW post (ec.1 + 136) ∈ S ∧ memW post (ec.1 + 168) ∈ S ∧ memW post (ec.1 + 176) ∈ S := by
    rw [hStepCC.1.2.2.2]
    intro ec hec
    have hFW_s := hInvAt.2.2.2.2.1 ec hec
    have hfo_disj_s := hInvAt.2.2.2.2.2.2.2.2.1 ec hec (ec.1, 280) (by simp [frameObjects])
    have hscr_ec := hFW_s.1 (ec.1, 280) (by simp)
    have hal_ec : (ec.1, 280).2 = 0 ∨ AllocatedEvmB4d s (ec.1, 280) :=
      Or.inr (Or.inr (Or.inr hscr_ec.1))
    have hb_ec : ec.1 + 280 ≤ 2 ^ 64 :=
      allocatedEvm_bound_b4d hAs.2 (Or.inr (Or.inr hscr_ec.1))
    have hnt_disj : ∀ j ∈ nonTrieOwned s S, Disj (ec.1, 280) j := by
      intro j hj
      unfold nonTrieOwned at hj
      rcases List.mem_append.1 hj with htab | hfix
      · obtain ⟨t, ht, hit⟩ := List.mem_flatMap.1 htab
        exact hfo_disj_s.1 t ht j hit
      · exact hfo_disj_s.2 j hfix
    have hbuf_disj : ∀ j ∈ bufRegions B s, Disj (ec.1, 280) j := by
      intro j hj
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hj
      obtain ⟨sz, hgb, _, _⟩ := hB.1 b hb
      by_cases hz : globN s b.1 = 0
      · exact Or.inr (Or.inl (by simp [Wave8GuestInv.bufferRegion, hz]))
      · have hfix : Wave8GuestInv.bufferRegion s (b.1, sz) ∈ fixedObjects s := by
          unfold fixedObjects
          apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
          exact List.mem_map.2 ⟨(b.1, sz), hgb, rfl⟩
        have hd := hfo_disj_s.2 _ hfix
        have hin : Inside (Wave8GuestInv.bufferRegion s b)
            (Wave8GuestInv.bufferRegion s (b.1, sz)).1
            ((Wave8GuestInv.bufferRegion s (b.1, sz)).1 +
              (Wave8GuestInv.bufferRegion s (b.1, sz)).2) := by
          simp only [Wave8GuestInv.bufferRegion, hz, ↓reduceIte, Inside]
          exact ⟨le_rfl, by omega⟩
        exact disj_of_inside_right hin hd
    have hunhit : IvlUnhit s post (ec.1, 280) :=
      ivlUnhit_of_worldStep_frameOutside_b4d hAs.2 hfr_nt hold_z hR_z
        hscr_ec.2.1 hscr_ec.2.2.1 hal_ec hnt_disj hbuf_disj
    have he1_8 : ec.1 % 8 = 0 := hscr_ec.2.1
    have h136_eq : memW post (ec.1 + 136) = memW s (ec.1 + 136) :=
      memW_eq_of_ivlUnhit hunhit (by omega) hb_ec ⟨by omega, by omega⟩
    have h168_eq : memW post (ec.1 + 168) = memW s (ec.1 + 168) :=
      memW_eq_of_ivlUnhit hunhit (by omega) hb_ec ⟨by omega, by omega⟩
    have h176_eq : memW post (ec.1 + 176) = memW s (ec.1 + 176) :=
      memW_eq_of_ivlUnhit hunhit (by omega) hb_ec ⟨by omega, by omega⟩
    rw [h136_eq, h168_eq, h176_eq]
    exact ⟨hFW_s.2.2.2.2.2.2.2.1, hFW_s.2.2.2.2.2.2.2.2.1, hFW_s.2.2.2.2.2.2.2.2.2.1⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_S_post.1, hWT_S_post.2.1, hWT_S_post.2.2.1, ⟨Nd_nt, hWT_S_post.2.2.2⟩⟩
  have hInvAt_S : EvmInvAt post S := evmInvAt_sub_b4d hW_post hS_sub_S' hInvAt' hslots
  have hMO_S : MsgOwned post S (memW post (globN post "ev" + 112)) :=
    msgOwned_sub_b4d hS_sub_S' hMO'
  exact ⟨⟨hAp, hM_post, S, hInvAt_S, hMO_S, hC_post⟩, hStepCC, h112_eq⟩

theorem worldOK_of_msgBounded {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : EvmMsgReadyMsgBounded s) : WorldOK s := by
  obtain ⟨hAs, _, S, hInvAt, _, _⟩ := h
  exact ⟨hAs, S, hInvAt.1⟩

/-- Lift any `WorldKeepsCodeSc B gw fname` to `FunSpec EvmMsgReadyMsgBounded`. -/
theorem funSpec_msgBounded_of_worldKeepsCodeSc {B : BufList} {gw : List String} {fname : MlS}
    (hB : PosBufList B) (hgw : SafeStepGlobals gw)
    (hf : WorldKeepsCodeSc B gw fname) :
    FunSpec EvmMsgReadyMsgBounded
      (fun s r post => Resumes r →
        EvmMsgReadyMsgBounded post ∧ EvmStepCC gw s post ∧
          memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112)) fname := by
  obtain ⟨ps, body, rs, hl, hsp⟩ := hf
  exact ⟨ps, body, rs, hl, fun s hc hMB hex hnt hres =>
    msgBounded_stepCC_of_worldStepCodeSc hB hgw (fun _ hg => hg) hMB
      (hsp s hc (worldOK_of_msgBounded hMB) hex hnt hres)⟩

/-- Destination-free call wrapper on `D0PreB` for any `WorldKeepsCodeSc` callee. -/
theorem hoare_d0PreB_call0_wkCodeSc {B : BufList} {gw gw_c : List String} {hp : Nat}
    {G : MlS → Option (ValueHOL 64)} {ch : List Ivl} {cells : List (Nat × Nat × Nat × Nat)}
    {L : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {fname : MlS}
    (hB : PosBufList B) (hgw : SafeStepGlobals gw_c)
    (hL : ∀ {F : Type} (s t : PanSemStateFiniteExact 64 F), t.locals = s.locals → L s → L t)
    (hsub : ∀ g ∈ gw_c, g ∈ gw)
    (hf : WorldKeepsCodeSc B gw_c fname)
    (args : List (ExpHOL 64)) :
    Hoare (fun s => D0PreB gw hp G ch cells s ∧ L s)
      (.call (some (none, none)) fname args)
      (D0CallPostB gw hp G ch cells L) :=
  hoare_d0PreB_call0_step hL hsub (hgw.not_mem_map (by decide))
    (funSpec_msgBounded_of_worldKeepsCodeSc hB hgw hf) args

/-- Catchable-exception handler for any `WorldKeepsCodeSc` callee under `D0PreB`. -/
theorem wkCodeSc_exception_stepB {B : BufList} {gw gw_c : List String}
    (hB : PosBufList B) (hgw : SafeStepGlobals gw_c) (hsub : ∀ g ∈ gw_c, g ∈ gw)
    {fname : MlS} (hf : WorldKeepsCodeSc B gw_c fname)
    (hp : Nat) (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (cells : List (Nat × Nat × Nat × Nat))
    {F : Type} (s : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hc : s.code = originalRuntimeCode) (hD : D0PreB gw hp G ch cells s)
    (hl : lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret))
    (e : MlS) (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hne : e ≠ ofString "TrapErr")
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.exception e v), post)) :
    EvmMsgReadyMsgBounded post ∧ StepFromCC gw hp G ch cells post := by
  have hBe : EvmMsgReadyMsgBounded (callEntryStateHOLFinite s callee) :=
    localsFree_evmMsgReadyMsgBounded s callee (s.clock - 1) hD.1.1
  have hSe : StepFromCC gw hp G ch cells (callEntryStateHOLFinite s callee) :=
    localsFree_stepFromCC gw hp G ch cells s callee (s.clock - 1) hD.1.2
  have hsp := FunSpec.at_lookup (funSpec_msgBounded_of_worldKeepsCodeSc hB hgw hf)
    s hc values body callee ret hl hBe (by rw [hr]; simp)
  rw [hr] at hsp
  obtain ⟨hBp, hStep, _⟩ := hsp (Or.inr ⟨e, v, rfl, hne⟩)
  exact ⟨hBp, stepFromCC_of_evmStepCC hsub hSe hStep⟩

/-- `DecCallResumeOn` wrapper for any `WorldKeepsCodeSc` callee returning a `.one` word. -/
theorem wkCodeSc_word_resumeB {B : BufList} {gw gw_c : List String}
    {hp : Nat} {G : MlS → Option (ValueHOL 64)} {ch : List Ivl}
    {cells : List (Nat × Nat × Nat × Nat)}
    {L : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {name fname : MlS} {params : List (MlS × ShapeHOL)} {fbody : ProgHOL 64}
    (hB : PosBufList B) (hgw : SafeStepGlobals gw_c) (hsub : ∀ g ∈ gw_c, g ∈ gw)
    (hf : WorldKeepsCodeSc B gw_c fname)
    (hlook : originalRuntimeCode.lookup fname = some (params, fbody, .one))
    (hne : name ≠ ofString "msg")
    (hL : ∀ {F : Type} (s t : PanSemStateFiniteExact 64 F),
      (∀ y, y ≠ name → t.locals.lookup y = s.locals.lookup y) → L s → L t)
    (args : List (ExpHOL 64))
    (hret : ∀ {F : Type} (ent post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      ent.code = originalRuntimeCode → EvmMsgReadyMsgBounded ent →
      evaluateHOLFiniteState ent fbody = (some (.returned v), post) →
      ∃ w : BitVec 64, v = .val (.word w)) :
    DecCallResumeOn
      (fun s => D0PreB gw hp G ch cells s ∧ L s)
      (fun s => D0PreB gw hp G ch cells s ∧ L s ∧
        ∃ w : BitVec 64, s.locals.lookup name = some (.val (.word w)))
      name fname args := by
  intro F s values body callee ret v post hc ⟨hD, hLs⟩ _ha hl hr
  have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
      some (body, callee, ret) := by rwa [← hc]
  have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
    fname params fbody body .one ret values callee hlook hl'
  have hBe : EvmMsgReadyMsgBounded (callEntryStateHOLFinite s callee) :=
    localsFree_evmMsgReadyMsgBounded s callee (s.clock - 1) hD.1.1
  have hSe : StepFromCC gw hp G ch cells (callEntryStateHOLFinite s callee) :=
    localsFree_stepFromCC gw hp G ch cells s callee (s.clock - 1) hD.1.2
  have hsp := FunSpec.at_lookup (funSpec_msgBounded_of_worldKeepsCodeSc hB hgw hf)
    s hc values body callee ret hl hBe (by rw [hr]; simp)
  rw [hr] at hsp
  obtain ⟨hBp, hStep, h112⟩ := hsp (Or.inl ⟨v, rfl⟩)
  have hev_p : post.globals.lookup (ofString "ev") = s.globals.lookup (ofString "ev") :=
    (hStep.1.2.2.1 (ofString "ev") (hgw.not_mem_map (by decide))).symm
  have hSp := stepFromCC_of_evmStepCC hsub hSe hStep
  have hD_mid : D0PreB gw hp G ch cells { post with locals := s.locals } :=
    d0PreB_of_stepFromCC gw hp G ch cells hD
      (localsFree_evmMsgReadyMsgBounded post s.locals post.clock hBp)
      (localsFree_stepFromCC gw hp G ch cells post s.locals post.clock hSp)
      rfl hev_p h112
  have hent_code : (callEntryStateHOLFinite s callee).code = originalRuntimeCode := hc
  have hr_fbody : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) fbody =
      (some (.returned v), post) := hbody ▸ hr
  obtain ⟨w, rfl⟩ := hret _ post v hent_code hBe hr_fbody
  set res := setVarHOLFinite name (.val (.word w)) { post with locals := s.locals }
  have hD_res : D0PreB gw hp G ch cells res := by
    apply d0PreB_locals gw hp G ch cells { post with locals := s.locals }
      (s.locals.update (name, .val (.word w))) post.clock ?_ hD_mid
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have hL_res : L res := hL s res (fun y hy => by
    simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy.symm]) hLs
  refine ⟨hD_res, hL_res, w, ?_⟩
  simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

/-- Returning `DecCallResumeOn` wrapper for `get_code` on `D0PreB`: preserves `D0PreB ∧ L` and
yields `code, code_n` with `code_n.toNat < 2 ^ 40`. -/
theorem get_code_resumeB {gw : List String} {hp : Nat}
    {G : MlS → Option (ValueHOL 64)} {ch : List Ivl} {cells : List (Nat × Nat × Nat × Nat)}
    {L : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hhp_gw : "heap_ptr" ∈ gw)
    (name : MlS) (hne : name ≠ ofString "msg")
    (hL : ∀ {F : Type} (s t : PanSemStateFiniteExact 64 F),
      (∀ y, y ≠ name → t.locals.lookup y = s.locals.lookup y) → L s → L t)
    (args : List (ExpHOL 64)) :
    DecCallResumeOn
      (fun s => D0PreB gw hp G ch cells s ∧ L s)
      (fun s => D0PreB gw hp G ch cells s ∧ L s ∧
        ∃ code code_n : BitVec 64,
          s.locals.lookup name = some (.rStruct [.val (.word code), .val (.word code_n)]) ∧
          code_n.toNat < 2 ^ 40)
      name (ofString "get_code") args := by
  intro F s values body callee ret v post hc ⟨hD, hLs⟩ _ha hl hr
  obtain ⟨S0, Nd0, hctx⟩ := codeBoundedCtxNz0_of_msgBounded hc hD.1.1
  obtain ⟨code, code_n, rfl, hnb⟩ := get_code_call_return_of_codeBoundedCtxNz0 hctx hl hr
  have hBe : EvmMsgReadyMsgBounded (callEntryStateHOLFinite s callee) :=
    localsFree_evmMsgReadyMsgBounded s callee (s.clock - 1) hD.1.1
  have hSe : StepFromCC gw hp G ch cells (callEntryStateHOLFinite s callee) :=
    localsFree_stepFromCC gw hp G ch cells s callee (s.clock - 1) hD.1.2
  have hgw_hp : SafeStepGlobals ["heap_ptr"] := by
    intro g hg; simp at hg; subst hg; simp
  have hsp := FunSpec.at_lookup
    (funSpec_msgBounded_of_worldKeepsCodeSc posBufList_sk hgw_hp wkCodeSc_get_code)
    s hc values body callee ret hl hBe (by rw [hr]; simp)
  rw [hr] at hsp
  obtain ⟨hBp, hStep, h112⟩ := hsp (Or.inl ⟨_, rfl⟩)
  have hev_p : post.globals.lookup (ofString "ev") = s.globals.lookup (ofString "ev") :=
    (hStep.1.2.2.1 (ofString "ev") (hgw_hp.not_mem_map (by decide))).symm
  have hSp := stepFromCC_of_evmStepCC
    (fun g hg => by simp at hg; subst hg; exact hhp_gw) hSe hStep
  have hD_mid : D0PreB gw hp G ch cells { post with locals := s.locals } :=
    d0PreB_of_stepFromCC gw hp G ch cells hD
      (localsFree_evmMsgReadyMsgBounded post s.locals post.clock hBp)
      (localsFree_stepFromCC gw hp G ch cells post s.locals post.clock hSp)
      rfl hev_p h112
  set res := setVarHOLFinite name (.rStruct [.val (.word code), .val (.word code_n)])
    { post with locals := s.locals }
  have hD_res : D0PreB gw hp G ch cells res := by
    apply d0PreB_locals gw hp G ch cells { post with locals := s.locals }
      (s.locals.update (name, .rStruct [.val (.word code), .val (.word code_n)])) post.clock ?_ hD_mid
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have hL_res : L res := hL s res (fun y hy => by
    simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy.symm]) hLs
  refine ⟨hD_res, hL_res, code, code_n, ?_, hnb⟩
  simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

/-- Returning `DecCallResumeOn` wrapper for `ext_code_of` on `D0PreB`: preserves `D0PreB ∧ L` and
yields `code, code_n` with `code_n.toNat < 2 ^ 40`. -/
theorem ext_code_of_resumeB {gw : List String} {hp : Nat}
    {G : MlS → Option (ValueHOL 64)} {ch : List Ivl} {cells : List (Nat × Nat × Nat × Nat)}
    {L : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hhp_gw : "heap_ptr" ∈ gw) (hsp_gw : "scratch_ptr" ∈ gw)
    (name : MlS) (hne : name ≠ ofString "msg")
    (hL : ∀ {F : Type} (s t : PanSemStateFiniteExact 64 F),
      (∀ y, y ≠ name → t.locals.lookup y = s.locals.lookup y) → L s → L t)
    (args : List (ExpHOL 64)) :
    DecCallResumeOn
      (fun s => D0PreB gw hp G ch cells s ∧ L s)
      (fun s => D0PreB gw hp G ch cells s ∧ L s ∧
        ∃ code code_n : BitVec 64,
          s.locals.lookup name = some (.rStruct [.val (.word code), .val (.word code_n)]) ∧
          code_n.toNat < 2 ^ 40)
      name (ofString "ext_code_of") args := by
  intro F s values body callee ret v post hc ⟨hD, hLs⟩ _ha hl hr
  obtain ⟨S0, Nd0, hctx⟩ := codeBoundedCtxNz0_of_msgBounded hc hD.1.1
  obtain ⟨code, code_n, rfl, hnb⟩ := ext_code_of_call_return_of_codeBoundedCtxNz0 hctx hl hr
  have hBe : EvmMsgReadyMsgBounded (callEntryStateHOLFinite s callee) :=
    localsFree_evmMsgReadyMsgBounded s callee (s.clock - 1) hD.1.1
  have hSe : StepFromCC gw hp G ch cells (callEntryStateHOLFinite s callee) :=
    localsFree_stepFromCC gw hp G ch cells s callee (s.clock - 1) hD.1.2
  have hsp := FunSpec.at_lookup
    (funSpec_msgBounded_of_worldKeepsCodeSc posBufList_extCodeBufs safeStepGlobals_hp_sp wkCodeSc_ext_code_of)
    s hc values body callee ret hl hBe (by rw [hr]; simp)
  rw [hr] at hsp
  obtain ⟨hBp, hStep, h112⟩ := hsp (Or.inl ⟨_, rfl⟩)
  have hev_p : post.globals.lookup (ofString "ev") = s.globals.lookup (ofString "ev") :=
    (hStep.1.2.2.1 (ofString "ev") (safeStepGlobals_hp_sp.not_mem_map (by decide))).symm
  have hSp := stepFromCC_of_evmStepCC
    (fun g hg => by simp at hg; rcases hg with rfl | rfl; exact hhp_gw; exact hsp_gw) hSe hStep
  have hD_mid : D0PreB gw hp G ch cells { post with locals := s.locals } :=
    d0PreB_of_stepFromCC gw hp G ch cells hD
      (localsFree_evmMsgReadyMsgBounded post s.locals post.clock hBp)
      (localsFree_stepFromCC gw hp G ch cells post s.locals post.clock hSp)
      rfl hev_p h112
  set res := setVarHOLFinite name (.rStruct [.val (.word code), .val (.word code_n)])
    { post with locals := s.locals }
  have hD_res : D0PreB gw hp G ch cells res := by
    apply d0PreB_locals gw hp G ch cells { post with locals := s.locals }
      (s.locals.update (name, .rStruct [.val (.word code), .val (.word code_n)])) post.clock ?_ hD_mid
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have hL_res : L res := hL s res (fun y hy => by
    simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy.symm]) hLs
  refine ⟨hD_res, hL_res, code, code_n, ?_, hnb⟩
  simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
