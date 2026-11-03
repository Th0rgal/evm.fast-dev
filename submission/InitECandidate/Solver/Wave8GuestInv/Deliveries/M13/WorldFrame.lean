import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.Core

/-! W1 typed-cell congruence (`WorldTypedWith` preserved across updates that preserve
typed cells and world globals, with monotonic allocator growth and fresh global buffer
rebindings) and W2 set-table update (`HtabExit` on `"ts+56"` preserves `WorldTypedWith`). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.M13

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Globals relevant to `WorldTypedWith` -/

/-- Globals read by `TablesTyped`, `JournalTyped`, `TriesTypedWith` (excluding `heap_ptr`,
`scratch_ptr`, and content-free `globalBuffers` other than `ws`, `bs`, `ts`, `bo`). -/
def coreWorldGlobals : List String :=
  ["ws", "bs", "ts", "bo", "bal_accounts", "bal_idx_accts", "bal_idx_stor",
   "journal", "journal_cap", "journal_n"]

theorem globN_eq_of_coreKept {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g) :
    globN post "ws" = globN s "ws" ∧
    globN post "bs" = globN s "bs" ∧
    globN post "ts" = globN s "ts" ∧
    globN post "bo" = globN s "bo" ∧
    globN post "bal_accounts" = globN s "bal_accounts" ∧
    globN post "bal_idx_accts" = globN s "bal_idx_accts" ∧
    globN post "bal_idx_stor" = globN s "bal_idx_stor" ∧
    globN post "journal" = globN s "journal" ∧
    globN post "journal_cap" = globN s "journal_cap" ∧
    globN post "journal_n" = globN s "journal_n" :=
  ⟨hg "ws" (by decide), hg "bs" (by decide), hg "ts" (by decide), hg "bo" (by decide),
   hg "bal_accounts" (by decide), hg "bal_idx_accts" (by decide), hg "bal_idx_stor" (by decide),
   hg "journal" (by decide), hg "journal_cap" (by decide), hg "journal_n" (by decide)⟩

/-! ## 2. Congruence of `blockOutObjects`, `balRecords`, `balObjects`, `worldRoleSlots`, `journalRoleSlots`, `nodeExtents` -/

theorem lstOK_congr_of_ivl {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hcell : SameTypedCells s post S Nd) {l : Nat}
    (hb : l + 24 ≤ 2 ^ 64) (hi : (l, 24) ∈ worldTypedIvls s S Nd) :
    LstOK post l ↔ LstOK s l := by
  unfold LstOK
  rw [memW_eq_of_cellHits hcell (by omega) hi ⟨by dsimp only; omega, by dsimp only; omega⟩,
      memW_eq_of_cellHits hcell (by omega) hi ⟨by dsimp only; omega, by dsimp only; omega⟩]

theorem lstObjects_eq_of_ivl {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hcell : SameTypedCells s post S Nd) {l esz : Nat}
    (hb : l + 24 ≤ 2 ^ 64) (hi : (l, 24) ∈ worldTypedIvls s S Nd) :
    lstObjects post l esz = lstObjects s l esz := by
  unfold lstObjects
  rw [memW_eq_of_cellHits hcell (by omega) hi ⟨by dsimp only; omega, by dsimp only; omega⟩,
      memW_eq_of_cellHits hcell (by omega) hi ⟨by dsimp only; omega, by dsimp only; omega⟩]

theorem blockOut_in_fixedObjects {F : Type} {s : PanSemStateFiniteExact 64 F} {i : Ivl}
    (hi : i ∈ blockOutObjects s) : i ∈ fixedObjects s := by
  unfold fixedObjects
  apply List.mem_append_left
  apply List.mem_append_right
  exact hi

theorem bal_in_fixedObjects {F : Type} {s : PanSemStateFiniteExact 64 F} {i : Ivl}
    (hi : i ∈ balObjects s) : i ∈ fixedObjects s := by
  unfold fixedObjects
  exact List.mem_append_right _ hi

theorem blockOutObjects_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hA : ArenaOK s) (hF : FixedTyped s) (hcell : SameTypedCells s post S Nd)
    (hbo : globN post "bo" = globN s "bo") :
    blockOutObjects post = blockOutObjects s := by
  unfold blockOutObjects
  rw [hbo]
  by_cases hb0 : globN s "bo" = 0
  · simp [hb0]
  · have hr : ("bo", 88) ∈ typedRecords := by decide
    have ew24 := memW_typedRec_eq hA hF hcell hr hb0 (k := 24) (by omega)
    have ew32 := memW_typedRec_eq hA hF hcell hr hb0 (k := 32) (by omega)
    have ew40 := memW_typedRec_eq hA hF hcell hr hb0 (k := 40) (by omega)
    have ew56 := memW_typedRec_eq hA hF hcell hr hb0 (k := 56) (by omega)
    have ew72 := memW_typedRec_eq hA hF hcell hr hb0 (k := 72) (by omega)
    have ew80 := memW_typedRec_eq hA hF hcell hr hb0 (k := 80) (by omega)
    have hlst : ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) ≠ 0 →
        memW post (memW s (globN s "bo" + k)) = memW s (memW s (globN s "bo" + k)) ∧
        memW post (memW s (globN s "bo" + k) + 16) = memW s (memW s (globN s "bo" + k) + 16) := by
      intro k hk hp0
      have hmem_bo : (memW s (globN s "bo" + k), 24) ∈ blockOutObjects s := by
        unfold blockOutObjects
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl
        · left; right; simp [hb0, hp0]
        · right; simp [hb0, hp0]
      rcases fixedObject_le_2pow64 hA hF (blockOut_in_fixedObjects hmem_bo) with h0 | hbnd
      · dsimp only at h0; omega
      · dsimp only at hbnd
        have hwti := mem_worldTypedIvls_blockOut (S := S) (Nd := Nd) hmem_bo
        exact ⟨memW_eq_of_cellHits hcell (by omega) hwti ⟨by dsimp only; omega, by dsimp only; omega⟩,
               memW_eq_of_cellHits hcell (by omega) hwti ⟨by dsimp only; omega, by dsimp only; omega⟩⟩
    dsimp only
    rw [ew24, ew32, ew40, ew56, ew72, ew80]
    have h0_eq : memW post 0 = memW s 0 ∧ memW post 16 = memW s 16 :=
      ⟨memW_eq_of_lt_sourceBase hcell (by rw [sourceBase_val]; omega),
       memW_eq_of_lt_sourceBase hcell (by rw [sourceBase_val]; omega)⟩
    have h40_eq :
        memW post (memW s (globN s "bo" + 40)) = memW s (memW s (globN s "bo" + 40)) ∧
        memW post (memW s (globN s "bo" + 40) + 16) = memW s (memW s (globN s "bo" + 40) + 16) := by
      by_cases h40 : memW s (globN s "bo" + 40) = 0
      · rw [h40]; exact h0_eq
      · exact hlst 40 (by simp) h40
    have h72_eq :
        memW post (memW s (globN s "bo" + 72)) = memW s (memW s (globN s "bo" + 72)) ∧
        memW post (memW s (globN s "bo" + 72) + 16) = memW s (memW s (globN s "bo" + 72) + 16) := by
      by_cases h72 : memW s (globN s "bo" + 72) = 0
      · rw [h72]; exact h0_eq
      · exact hlst 72 (by simp) h72
    rw [h40_eq.1, h40_eq.2, h72_eq.1, h72_eq.2]

theorem balRecords_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hT : TablesTyped s S) (hcell : SameTypedCells s post S Nd)
    (hba : globN post "bal_accounts" = globN s "bal_accounts") :
    balRecords post = balRecords s := by
  have heq : ∀ x : PanSemStateFiniteExact 64 F,
      balRecords x = if globN x "bal_accounts" = 0 then [] else htabValues x (globN x "bal_accounts") :=
    fun _ => rfl
  rw [heq, heq, hba]
  split
  · rfl
  · rename_i hne
    have hroot := hT.2.2.2.2.2.2.1 "bal_accounts" (by decide)
    rcases hroot with h0 | hmem
    · exact absurd h0 hne
    · exact htabValues_eq hcell hmem (hT.2.1 _ hmem).1

theorem balRecord_ivl_mem {F : Type} {s : PanSemStateFiniteExact 64 F} {ad : Nat}
    (had : ad ∈ balRecords s) : (ad, 40) ∈ balObjects s := by
  unfold balObjects
  exact List.mem_flatMap.2 ⟨ad, had, by simp⟩

theorem balRecord_lst_ivl_mem {F : Type} {s : PanSemStateFiniteExact 64 F} {ad k : Nat}
    (had : ad ∈ balRecords s) (hk : k ∈ ([16, 24, 32] : List Nat))
    (hnz : memW s (ad + k) ≠ 0) :
    (memW s (ad + k), 24) ∈ balObjects s := by
  unfold balObjects
  refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl <;> simp [lstObjects, hnz]

theorem balRecord_storLst_ivl_mem {F : Type} {s : PanSemStateFiniteExact 64 F} {ad l : Nat}
    (had : ad ∈ balRecords s) (hl : l ∈ htabValues s (memW s ad)) (hnz : l ≠ 0) :
    (l, 24) ∈ balObjects s := by
  unfold balObjects
  refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  exact List.mem_flatMap.2 ⟨l, hl, by simp [lstObjects, hnz]⟩

theorem balObjects_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hA : ArenaOK s) (hT : TablesTyped s S) (hF : FixedTyped s)
    (hcell : SameTypedCells s post S Nd)
    (hba : globN post "bal_accounts" = globN s "bal_accounts") :
    balObjects post = balObjects s := by
  unfold balObjects
  rw [balRecords_eq hT hcell hba]
  apply List.flatMap_congr
  intro ad had
  have had_mem := balRecord_ivl_mem had
  rcases fixedObject_le_2pow64 hA hF (bal_in_fixedObjects had_mem) with h0 | had_bnd
  · dsimp only at h0; omega
  · dsimp only at had_bnd
    have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd) had_mem
    have e0 : memW post ad = memW s ad :=
      memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩
    have e16 : memW post (ad + 16) = memW s (ad + 16) :=
      memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩
    have e24 : memW post (ad + 24) = memW s (ad + 24) :=
      memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩
    have e32 : memW post (ad + 32) = memW s (ad + 32) :=
      memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩
    have hbal := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hl_eq : ∀ (k esz : Nat), k ∈ ([16, 24, 32] : List Nat) →
        lstObjects post (memW s (ad + k)) esz = lstObjects s (memW s (ad + k)) esz := by
      intro k esz hk
      by_cases hk0 : memW s (ad + k) = 0
      · simp [lstObjects, hk0]
      · have hm := balRecord_lst_ivl_mem had hk hk0
        rcases fixedObject_le_2pow64 hA hF (bal_in_fixedObjects hm) with h0 | hbnd
        · dsimp only at h0; omega
        · exact lstObjects_eq_of_ivl hcell hbnd (mem_worldTypedIvls_bal hm)
    have hval_eq : htabValues post (memW s ad) = htabValues s (memW s ad) :=
      htabValues_eq hcell hbal.1 (hT.2.1 _ hbal.1).1
    have hfl : (htabValues s (memW s ad)).flatMap (fun l => lstObjects post l 40) =
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
      apply List.flatMap_congr
      intro l hl
      by_cases hl0 : l = 0
      · simp [lstObjects, hl0]
      · have hm := balRecord_storLst_ivl_mem had hl hl0
        rcases fixedObject_le_2pow64 hA hF (bal_in_fixedObjects hm) with h0 | hbnd
        · dsimp only at h0; omega
        · exact lstObjects_eq_of_ivl hcell hbnd (mem_worldTypedIvls_bal hm)
    rw [e0, e16, e24, e32, hl_eq 16 40 (by simp), hl_eq 24 16 (by simp), hl_eq 32 24 (by simp), hval_eq, hfl]

theorem nodeIvl_eq_of_mem {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hNH : NodeHeap s Nd) (hcell : SameTypedCells s post S Nd) {n : Nat} (hn : n ∈ Nd) :
    memW post n = memW s n ∧ nodeIvl post n = nodeIvl s n := by
  have hmem_ni : nodeIvl s n ∈ nodeExtents s Nd := by
    unfold nodeExtents
    exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
  have hns_pos : 8 ≤ nodeSize (memW s n) := by
    unfold nodeSize; split_ifs <;> omega
  have hin := (hNH.1 n hn).2.2.1
  have hhl : heapLimit ≤ 2 ^ 64 := by rw [heapLimit_val]; norm_num
  have hbnd : n + nodeSize (memW s n) ≤ 2 ^ 64 := le_trans hin.2 hhl
  have heq : memW post n = memW s n :=
    memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_nodeExtents hmem_ni)
      ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
  exact ⟨heq, by simp only [nodeIvl, heq]⟩

theorem nodePath_eq_of_mem {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hNH : NodeHeap s Nd) (hcell : SameTypedCells s post S Nd) {n : Nat} (hn : n ∈ Nd) :
    nodePath post n = nodePath s n := by
  obtain ⟨hk0, hni⟩ := nodeIvl_eq_of_mem hNH hcell hn
  unfold nodePath
  rw [hk0]
  by_cases h12 : memW s n = 1 ∨ memW s n = 2
  · have hns_ge : 56 ≤ nodeSize (memW s n) := by
      unfold nodeSize; rcases h12 with h1 | h2
      · simp [h1]
      · simp [h2]
    have hmem_ni : nodeIvl s n ∈ nodeExtents s Nd := by
      unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
    have hin := (hNH.1 n hn).2.2.1
    have hhl : heapLimit ≤ 2 ^ 64 := by rw [heapLimit_val]; norm_num
    have hbnd : n + nodeSize (memW s n) ≤ 2 ^ 64 := le_trans hin.2 hhl
    have e32 : memW post (n + 32) = memW s (n + 32) :=
      memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_nodeExtents hmem_ni)
        ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
    have e40 : memW post (n + 40) = memW s (n + 40) :=
      memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_nodeExtents hmem_ni)
        ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
    rw [e32, e40]
  · simp [h12]

theorem nodeExtents_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hNH : NodeHeap s Nd) (hcell : SameTypedCells s post S Nd) :
    nodeExtents post Nd = nodeExtents s Nd := by
  unfold nodeExtents
  apply List.flatMap_congr
  intro n hn
  rw [(nodeIvl_eq_of_mem hNH hcell hn).2, nodePath_eq_of_mem hNH hcell hn]

theorem nodeHeap_congr {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hNH : NodeHeap s Nd) (hcell : SameTypedCells s post S Nd)
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr") :
    NodeHeap post Nd := by
  have hhl : heapLimit ≤ 2 ^ 64 := by rw [heapLimit_val]; norm_num
  refine ⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩
  · obtain ⟨hk0, hni⟩ := nodeIvl_eq_of_mem hNH hcell hn
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hNH.1 n hn
    have hmem_ni : nodeIvl s n ∈ nodeExtents s Nd := by
      unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
    have hbnd : (nodeIvl s n).1 + (nodeIvl s n).2 ≤ 2 ^ 64 := le_trans h3.2 hhl
    rw [hk0, hni]
    refine ⟨h1, allocated_mono hh hsc h2, h3,
      (wordsOK_congr_of_ivl hcell hbnd (mem_worldTypedIvls_nodeExtents hmem_ni)).2 h4,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hk2
      have h56 : nodeSize (memW s n) = 56 := by unfold nodeSize; simp [hk2]
      have e48 : memW post (n + 48) = memW s (n + 48) :=
        memW_eq_of_cellHits hcell (by unfold nodeIvl at hbnd; omega)
          (mem_worldTypedIvls_nodeExtents hmem_ni)
          ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
      rw [e48]; exact h5 hk2
    · intro hk3 i hi
      have h176 : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [hk3]
      have ei : memW post (n + 32 + 8 * i) = memW s (n + 32 + 8 * i) :=
        memW_eq_of_cellHits hcell (by unfold nodeIvl at hbnd; omega)
          (mem_worldTypedIvls_nodeExtents hmem_ni)
          ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
      rw [ei]; exact h6 hk3 i hi
    · intro h12
      have hns_ge : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize; rcases h12 with c1 | c2
        · simp [c1]
        · simp [c2]
      have e32 : memW post (n + 32) = memW s (n + 32) :=
        memW_eq_of_cellHits hcell (by unfold nodeIvl at hbnd; omega)
          (mem_worldTypedIvls_nodeExtents hmem_ni)
          ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
      have e40 : memW post (n + 40) = memW s (n + 40) :=
        memW_eq_of_cellHits hcell (by unfold nodeIvl at hbnd; omega)
          (mem_worldTypedIvls_nodeExtents hmem_ni)
          ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
      rw [e32, e40]
      rcases h7 h12 with hz | ⟨hnib, hal, hin, hdisj⟩
      · exact Or.inl hz
      · by_cases hnz : memW s (n + 40) = 0
        · exact Or.inl hnz
        · right
          have hp_mem : nodePath s n ∈ nodeExtents s Nd := by
            unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
          have hp_eq : nodePath s n = (memW s (n + 32), memW s (n + 40)) := by
            unfold nodePath; simp [h12, hnz]
          rw [hp_eq] at hp_mem
          refine ⟨(nibblesOK_congr_of_ivl hcell (le_trans hin.2 hhl)
            (mem_worldTypedIvls_nodeExtents hp_mem)).2 hnib,
            allocated_mono hh hsc hal, hin, fun m hm => ?_⟩
          rw [(nodeIvl_eq_of_mem hNH hcell hm).2]
          exact hdisj m hm
    · have h32 : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
      have e16 : memW post (n + 16) = memW s (n + 16) :=
        memW_eq_of_cellHits hcell (by unfold nodeIvl at hbnd; omega)
          (mem_worldTypedIvls_nodeExtents hmem_ni)
          ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
      rw [e16]; exact h8
    · intro hk1
      have h64 : nodeSize (memW s n) = 64 := by unfold nodeSize; simp [hk1]
      have e56 : memW post (n + 56) = memW s (n + 56) :=
        memW_eq_of_cellHits hcell (by unfold nodeIvl at hbnd; omega)
          (mem_worldTypedIvls_nodeExtents hmem_ni)
          ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
      rw [e56]; exact h9 hk1
    · intro hk3
      have h176 : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [hk3]
      have e168 : memW post (n + 168) = memW s (n + 168) :=
        memW_eq_of_cellHits hcell (by unfold nodeIvl at hbnd; omega)
          (mem_worldTypedIvls_nodeExtents hmem_ni)
          ⟨by unfold nodeIvl; dsimp only; omega, by unfold nodeIvl; dsimp only; omega⟩
      rw [e168]; exact h10 hk3
  · rw [(nodeIvl_eq_of_mem hNH hcell hn).2, (nodeIvl_eq_of_mem hNH hcell hm).2]
    exact hNH.2 n hn m hm hne

theorem recRoles_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hA : ArenaOK s) (hF : FixedTyped s) (hcell : SameTypedCells s post S Nd)
    {g : String} {sz : Nat} (hr : (g, sz) ∈ typedRecords)
    (hg : globN post g = globN s g)
    {ks : List (Nat × String)} (hks : ∀ p ∈ ks, p.1 + 8 ≤ sz) :
    recRoles post g ks = recRoles s g ks := by
  unfold recRoles
  rw [hg]
  split
  · rfl
  · rename_i hne
    apply List.map_congr_left
    intro p hp
    rw [memW_typedRec_eq hA hF hcell hr hne (hks p hp)]

theorem nestRoles_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hA : ArenaOK s) (hT : TablesTyped s S) (hF : FixedTyped s)
    (hcell : SameTypedCells s post S Nd)
    {g r : String} {sz : Nat} (hr : (g, sz) ∈ typedRecords) (hsz : 40 ≤ sz)
    (hg : globN post g = globN s g)
    (hslot : globN s g ≠ 0 → RootIn S (memW s (globN s g + 32))) :
    nestRoles post g r = nestRoles s g r := by
  unfold nestRoles
  rw [hg]
  split
  · rfl
  · rename_i hne
    rw [memW_typedRec_eq hA hF hcell hr hne (by omega)]
    split
    · rfl
    · rename_i htne
      rcases hslot hne with h0 | hmem
      · exact absurd h0 htne
      · rw [htabValues_eq hcell hmem (hT.2.1 _ hmem).1]

theorem worldRoleSlots_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hA : ArenaOK s) (hT : TablesTyped s S) (hF : FixedTyped s)
    (hcell : SameTypedCells s post S Nd)
    (hg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g) :
    worldRoleSlots post = worldRoleSlots s := by
  obtain ⟨ews, ebs, ets, _, eba, ebia, ebis, _, _, _⟩ := globN_eq_of_coreKept hg
  unfold worldRoleSlots
  rw [recRoles_eq hA hF hcell (sz := 40) (by decide) ews (by decide),
      recRoles_eq hA hF hcell (sz := 80) (by decide) ebs (by decide),
      recRoles_eq hA hF hcell (sz := 72) (by decide) ets (by decide),
      eba, ebia, ebis,
      nestRoles_eq hA hT hF hcell (sz := 80) (by decide) (by omega) ebs (hT.2.2.2.2.1 32 (by decide)),
      nestRoles_eq hA hT hF hcell (sz := 72) (by decide) (by omega) ets (hT.2.2.2.2.2.1 32 (by decide)),
      balRecords_eq hT hcell eba]
  congr 1; congr 1
  apply List.flatMap_congr
  intro ad had
  have had_mem := balRecord_ivl_mem had
  rcases fixedObject_le_2pow64 hA hF (bal_in_fixedObjects had_mem) with h0 | had_bnd
  · dsimp only at h0; omega
  · dsimp only at had_bnd
    have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd) had_mem
    rw [memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
        memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]

theorem journalRole_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hA : ArenaOK s) (hF : FixedTyped s) (hcell : SameTypedCells s post S Nd)
    (hts : globN post "ts" = globN s "ts") (t : Nat) :
    journalRole post t = journalRole s t := by
  unfold journalRole
  rw [hts]
  by_cases hz : globN s "ts" = 0
  · simp [hz]
  · have hr : ("ts", 72) ∈ typedRecords := by decide
    rw [memW_typedRec_eq hA hF hcell hr hz (by omega),
        memW_typedRec_eq hA hF hcell hr hz (by omega),
        memW_typedRec_eq hA hF hcell hr hz (by omega),
        memW_typedRec_eq hA hF hcell hr hz (by omega)]

theorem journalRoleSlots_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hA : ArenaOK s) (hJ : JournalTyped s S) (hF : FixedTyped s)
    (hcell : SameTypedCells s post S Nd)
    (hg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g) :
    journalRoleSlots post = journalRoleSlots s := by
  obtain ⟨_, _, ets, _, _, _, _, ej, ejc, ejn⟩ := globN_eq_of_coreKept hg
  unfold journalRoleSlots
  rw [ejn, ej]
  apply List.flatMap_congr
  intro i hi
  rw [List.mem_range] at hi
  have hjcap_pos : 0 < globN s "journal_cap" := by have := hJ.1; omega
  rcases hJ.2.2.1 with h0 | ⟨hal, _⟩
  · omega
  · have hbnd := allocated_le_2pow64 hA hal
    dsimp only at hbnd
    have hwti := mem_worldTypedIvls_journal (s := s) (S := S) (Nd := Nd) (by omega)
    have hlt : 32 * i + 32 ≤ 32 * globN s "journal_cap" := by have := hJ.1; omega
    have e0 : memW post (globN s "journal" + 32 * i) = memW s (globN s "journal" + 32 * i) :=
      memW_eq_of_cellHits hcell (by omega) hwti ⟨by dsimp only; omega, by dsimp only; omega⟩
    have e16 : memW post (globN s "journal" + 32 * i + 16) = memW s (globN s "journal" + 32 * i + 16) :=
      memW_eq_of_cellHits hcell (by omega) hwti ⟨by dsimp only; omega, by dsimp only; omega⟩
    have e24 : memW post (globN s "journal" + 32 * i + 24) = memW s (globN s "journal" + 32 * i + 24) :=
      memW_eq_of_cellHits hcell (by omega) hwti ⟨by dsimp only; omega, by dsimp only; omega⟩
    dsimp only
    rw [e0, e16, e24, journalRole_eq hA hF hcell ets]

/-! ## 3. Master W1 theorem: `WorldTypedWith` preserved across untyped/fresh writes -/

/-- Master W1 congruence: if typed cells are preserved, core world globals are preserved,
`heap_ptr` grows, `scratch_ptr` shrinks/stays, and any modified `globalBuffers` global was rebound
either to the same value or to a fresh aligned heap block (pairwise disjoint among newly rebound
globals and inside `[heap_ptr s, heap_ptr post)`), then `WorldTypedWith post S Nd` and
`OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd)`. -/
theorem worldTypedWith_congr_w1 {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaReady s) (hApost : ArenaReady post)
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g)
    (hcell : SameTypedCells s post S Nd)
    (hWT : WorldTypedWith s S Nd)
    (hbuf : FixedTyped post ∧
      (∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o = (0, 0) ∨
        Inside o (globN s "heap_ptr") (globN post "heap_ptr"))) :
    WorldTypedWith post S Nd ∧
    OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd) := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨ews, ebs, ets, ebo, eba, ebia, ebis, ej, ejc, ejn⟩ := globN_eq_of_coreKept hg
  have hbo_eq := blockOutObjects_eq hAs.2 hF hcell ebo
  have hbal_eq := balObjects_eq hAs.2 hT hF hcell eba
  have hne_eq := nodeExtents_eq hTr.1 hcell
  have hwrs_eq := worldRoleSlots_eq hAs.2 hT hF hcell hg
  have hjrs_eq := journalRoleSlots_eq hAs.2 hJ hF hcell hg
  -- Every interval in S.flatMap (htabFootprint s) or nodeExtents s Nd was allocated in s,
  -- hence disjoint from [heap_ptr s, heap_ptr post) because ArenaOK s ∧ ArenaOK post!
  have hdisj_fresh : ∀ i : Ivl, Allocated s i →
      ∀ o : Ivl, Inside o (globN s "heap_ptr") (globN post "heap_ptr") → Disj i o := by
    intro i hi o ho
    rcases hi with ⟨_, hi2⟩ | ⟨hi1, _⟩
    · exact Or.inr (Or.inr (Or.inl (le_trans hi2 ho.1)))
    · have hp_lim := hApost.2.2.1
      have hs_fr := hAs.2.2.2.1
      have hs_gap := hAs.2.2.2.2.1
      rw [heapLimit_val] at hp_lim
      rw [scratchStart_val] at hs_fr
      have ho2 : o.1 + o.2 ≤ 2952790016 := le_trans ho.2 hp_lim
      have hi_lo : 2952790016 ≤ i.1 := le_trans hs_fr (le_trans hs_gap hi1)
      exact Or.inr (Or.inr (Or.inr (le_trans ho2 hi_lo)))
  have hbrec_eq := balRecords_eq hT hcell eba
  have hT_post : TablesTyped post S := by
    obtain ⟨hnd, htwf, htpw, hws, hbs, hts, hgr, hbs32, hts32, hbal_ok, hbo_ok, hroles⟩ := hT
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      have hW := (htwf t ht).1
      rw [htabFootprint_eq hcell ht hW]
      refine ⟨htabWF_congr hcell ht hW, fun i hi => ?_⟩
      obtain ⟨hal, hdf⟩ := (htwf t ht).2 i hi
      refine ⟨allocated_mono hh hsc hal, fun j hj => ?_⟩
      rcases hbuf.2 j hj with hj_old | rfl | hj_fr
      · exact hdf j hj_old
      · exact Or.inr (Or.inl rfl)
      · exact hdisj_fresh i hal j hj_fr
    · intro t ht u hu htu i hi j hj
      rw [htabFootprint_eq hcell ht (htwf t ht).1] at hi
      rw [htabFootprint_eq hcell hu (htwf u hu).1] at hj
      exact htpw t ht u hu htu i hi j hj
    · intro k hk hnz
      rw [ews] at hnz ⊢
      have hk_le : k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [memW_typedRec_eq hAs.2 hF hcell (by decide) hnz hk_le]
      exact hws k hk hnz
    · intro k hk hnz
      rw [ebs] at hnz ⊢
      have hk_le : k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [memW_typedRec_eq hAs.2 hF hcell (by decide) hnz hk_le]
      exact hbs k hk hnz
    · intro k hk hnz
      rw [ets] at hnz ⊢
      have hk_le : k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [memW_typedRec_eq hAs.2 hF hcell (by decide) hnz hk_le]
      exact hts k hk hnz
    · intro g hg_mem
      simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg_mem
      rcases hg_mem with rfl | rfl | rfl
      · rw [eba]; exact hgr "bal_accounts" (by decide)
      · rw [ebia]; exact hgr "bal_idx_accts" (by decide)
      · rw [ebis]; exact hgr "bal_idx_stor" (by decide)
    · intro hnz hmem
      rw [ebs] at hnz hmem ⊢
      rw [memW_typedRec_eq hAs.2 hF hcell (sz := 80) (by decide) hnz (by omega)] at hmem ⊢
      exact htabValuesIn_congr hcell hmem (htwf _ hmem).1 (fun _ h => h) (hbs32 hnz hmem)
    · intro hnz hmem
      rw [ets] at hnz hmem ⊢
      rw [memW_typedRec_eq hAs.2 hF hcell (sz := 72) (by decide) hnz (by omega)] at hmem ⊢
      exact htabValuesIn_congr hcell hmem (htwf _ hmem).1 (fun _ h => h) (hts32 hnz hmem)
    · rw [hbrec_eq]
      intro ad had
      have had_mem := balRecord_ivl_mem had
      rcases fixedObject_le_2pow64 hAs.2 hF (bal_in_fixedObjects had_mem) with h0 | had_bnd
      · dsimp only at h0; omega
      · dsimp only at had_bnd
        have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd) had_mem
        obtain ⟨c1, c2, c3, c4⟩ := hbal_ok ad had
        have e0 : memW post ad = memW s ad :=
          memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩
        have e8 : memW post (ad + 8) = memW s (ad + 8) :=
          memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩
        rw [e0, e8]
        refine ⟨c1, c2, ?_, ?_⟩
        · intro k hk
          have hk_le : k + 8 ≤ 40 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl | rfl <;> omega
          have ek : memW post (ad + k) = memW s (ad + k) :=
            memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩
          rw [ek]
          by_cases hk0 : memW s (ad + k) = 0
          · have hck := c3 k hk
            unfold LstOK at hck ⊢
            rw [hk0, memW_eq_of_lt_sourceBase hcell (by rw [sourceBase_val]; omega),
                memW_eq_of_lt_sourceBase hcell (by rw [sourceBase_val]; omega)]
            simpa [hk0] using hck
          · have hm := balRecord_lst_ivl_mem had hk hk0
            rcases fixedObject_le_2pow64 hAs.2 hF (bal_in_fixedObjects hm) with h0 | hbnd
            · dsimp only at h0; omega
            · exact (lstOK_congr_of_ivl hcell hbnd (mem_worldTypedIvls_bal hm)).2 (c3 k hk)
        · rw [htabValues_eq hcell c1 (htwf _ c1).1]
          intro l hl
          by_cases hl0 : l = 0
          · subst hl0
            have hcl := c4 0 hl
            unfold LstOK at hcl ⊢
            rw [memW_eq_of_lt_sourceBase hcell (by rw [sourceBase_val]; omega),
                memW_eq_of_lt_sourceBase hcell (by rw [sourceBase_val]; omega)]
            exact hcl
          · have hm := balRecord_storLst_ivl_mem had hl hl0
            rcases fixedObject_le_2pow64 hAs.2 hF (bal_in_fixedObjects hm) with h0 | hbnd
            · dsimp only at h0; omega
            · exact (lstOK_congr_of_ivl hcell hbnd (mem_worldTypedIvls_bal hm)).2 (c4 l hl)
    · rw [ebo]
      intro hnz k hk hp0
      have hk_le : k + 8 ≤ 88 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      have ek := memW_typedRec_eq hAs.2 hF hcell (sz := 88) (by decide) hnz hk_le
      rw [ek] at hp0 ⊢
      have hmem_bo : (memW s (globN s "bo" + k), 24) ∈ blockOutObjects s := by
        unfold blockOutObjects
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> simp [hnz, hp0]
      rcases fixedObject_le_2pow64 hAs.2 hF (blockOut_in_fixedObjects hmem_bo) with h0 | hbnd
      · dsimp only at h0; omega
      · exact (lstOK_congr_of_ivl hcell hbnd (mem_worldTypedIvls_blockOut hmem_bo)).2 (hbo_ok hnz k hk hp0)
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjrs_eq]
      refine ⟨fun a ha => ?_, hroles.2⟩
      obtain ⟨haS, hkl⟩ := hroles.1 a ha
      have htb := ((htwf a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
      rw [htab_hdr_eq hcell haS htb 0 (by omega)]
      exact ⟨haS, hkl⟩
  have hJ_post : JournalTyped post S := by
    obtain ⟨hj1, hj2, hj3, hj4⟩ := hJ
    unfold JournalTyped
    rw [ejn, ejc, ej]
    refine ⟨hj1, hj2, ?_, ?_⟩
    · by_cases hjc0 : globN s "journal_cap" = 0
      · exact Or.inl hjc0
      · rcases hj3 with hz | ⟨hal, hw⟩
        · exact Or.inl hz
        · exact Or.inr ⟨allocated_mono hh hsc hal,
            (wordsOK_congr_of_ivl hcell (allocated_le_2pow64 hAs.2 hal) (mem_worldTypedIvls_journal hjc0)).2 hw⟩
    · intro i hi
      have hjc0 : globN s "journal_cap" ≠ 0 := by omega
      rcases hj3 with hz | ⟨hal, _⟩
      · omega
      · have hbnd := allocated_le_2pow64 hAs.2 hal
        dsimp only at hbnd
        have e0 : memW post (globN s "journal" + 32 * i) = memW s (globN s "journal" + 32 * i) :=
          memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_journal hjc0)
            ⟨by dsimp only; omega, by dsimp only; omega⟩
        rw [e0]; exact hj4 i hi
  have hTr_post : TriesTypedWith post S Nd := by
    obtain ⟨hNH, hndisj, hws_tr⟩ := hTr
    refine ⟨nodeHeap_congr hNH hcell hh hsc, ?_, ?_⟩
    · rw [hne_eq]
      intro o ho
      have ho_alloc : o = (0, 0) ∨ Allocated s o := by
        unfold nodeExtents at ho
        obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
        rcases hno with rfl | rfl
        · exact Or.inr (hNH.1 n hn).2.1
        · unfold nodePath
          split
          · rename_i hcond
            rcases (hNH.1 n hn).2.2.2.2.2.2.1 hcond.1 with h0 | ⟨_, hal, _⟩
            · exact absurd h0 hcond.2
            · exact Or.inr hal
          · exact Or.inl rfl
      refine ⟨fun t ht i hi => ?_, fun j hj => ?_⟩
      · rw [htabFootprint_eq hcell ht (hT.2.1 t ht).1] at hi
        exact (hndisj o ho).1 t ht i hi
      · rcases hbuf.2 j hj with hj_old | rfl | hj_fr
        · exact (hndisj o ho).2 j hj_old
        · exact Or.inr (Or.inl rfl)
        · rcases ho_alloc with rfl | hal
          · exact Or.inl rfl
          · exact hdisj_fresh o hal j hj_fr
    · rw [ews]
      intro hws_nz
      have e24 := memW_typedRec_eq hAs.2 hF hcell (sz := 40) (by decide) hws_nz (k := 24) (by omega)
      have e32 := memW_typedRec_eq hAs.2 hF hcell (sz := 40) (by decide) hws_nz (k := 32) (by omega)
      rw [e24, e32]
      obtain ⟨hr24, hr32⟩ := hws_tr hws_nz
      refine ⟨hr24, fun htS i hi => ?_⟩
      have hW32 := (hT.2.1 _ htS).1
      have hcnt32 := htabCount_le_ncap hW32
      have htb32 := (hW32.1 (memW s (globN s "ws" + 32), 88) (by simp [htabFootprint])).1
      rw [htab_hdr_eq hcell htS htb32 3 (by omega)] at hi
      rw [htab_hdr_eq hcell htS htb32 5 (by omega), htab_hdr_eq hcell htS htb32 6 (by omega)]
      have hfp3 : (hdr s (memW s (globN s "ws" + 32)) 6, (hdr s (memW s (globN s "ws" + 32)) 10 + 1) * 8) ∈
          htabFootprint s (memW s (globN s "ws" + 32)) := by simp [htabFootprint]
      have hob := (hW32.1 _ hfp3).1
      have h264 : heapEnd ≤ 2 ^ 64 := by rw [heapEnd_val]; norm_num
      have ho_eq : memW post (hdr s (memW s (globN s "ws" + 32)) 6 + 8 * i) =
          memW s (hdr s (memW s (globN s "ws" + 32)) 6 + 8 * i) :=
        memW_eq_of_cellHits hcell (by have := le_trans hob.2 h264; omega)
          (mem_worldTypedIvls_htab htS hfp3) ⟨by dsimp only; omega, by dsimp only; omega⟩
      rw [ho_eq, nodeF_eq_of_lt hcell htS hW32 (htabOrder_entry_le_ncap hW32 hi) (by omega)]
      exact hr32 htS i hi
  refine ⟨⟨hT_post, hJ_post, hbuf.1, hTr_post⟩, ?_⟩
  -- OwnedGrows:
  intro o ho
  unfold worldOwned at ho
  simp only [List.mem_append] at ho
  rcases ho with (ho_htab | ho_fix) | ho_nd
  · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.1 ho_htab
    rw [htabFootprint_eq hcell ht (hT.2.1 t ht).1] at hi
    refine Or.inr (Or.inl ⟨o, ?_, le_refl _, le_refl _⟩)
    unfold worldOwned
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, ht, hi⟩))
  · rcases hbuf.2 o ho_fix with ho_old | rfl | ho_fr
    · refine Or.inr (Or.inl ⟨o, ?_, le_refl _, le_refl _⟩)
      unfold worldOwned
      exact List.mem_append_left _ (List.mem_append_right _ ho_old)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ho_fr)
  · rw [hne_eq] at ho_nd
    refine Or.inr (Or.inl ⟨o, ?_, le_refl _, le_refl _⟩)
    unfold worldOwned
    exact List.mem_append_right _ ho_nd

theorem fixedObjects_eq_of_nonHeapGlobalsKept {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat}
    (hAs : ArenaOK s) (hT : TablesTyped s S) (hF : FixedTyped s)
    (hcell : SameTypedCells s post S Nd)
    (hglob : ∀ name, name ≠ "heap_ptr" → name ≠ "scratch_ptr" → name ≠ "frame_mem_ptr" →
      s.globals.lookup (ofString name) = post.globals.lookup (ofString name)) :
    fixedObjects post = fixedObjects s := by
  have hg : ∀ name, name ≠ "heap_ptr" → name ≠ "scratch_ptr" → name ≠ "frame_mem_ptr" →
      globN post name = globN s name :=
    fun n h1 h2 h3 => (globN_eq_of_lookup_eq (hglob n h1 h2 h3)).symm
  unfold fixedObjects
  rw [blockOutObjects_eq hAs hF hcell (hg "bo" (by decide) (by decide) (by decide)),
      balObjects_eq hAs hT hF hcell (hg "bal_accounts" (by decide) (by decide) (by decide)),
      hg "journal" (by decide) (by decide) (by decide),
      hg "journal_cap" (by decide) (by decide) (by decide)]
  congr 3
  apply List.map_congr_left
  intro gn hgn
  have hne : gn.1 ≠ "heap_ptr" ∧ gn.1 ≠ "scratch_ptr" ∧ gn.1 ≠ "frame_mem_ptr" := by
    revert gn hgn; decide
  rw [hg gn.1 hne.1 hne.2.1 hne.2.2]

theorem wordsOK_of_allocated {F : Type} {post : PanSemStateFiniteExact 64 F}
    (hApost : ArenaReady post) {i : Ivl}
    (hal : Allocated post i) (h1 : i.1 % 8 = 0) (h2 : i.2 % 8 = 0) :
    WordsOK post i := by
  have hlo : sourceBase ≤ i.1 := by
    rcases hal with ⟨hl, _⟩ | ⟨hl, _⟩
    · exact hl
    · have := hApost.2.2.2.1; have := hApost.2.2.2.2.1
      rw [sourceBase_val]; rw [scratchStart_val] at *; omega
  have hhi : i.1 + i.2 ≤ heapEnd := by
    rcases hal with ⟨_, hr⟩ | ⟨_, hr⟩
    · have := hApost.2.2.1; rw [heapLimit_val] at this; rw [heapEnd_val]; omega
    · rw [scratchEnd_val] at hr; rw [heapEnd_val]; omega
  exact wordsOK_of_inside_heap post hApost.1.memaddrs i.1 i.2 h1 h2 hlo hhi

theorem fixedTyped_of_eq {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hApost : ArenaReady post) (hF : FixedTyped s)
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hfeq : fixedObjects post = fixedObjects s) :
    FixedTyped post := by
  unfold FixedTyped
  rw [hfeq]
  refine ⟨fun i hi => ?_, hF.2⟩
  rcases hF.1 i hi with h0 | ⟨hal, hw⟩
  · exact Or.inl h0
  · have hal' := allocated_mono hh hsc hal
    exact Or.inr ⟨hal', wordsOK_of_allocated hApost hal' hw.1 hw.2.1⟩

/-! ### Deriving `SameTypedCells` from `ByteFrameOutside` -/

theorem allocated_disj_heapFree {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {i : Ivl} (hi : Allocated s i) : Disj i (heapFree s) := by
  unfold heapFree
  rcases hi with ⟨_, hi2⟩ | ⟨hi1, _⟩
  · exact Or.inr (Or.inr (Or.inl hi2))
  · have hlim := hA.2.1
    have hfr := hA.2.2.1
    have hgap := hA.2.2.2.1
    rw [heapLimit_val] at hlim ⊢; rw [scratchStart_val] at hfr
    exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))

theorem allocated_disj_freeGap {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {i : Ivl} (hi : Allocated s i) : Disj i (freeGap s) := by
  unfold freeGap
  rcases hi with ⟨_, hi2⟩ | ⟨hi1, _⟩
  · have hlim := hA.2.1
    have hfr := hA.2.2.1
    rw [heapLimit_val] at hlim; rw [scratchStart_val] at hfr
    exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
  · have hgap := hA.2.2.2.1
    exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))

theorem worldTypedIvls_allocated {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hWT : WorldTypedWith s S Nd) {i : Ivl} (hi : i ∈ worldTypedIvls s S Nd) :
    i.2 = 0 ∨ Allocated s i := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  unfold worldTypedIvls at hi
  simp only [List.mem_append] at hi
  rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
  · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
    exact Or.inr (((hT.2.1 t ht).2 i hfp).1)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
    rcases hF.1 _ (typedRec_in_fixedObjects s hr) with h0 | ⟨hal, _⟩
    · exact Or.inl h0
    · exact Or.inr hal
  · simp only [List.mem_singleton] at h3
    subst h3
    by_cases hjc0 : globN s "journal_cap" = 0
    · exact Or.inl (by dsimp only; omega)
    · rcases hJ.2.2.1 with h0 | ⟨hal, _⟩
      · exact absurd h0 hjc0
      · exact Or.inr (by simpa [hjc0] using hal)
  · rcases hF.1 i (blockOut_in_fixedObjects h4) with h0 | ⟨hal, _⟩
    · exact Or.inl h0
    · exact Or.inr hal
  · rcases hF.1 i (bal_in_fixedObjects h5) with h0 | ⟨hal, _⟩
    · exact Or.inl h0
    · exact Or.inr hal
  · unfold nodeExtents at h6
    obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 h6
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
    rcases hno with rfl | rfl
    · exact Or.inr (hTr.1.1 n hn).2.1
    · unfold nodePath
      split
      · rename_i hcond
        rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hcond.1 with h0 | ⟨_, hal, _⟩
        · exact absurd h0 hcond.2
        · exact Or.inr hal
      · exact Or.inl rfl


/-! ## 1. `ByteRegionEffect`: byte-accurate and cell-accurate write frame -/

structure ByteRegionEffect {F : Type} (s post : PanSemStateFiniteExact 64 F) (Rl : List Ivl) : Prop where
  code       : post.code = s.code
  memaddrs   : post.memaddrs = s.memaddrs
  shMemaddrs : post.shMemaddrs = s.shMemaddrs
  baseAddr   : post.baseAddr = s.baseAddr
  be         : post.be = s.be
  globals    : post.globals = s.globals
  out_dom    : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a
  cell_frame : ∀ a : BitVec 64, (∀ i ∈ Rl, ¬ CellHits a.toNat i) → post.memory a = s.memory a
  byte_frame : ∀ b : Nat, b < 2 ^ 64 → (∀ i ∈ Rl, ¬ InIvl b i) → memB post b = memB s b

theorem ByteRegionEffect.refl {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    ByteRegionEffect s s Rl :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem ByteRegionEffect.with_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} (h : ByteRegionEffect s post Rl)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ByteRegionEffect s { post with locals := L, clock := k } Rl :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals,
   h.out_dom, h.cell_frame, h.byte_frame⟩

theorem ByteRegionEffect.trans {F : Type} {a b c : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h1 : ByteRegionEffect a b Rl) (h2 : ByteRegionEffect b c Rl) :
    ByteRegionEffect a c Rl := by
  refine ⟨h2.code.trans h1.code, h2.memaddrs.trans h1.memaddrs,
    h2.shMemaddrs.trans h1.shMemaddrs, h2.baseAddr.trans h1.baseAddr,
    h2.be.trans h1.be, h2.globals.trans h1.globals, ?_, ?_, ?_⟩
  · intro x hx
    have hxb : ¬ b.memaddrs x := by rw [h1.memaddrs]; exact hx
    rw [h2.out_dom x hxb, h1.out_dom x hx]
  · intro x hx
    rw [h2.cell_frame x hx, h1.cell_frame x hx]
  · intro x hx hno
    rw [h2.byte_frame x hx hno, h1.byte_frame x hx hno]

theorem ByteRegionEffect.mono {F : Type} {s post : PanSemStateFiniteExact 64 F} {R1 R2 : List Ivl}
    (h : ByteRegionEffect s post R1)
    (hsub : ∀ i ∈ R1, ∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) :
    ByteRegionEffect s post R2 := by
  refine ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals, h.out_dom, ?_, ?_⟩
  · intro a ha
    apply h.cell_frame a
    intro i hi hch
    obtain ⟨hc1, hc2⟩ := hch
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi
    exact ha j hj ⟨by omega, by omega⟩
  · intro b hb hno
    apply h.byte_frame b hb
    intro i hi hbi
    obtain ⟨hb1, hb2⟩ := hbi
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi
    exact hno j hj ⟨by omega, by omega⟩

/-! ### `panGetByteHOL` / `panSetByteHOL` disjoint-byte preservation -/

private theorem pow_div_low (x y z K J : Nat) (_hy : y < 256) (_hz : z < 2 ^ K) (hJK : J + 8 ≤ K) :
    (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ J % 256 = z / 2 ^ J % 256 := by
  have hpJ : 0 < 2 ^ J := Nat.two_pow_pos J
  have hdK : 2 ^ K = 2 ^ (K - J - 8) * (256 * 2 ^ J) := by
    have hk_eq : K = (K - J - 8) + 8 + J := by omega
    conv_lhs => rw [hk_eq]
    rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.mul_assoc]
  have hdK8 : 2 ^ (K + 8) = 2 ^ (K - J) * (256 * 2 ^ J) := by
    have hk_eq : K + 8 = (K - J) + 8 + J := by omega
    conv_lhs => rw [hk_eq]
    rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.mul_assoc]
  have h1 : x * 2 ^ (K + 8) + y * 2 ^ K + z =
      z + ((x * 2 ^ (K - J) + y * 2 ^ (K - J - 8)) * 256) * 2 ^ J := by
    rw [hdK, hdK8, ← Nat.mul_assoc x, ← Nat.mul_assoc y, ← Nat.add_mul, ← Nat.mul_assoc]
    omega
  rw [h1, Nat.add_mul_div_right _ _ hpJ]
  omega

private theorem pow_div_high (x y z K J : Nat) (hy : y < 256) (hz : z < 2 ^ K) (hKJ : K + 8 ≤ J) :
    (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ J % 256 =
      (x * 2 ^ (K + 8)) / 2 ^ J % 256 := by
  have hyz : y * 2 ^ K + z < 2 ^ (K + 8) := by
    have : y * 2 ^ K ≤ 255 * 2 ^ K := Nat.mul_le_mul_right _ (by omega)
    have h2 : 255 * 2 ^ K + 2 ^ K = 2 ^ (K + 8) := by
      rw [Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide]; omega
    omega
  have hdJ : 2 ^ J = 2 ^ (K + 8) * 2 ^ (J - (K + 8)) := by
    have hj_eq : J = (K + 8) + (J - (K + 8)) := by omega
    conv_lhs => rw [hj_eq]
    rw [Nat.pow_add]
  have hpK8 : 0 < 2 ^ (K + 8) := Nat.two_pow_pos _
  have hsum : x * 2 ^ (K + 8) + y * 2 ^ K + z = (y * 2 ^ K + z) + x * 2 ^ (K + 8) := by omega
  rw [hsum, hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_right _ _ hpK8, Nat.div_eq_of_lt hyz, Nat.zero_add,
    Nat.mul_div_cancel _ hpK8]

theorem panGetByte_panSetByte_ne (addr' addr : BitVec 64) (b : UInt8) (cell : BitVec 64) (be : Bool)
    (hal : panByteAlignHOL addr' = panByteAlignHOL addr) (hne : addr' ≠ addr) :
    panGetByteHOL addr' (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be) be =
      panGetByteHOL addr' cell be := by
  have hb8 : b.toNat < 256 := b.toNat_lt_size
  have hset_nat := panSetByteHOL_toNat (width := 64) (by decide) addr cell b be
  have h256_pow : ∀ a : BitVec 64,
      (256 : Nat) ^ (if be then 8 - 1 - a.toNat % 8 else a.toNat % 8) = 2 ^ byteBitIndex a be := by
    intro a
    rw [pow256_eq_two_pow_mul]
    cases be <;> simp [byteBitIndex]
  have hmod_ne : addr'.toNat % 8 ≠ addr.toNat % 8 := by
    intro hmeq
    apply hne
    apply BitVec.eq_of_toNat_eq
    have ha1 := panByteAlign_toNat64 addr'
    have ha2 := panByteAlign_toNat64 addr
    rw [hal] at ha1
    omega
  have hidx_sep : byteBitIndex addr' be + 8 ≤ byteBitIndex addr be ∨
      byteBitIndex addr be + 8 ≤ byteBitIndex addr' be := by
    have hm1 : addr'.toNat % 8 < 8 := by omega
    have hm2 : addr.toNat % 8 < 8 := by omega
    cases be <;> simp only [byteBitIndex, Bool.false_eq_true, if_true, if_false] <;> omega
  simp only [panGetByteHOL]
  apply congrArg UInt8.ofNat
  change (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
      256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256 =
    cell.toNat / 256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256
  rw [hset_nat, h256_pow addr']
  rcases hidx_sep with hlow | hhigh
  · rw [pow_div_low _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hlow]
    have hc_eq : 2 ^ byteBitIndex addr be =
        (2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8)) * 256) *
          2 ^ byteBitIndex addr' be := by
      have hk_eq : byteBitIndex addr be =
          (byteBitIndex addr be - (byteBitIndex addr' be + 8)) + 8 + byteBitIndex addr' be := by omega
      conv_lhs => rw [hk_eq]
      rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide]
    have hcell_eq : cell.toNat =
        cell.toNat % 2 ^ byteBitIndex addr be +
        (((cell.toNat / 2 ^ byteBitIndex addr be) *
          2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8))) * 256) *
          2 ^ byteBitIndex addr' be := by
      have hdm := (Nat.div_add_mod cell.toNat (2 ^ byteBitIndex addr be)).symm
      rw [Nat.mul_comm (2 ^ byteBitIndex addr be)] at hdm
      have hmul : (cell.toNat / 2 ^ byteBitIndex addr be) * 2 ^ byteBitIndex addr be =
          (((cell.toNat / 2 ^ byteBitIndex addr be) *
            2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8))) * 256) *
            2 ^ byteBitIndex addr' be := by
        rw [hc_eq, ← Nat.mul_assoc, ← Nat.mul_assoc]
      rw [hmul] at hdm
      omega
    conv_rhs => rw [hcell_eq]
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]
    omega
  · rw [pow_div_high _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hhigh]
    have hdJ : 2 ^ byteBitIndex addr' be =
        2 ^ (byteBitIndex addr be + 8) * 2 ^ (byteBitIndex addr' be - (byteBitIndex addr be + 8)) := by
      have hj_eq : byteBitIndex addr' be =
          (byteBitIndex addr be + 8) + (byteBitIndex addr' be - (byteBitIndex addr be + 8)) := by omega
      conv_lhs => rw [hj_eq]
      rw [Nat.pow_add]
    have hpK8 : 0 < 2 ^ (byteBitIndex addr be + 8) := Nat.two_pow_pos _
    rw [hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hpK8]

theorem ByteRegionEffect.of_storeByte {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {Rl : List Ivl}
    (hrun : evaluateHOLFiniteState s (.storeByte dst val) = (none, post))
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
        some (.val (.word addr)) →
      s.memaddrs (panByteAlignHOL addr) →
      ∃ i ∈ Rl, i.1 ≤ addr.toNat ∧ addr.toNat < i.1 + i.2) :
    ByteRegionEffect s post Rl ∧ post.locals = s.locals := by
  rw [evaluateHOLFiniteState_storeByte] at hrun
  revert hrun
  rcases hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with
    _ | dv
  · simp
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with
        _ | vv
      · simp
      · rcases vv with ⟨⟨v⟩⟩ | _ | _
        · dsimp only
          split
          · rename_i m' hst
            unfold panMemStoreByteWord8HOL at hst
            dsimp only at hst
            cases hm : s.memory (panByteAlignHOL addr) with
            | word cell =>
              have hcell : (s.memory (panByteAlignHOL addr)).1 = cell := by rw [hm]
              rw [hcell] at hst
              by_cases hdom : s.memaddrs (panByteAlignHOL addr)
              · simp only [hdom, ↓reduceIte, Option.some.injEq] at hst
                subst hst
                intro hrun
                injection hrun with _ hpost
                subst hpost
                obtain ⟨i, hi, h1, h2⟩ := hin addr hdst hdom
                have hal : (panByteAlignHOL addr).toNat = addr.toNat / 8 * 8 := panByteAlign_toNat64 addr
                refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩, rfl⟩
                · intro a hna
                  dsimp only
                  have hne : a ≠ panByteAlignHOL addr := by rintro rfl; exact hna hdom
                  rw [if_neg hne]
                · intro a hna
                  dsimp only
                  have hne : a ≠ panByteAlignHOL addr := by
                    rintro rfl
                    exact hna i hi ⟨by rw [hal]; omega, by rw [hal]; omega⟩
                  rw [if_neg hne]
                · intro b hb hno
                  unfold memB
                  dsimp only
                  by_cases hal_eq : panByteAlignHOL (BitVec.ofNat 64 b) = panByteAlignHOL addr
                  · rw [if_pos hal_eq]
                    have hrhs : (s.memory (panByteAlignHOL (BitVec.ofNat 64 b))).1 = cell := by
                      rw [hal_eq, hcell]
                    change (panGetByteHOL (BitVec.ofNat 64 b)
                        (panSetByteHOL addr (BitVec.ofNat 64 (BitVec.ofNat 8 v.toNat).toNat) cell s.be) s.be).toNat =
                      (panGetByteHOL (BitVec.ofNat 64 b) (s.memory (panByteAlignHOL (BitVec.ofNat 64 b))).1 s.be).toNat
                    rw [hrhs]
                    have hne : BitVec.ofNat 64 b ≠ addr := by
                      intro heq
                      have hbt : (BitVec.ofNat 64 b).toNat = b := Nat.mod_eq_of_lt hb
                      rw [heq] at hbt
                      subst hbt
                      exact hno i hi ⟨h1, h2⟩
                    let byte8 : UInt8 := UInt8.ofNat (BitVec.ofNat 8 v.toNat).toNat
                    have hbyte8 : byte8.toNat = (BitVec.ofNat 8 v.toNat).toNat := by
                      simp [byte8]
                    rw [← hbyte8, panGetByte_panSetByte_ne _ _ byte8 cell s.be hal_eq hne]
                  · rw [if_neg hal_eq]
              · simp [hdom] at hst
          · simp
        · simp
        · simp
    · simp
    · simp

theorem ByteRegionEffect.of_store_word {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {Rl : List Ivl}
    (hma_ord : s.memaddrs = ordinaryDomain)
    (hrun : evaluateHOLFiniteState s (.store dst val) = (none, post))
    (hval_word : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
        some (.val (.word addr)) →
      s.memaddrs addr →
      ∃ i ∈ Rl, i.1 ≤ addr.toNat ∧ addr.toNat + 8 ≤ i.1 + i.2) :
    ByteRegionEffect s post Rl ∧ post.locals = s.locals := by
  rw [evaluateHOLFiniteState_store] at hrun
  revert hrun
  rcases hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with
    _ | dv
  · simp
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with
        _ | v
      · simp
      · obtain ⟨w, rfl⟩ := hval_word v hv
        dsimp only
        split
        · rename_i m' hst
          unfold flattenHOL at hst
          unfold panMemStoresHOL at hst
          unfold panMemStoreHOL at hst
          by_cases hdom : s.memaddrs addr
          · simp only [hdom, ↓reduceIte, panMemStoresHOL, Option.some.injEq] at hst
            subst hst
            intro hrun
            injection hrun with _ hpost
            subst hpost
            obtain ⟨i, hi, h1, h2⟩ := hin addr hdst hdom
            have ha8 : addr.toNat % 8 = 0 := by
              have hdom' := hma_ord ▸ hdom
              rw [ordinaryDomain_iff] at hdom'; exact hdom'.2.2
            refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩, rfl⟩
            · intro a hna
              dsimp only
              have hne : a ≠ addr := by rintro rfl; exact hna hdom
              rw [if_neg hne]
            · intro a hna
              dsimp only
              have hne : a ≠ addr := by
                rintro rfl
                exact hna i hi ⟨by omega, by omega⟩
              rw [if_neg hne]
            · intro b hb hno
              unfold memB
              dsimp only
              have hne : panByteAlignHOL (BitVec.ofNat 64 b) ≠ addr := by
                intro heq
                have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
                  rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
                rw [heq] at hal_b
                exact hno i hi ⟨by omega, by omega⟩
              rw [if_neg hne]
          · simp [hdom] at hst
        · simp
    · simp
    · simp

/-! ## 2. Lifting `ByteRegionEffect` to `WorldStep` -/

theorem untypedGlobalBuf_disj_worldTypedIvls {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hWT : WorldTypedWith s S Nd) {g : String} {sz : Nat}
    (hgb : (g, sz) ∈ globalBuffers)
    (huntyped : g ∉ ["ws", "bs", "ts", "bo"]) :
    ∀ i ∈ worldTypedIvls s S Nd,
      i.2 = 0 ∨ Disj (globN s g, if globN s g = 0 then 0 else sz) i := by
  by_cases hg0 : globN s g = 0
  · intro i _; simp [hg0]; exact Or.inr (Or.inl rfl)
  · obtain ⟨hT, hJ, hF, hTr⟩ := hWT
    have hsz : (if globN s g = 0 then 0 else sz) = sz := if_neg hg0
    rw [hsz]
    have hmem_fix : (globN s g, sz) ∈ fixedObjects s := by
      have : (globN s g, if globN s g = 0 then 0 else sz) ∈ fixedObjects s := by
        unfold fixedObjects
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.2 ⟨(g, sz), hgb, rfl⟩
      rwa [hsz] at this
    intro i hi
    unfold worldTypedIvls at hi
    simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr (Disj.symm (((hT.2.1 t ht).2 i hfp).2 _ hmem_fix))
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      by_cases hr0 : globN s r.1 = 0
      · simp [hr0]
      · right
        have hne_name : g ≠ r.1 := by
          intro heq; subst heq
          apply huntyped
          simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with h | h | h | h <;> (rw [Prod.mk.injEq] at h; simp [h.1])
        obtain ⟨idx1, hidx1, heq1⟩ := List.mem_iff_getElem.1 hgb
        have hr_gb : r ∈ globalBuffers := by
          simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with h | h | h | h <;> (rw [h]; decide)
        obtain ⟨idx2, hidx2, heq2⟩ := List.mem_iff_getElem.1 hr_gb
        have hidx_ne : idx1 ≠ idx2 := by
          intro h; subst h; rw [heq1] at heq2
          exact hne_name (congrArg Prod.fst heq2)
        have hpw_gb : ((globalBuffers.map fun gn =>
            (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2))).Pairwise Disj := by
          have hpw := hF.2
          unfold fixedObjects at hpw
          exact (List.pairwise_append.1 (List.pairwise_append.1 (List.pairwise_append.1 hpw).1).1).1
        have hget := List.pairwise_iff_getElem.1 hpw_gb
        rcases Nat.lt_or_gt_of_ne hidx_ne with hlt | hgt
        · have hd := hget idx1 idx2 (by simp; exact hidx1) (by simp; exact hidx2) hlt
          simp only [List.getElem_map, heq1, heq2, hsz] at hd
          exact hd
        · have hd := hget idx2 idx1 (by simp; exact hidx2) (by simp; exact hidx1) hgt
          simp only [List.getElem_map, heq1, heq2, hsz] at hd
          exact Disj.symm hd
    · simp only [List.mem_singleton] at h3
      subst h3
      have hpw12 := (List.pairwise_append.1 (List.pairwise_append.1 hF.2).1).1
      have hm1 : (globN s g, sz) ∈ (globalBuffers.map fun gn =>
          (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
        rw [← hsz]; exact List.mem_map.2 ⟨(g, sz), hgb, rfl⟩
      exact Or.inr ((List.pairwise_append.1 hpw12).2.2 _ hm1 _ (List.mem_singleton.2 rfl))
    · have hpw13 := (List.pairwise_append.1 hF.2).1
      have hm1 : (globN s g, sz) ∈ (globalBuffers.map fun gn =>
          (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++ [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] := by
        apply List.mem_append_left; rw [← hsz]; exact List.mem_map.2 ⟨(g, sz), hgb, rfl⟩
      exact Or.inr ((List.pairwise_append.1 hpw13).2.2 _ hm1 _ h4)
    · have hm1 : (globN s g, sz) ∈ (globalBuffers.map fun gn =>
          (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
          [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++ blockOutObjects s := by
        apply List.mem_append_left; apply List.mem_append_left
        rw [← hsz]; exact List.mem_map.2 ⟨(g, sz), hgb, rfl⟩
      exact Or.inr ((List.pairwise_append.1 hF.2).2.2 _ hm1 _ h5)
    · exact Or.inr (Disj.symm ((hTr.2.1 i h6).2 _ hmem_fix))

theorem ByteRegionEffect.to_worldStep {F : Type}
    {R extra : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hW : WorldOK s)
    (hextra_fix : ∀ x ∈ extra s, x ∈ fixedObjects s ∧
      ∀ S Nd, WorldTypedWith s S Nd → ∀ i ∈ worldTypedIvls s S Nd, i.2 = 0 ∨ Disj x i)
    (heff : ByteRegionEffect s post (R s ++ extra s)) :
    WorldStep R [] stdKeep NoExtra s r post := by
  have hinv_post : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hW.1.1
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  have hA_post : ArenaReady post := ⟨hinv_post, arenaOK_congr heff.globals hW.1.2⟩
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hG : GlobalsKept [] s post := fun _ _ => by rw [heff.globals]
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hTr0⟩ := hWT0_ex.2.2.2
  have hWT0 : WorldTypedWith s S0 Nd0 := ⟨hWT0_ex.1, hWT0_ex.2.1, hWT0_ex.2.2.1, hTr0⟩
  have hmem_eq_bytes : ∀ a : BitVec 64, ordinaryDomain a →
      (∀ k : Nat, k < 8 → memB post (a.toNat + k) = memB s (a.toNat + k)) →
      post.memory a = s.memory a := by
    intro a ha_dom hb
    have hdom' := (ordinaryDomain_iff a).mp ha_dom
    have ha_ord : a.toNat % 8 = 0 ∧ sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
      rw [sourceBase_val, heapEnd_val]; omega
    have hhe_lt : heapEnd ≤ 2 ^ 64 := by rw [heapEnd_val]; decide
    have hhe_8 : heapEnd % 8 = 0 := by decide
    have ha_hi : a.toNat + 8 ≤ 2 ^ 64 := by omega
    rcases hp_m : post.memory a with ⟨wp⟩
    rcases hs_m : s.memory a with ⟨ws⟩
    congr 1
    apply BitVec.eq_of_toNat_eq
    have hbyte_val : ∀ k : Nat, k < 8 →
        (panGetByteHOL (BitVec.ofNat 64 (a.toNat + k)) wp s.be).toNat =
        (panGetByteHOL (BitVec.ofNat 64 (a.toNat + k)) ws s.be).toNat := by
      intro k hk
      have hal_eq : panByteAlignHOL (BitVec.ofNat 64 (a.toNat + k)) = a := by
        apply BitVec.eq_of_toNat_eq
        rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega
      have hbk := hb k hk
      unfold memB at hbk
      rw [hal_eq, hp_m, hs_m, heff.be] at hbk
      exact hbk
    have hshift : ∀ (w : BitVec 64) (idx : Nat), idx < 8 →
        w.toNat / 256 ^ idx % 256 =
        (panGetByteHOL (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))) w s.be).toNat := by
      intro w idx hidx
      unfold panGetByteHOL
      change w.toNat / 256 ^ idx % 256 =
        (UInt8.ofNat (w.toNat / 256 ^ (if s.be then 8 - 1 - (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8
          else (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8) % 256)).toNat
      have hexp : (if s.be then 8 - 1 - (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8
          else (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8) = idx := by
        have hmod_lt : (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat =
            a.toNat + (if s.be then 7 - idx else idx) :=
          Nat.mod_eq_of_lt (by cases s.be <;> simp <;> omega)
        rw [hmod_lt]
        cases s.be <;> simp <;> omega
      rw [hexp, UInt8.toNat_ofNat']
      have h256 : (2 ^ 8 : Nat) = 256 := by decide
      rw [h256, Nat.mod_mod]
    have hpow_eq : ∀ idx : Nat, idx < 8 → wp.toNat / 256 ^ idx % 256 = ws.toNat / 256 ^ idx % 256 := by
      intro idx hidx
      rw [hshift wp idx hidx, hshift ws idx hidx]
      exact hbyte_val (if s.be then 7 - idx else idx) (by cases s.be <;> simp <;> omega)
    have hdecomp : ∀ n : Nat, n < 2 ^ 64 →
        n = (n / 256 ^ 0 % 256) +
            (n / 256 ^ 1 % 256) * 256 ^ 1 +
            (n / 256 ^ 2 % 256) * 256 ^ 2 +
            (n / 256 ^ 3 % 256) * 256 ^ 3 +
            (n / 256 ^ 4 % 256) * 256 ^ 4 +
            (n / 256 ^ 5 % 256) * 256 ^ 5 +
            (n / 256 ^ 6 % 256) * 256 ^ 6 +
            (n / 256 ^ 7 % 256) * 256 ^ 7 := by
      intro n hn; omega
    rw [hdecomp wp.toNat wp.isLt, hdecomp ws.toNat ws.isLt]
    rw [hpow_eq 0 (by omega), hpow_eq 1 (by omega), hpow_eq 2 (by omega), hpow_eq 3 (by omega),
        hpow_eq 4 (by omega), hpow_eq 5 (by omega), hpow_eq 6 (by omega), hpow_eq 7 (by omega)]
  have hRK : RecordsKept R stdKeep s post := by
    intro rec hrec hgnz k hk hnoR
    have hsz_ex : ∃ sz : Nat, (rec.1, sz) ∈ typedRecords ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by decide, ?_⟩; simp at hk; omega
      · refine ⟨80, by decide, ?_⟩; simp at hk; omega
      · refine ⟨72, by decide, ?_⟩; simp at hk; omega
      · refine ⟨88, by decide, ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hk8, hkle⟩ := hsz_ex
    have hfix0 := typedRec_in_fixedObjects s htr
    have hsz : (if globN s rec.1 = 0 then 0 else sz) = sz := if_neg hgnz
    rcases hWT0.2.2.1.1 _ hfix0 with h0 | ⟨hal0, hw0⟩
    · dsimp only at h0; rw [hsz] at h0; omega
    · have hb := allocated_le_2pow64 hW.1.2 hal0
      dsimp only at hb; rw [hsz] at hb
      have hg8 : (globN s rec.1) % 8 = 0 := hw0.1
      have ha64 : globN s rec.1 + k < 2 ^ 64 := by omega
      unfold memW
      have hbit : (BitVec.ofNat 64 (globN s rec.1 + k)).toNat = globN s rec.1 + k :=
        Nat.mod_eq_of_lt ha64
      by_cases hdom : ordinaryDomain (BitVec.ofNat 64 (globN s rec.1 + k))
      · rw [hmem_eq_bytes _ hdom]
        intro idx hidx
        rw [hbit]
        apply heff.byte_frame (globN s rec.1 + k + idx) (by omega)
        intro x hx hbx
        rcases List.mem_append.1 hx with hxR | hxE
        · apply hnoR x hxR
          obtain ⟨_, _⟩ := hbx
          exact ⟨by omega, by omega⟩
        · have hwti := mem_worldTypedIvls_typedRec (s := s) (S := S0) (Nd := Nd0) htr
          rw [hsz] at hwti
          rcases (hextra_fix x hxE).2 S0 Nd0 hWT0 _ hwti with h0 | hdj
          · dsimp only at h0; omega
          · obtain ⟨_, _⟩ := hbx
            rcases hdj with h0 | h0 | h | h
            · omega
            · dsimp only at h0; omega
            · dsimp only at h; omega
            · dsimp only at h; omega
      · rw [heff.out_dom]
        rwa [hW.1.1.memaddrs]
  refine ⟨hA_post, hh, hG, hRK, fun S Nd hWT hdisj => ?_⟩
  have hcell : SameTypedCells s post S Nd := by
    refine ⟨heff.be, heff.memaddrs, hW.1.1.memaddrs, ?_, ?_, ?_⟩
    · intro a hna
      apply heff.out_dom a
      rwa [hW.1.1.memaddrs]
    · intro a ha ha8 ⟨i, hi, ha1, ha2⟩
      by_cases hdom : ordinaryDomain (BitVec.ofNat 64 a)
      · have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
        apply hmem_eq_bytes _ hdom
        intro k hk
        rw [hbit]
        apply heff.byte_frame (a + k) (by omega)
        intro x hx hbx
        rcases List.mem_append.1 hx with hxR | hxE
        · have hdj := hdisj x hxR i hi
          obtain ⟨_, _⟩ := hbx
          rcases hdj with h0 | h0 | h | h <;> omega
        · rcases (hextra_fix x hxE).2 S Nd hWT i hi with hi0 | hdj
          · omega
          · obtain ⟨_, _⟩ := hbx
            rcases hdj with h0 | h0 | h | h <;> omega
      · apply heff.out_dom
        rwa [hW.1.1.memaddrs]
    · intro b hb ⟨i, hi, hb1, hb2⟩
      apply heff.byte_frame b hb
      intro x hx hbx
      rcases List.mem_append.1 hx with hxR | hxE
      · have hdj := hdisj x hxR i hi
        obtain ⟨_, _⟩ := hbx
        rcases hdj with h0 | h0 | h | h <;> omega
      · rcases (hextra_fix x hxE).2 S Nd hWT i hi with hi0 | hdj
        · omega
        · obtain ⟨_, _⟩ := hbx
          rcases hdj with h0 | h0 | h | h <;> omega
  have hfeq := fixedObjects_eq_of_nonHeapGlobalsKept hW.1.2 hWT.1 hWT.2.2.1 hcell
    (fun name _ _ _ => by rw [heff.globals])
  have hFT_post := fixedTyped_of_eq hA_post hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, hOG⟩ := worldTypedWith_congr_w1 hW.1 hA_post hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  refine ⟨S, Nd, fun _ h => h, hWT_post, hOG, ?_, trivial⟩
  intro a ha _
  apply heff.cell_frame a
  intro x hx
  rcases List.mem_append.1 hx with hxR | hxE
  · exact ha x (List.mem_append_left [freeGap s] (List.mem_append_right (worldOwned s S Nd) hxR))
  · have hx_wo : x ∈ worldOwned s S Nd := by
      unfold worldOwned
      exact List.mem_append_left _ (List.mem_append_right _ (hextra_fix x hxE).1)
    exact ha x (List.mem_append_left [freeGap s] (List.mem_append_left (R s) hx_wo))

/-! ## 3. Loop combinator for `ByteRegionEffect` -/

theorem eval_while_byteRegion {F : Type}
    (cond : ExpHOL 64) (body : ProgHOL 64) (Rl : List Ivl)
    (P : PanSemStateFiniteExact 64 F → Prop)
    (hP_dec : ∀ t, P t → P (decClockHOLFinite t))
    (hbody : ∀ t, P t →
      (evaluateHOLFiniteState t body).1 ≠ some .timeOut →
        (((evaluateHOLFiniteState t body).1 = none ∨
          (evaluateHOLFiniteState t body).1 = some .continue) →
            P (evaluateHOLFiniteState t body).2 ∧
            ByteRegionEffect t (evaluateHOLFiniteState t body).2 Rl) ∧
        ((evaluateHOLFiniteState t body).1 = some .break →
          ByteRegionEffect t (evaluateHOLFiniteState t body).2 Rl) ∧
        (∀ r, (evaluateHOLFiniteState t body).1 = some r →
          r ≠ .continue → r ≠ .break → r ≠ .timeOut →
          (∀ v, r ≠ .returned v) ∧ (∀ e v, e ≠ ofString "TrapErr" → r ≠ .exception e v))) :
    ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F), s.clock = k → P s →
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .timeOut →
        ((evaluateHOLFiniteState s (.while cond body)).1 = none →
          ByteRegionEffect s (evaluateHOLFiniteState s (.while cond body)).2 Rl) ∧
        ((evaluateHOLFiniteState s (.while cond body)).1 ≠ none →
          ¬ Resumes (evaluateHOLFiniteState s (.while cond body)).1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s hclk hPs hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    rcases hc : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) cond with
      _ | cv
    · simp only [hc] at hnt ⊢
      exact ⟨fun h => by simp at h, fun _ hres => by rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    · simp only [hc] at hnt ⊢
      rcases cv with ⟨⟨w⟩⟩ | _ | _
      · dsimp only at hnt ⊢
        by_cases hw : w = 0
        · subst hw
          exact ⟨fun _ => ByteRegionEffect.refl s Rl, fun h => False.elim (h rfl)⟩
        · rw [if_pos hw] at hnt ⊢
          by_cases hk0 : s.clock = 0
          · simp [hk0] at hnt
          · rw [if_neg hk0] at hnt ⊢
            have hPd : P (decClockHOLFinite s) := hP_dec s hPs
            have heff_dec : ByteRegionEffect s (decClockHOLFinite s) Rl :=
              ByteRegionEffect.refl s Rl |>.with_locals_clock s.locals (s.clock - 1)
            have hb_clk := Flapjack.evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
            have hd_clk : (decClockHOLFinite s).clock < k := by
              simp [decClockHOLFinite, hclk]; omega
            rcases hbo : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨rb, sb⟩
            simp only [hbo] at hnt hb_clk ⊢
            have hnt_b : rb ≠ some .timeOut := by
              rintro rfl; exact hnt rfl
            have hb_spec := hbody (decClockHOLFinite s) hPd (by rw [hbo]; exact hnt_b)
            rw [hbo] at hb_spec
            dsimp only at hb_spec
            cases rb with
            | none =>
              obtain ⟨hPsb, heff_b⟩ := hb_spec.1 (Or.inl rfl)
              have jih := ih sb.clock (lt_of_le_of_lt hb_clk hd_clk) sb rfl hPsb hnt
              exact ⟨fun hn => (heff_dec.trans heff_b).trans (jih.1 hn), jih.2⟩
            | some r =>
              cases r with
              | «continue» =>
                obtain ⟨hPsb, heff_b⟩ := hb_spec.1 (Or.inr rfl)
                have jih := ih sb.clock (lt_of_le_of_lt hb_clk hd_clk) sb rfl hPsb hnt
                exact ⟨fun hn => (heff_dec.trans heff_b).trans (jih.1 hn), jih.2⟩
              | «break» =>
                exact ⟨fun _ => heff_dec.trans (hb_spec.2.1 rfl), fun h => absurd rfl h⟩
              | timeOut => exact absurd rfl hnt_b
              | returned v =>
                obtain ⟨hnr, _⟩ := hb_spec.2.2 (.returned v) rfl (by simp) (by simp) (by simp)
                exact absurd rfl (hnr v)
              | exception e v =>
                refine ⟨fun h => by simp at h, fun _ hres => ?_⟩
                obtain ⟨_, hne⟩ := hb_spec.2.2 (.exception e v) rfl (by simp) (by simp) (by simp)
                rcases hres with ⟨_, h⟩ | ⟨e', v', h, he⟩
                · simp at h
                · injection h with h'; injection h' with h1 h2
                  subst h1 h2
                  exact hne e v he rfl
              | error =>
                exact ⟨fun h => by simp at h, fun _ hres => by rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
              | finalFfi ev =>
                exact ⟨fun h => by simp at h, fun _ hres => by rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
      · exact ⟨fun h => by simp at h, fun _ hres => by rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
      · exact ⟨fun h => by simp at h, fun _ hres => by rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

end InitECandidate.Solver.Wave8GuestInv.M13
