import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4J

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

/-! # Phase 4K: the loop-31 cell-miss cores

The callee-side cell preservation across the `lst_push` call: every
bo-record cell, both `l72`-header cells and the slice cells miss the pushed
list header `(w_l, 24)` (via the `blockOutObjects` pairwise disjointness
and the global-buffer disjointness) and the free heap (via the
`Allocated` two-case analysis), so the callee's write-set shape preserves
them. -/

/-- The loop-31 callee-cell preservation bundle: the `hbo_pres`, `hl72_head`,
`hl72_len` and `hslice_pres` inputs of `p4Loop31_hcells`, derived from the
callee's write-set shape and the world's disjointness structure. -/
theorem p4Loop31_calleeCellsUnhit {F : Type}
    {entry u post : PanSemStateFiniteExact 64 F} {w_l : BitVec 64}
    (hAR : ArenaReady u) (hE : TxEnv u) {S Nd : List Nat} (hW : WorldTypedWith u S Nd)
    (hidx : locN u "index" = locN entry "index")
    (hl40 : w_l.toNat = memW u (globN u "bo" + 40))
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (w_l.toNat, 24) →
      ¬ CellHits a.toNat (InitECandidate.Solver.Wave8Contracts.M08.heapFree u) →
      post.memory a = u.memory a) :
    (∀ off ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN u "bo" + off) = memW u (globN u "bo" + off)) ∧
    (memW post (memW u (globN u "bo" + 72)) = memW u (memW u (globN u "bo" + 72)) ∧
     memW post (memW u (globN u "bo" + 72) + 8) = memW u (memW u (globN u "bo" + 72) + 8)) ∧
    (∀ off ∈ ([24, 32] : List Nat), ∀ i ≤ locN entry "index",
      memW post (memW u (globN u "bo" + off) + 16 * i + 8) =
        memW u (memW u (globN u "bo" + off) + 16 * i + 8)) := by
  obtain ⟨hc40, hc72, hbo_eq⟩ := blockOutObjects_eq_list hE hW.1
  have hbo_len : (blockOutObjects u).length = 7 := by rw [hbo_eq]; rfl
  have hlen_nz : 16 * memW u (globN u "bo" + 80) + 16 ≠ 0 := by omega
  have hget0 : (blockOutObjects u)[0] =
      (memW u (globN u "bo" + 24), 16 * memW u (globN u "bo" + 80) + 16) := by
    simp [hbo_eq, hE.bo_nz, hE.bo24, hlen_nz]
  have hget1 : (blockOutObjects u)[1] =
      (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) := by
    simp [hbo_eq]
  have hget3 : (blockOutObjects u)[3] = (w_l.toNat, 24) := by
    rw [hl40]; simp [hbo_eq]
  have hget5 : (blockOutObjects u)[5] = (memW u (globN u "bo" + 72), 24) := by
    simp [hbo_eq]
  obtain ⟨-, hbo_pw, hgb_rest, -, -⟩ := fixedObjects_disj_parts hW.2.2.1
  have hpair := List.pairwise_iff_getElem.1 hbo_pw
  have he0_mem : (memW u (globN u "bo" + 24), 16 * memW u (globN u "bo" + 80) + 16) ∈
      blockOutObjects u := hget0 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have he1_mem : (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) ∈
      blockOutObjects u := hget1 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have he3_mem : (w_l.toNat, 24) ∈ blockOutObjects u :=
    hget3 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have he5_mem : (memW u (globN u "bo" + 72), 24) ∈ blockOutObjects u :=
    hget5 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have hd03 : Disj (memW u (globN u "bo" + 24), 16 * memW u (globN u "bo" + 80) + 16)
      (w_l.toNat, 24) := by
    have h := hpair 0 3 (by rw [hbo_len]; decide) (by rw [hbo_len]; decide) (by decide)
    rw [hget0, hget3] at h
    exact h
  have hd13 : Disj (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16)
      (w_l.toNat, 24) := by
    have h := hpair 1 3 (by rw [hbo_len]; decide) (by rw [hbo_len]; decide) (by decide)
    rw [hget1, hget3] at h
    exact h
  have hd53 : Disj (memW u (globN u "bo" + 72), 24) (w_l.toNat, 24) := by
    have h := hpair 3 5 (by rw [hbo_len]; decide) (by rw [hbo_len]; decide) (by decide)
    rw [hget3, hget5] at h
    exact disj_symm h
  have hbo_words := bo_words hW.2.2.1 hE.bo_nz
  have hbo8 : globN u "bo" % 8 = 0 := hbo_words.2.1
  have hbo_hi : globN u "bo" + 88 ≤ 2 ^ 64 := (ivl_allocated_bound hAR.2 hbo_words.1).2
  have hbo_e3 : Disj (globN u "bo", 88) (w_l.toNat, 24) := by
    have hbo_gbs : (globN u "bo", 88) ∈
        (globalBuffers.map fun gn => (globN u gn.1, if globN u gn.1 = 0 then 0 else gn.2)) :=
      List.mem_map.2 ⟨("bo", 88), by decide, by simp [hE.bo_nz]⟩
    have he3_in : (w_l.toNat, 24) ∈
        [(if globN u "journal_cap" = 0 then 0 else globN u "journal",
          32 * globN u "journal_cap")] ++ blockOutObjects u ++ balObjects u := by
      apply List.mem_append_left
      apply List.mem_append_right
      exact he3_mem
    exact hgb_rest _ hbo_gbs _ he3_in
  have hcontain : ∀ e : Ivl, e ∈ blockOutObjects u → e.2 ≠ 0 →
      Allocated u e ∧ e.1 % 8 = 0 ∧ e.2 % 8 = 0 ∧ e.1 + e.2 ≤ 2 ^ 64 := by
    intro e he_mem he_nz
    have he_fix : e ∈ fixedObjects u := by
      unfold fixedObjects
      apply List.mem_append_left
      apply List.mem_append_right
      exact he_mem
    obtain ⟨halloc, hwords⟩ := (hW.2.2.1.1 e he_fix).resolve_left he_nz
    exact ⟨halloc, hwords.1, hwords.2.1, (ivl_allocated_bound hAR.2 halloc).2⟩
  have hsep : heapLimit ≤ scratchStart := by decide
  have hidx_lt : locN u "index" < memW u (globN u "bo" + 80) := hE.idx_lt
  have hcell : ∀ c : Ivl, Allocated u c → c.1 % 8 = 0 → c.2 % 8 = 0 →
      Disj c (w_l.toNat, 24) →
      ∀ k : Nat, k % 8 = 0 → c.1 ≤ k → k + 8 ≤ c.1 + c.2 → k < 2 ^ 64 →
      memW post k = memW u k := by
    intro c halloc hc8 hc2 hd k hk8 hk1 hk2 hk64
    have hj0 : (w_l.toNat, 24).2 = 0 → (w_l.toNat, 24).1 % 8 = 0 := by simp
    have hhit : CellHits k c := ⟨by omega, by omega⟩
    have hm1 : ¬ CellHits k (w_l.toNat, 24) :=
      not_cellHits_of_disj hc8 hc2 hk8 hj0 hhit hd
    have hm2 : ¬ CellHits k (InitECandidate.Solver.Wave8Contracts.M08.heapFree u) := by
      intro ⟨hc1, hc2⟩
      simp only [InitECandidate.Solver.Wave8Contracts.M08.heapFree] at hc1 hc2
      unfold Allocated at halloc
      unfold Inside at halloc
      rcases halloc with ⟨_, hhi⟩ | ⟨hlo, _⟩
      · omega
      · have h1 := hAR.2.2.1; have h2 := hAR.2.2.2.1; have h3 := hAR.2.2.2.2.1
        omega
    exact p4Loop31_memW_of_miss hmem hk64 hm1 hm2
  refine ⟨?_, ?_, ?_⟩
  · intro off hoff
    have hoff_facts : off % 8 = 0 ∧ off + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    obtain ⟨hoff8, hoff88⟩ := hoff_facts
    have hk8 : (globN u "bo" + off) % 8 = 0 := by omega
    have hk1 : globN u "bo" ≤ globN u "bo" + off := by omega
    have hk2 : globN u "bo" + off + 8 ≤ globN u "bo" + 88 := by omega
    have hk64 : globN u "bo" + off < 2 ^ 64 := by omega
    exact hcell (globN u "bo", 88) hbo_words.1 hbo8 hbo_words.2.2.1 hbo_e3
      (globN u "bo" + off) hk8 hk1 hk2 hk64
  · have he5_nz : (memW u (globN u "bo" + 72), 24).2 ≠ 0 := by simp
    obtain ⟨halloc5, halign5, hlen5, hhi5⟩ := hcontain _ he5_mem he5_nz
    have hl72_8 : memW u (globN u "bo" + 72) % 8 = 0 := halign5
    have hl72_hi : memW u (globN u "bo" + 72) + 24 ≤ 2 ^ 64 := hhi5
    have hk1 : memW u (globN u "bo" + 72) ≤ memW u (globN u "bo" + 72) := le_rfl
    have hk2 : memW u (globN u "bo" + 72) + 8 ≤ memW u (globN u "bo" + 72) + 24 := by omega
    have hk1b : memW u (globN u "bo" + 72) ≤ memW u (globN u "bo" + 72) + 8 := by omega
    have hk2b : memW u (globN u "bo" + 72) + 8 + 8 ≤ memW u (globN u "bo" + 72) + 24 := by omega
    have hk64 : memW u (globN u "bo" + 72) < 2 ^ 64 := by omega
    have hk64b : memW u (globN u "bo" + 72) + 8 < 2 ^ 64 := by omega
    have hk8b : (memW u (globN u "bo" + 72) + 8) % 8 = 0 := by omega
    exact ⟨hcell _ halloc5 hl72_8 hlen5 hd53 (memW u (globN u "bo" + 72)) hl72_8 hk1 hk2 hk64,
      hcell _ halloc5 hl72_8 hlen5 hd53 (memW u (globN u "bo" + 72) + 8) hk8b hk1b hk2b hk64b⟩
  · intro off hoff i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl
    · obtain ⟨halloc0, halign0, hlen0, hhi0⟩ := hcontain _ he0_mem hlen_nz
      have hb8 : memW u (globN u "bo" + 24) % 8 = 0 := halign0
      have hb_hi : memW u (globN u "bo" + 24) + (16 * memW u (globN u "bo" + 80) + 16)
          ≤ 2 ^ 64 := hhi0
      have hk8 : (memW u (globN u "bo" + 24) + 16 * i + 8) % 8 = 0 := by omega
      have hk1 : memW u (globN u "bo" + 24) ≤ memW u (globN u "bo" + 24) + 16 * i + 8 := by omega
      have hk2 : memW u (globN u "bo" + 24) + 16 * i + 8 + 8
          ≤ memW u (globN u "bo" + 24) + 16 * memW u (globN u "bo" + 80) + 16 := by omega
      have hk64 : memW u (globN u "bo" + 24) + 16 * i + 8 < 2 ^ 64 := by omega
      exact hcell _ halloc0 hb8 hlen0 hd03 _ hk8 hk1 hk2 hk64
    · obtain ⟨halloc1, halign1, hlen1, hhi1⟩ := hcontain _ he1_mem hlen_nz
      have hb8 : memW u (globN u "bo" + 32) % 8 = 0 := halign1
      have hb_hi : memW u (globN u "bo" + 32) + (16 * memW u (globN u "bo" + 80) + 16)
          ≤ 2 ^ 64 := hhi1
      have hk8 : (memW u (globN u "bo" + 32) + 16 * i + 8) % 8 = 0 := by omega
      have hk1 : memW u (globN u "bo" + 32) ≤ memW u (globN u "bo" + 32) + 16 * i + 8 := by omega
      have hk2 : memW u (globN u "bo" + 32) + 16 * i + 8 + 8
          ≤ memW u (globN u "bo" + 32) + 16 * memW u (globN u "bo" + 80) + 16 := by omega
      have hk64 : memW u (globN u "bo" + 32) + 16 * i + 8 < 2 ^ 64 := by omega
      exact hcell _ halloc1 hb8 hlen1 hd13 _ hk8 hk1 hk2 hk64

theorem p4Loop31_storeMisses {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {w : BitVec 64} {l : Nat}
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (hl : l = memW s (globN s "bo" + 40))
    (hdata_nz : memW s l ≠ 0)
    (hientry : locN entry "index" < memW s (globN s "bo" + 80))
    (hin : Inside (w.toNat, 8) (memW s l) (memW s l + 8 * memW s (l + 16))) :
    (∀ off ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      BitVec.ofNat 64 (globN s "bo" + off) ≠ w) ∧
    (BitVec.ofNat 64 (memW s (globN s "bo" + 72)) ≠ w ∧
     BitVec.ofNat 64 (memW s (globN s "bo" + 72) + 8) ≠ w ∧
     BitVec.ofNat 64 (memW s (globN s "bo" + 40)) ≠ w) ∧
    (∀ off ∈ ([24, 32] : List Nat), ∀ i ≤ locN entry "index",
      BitVec.ofNat 64 (memW s (globN s "bo" + off) + 16 * i + 8) ≠ w) := by
  obtain ⟨harr_mem, hcap⟩ := p4Loop31_arrFacts hE hW.1 hl hdata_nz
  have hlen8_nz : 8 * memW s (l + 16) ≠ 0 := by omega
  obtain ⟨hc40, hc72, hbo_eq⟩ := blockOutObjects_eq_list hE hW.1
  have hbo_len : (blockOutObjects s).length = 7 := by rw [hbo_eq]; rfl
  have hlen_nz : 16 * memW s (globN s "bo" + 80) + 16 ≠ 0 := by omega
  have hget0 : (blockOutObjects s)[0] =
      (memW s (globN s "bo" + 24), 16 * memW s (globN s "bo" + 80) + 16) := by
    simp [hbo_eq, hE.bo_nz, hE.bo24, hlen_nz]
  have hget1 : (blockOutObjects s)[1] =
      (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) := by
    simp [hbo_eq]
  have hget3 : (blockOutObjects s)[3] = (memW s (globN s "bo" + 40), 24) := by
    simp [hbo_eq]
  have hget4 : (blockOutObjects s)[4] = (memW s l, 8 * memW s (l + 16)) := by
    simp [hbo_eq, ← hl, hE.bo_nz, hdata_nz, hlen8_nz]
  have hget5 : (blockOutObjects s)[5] = (memW s (globN s "bo" + 72), 24) := by
    simp [hbo_eq]
  obtain ⟨-, hbo_pw, hgb_rest, -, -⟩ := fixedObjects_disj_parts hW.2.2.1
  have hpair := List.pairwise_iff_getElem.1 hbo_pw
  have hd04 : Disj (memW s (globN s "bo" + 24), 16 * memW s (globN s "bo" + 80) + 16)
      (memW s l, 8 * memW s (l + 16)) := by
    have h := hpair 0 4 (by rw [hbo_len]; decide) (by rw [hbo_len]; decide) (by decide)
    rw [hget0, hget4] at h
    exact h
  have hd14 : Disj (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16)
      (memW s l, 8 * memW s (l + 16)) := by
    have h := hpair 1 4 (by rw [hbo_len]; decide) (by rw [hbo_len]; decide) (by decide)
    rw [hget1, hget4] at h
    exact h
  have hd34 : Disj (memW s (globN s "bo" + 40), 24)
      (memW s l, 8 * memW s (l + 16)) := by
    have h := hpair 3 4 (by rw [hbo_len]; decide) (by rw [hbo_len]; decide) (by decide)
    rw [hget3, hget4] at h
    exact h
  have hd54 : Disj (memW s (globN s "bo" + 72), 24)
      (memW s l, 8 * memW s (l + 16)) := by
    have h := hpair 4 5 (by rw [hbo_len]; decide) (by rw [hbo_len]; decide) (by decide)
    rw [hget4, hget5] at h
    exact disj_symm h
  have hbo_words := bo_words hW.2.2.1 hE.bo_nz
  have hbo_d4 : Disj (globN s "bo", 88) (memW s l, 8 * memW s (l + 16)) := by
    have hbo_gbs : (globN s "bo", 88) ∈
        (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) :=
      List.mem_map.2 ⟨("bo", 88), by decide, by simp [hE.bo_nz]⟩
    have he4_in : (memW s l, 8 * memW s (l + 16)) ∈
        [(if globN s "journal_cap" = 0 then 0 else globN s "journal",
          32 * globN s "journal_cap")] ++ blockOutObjects s ++ balObjects s := by
      apply List.mem_append_left
      apply List.mem_append_right
      exact harr_mem
    exact hgb_rest _ hbo_gbs _ he4_in
  have hbound : ∀ e : Ivl, e ∈ blockOutObjects s → e.2 ≠ 0 → e.1 + e.2 ≤ 2 ^ 64 := by
    intro e he_mem he_nz
    have he_fix : e ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left
      apply List.mem_append_right
      exact he_mem
    obtain ⟨halloc, -⟩ := (hW.2.2.1.1 e he_fix).resolve_left he_nz
    exact (ivl_allocated_bound hA.2 halloc).2
  have he0_mem : (memW s (globN s "bo" + 24), 16 * memW s (globN s "bo" + 80) + 16) ∈
      blockOutObjects s := hget0 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have he1_mem : (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) ∈
      blockOutObjects s := hget1 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have he3_mem : (memW s (globN s "bo" + 40), 24) ∈ blockOutObjects s :=
    hget3 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have he5_mem : (memW s (globN s "bo" + 72), 24) ∈ blockOutObjects s :=
    hget5 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have he3_nz : (memW s (globN s "bo" + 40), 24).2 ≠ 0 := by simp
  have he5_nz : (memW s (globN s "bo" + 72), 24).2 ≠ 0 := by simp
  have he0_hi : memW s (globN s "bo" + 24) + (16 * memW s (globN s "bo" + 80) + 16)
      ≤ 2 ^ 64 := hbound _ he0_mem hlen_nz
  have he1_hi : memW s (globN s "bo" + 32) + (16 * memW s (globN s "bo" + 80) + 16)
      ≤ 2 ^ 64 := hbound _ he1_mem hlen_nz
  have he3_hi : memW s (globN s "bo" + 40) + 24 ≤ 2 ^ 64 := hbound _ he3_mem he3_nz
  have he5_hi : memW s (globN s "bo" + 72) + 24 ≤ 2 ^ 64 := hbound _ he5_mem he5_nz
  have hbo_hi : globN s "bo" + 88 ≤ 2 ^ 64 := (ivl_allocated_bound hA.2 hbo_words.1).2
  have hcell_miss : ∀ c : Ivl, Disj c (w.toNat, 8) → ∀ k : Nat,
      c.1 ≤ k → k + 8 ≤ c.1 + c.2 → k < 2 ^ 64 →
      BitVec.ofNat 64 k ≠ w := by
    intro c hd k hk1 hk2 hk64 heq
    have htonat := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at htonat
    rcases hd with h0 | h0 | h1 | h1 <;> omega
  have hdisj_w : ∀ c : Ivl, Disj c (memW s l, 8 * memW s (l + 16)) →
      Disj c (w.toNat, 8) := fun c hd => disj_of_inside_right hin hd
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro off hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl
    · have hk1 : globN s "bo" ≤ globN s "bo" + 24 := by omega
      have hk2 : globN s "bo" + 24 + 8 ≤ globN s "bo" + 88 := by omega
      have hk64 : globN s "bo" + 24 < 2 ^ 64 := by omega
      exact hcell_miss _ (hdisj_w _ hbo_d4) _ hk1 hk2 hk64
    · have hk1 : globN s "bo" ≤ globN s "bo" + 32 := by omega
      have hk2 : globN s "bo" + 32 + 8 ≤ globN s "bo" + 88 := by omega
      have hk64 : globN s "bo" + 32 < 2 ^ 64 := by omega
      exact hcell_miss _ (hdisj_w _ hbo_d4) _ hk1 hk2 hk64
    · have hk1 : globN s "bo" ≤ globN s "bo" + 40 := by omega
      have hk2 : globN s "bo" + 40 + 8 ≤ globN s "bo" + 88 := by omega
      have hk64 : globN s "bo" + 40 < 2 ^ 64 := by omega
      exact hcell_miss _ (hdisj_w _ hbo_d4) _ hk1 hk2 hk64
    · have hk1 : globN s "bo" ≤ globN s "bo" + 56 := by omega
      have hk2 : globN s "bo" + 56 + 8 ≤ globN s "bo" + 88 := by omega
      have hk64 : globN s "bo" + 56 < 2 ^ 64 := by omega
      exact hcell_miss _ (hdisj_w _ hbo_d4) _ hk1 hk2 hk64
    · have hk1 : globN s "bo" ≤ globN s "bo" + 72 := by omega
      have hk2 : globN s "bo" + 72 + 8 ≤ globN s "bo" + 88 := by omega
      have hk64 : globN s "bo" + 72 < 2 ^ 64 := by omega
      exact hcell_miss _ (hdisj_w _ hbo_d4) _ hk1 hk2 hk64
    · have hk1 : globN s "bo" ≤ globN s "bo" + 80 := by omega
      have hk2 : globN s "bo" + 80 + 8 ≤ globN s "bo" + 88 := by omega
      have hk64 : globN s "bo" + 80 < 2 ^ 64 := by omega
      exact hcell_miss _ (hdisj_w _ hbo_d4) _ hk1 hk2 hk64
  · have hk1a : memW s (globN s "bo" + 72) ≤ memW s (globN s "bo" + 72) := le_rfl
    have hk2a : memW s (globN s "bo" + 72) + 8 ≤ memW s (globN s "bo" + 72) + 24 := by omega
    have hk64a : memW s (globN s "bo" + 72) < 2 ^ 64 := by omega
    exact hcell_miss _ (hdisj_w _ hd54) _ hk1a hk2a hk64a
  · have hk1b : memW s (globN s "bo" + 72) ≤ memW s (globN s "bo" + 72) + 8 := by omega
    have hk2b : memW s (globN s "bo" + 72) + 8 + 8
        ≤ memW s (globN s "bo" + 72) + 24 := by omega
    have hk64b : memW s (globN s "bo" + 72) + 8 < 2 ^ 64 := by omega
    exact hcell_miss _ (hdisj_w _ hd54) _ hk1b hk2b hk64b
  · have hk1c : memW s (globN s "bo" + 40) ≤ memW s (globN s "bo" + 40) := le_rfl
    have hk2c : memW s (globN s "bo" + 40) + 8 ≤ memW s (globN s "bo" + 40) + 24 := by omega
    have hk64c : memW s (globN s "bo" + 40) < 2 ^ 64 := by omega
    exact hcell_miss _ (hdisj_w _ hd34) _ hk1c hk2c hk64c
  · intro off hoff i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl
    · have hk1 : memW s (globN s "bo" + 24) ≤ memW s (globN s "bo" + 24) + 16 * i + 8 := by omega
      have hk2 : memW s (globN s "bo" + 24) + 16 * i + 8 + 8
          ≤ memW s (globN s "bo" + 24) + 16 * memW s (globN s "bo" + 80) + 16 := by omega
      have hk64 : memW s (globN s "bo" + 24) + 16 * i + 8 < 2 ^ 64 := by omega
      exact hcell_miss _ (hdisj_w _ hd04) _ hk1 hk2 hk64
    · have hk1 : memW s (globN s "bo" + 32) ≤ memW s (globN s "bo" + 32) + 16 * i + 8 := by omega
      have hk2 : memW s (globN s "bo" + 32) + 16 * i + 8 + 8
          ≤ memW s (globN s "bo" + 32) + 16 * memW s (globN s "bo" + 80) + 16 := by omega
      have hk64 : memW s (globN s "bo" + 32) + 16 * i + 8 < 2 ^ 64 := by omega
      exact hcell_miss _ (hdisj_w _ hd14) _ hk1 hk2 hk64

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk