import InitECandidate.Solver.Wave8GuestInv.ContractParts.C16
import InitECandidate.Solver.GuestTrapOutcomes

/-! Helper lemmas and body proofs for `gbody_process_message_call`,
`gbody_process_unchecked_system_transaction`, and `gbody_process_general_purpose_requests`
on R10 (`ContractParts/C17.lean`).
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodySysTxReqs

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Ordinary domain & interval disjointness / frame helpers -/

theorem ordinaryDomain_iff (x : BitVec 64) :
    ordinaryDomain x ↔ x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
  unfold ordinaryDomain
  rw [StackRemove.mem_addresses]
  have hx := x.isLt
  have hconst : (stackStart - sourceBase) / 8 - globalsWords = 3888119741 ∧
      sourceBase = 2701131776 ∧ heapEnd = 33806089704 ∧
      StackRemove.bytesInWord 64 = BitVec.ofNat 64 8 := by
    refine ⟨by decide, by decide, by decide, ?_⟩
    decide
  rcases hconst with ⟨hn, hsb, hhe, hbw⟩
  rw [hn, hbw]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    simp only [hsb, hhe]
    omega
  · rintro ⟨hal, hlo, hhi⟩
    refine ⟨(x.toNat - sourceBase) / 8, by simp only [hsb, hhe] at hlo hhi; omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    simp only [hsb, hhe] at hlo hhi ⊢
    omega

theorem wordAt_of_ordinary {F : Type} {s : PanSemStateFiniteExact 64 F} (hg : GuestInv s)
    {a : Nat} (ha8 : a % 8 = 0) (hlo : sourceBase ≤ a) (hhi : a < heapEnd) :
    WordAt s a := by
  have ha_lt : a < 2 ^ 64 := by
    have : heapEnd < 2 ^ 64 := by decide
    omega
  rcases hm : s.memory (BitVec.ofNat 64 a) with ⟨w⟩
  refine ⟨w, ?_, hm⟩
  rw [hg.memaddrs, ordinaryDomain_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  exact ⟨ha8, hlo, hhi⟩

theorem disj_zero_left (j : Ivl) : Disj (0, 0) j := Or.inl rfl
theorem disj_zero_right (i : Ivl) : Disj i (0, 0) := Or.inr (Or.inl rfl)

theorem disj_of_len_zero_left {i j : Ivl} (hi : i.2 = 0) : Disj i j := Or.inl hi
theorem disj_of_len_zero_right {i j : Ivl} (hj : j.2 = 0) : Disj i j := Or.inr (Or.inl hj)

theorem disj_of_inside_left {i i' j : Ivl} (hin : Inside i i'.1 (i'.1 + i'.2))
    (hd : Disj i' j) : Disj i j := by
  rcases hin with ⟨h1, h2⟩
  rcases hd with hd | hd | hd | hd
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl hd)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem disj_of_inside_right {i j j' : Ivl} (hin : Inside j j'.1 (j'.1 + j'.2))
    (hd : Disj i j') : Disj i j :=
  (disj_of_inside_left hin hd.flip).flip

def IvlUnhit {F : Type} (s post : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  ∀ a : BitVec 64, a.toNat % 8 = 0 → CellHits a.toNat i → post.memory a = s.memory a

theorem not_cellHits_zero (a : Nat) : ¬ CellHits a (0, 0) := by
  intro ⟨_, hc2⟩
  dsimp at hc2
  omega

theorem not_cellHits_of_disj {a : Nat} {i j : Ivl}
    (hi1 : i.1 % 8 = 0) (hi2 : i.2 % 8 = 0) (ha8 : a % 8 = 0)
    (hj_zero : j.2 = 0 → j.1 % 8 = 0)
    (hhit : CellHits a i) (hd : Disj i j) :
    ¬ CellHits a j := by
  obtain ⟨hi_lo, hi_hi⟩ := hhit
  intro ⟨hc1, hc2⟩
  rcases hd with hd | hd | hd | hd
  · omega
  · have hj1 := hj_zero hd; omega
  · omega
  · omega

theorem ivlUnhit_of_frameOutside_aligned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hfr : FrameOutside s post keep fresh)
    (hi_zero : i.2 = 0 → i.1 % 8 = 0)
    (hk_al : ∀ j ∈ keep, j.1 % 8 = 0 ∧ j.2 % 8 = 0)
    (hf_al : fresh.1 % 8 = 0 ∧ fresh.2 % 8 = 0)
    (hk : ∀ j ∈ keep, Disj i j) (hf : Disj i fresh) :
    IvlUnhit s post i := by
  intro a ha8 hhit
  apply hfr a
  · intro j hj hcj
    obtain ⟨hj1, hj2⟩ := hk_al j hj
    exact not_cellHits_of_disj hj1 hj2 ha8 hi_zero hcj (hk j hj).flip hhit
  · intro hcf
    obtain ⟨hf1, hf2⟩ := hf_al
    exact not_cellHits_of_disj hf1 hf2 ha8 hi_zero hcf hf.flip hhit

theorem ivlUnhit_of_single_cell_disj {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {x : BitVec 64} {i : Ivl}
    (hi_zero : i.2 = 0 → i.1 % 8 = 0)
    (hm : ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a)
    (hd : Disj i (x.toNat, 8)) :
    IvlUnhit s post i := by
  intro a ha8 hhit
  apply hm
  rintro rfl
  exact not_cellHits_of_disj (i := (a.toNat, 8)) ha8 (by omega) ha8 hi_zero
    (by unfold CellHits; omega) hd.flip hhit

theorem memW_eq_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {i : Ivl} (hu : IvlUnhit s post i) {a : Nat}
    (ha8 : a % 8 = 0) (hhi : i.1 + i.2 ≤ 2 ^ 64) (hin : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) :
    memW post a = memW s a := by
  have ha_lt : a < 2 ^ 64 := by omega
  have hmem := hu (BitVec.ofNat 64 a)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; exact ha8)
    (by unfold CellHits; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega)
  unfold memW
  rw [hmem]

theorem memB_eq_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {i : Ivl} (hu : IvlUnhit s post i) (hbe : post.be = s.be)
    {a : Nat} (hhi : i.1 + i.2 ≤ 2 ^ 64) (hin : i.1 ≤ a ∧ a < i.1 + i.2) :
    memB post a = memB s a := by
  have ha_lt : a < 2 ^ 64 := by omega
  let c := panByteAlignHOL (BitVec.ofNat 64 a)
  have hc_nat : c.toNat = a / 8 * 8 := by
    have hal : 2 ^ ((64 : Nat) / 8).log2 = 8 := by decide
    change (BitVec.ofNat 64 ((BitVec.ofNat 64 a).toNat / 2 ^ ((64 : Nat) / 8).log2 *
      2 ^ ((64 : Nat) / 8).log2)).toNat = a / 8 * 8
    rw [hal, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self a 8) ha_lt)]
  have hmem := hu c (by rw [hc_nat]; omega) (by unfold CellHits; rw [hc_nat]; omega)
  unfold memB
  change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 a) v post.be).toNat) =
         (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 a) v s.be).toNat)
  rw [hmem, hbe]

theorem ivl_allocated_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {i : Ivl} (hal : Allocated s i) :
    i.1 + i.2 ≤ heapEnd ∧ i.1 + i.2 ≤ 2 ^ 64 := by
  have h1 : heapLimit ≤ heapEnd := by decide
  have h2 : scratchEnd ≤ heapEnd := by decide
  have h3 : heapEnd < 2 ^ 64 := by decide
  rcases hal with ⟨_, hi⟩ | ⟨_, hi⟩
  · have := hA.2.1; omega
  · have := hA.2.2.2.2.1; omega

theorem wordsOK_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) {i : Ivl} (hw : WordsOK s i) :
    WordsOK post i := by
  refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
  obtain ⟨_, hdom, _⟩ := hw.2.2 k hk
  rcases hm : post.memory (BitVec.ofNat 64 (i.1 + 8 * k)) with ⟨w⟩
  refine ⟨w, ?_, hm⟩
  rw [hgP.memaddrs, ← hgS.memaddrs]
  exact hdom

/-! ## 2. R10 empty-or-allocated property of `worldOwned` (unconditional!) -/

theorem typedRecord_mem_globalBuffers {r : String × Nat} (hr : r ∈ typedRecords) :
    r ∈ globalBuffers := by
  simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp [globalBuffers]

theorem typedRecord_mem_fixedObjects {F : Type} (s : PanSemStateFiniteExact 64 F)
    {r : String × Nat} (hr : r ∈ typedRecords) :
    (globN s r.1, if globN s r.1 = 0 then 0 else r.2) ∈ fixedObjects s := by
  unfold fixedObjects
  apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
  exact List.mem_map.2 ⟨r, typedRecord_mem_globalBuffers hr, rfl⟩

theorem worldTypedIvls_sub_worldOwned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) : ∀ i ∈ worldTypedIvls s S Nd, i ∈ worldOwned s S Nd := by
  intro i hi
  unfold worldTypedIvls at hi
  unfold worldOwned
  rcases List.mem_append.1 hi with h1 | hnd
  · apply List.mem_append.2; left
    rcases List.mem_append.1 h1 with h2 | hbal
    · rcases List.mem_append.1 h2 with h3 | hbo
      · rcases List.mem_append.1 h3 with h4 | hjr
        · rcases List.mem_append.1 h4 with htab | hrec
          · exact List.mem_append.2 (Or.inl htab)
          · apply List.mem_append.2; right
            obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hrec
            exact typedRecord_mem_fixedObjects s hr
        · apply List.mem_append.2; right
          unfold fixedObjects
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact hjr
      · apply List.mem_append.2; right
        unfold fixedObjects
        exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hbo)))
    · apply List.mem_append.2; right
      unfold fixedObjects
      exact List.mem_append.2 (Or.inr hbal)
  · exact List.mem_append.2 (Or.inr hnd)

/-- On R10, every zero-length interval in `fixedObjects s` is normalized to `(0, 0)`. -/
theorem fixedObjects_zero_len_eq {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ∀ j ∈ fixedObjects s, j.2 = 0 → j = (0, 0) := by
  intro j hj hz
  unfold fixedObjects at hj
  rcases List.mem_append.1 hj with hf1 | hbal
  · rcases List.mem_append.1 hf1 with hf2 | hbo
    · rcases List.mem_append.1 hf2 with hbuf | hjr
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hbuf
        by_cases h0 : globN s p.1 = 0
        · simp [h0]
        · simp only [h0, ↓reduceIte] at hz
          have hpos : ∀ q ∈ globalBuffers, 0 < q.2 := by decide
          exact absurd hz (Nat.ne_of_gt (hpos p hp))
      · simp only [List.mem_singleton] at hjr
        subst hjr; dsimp at hz
        have hc : globN s "journal_cap" = 0 := by omega
        simp [hc]
    · have hobj : ∀ (bo p len : Nat),
          (if bo = 0 ∨ p = 0 ∨ len = 0 then (0, 0) else (p, len)).2 = 0 →
          (if bo = 0 ∨ p = 0 ∨ len = 0 then (0, 0) else (p, len)) = (0, 0) := by
        intro bo p len h
        split_ifs at h ⊢ with hc
        · rfl
        · dsimp at h; exact absurd (Or.inr (Or.inr h)) hc
      have hblst : ∀ (bo l : Nat), ∀ x ∈ (if bo = 0 ∨ l = 0 then [(0, 0), (0, 0)]
          else [(if bo = 0 ∨ l = 0 ∨ 24 = 0 then (0, 0) else (l, 24)),
                (if bo = 0 ∨ memW s l = 0 ∨ 8 * memW s (l + 16) = 0 then (0, 0)
                 else (memW s l, 8 * memW s (l + 16)))]),
          x.2 = 0 → x = (0, 0) := by
        intro bo l x hx hxz
        by_cases hc : bo = 0 ∨ l = 0
        · simp only [hc, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl <;> rfl
        · simp only [hc, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact hobj _ _ _ hxz
          · exact hobj _ _ _ hxz
      unfold blockOutObjects at hbo
      rcases List.mem_append.1 hbo with hbo12 | h72
      · rcases List.mem_append.1 hbo12 with hbo1 | h40
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hbo1
          rcases hbo1 with rfl | rfl | rfl <;> exact hobj _ _ _ hz
        · exact hblst _ _ j h40 hz
      · exact hblst _ _ j h72 hz
  · have hlst : ∀ (l esz : Nat), ∀ x ∈ lstObjects s l esz, x.2 = 0 → x = (0, 0) := by
      intro l esz x hx hxz
      unfold lstObjects at hx
      by_cases hl0 : l = 0
      · simp only [hl0, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> rfl
      · simp only [hl0, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · dsimp at hxz; omega
        · dsimp at hxz; simp [hxz]
    unfold balObjects at hbal
    obtain ⟨ad, _, hj_ad⟩ := List.mem_flatMap.1 hbal
    rcases List.mem_cons.1 hj_ad with rfl | hj_rest
    · dsimp at hz; omega
    · rcases List.mem_append.1 hj_rest with hj123 | hj_stor
      · rcases List.mem_append.1 hj123 with hj12 | hj32
        · rcases List.mem_append.1 hj12 with hj16 | hj24
          · exact hlst _ _ j hj16 hz
          · exact hlst _ _ j hj24 hz
        · exact hlst _ _ j hj32 hz
      · obtain ⟨l, _, hj_l⟩ := List.mem_flatMap.1 hj_stor
        exact hlst _ _ j hj_l hz

/-- On R10, every interval in `worldOwned s S Nd` satisfies `(j = (0, 0)) ∨ (j.2 ≠ 0 ∧ Allocated s j)`! -/
theorem worldOwned_zero_or_allocated {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) :
    ∀ j ∈ worldOwned s S Nd, j = (0, 0) ∨ (j.2 ≠ 0 ∧ Allocated s j) := by
  obtain ⟨hT, _, hF, hTr⟩ := hW
  intro j hj
  unfold worldOwned at hj
  rcases List.mem_append.1 hj with h1 | hnd
  · rcases List.mem_append.1 h1 with htab | hfix
    · obtain ⟨u, hu, hj_fp⟩ := List.mem_flatMap.1 htab
      have hwf := (hT.2.1 u hu).1
      have hpos : j.2 ≠ 0 := by
        have hk1 := hwf.2.2.1
        have hstr := hwf.2.2.2.2.1
        have hnc := hwf.2.2.2.2.2.1
        simp only [htabFootprint, List.mem_cons, List.not_mem_nil, or_false] at hj_fp
        rcases hj_fp with rfl | rfl | rfl | rfl
        · omega
        · dsimp; rw [hstr]; have : 8 ≤ (hdr s u 0 + 7) / 8 * 8 := by omega
          exact Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))
        · dsimp; omega
        · dsimp; omega
      exact Or.inr ⟨hpos, ((hT.2.1 u hu).2 j hj_fp).1⟩
    · rcases hF.1 j hfix with hz | ⟨hal, _⟩
      · exact Or.inl (fixedObjects_zero_len_eq s j hfix hz)
      · by_cases hz : j.2 = 0
        · exact Or.inl (fixedObjects_zero_len_eq s j hfix hz)
        · exact Or.inr ⟨hz, hal⟩
  · obtain ⟨n, hn, hj_n⟩ := List.mem_flatMap.1 hnd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj_n
    rcases hj_n with rfl | rfl
    · have hpos : (nodeIvl s n).2 ≠ 0 := by
        show nodeSize (memW s n) ≠ 0
        unfold nodeSize; split_ifs <;> omega
      exact Or.inr ⟨hpos, (hTr.1.1 n hn).2.1⟩
    · unfold nodePath
      split_ifs with hp
      · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hp.1 with h0 | ⟨_, hal, _⟩
        · exact absurd h0 hp.2
        · exact Or.inr ⟨hp.2, hal⟩
      · exact Or.inl rfl

theorem worldOwned_zero_aligned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) :
    ∀ j ∈ worldOwned s S Nd, j.2 = 0 → j.1 % 8 = 0 := by
  intro j hj hz
  rcases worldOwned_zero_or_allocated hW j hj with rfl | ⟨hnz, _⟩
  · omega
  · exact absurd hz hnz

theorem ivl_disj_free_of_zero_or_allocated {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hag : AllocatorGrows s post)
    {j : Ivl} (hj : j = (0, 0) ∨ (j.2 ≠ 0 ∧ Allocated s j)) :
    Disj j (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") ∧
    Disj j (globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr") := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  obtain ⟨_, hp_hp, hp_fm, hp_sc, _⟩ := hAp
  have hg_hp := hag.1; have hg_sc := hag.2
  rcases hj with rfl | ⟨_, ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩⟩
  · exact ⟨disj_zero_left _, disj_zero_left _⟩
  · exact ⟨Or.inr (Or.inr (Or.inl (by dsimp; omega))), Or.inr (Or.inr (Or.inl (by dsimp; omega)))⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (by dsimp; omega))), Or.inr (Or.inr (Or.inr (by dsimp; omega)))⟩

theorem ivl_unhit_free_of_zero_or_allocated {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hag : AllocatorGrows s post)
    {keep : List Ivl} {fresh : Ivl}
    (hfr : FrameOutside s post keep fresh)
    (hk_sub : ∀ k ∈ keep, k = (globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr"))
    (hf_eq : fresh = (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    {j : Ivl} (hj : j = (0, 0) ∨ (j.2 ≠ 0 ∧ Allocated s j)) :
    IvlUnhit s post j := by
  obtain ⟨hd_hp, hd_sc⟩ := ivl_disj_free_of_zero_or_allocated hAs hAp hag hj
  obtain ⟨_, _, _, _, _, hs_hp8, _, hs_sc8⟩ := hAs
  obtain ⟨_, _, _, _, _, hp_hp8, _, hp_sc8⟩ := hAp
  have hg_hp := hag.1; have hg_sc := hag.2
  have hj_z : j.2 = 0 → j.1 % 8 = 0 := by
    intro hz; rcases hj with rfl | ⟨hnz, _⟩
    · omega
    · exact absurd hz hnz
  exact ivlUnhit_of_frameOutside_aligned hfr hj_z
    (fun k hk => by rw [hk_sub k hk]; exact ⟨hp_sc8, by omega⟩)
    (by rw [hf_eq]; exact ⟨hs_hp8, by omega⟩)
    (fun k hk => by rw [hk_sub k hk]; exact hd_sc)
    (by rw [hf_eq]; exact hd_hp)

theorem heap_ivl_survives_step {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {old new R : List Ivl}
    (hog : OwnedGrows s post old new)
    (hfr : FrameOutside s post (old ++ R ++ [freeGap s]) (heapFree s))
    (hold_z : ∀ j ∈ old, j.2 = 0 → j.1 % 8 = 0)
    (hR_z : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    {b : Ivl} (hb1 : b.1 % 8 = 0) (hb2 : b.2 % 8 = 0)
    (hb_in : Inside b sourceBase (globN s "heap_ptr"))
    (hb_old : ∀ j ∈ old, Disj b j)
    (hb_R : ∀ j ∈ R, Disj b j) :
    Inside b sourceBase (globN post "heap_ptr") ∧
    (∀ o ∈ new, Disj b o) ∧
    IvlUnhit s post b := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  refine ⟨⟨hb_in.1, Nat.le_trans hb_in.2 hhp⟩, ?_, ?_⟩
  · intro o ho
    rcases hog o ho with rfl | ⟨j, hj, hin⟩ | hfresh
    · exact disj_zero_right b
    · exact disj_of_inside_right hin (hb_old j hj)
    · exact Or.inr (Or.inr (Or.inl (Nat.le_trans hb_in.2 hfresh.1)))
  · intro a ha8 hhit
    apply hfr a
    · intro j hj hcj
      rcases List.mem_append.1 hj with hj12 | hfg
      · rcases List.mem_append.1 hj12 with hj_old | hj_R
        · exact not_cellHits_of_disj hb1 hb2 ha8 (hold_z j hj_old) hhit (hb_old j hj_old) hcj
        · exact not_cellHits_of_disj hb1 hb2 ha8 (hR_z j hj_R) hhit (hb_R j hj_R) hcj
      · simp only [List.mem_singleton] at hfg; subst hfg
        obtain ⟨hc1, hc2⟩ := hhit
        obtain ⟨hj1, hj2⟩ := hcj
        unfold freeGap at hj1 hj2
        unfold Inside at hb_in
        dsimp at hj1 hj2
        omega
    · intro ⟨hf1, hf2⟩
      obtain ⟨hc1, hc2⟩ := hhit
      unfold heapFree at hf1 hf2
      unfold Inside at hb_in
      dsimp at hf1 hf2
      omega

/-! ## 3. R10 World-Typing Congruence, Table Steps, and `MsgReady` Preservation -/

theorem freeChain_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {nodes ncap : Nat} (hn8 : nodes % 8 = 0) (hhi : nodes + (ncap + 1) * 32 ≤ 2 ^ 64)
    (hu : IvlUnhit s post (nodes, (ncap + 1) * 32)) :
    ∀ (Fr : List Nat) (head : Nat),
      (∀ f ∈ Fr, 1 ≤ f ∧ f ≤ ncap) →
      (FreeChain post nodes head Fr ↔ FreeChain s nodes head Fr)
  | [], head, _ => Iff.rfl
  | f :: rest, head, hFr => by
    have hf : 1 ≤ f ∧ f ≤ ncap := hFr f (by simp)
    have hnd : nodeF post nodes f 0 = nodeF s nodes f 0 := by
      unfold nodeF
      exact memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
    simp only [FreeChain, hnd]
    exact and_congr Iff.rfl (freeChain_congr_unhit hn8 hhi hu rest _ (fun x hx => hFr x (by simp [hx])))

theorem htabFootprint_eq_of_hdr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : Nat} (ht8 : t % 8 = 0) (hhdr_hi : t + 88 ≤ 2 ^ 64) (hu : IvlUnhit s post (t, 88)) :
    (∀ k, k < 11 → hdr post t k = hdr s t k) ∧ htabFootprint post t = htabFootprint s t := by
  have hhdr : ∀ k, k < 11 → hdr post t k = hdr s t k := fun k hk => by
    unfold hdr
    exact memW_eq_of_ivlUnhit hu (by omega) hhdr_hi ⟨by omega, by omega⟩
  refine ⟨hhdr, ?_⟩
  simp only [htabFootprint, hhdr 1 (by omega), hhdr 4 (by omega), hhdr 5 (by omega),
    hhdr 6 (by omega), hhdr 10 (by omega)]

theorem nodup_len_le {l : List Nat} {n : Nat} (hnd : l.Nodup)
    (hr : ∀ x ∈ l, 1 ≤ x ∧ x < n) : l.length ≤ n - 1 := by
  have hsub : l.toFinset ⊆ Finset.Ico 1 n := by
    intro x hx
    simp only [List.mem_toFinset] at hx
    simp only [Finset.mem_Ico]
    exact hr x hx
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Nat.card_Ico] at this
  exact this

theorem htabValues_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : Nat} (hwf : HtabWF s t)
    (hu : ∀ i ∈ htabFootprint s t, IvlUnhit s post i) :
    htabValues post t = htabValues s t := by
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hfp := hwf.1
  have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
  have hnd_fp : (hdr s t 5, (hdr s t 10 + 1) * 32) ∈ htabFootprint s t := by simp [htabFootprint]
  have hord_fp : (hdr s t 6, (hdr s t 10 + 1) * 8) ∈ htabFootprint s t := by simp [htabFootprint]
  have ht8 : t % 8 = 0 := (hfp _ ht_fp).2.1
  have hnd8 : (hdr s t 5) % 8 = 0 := (hfp _ hnd_fp).2.1
  have hord8 : (hdr s t 6) % 8 = 0 := (hfp _ hord_fp).2.1
  have hhdr_hi : t + 88 ≤ 2 ^ 64 := by have := (hfp _ ht_fp).1.2; omega
  obtain ⟨hhdr, _⟩ := htabFootprint_eq_of_hdr_unhit ht8 hhdr_hi (hu _ ht_fp)
  have hnd_hi : hdr s t 5 + (hdr s t 10 + 1) * 32 ≤ 2 ^ 64 := by have := (hfp _ hnd_fp).1.2; omega
  have hord_hi : hdr s t 6 + (hdr s t 10 + 1) * 8 ≤ 2 ^ 64 := by have := (hfp _ hord_fp).1.2; omega
  obtain ⟨-, -, -, -, -, _, _, hnext_le, L, I, Fr, hLlen, hnodup, hmem, _, hL, -⟩ := hwf
  have hlen_all := nodup_len_le hnodup (fun x hx => (hmem x).1 hx)
  have hlen_L : L.length ≤ hdr s t 10 := by
    simp only [List.length_append] at hlen_all; omega
  unfold htabValues
  rw [hhdr 3 (by omega), hhdr 5 (by omega), hhdr 6 (by omega)]
  apply List.map_congr_left
  intro idx hidx
  rw [List.mem_range] at hidx
  have hidx_L : idx < L.length := by omega
  have hLi_mem : L[idx] ∈ L ++ I ++ Fr := by
    apply List.mem_append.2; left; apply List.mem_append.2; left; exact List.getElem_mem hidx_L
  have hLi_bound : 1 ≤ L[idx] ∧ L[idx] ≤ hdr s t 10 := by
    have := (hmem L[idx]).1 hLi_mem; omega
  have hord_eq : memW post (hdr s t 6 + 8 * idx) = memW s (hdr s t 6 + 8 * idx) :=
    memW_eq_of_ivlUnhit (hu _ hord_fp) (by omega) hord_hi ⟨by omega, by omega⟩
  rw [hord_eq, (hL idx hidx_L).1]
  unfold nodeF
  exact memW_eq_of_ivlUnhit (hu _ hnd_fp) (by omega) hnd_hi ⟨by omega, by omega⟩

theorem htabValuesIn_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : Nat} {S S' : List Nat} (hwf : HtabWF s t)
    (hu : ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hsub : ∀ x ∈ S, x ∈ S')
    (hval : HtabValuesIn s t S) :
    HtabValuesIn post t S' := by
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hfp := hwf.1
  have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
  have ht8 : t % 8 = 0 := (hfp _ ht_fp).2.1
  have hhdr_hi : t + 88 ≤ 2 ^ 64 := by have := (hfp _ ht_fp).1.2; omega
  obtain ⟨hhdr, _⟩ := htabFootprint_eq_of_hdr_unhit ht8 hhdr_hi (hu _ ht_fp)
  have hvals := htabValues_eq_of_unhit hwf hu
  intro idx hidx
  rw [hhdr 3 (by omega)] at hidx
  have hmem_s : nodeF s (hdr s t 5) (memW s (hdr s t 6 + 8 * idx)) 8 ∈ S := hval idx hidx
  have hget : (htabValues post t)[idx]? = (htabValues s t)[idx]? := by rw [hvals]
  simp only [htabValues, List.getElem?_map, List.getElem?_range, hhdr 3 (by omega), hidx,
    Option.map_some, Option.some.injEq] at hget
  rw [hget]
  exact hsub _ hmem_s

theorem htabWF_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post)
    {t : Nat} (hwf : HtabWF s t)
    (hu : ∀ i ∈ htabFootprint s t, IvlUnhit s post i) :
    HtabWF post t := by
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hfp := hwf.1
  have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
  have hnd_fp : (hdr s t 5, (hdr s t 10 + 1) * 32) ∈ htabFootprint s t := by simp [htabFootprint]
  have hord_fp : (hdr s t 6, (hdr s t 10 + 1) * 8) ∈ htabFootprint s t := by simp [htabFootprint]
  have ht8 : t % 8 = 0 := (hfp _ ht_fp).2.1
  have hnd8 : (hdr s t 5) % 8 = 0 := (hfp _ hnd_fp).2.1
  have hord8 : (hdr s t 6) % 8 = 0 := (hfp _ hord_fp).2.1
  have hhdr_hi : t + 88 ≤ 2 ^ 64 := by have := (hfp _ ht_fp).1.2; omega
  obtain ⟨hhdr, hfp_eq⟩ := htabFootprint_eq_of_hdr_unhit ht8 hhdr_hi (hu _ ht_fp)
  have hnd_hi : hdr s t 5 + (hdr s t 10 + 1) * 32 ≤ 2 ^ 64 := by have := (hfp _ hnd_fp).1.2; omega
  have hord_hi : hdr s t 6 + (hdr s t 10 + 1) * 8 ≤ 2 ^ 64 := by have := (hfp _ hord_fp).1.2; omega
  obtain ⟨hfp1, hfp2, hk1, hk2, hstr, hncap, hnext1, hnext2,
    L, I, Fr, hLlen, hnodup, hmem, hcntI, hL, hI, hr0, hrpos, hnroot, hpI, hdep, hfc⟩ := hwf
  have hlen_all := nodup_len_le hnodup (fun x hx => (hmem x).1 hx)
  have hlen_L : L.length ≤ hdr s t 10 := by
    simp only [List.length_append] at hlen_all; omega
  have hnd_eq : ∀ n, 1 ≤ n → n ≤ hdr s t 10 → ∀ off ∈ ([0, 8, 16, 24] : List Nat),
      nodeF post (hdr s t 5) n off = nodeF s (hdr s t 5) n off := by
    intro n hn1 hn2 off hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    unfold nodeF
    rcases hoff with rfl | rfl | rfl | rfl <;>
      exact memW_eq_of_ivlUnhit (hu _ hnd_fp) (by omega) hnd_hi ⟨by omega, by omega⟩
  have hLI_bound : ∀ n ∈ L ++ I, 1 ≤ n ∧ n ≤ hdr s t 10 := fun n hn => by
    have := (hmem n).1 (List.mem_append.2 (Or.inl hn)); omega
  unfold HtabWF
  rw [hfp_eq, hhdr 0 (by omega), hhdr 1 (by omega), hhdr 3 (by omega), hhdr 5 (by omega),
    hhdr 6 (by omega), hhdr 7 (by omega), hhdr 8 (by omega), hhdr 9 (by omega), hhdr 10 (by omega)]
  refine ⟨fun i hi => ⟨(hfp1 i hi).1, wordsOK_transfer hgS hgP (hfp1 i hi).2⟩,
    hfp2, hk1, hk2, hstr, hncap, hnext1, hnext2, L, I, Fr, hLlen, hnodup, hmem, hcntI,
    ?_, ?_, hr0, ?_, ?_, ?_, ?_, ?_⟩
  · intro idx hidx
    have hLi : L[idx] ∈ L ++ I := List.mem_append.2 (Or.inl (List.getElem_mem hidx))
    obtain ⟨hb1, hb2⟩ := hLI_bound L[idx] hLi
    have hord_eq : memW post (hdr s t 6 + 8 * idx) = memW s (hdr s t 6 + 8 * idx) :=
      memW_eq_of_ivlUnhit (hu _ hord_fp) (by omega) hord_hi ⟨by omega, by omega⟩
    rw [hord_eq, hnd_eq L[idx] hb1 hb2 24 (by simp), hnd_eq L[idx] hb1 hb2 16 (by simp)]
    exact hL idx hidx
  · intro n hn
    have hnLI : n ∈ L ++ I := List.mem_append.2 (Or.inr hn)
    obtain ⟨hb1, hb2⟩ := hLI_bound n hnLI
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := hI n hn
    obtain ⟨h8_1, h8_2⟩ := hLI_bound _ hc2
    obtain ⟨h16_1, h16_2⟩ := hLI_bound _ hc3
    rw [hnd_eq n hb1 hb2 24 (by simp), hnd_eq n hb1 hb2 8 (by simp), hnd_eq n hb1 hb2 16 (by simp),
      hnd_eq _ h8_1 h8_2 0 (by simp), hnd_eq _ h16_1 h16_2 0 (by simp)]
    exact ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩
  · intro hpos
    obtain ⟨hrm, hrp⟩ := hrpos hpos
    obtain ⟨hb1, hb2⟩ := hLI_bound _ hrm
    rw [hnd_eq _ hb1 hb2 0 (by simp)]
    exact ⟨hrm, hrp⟩
  · intro n hn
    have hnLI : n ∈ L ++ I := List.mem_append.2 (Or.inr hn)
    obtain ⟨hb1, hb2⟩ := hLI_bound n hnLI
    rw [hnd_eq n hb1 hb2 8 (by simp), hnd_eq n hb1 hb2 16 (by simp)]
    exact hnroot n hn
  · intro n hn hnr
    obtain ⟨hb1, hb2⟩ := hLI_bound n hn
    rw [hnd_eq n hb1 hb2 0 (by simp)]
    exact hpI n hn hnr
  · obtain ⟨dep, hdep⟩ := hdep
    refine ⟨dep, fun n hn hnr => ?_⟩
    obtain ⟨hb1, hb2⟩ := hLI_bound n hn
    have hp_mem : nodeF s (hdr s t 5) n 0 ∈ L ++ I := List.mem_append.2 (Or.inr (hpI n hn hnr))
    obtain ⟨hpb1, hpb2⟩ := hLI_bound _ hp_mem
    rw [hnd_eq n hb1 hb2 0 (by simp), hnd_eq _ hpb1 hpb2 8 (by simp), hnd_eq _ hpb1 hpb2 16 (by simp)]
    exact hdep n hn hnr
  · exact (freeChain_congr_unhit hnd8 hnd_hi (hu _ hnd_fp) Fr (hdr s t 9)
      (fun f hf => by have := (hmem f).1 (List.mem_append.2 (Or.inr hf)); omega)).2 hfc

def WorldGlobalsSame {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  (∀ gn ∈ globalBuffers, globN post gn.1 = globN s gn.1) ∧
  (∀ g ∈ globalTableRoots, globN post g = globN s g) ∧
  globN post "journal" = globN s "journal" ∧
  globN post "journal_cap" = globN s "journal_cap" ∧
  globN post "journal_n" = globN s "journal_n"

theorem globN_eq_of_lookup {F : Type} {s post : PanSemStateFiniteExact 64 F} {name : String}
    (h : s.globals.lookup (ofString name) = post.globals.lookup (ofString name)) :
    globN post name = globN s name := by
  simp only [globN, ← h]

theorem worldGlobalsSame_of_globals_eq {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hg : post.globals = s.globals) : WorldGlobalsSame s post := by
  refine ⟨fun _ _ => by simp [globN, hg], fun _ _ => by simp [globN, hg],
    by simp [globN, hg], by simp [globN, hg], by simp [globN, hg]⟩

theorem worldGlobalsSame_of_globalsKept {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {gw : List String}
    (hkept : GlobalsKept gw s post)
    (hgb : ∀ gn ∈ globalBuffers, ofString gn.1 ∉ gw.map ofString)
    (hgtr : ∀ g ∈ globalTableRoots, ofString g ∉ gw.map ofString)
    (hj : ofString "journal" ∉ gw.map ofString)
    (hjc : ofString "journal_cap" ∉ gw.map ofString)
    (hjn : ofString "journal_n" ∉ gw.map ofString) :
    WorldGlobalsSame s post :=
  ⟨fun gn hgn => globN_eq_of_lookup (hkept _ (hgb gn hgn)),
   fun g hg => globN_eq_of_lookup (hkept _ (hgtr g hg)),
   globN_eq_of_lookup (hkept _ hj),
   globN_eq_of_lookup (hkept _ hjc),
   globN_eq_of_lookup (hkept _ hjn)⟩

theorem rec_word_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hF : FixedTyped s)
    (g : String) (sz : Nat) (hrec : (g, sz) ∈ typedRecords)
    (hg_eq : globN post g = globN s g) (hgnz : globN s g ≠ 0)
    (hu : IvlUnhit s post (globN s g, sz))
    {k : Nat} (hk8 : k % 8 = 0) (hksz : k + 8 ≤ sz) :
    memW post (globN post g + k) = memW s (globN s g + k) := by
  rw [hg_eq]
  have hmem_fix := typedRecord_mem_fixedObjects s hrec
  simp only [hgnz, ↓reduceIte] at hmem_fix
  have hsz_pos : sz ≠ 0 := by omega
  rcases hF.1 _ hmem_fix with h0 | ⟨hal, hwords⟩
  · exact absurd h0 hsz_pos
  · have hhi := (ivl_allocated_bound hA hal).2
    have hg8 : (globN s g) % 8 = 0 := hwords.1
    exact memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩

theorem blockOutObjects_eq_of_bo_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hF : FixedTyped s) (hbo_eq : globN post "bo" = globN s "bo")
    (hbo_lst_ok : globN s "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) ≠ 0 →
      LstOK s (memW s (globN s "bo" + k)))
    (hk24 : globN s "bo" ≠ 0 → memW post (globN s "bo" + 24) = memW s (globN s "bo" + 24))
    (hk32 : globN s "bo" ≠ 0 → memW post (globN s "bo" + 32) = memW s (globN s "bo" + 32))
    (hk40 : globN s "bo" ≠ 0 → memW post (globN s "bo" + 40) = memW s (globN s "bo" + 40))
    (hk56 : globN s "bo" ≠ 0 → memW post (globN s "bo" + 56) = memW s (globN s "bo" + 56))
    (hk72 : globN s "bo" ≠ 0 → memW post (globN s "bo" + 72) = memW s (globN s "bo" + 72))
    (hk80 : globN s "bo" ≠ 0 → memW post (globN s "bo" + 80) = memW s (globN s "bo" + 80))
    (hl40 : globN s "bo" ≠ 0 → memW s (globN s "bo" + 40) ≠ 0 →
      IvlUnhit s post (memW s (globN s "bo" + 40), 24))
    (hl72 : globN s "bo" ≠ 0 → memW s (globN s "bo" + 72) ≠ 0 →
      IvlUnhit s post (memW s (globN s "bo" + 72), 24)) :
    blockOutObjects post = blockOutObjects s ∧
    (globN post "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat), memW post (globN post "bo" + k) ≠ 0 →
      LstOK post (memW post (globN post "bo" + k))) := by
  by_cases hbo : globN s "bo" = 0
  · refine ⟨?_, fun hp => absurd (hbo_eq.trans hbo) hp⟩
    simp [blockOutObjects, hbo_eq, hbo]
  · have hlst_hdr : ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) ≠ 0 →
        ∀ off ∈ ([0, 8, 16] : List Nat),
          memW post (memW s (globN s "bo" + k) + off) = memW s (memW s (globN s "bo" + k) + off) := by
      intro k hk hknz off hoff
      have hmem_bo : (memW s (globN s "bo" + k), 24) ∈ blockOutObjects s := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> simp [blockOutObjects, hbo, hknz]
      have hmem_fix : (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
        unfold fixedObjects
        exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hmem_bo)))
      rcases hF.1 _ hmem_fix with h0 | ⟨hal, hwords⟩
      · simp at h0
      · have hhi := (ivl_allocated_bound hA hal).2
        have hp8 : (memW s (globN s "bo" + k)) % 8 = 0 := hwords.1
        have hu : IvlUnhit s post (memW s (globN s "bo" + k), 24) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl
          · exact hl40 hbo hknz
          · exact hl72 hbo hknz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        rcases hoff with rfl | rfl | rfl <;>
          exact memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
    constructor
    · unfold blockOutObjects
      simp only [hbo_eq, hbo, false_or, hk24 hbo, hk32 hbo, hk40 hbo, hk56 hbo, hk72 hbo, hk80 hbo]
      congr 1; congr 1
      · by_cases h40 : memW s (globN s "bo" + 40) = 0
        · simp [h40]
        · have h0 := hlst_hdr 40 (by simp) h40 0 (by simp)
          have h16 := hlst_hdr 40 (by simp) h40 16 (by simp)
          simp only [Nat.add_zero] at h0
          simp [h40, h0, h16]
      · by_cases h72 : memW s (globN s "bo" + 72) = 0
        · simp [h72]
        · have h0 := hlst_hdr 72 (by simp) h72 0 (by simp)
          have h16 := hlst_hdr 72 (by simp) h72 16 (by simp)
          simp only [Nat.add_zero] at h0
          simp [h72, h0, h16]
    · intro _ k hk hknz
      rw [hbo_eq] at hknz ⊢
      have hk_eq : memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        · exact hk40 hbo
        · exact hk72 hbo
      rw [hk_eq] at hknz ⊢
      unfold LstOK
      rw [hlst_hdr k hk hknz 8 (by simp), hlst_hdr k hk hknz 16 (by simp)]
      exact hbo_lst_ok hbo k hk hknz

theorem balRecords_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S : List Nat} (hT : TablesTyped s S)
    (hbal_eq : globN post "bal_accounts" = globN s "bal_accounts")
    (hu : globN s "bal_accounts" ≠ 0 → ∀ i ∈ htabFootprint s (globN s "bal_accounts"), IvlUnhit s post i) :
    balRecords post = balRecords s := by
  unfold balRecords
  rw [hbal_eq]
  by_cases hbal : globN s "bal_accounts" = 0
  · simp [hbal]
  · simp only [hbal, ↓reduceIte]
    have hmem_S : globN s "bal_accounts" ∈ S := by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hbal
      · exact hm
    have hwf := (hT.2.1 _ hmem_S).1
    exact htabValues_eq_of_unhit hwf (hu hbal)

theorem balObjects_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hbal_eq : globN post "bal_accounts" = globN s "bal_accounts")
    (hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hu_bal : ∀ i ∈ balObjects s, IvlUnhit s post i)
    (hm_low : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
    balObjects post = balObjects s ∧
    (∀ ad ∈ balRecords post, memW post ad = memW s ad ∧ memW post (ad + 8) = memW s (ad + 8) ∧
      htabValues post (memW post ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW post (ad + k))) ∧
      (∀ l ∈ htabValues post (memW post ad), LstOK post l)) := by
  have hrecs : balRecords post = balRecords s :=
    balRecords_eq_of_unhit hT hbal_eq (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_tab _ hm)
  have hmem_fix_of_bal : ∀ i ∈ balObjects s, i ∈ fixedObjects s := fun i hi => by
    unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)
  have hlst_eq_nz : ∀ l, l ≠ 0 → (l, 24) ∈ balObjects s →
      memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16) := by
    intro l _ hl_bal
    rcases hF.1 _ (hmem_fix_of_bal _ hl_bal) with h0 | ⟨hal_l, hw_l⟩
    · simp at h0
    have hhi_l := (ivl_allocated_bound hA hal_l).2
    have hl8 : l % 8 = 0 := hw_l.1
    have hul := hu_bal _ hl_bal
    refine ⟨?_, ?_, ?_⟩
    · simpa using memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
    · exact memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
    · exact memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
  have hlstObj_congr : ∀ l esz, (l ≠ 0 → (l, 24) ∈ balObjects s) →
      lstObjects post l esz = lstObjects s l esz ∧ (LstOK s l → LstOK post l) := by
    intro l esz hmem_fn
    by_cases hl0 : l = 0
    · subst hl0
      refine ⟨by simp [lstObjects], fun hok => ?_⟩
      unfold LstOK at hok ⊢
      simp only [Nat.zero_add, hm_low.1, hm_low.2] at hok ⊢
      exact hok
    · obtain ⟨h0, h8, h16⟩ := hlst_eq_nz l hl0 (hmem_fn hl0)
      refine ⟨by simp [lstObjects, hl0, h0, h16], fun hok => ?_⟩
      unfold LstOK at hok ⊢
      rw [h8, h16]; exact hok
  have had_props : ∀ ad ∈ balRecords s,
      (∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off)) ∧
      htabValues post (memW s ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat),
        lstObjects post (memW s (ad + k)) (if k = 16 then 40 else if k = 24 then 16 else 24) =
          lstObjects s (memW s (ad + k)) (if k = 16 then 40 else if k = 24 then 16 else 24) ∧
        LstOK post (memW s (ad + k))) ∧
      (∀ l ∈ htabValues s (memW s ad), lstObjects post l 40 = lstObjects s l 40 ∧ LstOK post l) := by
    intro ad had
    have had_bal : (ad, 40) ∈ balObjects s := by
      unfold balObjects
      exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
    rcases hF.1 _ (hmem_fix_of_bal _ had_bal) with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (ivl_allocated_bound hA hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hoff_eq : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off) := by
      intro off hoff
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
        exact memW_eq_of_ivlUnhit (hu_bal _ had_bal) (by omega) hhi_ad ⟨by omega, by omega⟩
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hvals_ad : htabValues post (memW s ad) = htabValues s (memW s ad) :=
      htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_tab _ had_T.1)
    refine ⟨hoff_eq, hvals_ad, ?_, ?_⟩
    · intro k hk
      have hc := hlstObj_congr (memW s (ad + k)) (if k = 16 then 40 else if k = 24 then 16 else 24) (fun hnz => by
        unfold balObjects
        refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> simp [lstObjects, hnz])
      exact ⟨hc.1, hc.2 (had_T.2.2.1 k hk)⟩
    · intro l hl
      have hc := hlstObj_congr l 40 (fun hnz => by
        unfold balObjects
        refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
        apply List.mem_cons_of_mem
        apply List.mem_append.2; right
        exact List.mem_flatMap.2 ⟨l, hl, by simp [lstObjects, hnz]⟩)
      exact ⟨hc.1, hc.2 (had_T.2.2.2 l hl)⟩
  constructor
  · unfold balObjects
    rw [hrecs]
    apply List.flatMap_congr
    intro ad had
    obtain ⟨hoff_eq, hvals_ad, hklst, hllst⟩ := had_props ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h16 := hoff_eq 16 (by simp)
    have h24 := hoff_eq 24 (by simp)
    have h32 := hoff_eq 32 (by simp)
    have hk16 := (hklst 16 (by simp)).1; simp only [↓reduceIte] at hk16
    have hk24 := (hklst 24 (by simp)).1; simp only [show ¬(24 = 16) by decide, ↓reduceIte] at hk24
    have hk32 := (hklst 32 (by simp)).1; simp only [show ¬(32 = 16) by decide, show ¬(32 = 24) by decide, ↓reduceIte] at hk32
    have htail : (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
      rw [h0, hvals_ad]
      exact List.flatMap_congr fun l hl => (hllst l hl).1
    rw [htail, h16, h24, h32, hk16, hk24, hk32]
  · intro ad had
    rw [hrecs] at had
    obtain ⟨hoff_eq, hvals_ad, hklst, hllst⟩ := had_props ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h8 := hoff_eq 8 (by simp)
    refine ⟨h0, h8, by rw [h0, hvals_ad], ?_, ?_⟩
    · intro k hk
      have hk_in : k ∈ ([0, 8, 16, 24, 32] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl <;> simp
      rw [hoff_eq k hk_in]
      exact (hklst k hk).2
    · intro l hl
      rw [h0, hvals_ad] at hl
      exact (hllst l hl).2

theorem worldRoleSlots_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hgs : WorldGlobalsSame s post)
    (hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80))
    (hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72))
    (hu_bal : ∀ i ∈ balObjects s, IvlUnhit s post i)
    (hm_low : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
    worldRoleSlots post = worldRoleSlots s := by
  have hws_g : globN post "ws" = globN s "ws" := hgs.1 ("ws", 40) (by simp [globalBuffers])
  have hbs_g : globN post "bs" = globN s "bs" := hgs.1 ("bs", 80) (by simp [globalBuffers])
  have hts_g : globN post "ts" = globN s "ts" := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hbia_g : globN post "bal_idx_accts" = globN s "bal_idx_accts" := hgs.2.1 "bal_idx_accts" (by simp [globalTableRoots])
  have hbis_g : globN post "bal_idx_stor" = globN s "bal_idx_stor" := hgs.2.1 "bal_idx_stor" (by simp [globalTableRoots])
  have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] =
      recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
    unfold recRoles
    by_cases h : globN s "ws" = 0
    · simp [hws_g, h]
    · simp only [hws_g, h, ↓reduceIte]
      apply List.map_congr_left
      intro ⟨k, r⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      have hw := rec_word_eq_of_unhit hA hF "ws" 40 (by simp [typedRecords]) hws_g h (hu_ws h) hk.1 hk.2
      simp only [hws_g] at hw
      simp [hw]
  have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
    unfold recRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · simp only [hbs_g, h, ↓reduceIte]
      apply List.map_congr_left
      intro ⟨k, r⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      have hw := rec_word_eq_of_unhit hA hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) hk.1 hk.2
      simp only [hbs_g] at hw
      simp [hw]
  have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
      recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
    unfold recRoles
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · simp only [hts_g, h, ↓reduceIte]
      apply List.map_congr_left
      intro ⟨k, r⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      have hw := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) hk.1 hk.2
      simp only [hts_g] at hw
      simp [hw]
  have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
    unfold nestRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · have hw32 := rec_word_eq_of_unhit hA hF "bs" 80 (by simp [typedRecords]) hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
      simp only [hbs_g] at hw32 ⊢
      simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "bs" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "bs" + 32) ∈ S := by
          rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
  have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
    unfold nestRoles
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · have hw32 := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      simp only [hts_g] at hw32 ⊢
      simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "ts" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "ts" + 32) ∈ S := by
          rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rw [htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
  have hrecs_bal := balRecords_eq_of_unhit hT hba_g (fun hnz => by
    rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 hnz
    · exact hu_tab _ hm)
  have hbal_part := (balObjects_eq_of_unhit hA hT hF hba_g hu_tab hu_bal hm_low).2
  unfold worldRoleSlots
  rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hnest_ts, hrecs_bal]
  congr 1; congr 1
  apply List.flatMap_congr
  intro ad had
  rw [← hrecs_bal] at had
  obtain ⟨h0, h8, _⟩ := hbal_part ad had
  rw [h0, h8]

theorem journalRoleSlots_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post)
    (hA : ArenaOK s) (hag : AllocatorGrows s post)
    {S S' : List Nat} (hsub : ∀ x ∈ S, x ∈ S')
    (hJ : JournalTyped s S) (hF : FixedTyped s)
    (hgs : WorldGlobalsSame s post)
    (hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72))
    (hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap")) :
    journalRoleSlots post = journalRoleSlots s ∧ JournalTyped post S' := by
  have hts_g : globN post "ts" = globN s "ts" := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hj_g := hgs.2.2.1
  have hjc_g := hgs.2.2.2.1
  have hjn_g := hgs.2.2.2.2
  have hrole_eq : ∀ t, journalRole post t = journalRole s t := fun t => by
    unfold journalRole
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · have hw16 := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 16) (by omega) (by omega)
      have hw32 := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      have hw48 := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 48) (by omega) (by omega)
      have hw64 := rec_word_eq_of_unhit hA hF "ts" 72 (by simp [typedRecords]) hts_g h (hu_ts h) (k := 64) (by omega) (by omega)
      simp only [hts_g] at hw16 hw32 hw48 hw64 ⊢
      rw [hw16, hw32, hw48, hw64]
  have hj_cells : ∀ i, i < globN s "journal_n" →
      memW post (globN s "journal" + 32 * i) = memW s (globN s "journal" + 32 * i) ∧
      memW post (globN s "journal" + 32 * i + 16) = memW s (globN s "journal" + 32 * i + 16) ∧
      memW post (globN s "journal" + 32 * i + 24) = memW s (globN s "journal" + 32 * i + 24) := by
    intro i hi
    have hcnz : globN s "journal_cap" ≠ 0 := by have := hJ.1; omega
    rcases hJ.2.2.1 with h0 | ⟨hal, hwords⟩
    · exact absurd h0 hcnz
    · have hhi := (ivl_allocated_bound hA hal).2
      have hj8 : (globN s "journal") % 8 = 0 := hwords.1
      have huj := hu_jr hcnz
      have hle : i < globN s "journal_cap" := lt_of_lt_of_le hi hJ.1
      refine ⟨?_, ?_, ?_⟩
      · exact memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩
      · exact memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩
      · exact memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩
  constructor
  · unfold journalRoleSlots
    rw [hjn_g, hj_g]
    apply List.flatMap_congr
    intro i hi
    rw [List.mem_range] at hi
    obtain ⟨hc0, hc16, hc24⟩ := hj_cells i hi
    simp only [hc0, hc16, hc24, hrole_eq]
  · unfold JournalTyped
    rw [hjn_g, hjc_g, hj_g]
    refine ⟨hJ.1, hJ.2.1, ?_, ?_⟩
    · rcases hJ.2.2.1 with h0 | ⟨hal, hwords⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hgS hgP hwords⟩
    · intro i hi
      rw [(hj_cells i hi).1]
      exact hsub _ (hJ.2.2.2 i hi)

theorem nodeHeap_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) (hbe : post.be = s.be)
    (hag : AllocatorGrows s post)
    {Nd : List Nat} (hN : NodeHeap s Nd)
    (hu : ∀ o ∈ nodeExtents s Nd, IvlUnhit s post o) :
    NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hn_props : ∀ n ∈ Nd,
      memW post n = memW s n ∧
      nodeIvl post n = nodeIvl s n ∧
      (∀ k, k < nodeSize (memW s n) / 8 → memW post (n + 8 * k) = memW s (n + 8 * k)) ∧
      nodePath post n = nodePath s n ∧
      ((memW s n = 1 ∨ memW s n = 2) → KeyIn post Nd (memW post (n + 32)) (memW post (n + 40))) := by
    intro n hn
    obtain ⟨hk3, hal_n, hin_n, hw_n, _, _, hkey_n, _⟩ := hN.1 n hn
    have hhi_n : n + nodeSize (memW s n) ≤ 2 ^ 64 := by
      have := hin_n.2; dsimp [nodeIvl] at this; omega
    have hn8 : n % 8 = 0 := hw_n.1
    have hu_n : IvlUnhit s post (n, nodeSize (memW s n)) := by
      apply hu; unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩
    have hsz_ge32 : 32 ≤ nodeSize (memW s n) := by
      unfold nodeSize; split_ifs <;> omega
    have hw_k : ∀ k, k < nodeSize (memW s n) / 8 → memW post (n + 8 * k) = memW s (n + 8 * k) := by
      intro k hk
      have hsz8 : nodeSize (memW s n) % 8 = 0 := by unfold nodeSize; split_ifs <;> omega
      exact memW_eq_of_ivlUnhit hu_n (by omega) hhi_n ⟨by omega, by omega⟩
    have hw0 : memW post n = memW s n := by simpa using hw_k 0 (by omega)
    have hivl_eq : nodeIvl post n = nodeIvl s n := by simp [nodeIvl, hw0]
    have hpath_eq : nodePath post n = nodePath s n := by
      by_cases h12 : memW s n = 1 ∨ memW s n = 2
      · have hsz_ge56 : 56 ≤ nodeSize (memW s n) := by
          unfold nodeSize; rcases h12 with h1 | h2
          · simp [h1]
          · simp [h2]
        have hw32 : memW post (n + 32) = memW s (n + 32) := hw_k 4 (by omega)
        have hw40 : memW post (n + 40) = memW s (n + 40) := hw_k 5 (by omega)
        unfold nodePath
        rw [hw0, hw32, hw40]
      · unfold nodePath; rw [hw0]; simp [h12]
    exact ⟨hw0, hivl_eq, hw_k, hpath_eq, fun h12 => by
      have hsz_ge56 : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize; rcases h12 with h1 | h2
        · simp [h1]
        · simp [h2]
      have hw32 : memW post (n + 32) = memW s (n + 32) := hw_k 4 (by omega)
      have hw40 : memW post (n + 40) = memW s (n + 40) := hw_k 5 (by omega)
      rw [hw32, hw40]
      by_cases hlen0 : memW s (n + 40) = 0
      · exact Or.inl hlen0
      · rcases hkey_n h12 with h0 | ⟨hnib, hal_p, hin_p, hdisj_p⟩
        · exact Or.inl h0
        · right
          have hu_p : IvlUnhit s post (memW s (n + 32), memW s (n + 40)) := by
            have hp_ext : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
              unfold nodeExtents
              refine List.mem_flatMap.2 ⟨n, hn, ?_⟩
              simp [nodePath, h12, hlen0]
            exact hu _ hp_ext
          have hhi_p : memW s (n + 32) + memW s (n + 40) ≤ 2 ^ 64 := by
            have := hin_p.2; omega
          refine ⟨fun k hk => ?_, hag.allocated hal_p, hin_p, ?_⟩
          · rw [memB_eq_of_ivlUnhit hu_p hbe hhi_p ⟨by omega, by omega⟩]
            exact hnib k hk
          · intro m hm
            have hm_ivl : nodeIvl post m = nodeIvl s m := by
              have hhm_hi : m + nodeSize (memW s m) ≤ 2 ^ 64 := by
                have := (hN.1 m hm).2.2.1.2; dsimp [nodeIvl] at this; omega
              have hm8 : m % 8 = 0 := (hN.1 m hm).2.2.2.1.1
              have hu_m : IvlUnhit s post (m, nodeSize (memW s m)) := by
                apply hu; unfold nodeExtents; exact List.mem_flatMap.2 ⟨m, hm, by simp [nodeIvl]⟩
              have hsz_m : 32 ≤ nodeSize (memW s m) := by unfold nodeSize; split_ifs <;> omega
              have hwm : memW post m = memW s m :=
                memW_eq_of_ivlUnhit hu_m hm8 hhm_hi ⟨by omega, by omega⟩
              simp [nodeIvl, hwm]
            rw [hm_ivl]
            exact hdisj_p m hm⟩
  constructor
  · refine ⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩
    · obtain ⟨hk3, hal_n, hin_n, hw_n, hext, hbr, _, hb16, hb56, hb168⟩ := hN.1 n hn
      obtain ⟨hw0, hivl_eq, hw_k, _, hkey_post⟩ := hn_props n hn
      have hsz_ge32 : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
      have hw16 : memW post (n + 16) = memW s (n + 16) := hw_k 2 (by omega)
      rw [hw0, hivl_eq]
      refine ⟨hk3, hag.allocated hal_n, hin_n, wordsOK_transfer hgS hgP hw_n, ?_, ?_, hkey_post,
        by rw [hw16]; exact hb16, ?_, ?_⟩
      · intro h2
        have hsz : nodeSize (memW s n) = 56 := by unfold nodeSize; simp [h2]
        have hw48 := hw_k 6 (by omega)
        simpa only [Nat.mul_succ, Nat.mul_zero] using (by rw [hw48]; exact hext h2 : RootIn Nd (memW post (n + 48)))
      · intro h3 i hi
        have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
        have hw_ch := hw_k (4 + i) (by omega)
        have hadd : n + 8 * (4 + i) = n + 32 + 8 * i := by omega
        rw [← hadd, hw_ch, hadd]
        exact hbr h3 i hi
      · intro h1
        have hsz : nodeSize (memW s n) = 64 := by unfold nodeSize; simp [h1]
        have hw56 := hw_k 7 (by omega)
        simpa using (by rw [hw56]; exact hb56 h1 : memW post (n + 56) < 2 ^ 40)
      · intro h3
        have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
        have hw168 := hw_k 21 (by omega)
        simpa using (by rw [hw168]; exact hb168 h3 : memW post (n + 168) < 2 ^ 40)
    · rw [(hn_props n hn).2.1, (hn_props m hm).2.1]
      exact hN.2 n hn m hm hne
  · unfold nodeExtents
    apply List.flatMap_congr
    intro n hn
    rw [(hn_props n hn).2.1, (hn_props n hn).2.2.2.1]

theorem fixedObjects_eq_of_parts {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgs : WorldGlobalsSame s post)
    (hbo_obj : blockOutObjects post = blockOutObjects s)
    (hbal_obj : balObjects post = balObjects s) :
    fixedObjects post = fixedObjects s := by
  unfold fixedObjects
  rw [hbo_obj, hbal_obj, hgs.2.2.1, hgs.2.2.2.1]
  congr 3
  apply List.map_congr_left
  intro gn hgn
  rw [hgs.1 gn hgn]

theorem fixedTyped_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) (hag : AllocatorGrows s post)
    (hF : FixedTyped s) (hfix_eq : fixedObjects post = fixedObjects s) :
    FixedTyped post := by
  unfold FixedTyped
  rw [hfix_eq]
  refine ⟨fun i hi => ?_, hF.2⟩
  rcases hF.1 i hi with h0 | ⟨hal, hwords⟩
  · exact Or.inl h0
  · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hgS hgP hwords⟩

theorem worldTypedWith_congr_bo {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hag : AllocatorGrows s post) (hgs : WorldGlobalsSame s post)
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80))
    (hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72))
    (hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap"))
    (hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i)
    (hu_bal : ∀ i ∈ balObjects s, IvlUnhit s post i)
    (hu_nd : ∀ o ∈ nodeExtents s Nd, IvlUnhit s post o)
    (hbo_words : globN s "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k))
    (hm_low : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
    WorldTypedWith post S Nd ∧
    worldOwned post S Nd = worldOwned s S Nd ∧
    worldRoleSlots post = worldRoleSlots s ∧
    journalRoleSlots post = journalRoleSlots s ∧
    (∀ t ∈ S, hdr post t 0 = hdr s t 0) := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hW
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hbo_g : globN post "bo" = globN s "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
  have hws_g : globN post "ws" = globN s "ws" := hgs.1 ("ws", 40) (by simp [globalBuffers])
  have hbs_g : globN post "bs" = globN s "bs" := hgs.1 ("bs", 80) (by simp [globalBuffers])
  have hts_g : globN post "ts" = globN s "ts" := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hbo_part := blockOutObjects_eq_of_bo_unhit hAs.2 hF hbo_g hT.2.2.2.2.2.2.2.2.2.2.1
    (fun h => hbo_words h 24 (by simp))
    (fun h => hbo_words h 32 (by simp))
    (fun h => hbo_words h 40 (by simp))
    (fun h => hbo_words h 56 (by simp))
    (fun h => hbo_words h 72 (by simp))
    (fun h => hbo_words h 80 (by simp))
    (fun h h40 => hu_bo_lst (memW s (globN s "bo" + 40), 24) (by simp [blockOutObjects, h, h40]) rfl)
    (fun h h72 => hu_bo_lst (memW s (globN s "bo" + 72), 24) (by simp [blockOutObjects, h, h72]) rfl)
  have hbal_part := balObjects_eq_of_unhit hAs.2 hT hF hba_g hu_tab hu_bal hm_low
  have hfix_eq := fixedObjects_eq_of_parts hgs hbo_part.1 hbal_part.1
  have hF_post := fixedTyped_transfer hAs.1 hAp.1 hag hF hfix_eq
  have hjr_part := journalRoleSlots_eq_of_unhit hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hgs hu_ts hu_jr
  have hwrs_eq := worldRoleSlots_eq_of_unhit hAs.2 hT hF hgs hu_tab hu_ws hu_bs hu_ts hu_bal hm_low
  have hnd_part := nodeHeap_congr_unhit hAs.1 hAp.1 hbe hag hTr.1 hu_nd
  have htab_fp_hdr : ∀ t ∈ S, (∀ k, k < 11 → hdr post t k = hdr s t k) ∧ htabFootprint post t = htabFootprint s t := by
    intro t ht
    have hwf := (hT.2.1 t ht).1
    have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; omega
    exact htabFootprint_eq_of_hdr_unhit ht8 hhi (hu_tab t ht _ ht_fp)
  have hflat_fp : S.flatMap (htabFootprint post) = S.flatMap (htabFootprint s) := by
    apply List.flatMap_congr
    intro t ht; exact (htab_fp_hdr t ht).2
  have howned_eq : worldOwned post S Nd = worldOwned s S Nd := by
    unfold worldOwned
    rw [hflat_fp, hfix_eq, hnd_part.2]
  have hT_post : TablesTyped post S := by
    obtain ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, hboT, hroles⟩ := hT
    refine ⟨hndS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_part.2, ?_⟩
    · intro t ht
      rw [(htab_fp_hdr t ht).2, hfix_eq]
      exact ⟨htabWF_congr_unhit hAs.1 hAp.1 (hTt t ht).1 (hu_tab t ht),
        fun i hi => ⟨hag.allocated ((hTt t ht).2 i hi).1, ((hTt t ht).2 i hi).2⟩⟩
    · intro t ht u hu_mem hne
      rw [(htab_fp_hdr t ht).2, (htab_fp_hdr u hu_mem).2]
      exact hTp t ht u hu_mem hne
    · intro k hk hnz
      rw [hws_g] at hnz
      have hwk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) hwk.1 hwk.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [hbs_g] at hnz
      have hbk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) hbk.1 hbk.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [hts_g] at hnz
      have htk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) htk.1 htk.2]
      exact htsR k hk hnz
    · intro g hg
      rw [hgs.2.1 g hg]; exact hgR g hg
    · intro hnz hm
      rw [hbs_g] at hnz
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact htabValuesIn_congr_unhit (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (hbsN hnz hm)
    · intro hnz hm
      rw [hts_g] at hnz
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact htabValuesIn_congr_unhit (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (htsN hnz hm)
    · intro ad had
      obtain ⟨h0, h8, _, hkl, hll⟩ := hbal_part.2 ad had
      have hrecs := balRecords_eq_of_unhit ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, hboT, hroles⟩
        hba_g (fun hnz => by
          rcases hgR "bal_accounts" (by simp [globalTableRoots]) with h0' | hm
          · exact absurd h0' hnz
          · exact hu_tab _ hm)
      rw [hrecs] at had
      have had_old := hbalT ad had
      refine ⟨by rw [h0]; exact had_old.1, by rw [h8]; exact had_old.2.1, hkl, hll⟩
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjr_part.1]
      refine ⟨fun a ha => ?_, hroles.2.1, hroles.2.2⟩
      obtain ⟨haS, hak⟩ := hroles.1 a ha
      rw [(htab_fp_hdr a.1 haS).1 0 (by omega)]
      exact ⟨haS, hak⟩
  have hTr_post : TriesTypedWith post S Nd := by
    refine ⟨hnd_part.1, ?_, ?_⟩
    · intro o ho
      rw [hnd_part.2] at ho
      rw [hfix_eq]
      refine ⟨fun t ht i hi => ?_, (hTr.2.1 o ho).2⟩
      rw [(htab_fp_hdr t ht).2] at hi
      exact (hTr.2.1 o ho).1 t ht i hi
    · intro hnz
      rw [hws_g] at hnz
      have hw24 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) (k := 24) (by omega) (by omega)
      have hw32 := rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) hws_g hnz (hu_ws hnz) (k := 32) (by omega) (by omega)
      rw [hw24, hw32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hnz
      refine ⟨hr24, fun hm i hi => ?_⟩
      have hwf32 := (hT.2.1 _ hm).1
      have hu32 := hu_tab _ hm
      have hh32 := htab_fp_hdr _ hm
      rw [hh32.1 3 (by omega)] at hi
      have hvals := htabValues_eq_of_unhit hwf32 hu32
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hh32.1 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]
      exact hr32 hm i hi
  exact ⟨⟨hT_post, hjr_part.2, hF_post, hTr_post⟩, howned_eq, hwrs_eq, hjr_part.1,
    fun t ht => (htab_fp_hdr t ht).1 0 (by omega)⟩

theorem worldTypedWith_store_word_disj {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) {x : BitVec 64}
    (hx_dom : s.memaddrs x)
    (hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
      ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a)
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (hdisj : ∀ j ∈ worldTypedIvls s S Nd, Disj j (x.toNat, 8)) :
    ArenaReady post ∧
    WorldTypedWith post S Nd ∧
    worldOwned post S Nd = worldOwned s S Nd ∧
    worldRoleSlots post = worldRoleSlots s ∧
    journalRoleSlots post = journalRoleSlots s ∧
    (∀ t ∈ S, hdr post t 0 = hdr s t 0) := by
  have hgP : GuestInv post := guestInv_congr hpost.1 hpost.2.1 hpost.2.2.1 hpost.2.2.2.1 hAs.1
  have hAp : ArenaReady post := by
    refine ⟨hgP, ?_⟩
    unfold ArenaOK; simp only [globN_congr hpost.2.2.2.2.2.1]; exact hAs.2
  have hag : AllocatorGrows s post := by
    unfold AllocatorGrows; simp only [globN_congr hpost.2.2.2.2.2.1]; exact ⟨le_rfl, le_rfl⟩
  have hgs := worldGlobalsSame_of_globals_eq hpost.2.2.2.2.2.1
  have hx_ord : x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
    rw [hAs.1.memaddrs, ordinaryDomain_iff] at hx_dom; exact hx_dom
  have hsb : 24 < sourceBase := by decide
  have hm_low : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    obtain ⟨_, hx_lo, _⟩ := hx_ord
    constructor
    · have hne : BitVec.ofNat 64 8 ≠ x := by
        rintro rfl; change sourceBase ≤ 8 at hx_lo; omega
      unfold memW; rw [hpost.2.2.2.2.2.2 _ hne]
    · have hne : BitVec.ofNat 64 16 ≠ x := by
        rintro rfl; change sourceBase ≤ 16 at hx_lo; omega
      unfold memW; rw [hpost.2.2.2.2.2.2 _ hne]
  have hunhit : ∀ i ∈ worldTypedIvls s S Nd, IvlUnhit s post i := fun i hi =>
    ivlUnhit_of_single_cell_disj
      (worldOwned_zero_aligned hW i (worldTypedIvls_sub_worldOwned s S Nd i hi))
      hpost.2.2.2.2.2.2 (hdisj i hi)
  have hbo_u : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) := fun hnz => by
    apply hunhit
    unfold worldTypedIvls
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; left; apply List.mem_append.2; right
    refine List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], ?_⟩
    simp [hnz]
  have hres := worldTypedWith_congr_bo hAs hAp hpost.2.2.2.2.1 hag hgs hW
    (fun t ht i hi => hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; left
      exact List.mem_flatMap.2 ⟨t, ht, hi⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("ws", 40), by simp [typedRecords], by simp [hnz]⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("bs", 80), by simp [typedRecords], by simp [hnz]⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("ts", 72), by simp [typedRecords], by simp [hnz]⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; right; simp [hnz]))
    (fun i hi _ => hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
      exact hi))
    (fun i hi => hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact hi))
    (fun o ho => hunhit o (by
      unfold worldTypedIvls
      exact List.mem_append.2 (Or.inr ho)))
    (fun hnz k hk => by
      have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simpa [globN_congr hpost.2.2.2.2.2.1] using
        rec_word_eq_of_unhit hAs.2 hW.2.2.1 "bo" 88 (by simp [typedRecords])
          (by simp [globN_congr hpost.2.2.2.2.2.1]) hnz (hbo_u hnz) hk_in.1 hk_in.2)
    hm_low
  exact ⟨hAp, hres⟩

theorem worldTypedWith_store_range_disj {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) {base len : Nat}
    (hbase8 : base % 8 = 0) (hlen8 : len % 8 = 0) (hbase_lo : sourceBase ≤ base)
    (hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
      FrameOutside s post [(base, len)] (0, 0))
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (hdisj : ∀ j ∈ worldTypedIvls s S Nd, Disj j (base, len)) :
    ArenaReady post ∧
    WorldTypedWith post S Nd ∧
    worldOwned post S Nd = worldOwned s S Nd ∧
    worldRoleSlots post = worldRoleSlots s ∧
    journalRoleSlots post = journalRoleSlots s ∧
    (∀ t ∈ S, hdr post t 0 = hdr s t 0) := by
  have hgP : GuestInv post := guestInv_congr hpost.1 hpost.2.1 hpost.2.2.1 hpost.2.2.2.1 hAs.1
  have hAp : ArenaReady post := by
    refine ⟨hgP, ?_⟩
    unfold ArenaOK; simp only [globN_congr hpost.2.2.2.2.2.1]; exact hAs.2
  have hag : AllocatorGrows s post := by
    unfold AllocatorGrows; simp only [globN_congr hpost.2.2.2.2.2.1]; exact ⟨le_rfl, le_rfl⟩
  have hgs := worldGlobalsSame_of_globals_eq hpost.2.2.2.2.2.1
  have hsb : 24 < sourceBase := by decide
  have hm_low : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hfr := hpost.2.2.2.2.2.2
    constructor
    · have hm := hfr (BitVec.ofNat 64 8) (fun j hj hcj => by
        simp only [List.mem_singleton] at hj; subst hj
        obtain ⟨h1, _⟩ := hcj
        have : (BitVec.ofNat 64 8).toNat = 8 := by decide
        rw [this] at h1; omega)
        (fun hcf => by obtain ⟨_, h2⟩ := hcf; omega)
      unfold memW; rw [hm]
    · have hm := hfr (BitVec.ofNat 64 16) (fun j hj hcj => by
        simp only [List.mem_singleton] at hj; subst hj
        obtain ⟨h1, _⟩ := hcj
        have : (BitVec.ofNat 64 16).toNat = 16 := by decide
        rw [this] at h1; omega)
        (fun hcf => by obtain ⟨_, h2⟩ := hcf; omega)
      unfold memW; rw [hm]
  have hunhit : ∀ i ∈ worldTypedIvls s S Nd, IvlUnhit s post i := fun i hi =>
    ivlUnhit_of_frameOutside_aligned hpost.2.2.2.2.2.2
      (worldOwned_zero_aligned hW i (worldTypedIvls_sub_worldOwned s S Nd i hi))
      (fun j hj => by simp only [List.mem_singleton] at hj; subst hj; exact ⟨hbase8, hlen8⟩)
      ⟨by omega, by omega⟩
      (fun j hj => by simp only [List.mem_singleton] at hj; subst hj; exact hdisj i hi)
      (disj_zero_right i)
  have hbo_u : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) := fun hnz => by
    apply hunhit
    unfold worldTypedIvls
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; left; apply List.mem_append.2; right
    exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hnz]⟩
  have hres := worldTypedWith_congr_bo hAs hAp hpost.2.2.2.2.1 hag hgs hW
    (fun t ht i hi => hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; left
      exact List.mem_flatMap.2 ⟨t, ht, hi⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("ws", 40), by simp [typedRecords], by simp [hnz]⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("bs", 80), by simp [typedRecords], by simp [hnz]⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("ts", 72), by simp [typedRecords], by simp [hnz]⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; right; simp [hnz]))
    (fun i hi _ => hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
      exact hi))
    (fun i hi => hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact hi))
    (fun o ho => hunhit o (by
      unfold worldTypedIvls
      exact List.mem_append.2 (Or.inr ho)))
    (fun hnz k hk => by
      have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simpa [globN_congr hpost.2.2.2.2.2.1] using
        rec_word_eq_of_unhit hAs.2 hW.2.2.1 "bo" 88 (by simp [typedRecords])
          (by simp [globN_congr hpost.2.2.2.2.2.1]) hnz (hbo_u hnz) hk_in.1 hk_in.2)
    hm_low
  exact ⟨hAp, hres⟩

theorem zero_not_mem_S {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
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
        apply Disj.flip; apply (hfp_t j hj).2 i
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨u, huU, hi⟩))))
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
        apply Disj.flip; apply (hfp_t i hi).2 o
        unfold worldOwned; exact List.mem_append.2 (Or.inr ho)
    · intro hnz
      refine ⟨(hTrU.2.2 hnz).1, fun hm => ?_⟩
      rcases List.mem_append.1 hm with hmU | hmt
      · exact (hTrU.2.2 hnz).2 hmU
      · simp only [List.mem_singleton] at hmt
        rcases hwsU 32 (by simp [wsTableSlots]) hnz with h0 | hmU
        · exact absurd (h0.symm.trans hmt).symm ht_nz
        · exact absurd (hmt ▸ hmU) ht_not_U
  exact ⟨ht_not_U, ht_nz, ht_unass, hTU', hJU', hFU, hTrU'⟩

theorem worldTypedWith_htab_new {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {t : Nat}
    (hAp : ArenaReady post) (hag : AllocatorGrows s post) (hwf_t : HtabWF post t)
    (hfp_t : ∀ i ∈ htabFootprint post t, Allocated post i ∧
      (Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∨
        Inside i (globN post "scratch_ptr") (globN s "scratch_ptr")))
    (hfr : FrameOutside s post
      [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hbe : post.be = s.be)
    (hg_kept : GlobalsKept ["heap_ptr", "scratch_ptr"] s post) :
    t ∉ S ∧ t ≠ 0 ∧
    (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ t) ∧
    WorldTypedWith post (S ++ [t]) Nd ∧
    worldRoleSlots post = worldRoleSlots s ∧
    journalRoleSlots post = journalRoleSlots s ∧
    (∀ u ∈ S, hdr post u 0 = hdr s u 0) ∧
    (∀ b : Ivl, b.1 % 8 = 0 → b.2 % 8 = 0 → Inside b sourceBase (globN s "heap_ptr") →
      (∀ j ∈ worldOwned s S Nd, Disj b j) →
      Inside b sourceBase (globN post "heap_ptr") ∧
      (∀ o ∈ worldOwned post (S ++ [t]) Nd, Disj b o) ∧
      IvlUnhit s post b) := by
  have hgs : WorldGlobalsSame s post :=
    worldGlobalsSame_of_globalsKept hg_kept (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsb : 24 < sourceBase := by decide
  have hsb264 : sourceBase < 2 ^ 64 := by decide
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨hs_lo, hs_hp, hs_fm, hs_sc, hs_end, hs_hp8, hs_fm8, hs_sc8⟩ := hAs.2
  obtain ⟨hp_lo, hp_hp, hp_fm, hp_sc, hp_end, hp_hp8, hp_fm8, hp_sc8⟩ := hAp.2
  have hg_hp := hag.1; have hg_sc := hag.2
  have hf_al : (globN s "heap_ptr") % 8 = 0 ∧ (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 :=
    ⟨hs_hp8, by omega⟩
  have hs_al : (globN post "scratch_ptr") % 8 = 0 ∧ (globN s "scratch_ptr" - globN post "scratch_ptr") % 8 = 0 :=
    ⟨hp_sc8, by omega⟩
  have hm_low : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW post a = memW s a := fun a ha => by
      have ha_lt : a < 2 ^ 64 := by omega
      have hm := hfr (BitVec.ofNat 64 a)
        (fun j hj hcj => by
          simp only [List.mem_singleton] at hj; subst hj
          obtain ⟨h1, _⟩ := hcj
          dsimp at h1
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          omega)
        (fun hcf => by
          obtain ⟨h1, _⟩ := hcf
          dsimp at h1
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          omega)
      unfold memW; rw [hm]
    exact ⟨hlow 8 (by omega), hlow 16 (by omega)⟩
  have hunhit_owned : ∀ j ∈ worldOwned s S Nd, IvlUnhit s post j := fun j hj =>
    ivl_unhit_free_of_zero_or_allocated hAs.2 hAp.2 hag hfr
      (fun k hk => List.mem_singleton.1 hk) rfl (worldOwned_zero_or_allocated hW j hj)
  have hunhit : ∀ i ∈ worldTypedIvls s S Nd, IvlUnhit s post i :=
    fun i hi => hunhit_owned i (worldTypedIvls_sub_worldOwned s S Nd i hi)
  have hbo_u : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) := fun hnz =>
    hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hnz]⟩)
  have hbase := worldTypedWith_congr_bo hAs hAp hbe hag hgs hW
    (fun u hu i hi => hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; left
      exact List.mem_flatMap.2 ⟨u, hu, hi⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("ws", 40), by simp [typedRecords], by simp [hnz]⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("bs", 80), by simp [typedRecords], by simp [hnz]⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("ts", 72), by simp [typedRecords], by simp [hnz]⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; right; simp [hnz]))
    (fun i hi _ => hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
      exact hi))
    (fun i hi => hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact hi))
    (fun o ho => hunhit o (by
      unfold worldTypedIvls
      exact List.mem_append.2 (Or.inr ho)))
    (fun hnz k hk => by
      have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      have hbo_g : globN post "bo" = globN s "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
      simpa [hbo_g] using
        rec_word_eq_of_unhit hAs.2 hW.2.2.1 "bo" 88 (by simp [typedRecords]) hbo_g hnz (hbo_u hnz) hk_in.1 hk_in.2)
    hm_low
  obtain ⟨hW_S, howned_S, hwrs_eq, hjr_eq, hhdr_S⟩ := hbase
  have ht_fp_disj : ∀ i ∈ htabFootprint post t, ∀ j ∈ worldOwned post S Nd, Disj i j := by
    intro i hi j hj
    rw [howned_S] at hj
    obtain ⟨hd_hp, hd_sc⟩ := ivl_disj_free_of_zero_or_allocated hAs.2 hAp.2 hag
      (worldOwned_zero_or_allocated hW j hj)
    rcases (hfp_t i hi).2 with hin_hp | hin_sc
    · have hin' : Inside i (globN s "heap_ptr") (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr")) := by
        unfold Inside at hin_hp ⊢; omega
      exact (disj_of_inside_right hin' hd_hp).flip
    · have hin' : Inside i (globN post "scratch_ptr") (globN post "scratch_ptr" + (globN s "scratch_ptr" - globN post "scratch_ptr")) := by
        unfold Inside at hin_sc ⊢; omega
      exact (disj_of_inside_right hin' hd_sc).flip
  obtain ⟨ht_not_S, ht_nz, hslot_ne_t, hW_ext⟩ :=
    adjoin_local_table hW_S hwf_t (fun i hi => ⟨(hfp_t i hi).1, ht_fp_disj i hi⟩) rfl
  refine ⟨ht_not_S, ht_nz, hslot_ne_t, hW_ext, hwrs_eq, hjr_eq, hhdr_S, ?_⟩
  intro b hb1 _ hb_in hb_disj
  have hd_hp : Disj b (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") :=
    Or.inr (Or.inr (Or.inl hb_in.2))
  have hd_sc : Disj b (globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr") :=
    Or.inr (Or.inr (Or.inl (by unfold Inside at hb_in; omega)))
  refine ⟨⟨hb_in.1, Nat.le_trans hb_in.2 hag.1⟩, ?_, ?_⟩
  · intro o ho
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · rw [List.flatMap_append] at htab
        rcases List.mem_append.1 htab with htabS | htab_t
        · apply hb_disj o; rw [← howned_S]; unfold worldOwned
          exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htabS)))
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at htab_t
          rcases (hfp_t o htab_t).2 with hin_hp | hin_sc
          · exact Or.inr (Or.inr (Or.inl (Nat.le_trans hb_in.2 hin_hp.1)))
          · exact Or.inr (Or.inr (Or.inl (by unfold Inside at hb_in hin_sc; omega)))
      · apply hb_disj o; rw [← howned_S]; unfold worldOwned
        exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
    · apply hb_disj o; rw [← howned_S]; unfold worldOwned
      exact List.mem_append.2 (Or.inr hnd)
  · exact ivlUnhit_of_frameOutside_aligned hfr (fun _ => hb1)
      (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hs_al)
      hf_al
      (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hd_sc)
      hd_hp

theorem rolesOK_msgReady {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hT : TablesTyped s S)
    {aa ak : Nat}
    (haa_S : aa ∈ S) (hak_S : ak ∈ S) (haa_ne_ak : aa ≠ ak)
    (haa_klen : hdr s aa 0 = 20) (hak_klen : hdr s ak 0 = 52)
    (haa_local : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa)
    (hak_local : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ ak) :
    RolesOK s S (worldRoleSlots s ++ [(aa, "frame.addr"), (ak, "frame.key")]) (journalRoleSlots s) := by
  have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨hr1, hr2, hr3⟩ := hroles
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [List.append_assoc] at ha
    rcases List.mem_append.1 ha with hw | hrest
    · exact hr1 a (List.mem_append.2 (Or.inl hw))
    · rcases List.mem_append.1 hrest with hfk | hjr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfk
        rcases hfk with rfl | rfl
        · exact ⟨haa_S, haa_klen⟩
        · exact ⟨hak_S, hak_klen⟩
      · exact hr1 a (List.mem_append.2 (Or.inr hjr))
  · rw [List.pairwise_append]
    refine ⟨hr2, ?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨fun b hb heq => ?_, List.pairwise_singleton _ _⟩
      simp only [List.mem_singleton] at hb; subst hb
      exact absurd heq haa_ne_ak
    · intro a ha b hb heq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact absurd heq (haa_local a (List.mem_append.2 (Or.inl ha)))
      · exact absurd heq (hak_local a (List.mem_append.2 (Or.inl ha)))
  · intro a ha b hb heq
    rw [List.append_assoc] at hb
    rcases List.mem_append.1 hb with hw | hrest
    · exact hr3 a ha b (List.mem_append.2 (Or.inl hw)) heq
    · rcases List.mem_append.1 hrest with hfk | hjr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfk
        rcases hfk with rfl | rfl
        · exact absurd heq (haa_local a (List.mem_append.2 (Or.inr ha)))
        · exact absurd heq (hak_local a (List.mem_append.2 (Or.inr ha)))
      · exact hr3 a ha b (List.mem_append.2 (Or.inr hjr)) heq

theorem msgReady_of_parts {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {m aa ak : Nat} (hm_loc : locN s "msg" = m)
    (hm152 : memW s (m + 152) = aa) (hm160 : memW s (m + 160) = ak)
    (haa_S : aa ∈ S) (hak_S : ak ∈ S) (haa_ne_ak : aa ≠ ak)
    (haa_klen : hdr s aa 0 = 20) (hak_klen : hdr s ak 0 = 52)
    (haa_local : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa)
    (hak_local : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ ak)
    (hm_in : Inside (m, 176) sourceBase (globN s "heap_ptr"))
    (hm8 : m % 8 = 0)
    (hm_disj : ∀ o ∈ worldOwned s S Nd, Disj (m, 176) o)
    (hmgas : memW s (m + 40) < 2 ^ 63) :
    MsgReady s := by
  have hm_words : WordsOK s (m, 176) := by
    refine ⟨hm8, by omega, fun k hk => ?_⟩
    have hhi := (ivl_allocated_bound hA.2 (Or.inl hm_in)).1
    exact wordAt_of_ordinary hA.1 (by omega) (by unfold Inside at hm_in; omega) (by dsimp at hhi; omega)
  refine ⟨hA, S, (worldTyped_iff_with s S).2 ⟨Nd, hW⟩, ?_⟩
  rw [hm_loc, hm152, hm160]
  refine ⟨haa_S, hak_S, hm_in, hm_words, ?_, ?_, ?_, hmgas,
    rolesOK_msgReady hW.1 haa_S hak_S haa_ne_ak haa_klen hak_klen haa_local hak_local⟩
  · intro t ht i hi
    exact hm_disj i (by unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨t, ht, hi⟩)))))
  · intro j hj
    exact hm_disj j (by unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj))))
  · refine ⟨Nd, hW.2.2.2, fun o ho j hj => ?_⟩
    simp only [List.mem_singleton] at ho; subst ho
    exact hm_disj j (by unfold worldOwned; exact List.mem_append.2 (Or.inr hj))

theorem role_not_frame_of_world_or_journal {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s,
      a.2 ≠ "frame.addr" ∧ a.2 ≠ "frame.key" := by
  intro a ha
  rcases List.mem_append.1 ha with hw | hjr
  · unfold worldRoleSlots at hw
    have hm := (List.mem_filter.1 hw).1
    rcases List.mem_append.1 hm with h1 | hbal
    · rcases List.mem_append.1 h1 with h2 | hnt
      · rcases List.mem_append.1 h2 with h3 | hnb
        · rcases List.mem_append.1 h3 with h4 | hg
          · rcases List.mem_append.1 h4 with h5 | hts
            · rcases List.mem_append.1 h5 with hws | hbs
              · unfold recRoles at hws; split_ifs at hws
                · simp at hws
                · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hws
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
                  rcases hk with rfl | rfl <;> (dsimp only; decide)
              · unfold recRoles at hbs; split_ifs at hbs
                · simp at hbs
                · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hbs
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
                  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)
            · unfold recRoles at hts; split_ifs at hts
              · simp at hts
              · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hts
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
                rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
            rcases hg with rfl | rfl | rfl <;> (dsimp only; decide)
        · unfold nestRoles at hnb; split_ifs at hnb
          · simp at hnb
          · simp at hnb
          · obtain ⟨_, _, rfl⟩ := List.mem_map.1 hnb; dsimp only; decide
      · unfold nestRoles at hnt; split_ifs at hnt
        · simp at hnt
        · simp at hnt
        · obtain ⟨_, _, rfl⟩ := List.mem_map.1 hnt; dsimp only; decide
    · obtain ⟨ad, _, ha_ad⟩ := List.mem_flatMap.1 hbal
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha_ad
      rcases ha_ad with rfl | rfl <;> (dsimp only; decide)
  · unfold journalRoleSlots at hjr
    obtain ⟨i, _, ha_i⟩ := List.mem_flatMap.1 hjr
    rcases List.mem_cons.1 ha_i with rfl | hrest
    · dsimp only; unfold journalRole; split_ifs <;> decide
    · split_ifs at hrest
      · simp only [List.mem_singleton] at hrest; subst hrest; dsimp only; decide
      · simp at hrest

theorem msgReady_extract {F : Type} {s : PanSemStateFiniteExact 64 F} (h : MsgReady s) :
    ArenaReady s ∧ ∃ S Nd,
      let m := locN s "msg"
      let aa := memW s (m + 152)
      let ak := memW s (m + 160)
      WorldTypedWith s S Nd ∧
      aa ∈ S ∧ ak ∈ S ∧ aa ≠ ak ∧
      hdr s aa 0 = 20 ∧ hdr s ak 0 = 52 ∧
      (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa) ∧
      (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ ak) ∧
      m % 8 = 0 ∧ Inside (m, 176) sourceBase (globN s "heap_ptr") ∧
      (∀ o ∈ worldOwned s S Nd, Disj (m, 176) o) ∧
      memW s (m + 40) < 2 ^ 63 := by
  obtain ⟨hA, S, hWT, haa_S, hak_S, hm_in, hm_words, hm_tab, hm_fix, ⟨Nd_tr, hTr_nd, hm_tr⟩, hmgas, hroles⟩ := h
  obtain ⟨hT, hJ, hF, _⟩ := hWT
  have hW : WorldTypedWith s S Nd_tr := ⟨hT, hJ, hF, hTr_nd⟩
  obtain ⟨hr1, hr2, hr3⟩ := hroles
  set m := locN s "msg"
  set aa := memW s (m + 152)
  set ak := memW s (m + 160)
  have haa_in_sl : (aa, "frame.addr") ∈ worldRoleSlots s ++ [(aa, "frame.addr"), (ak, "frame.key")] ++ journalRoleSlots s := by
    simp
  have hak_in_sl : (ak, "frame.key") ∈ worldRoleSlots s ++ [(aa, "frame.addr"), (ak, "frame.key")] ++ journalRoleSlots s := by
    simp
  have haa_klen : hdr s aa 0 = 20 := (hr1 _ haa_in_sl).2
  have hak_klen : hdr s ak 0 = 52 := (hr1 _ hak_in_sl).2
  have hp_f := (List.pairwise_append.1 hr2).2.1
  have hp_cross := (List.pairwise_append.1 hr2).2.2
  have haa_ne_ak : aa ≠ ak := by
    intro heq
    have : ("frame.addr" : String) = "frame.key" :=
      ((List.pairwise_cons.1 hp_f).1 (ak, "frame.key") (by simp) heq).1
    exact absurd this (by decide)
  have haa_loc : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa := by
    intro a ha heq
    have hnf := (role_not_frame_of_world_or_journal s a ha).1
    rcases List.mem_append.1 ha with hw | hjr
    · exact hnf (hp_cross a hw (aa, "frame.addr") (by simp) heq).1
    · exact hnf (hr3 a hjr (aa, "frame.addr") haa_in_sl heq)
  have hak_loc : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ ak := by
    intro a ha heq
    have hnf := (role_not_frame_of_world_or_journal s a ha).2
    rcases List.mem_append.1 ha with hw | hjr
    · exact hnf (hp_cross a hw (ak, "frame.key") (by simp) heq).1
    · exact hnf (hr3 a hjr (ak, "frame.key") hak_in_sl heq)
  refine ⟨hA, S, Nd_tr, hW, haa_S, hak_S, haa_ne_ak, haa_klen, hak_klen, haa_loc, hak_loc,
    hm_words.1, hm_in, ?_, hmgas⟩
  intro o ho
  unfold worldOwned at ho
  rcases List.mem_append.1 ho with h1 | hnd
  · rcases List.mem_append.1 h1 with htab | hfix
    · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.1 htab
      exact hm_tab t ht o hi
    · exact hm_fix o hfix
  · exact hm_tr (m, 176) (by simp) o hnd

/-- Explicit witness of `MsgReady s` at table set `S` and trie node set `Nd`. -/
def MsgReadyAt {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : Prop :=
  let m := locN s "msg"
  let aa := memW s (m + 152)
  let ak := memW s (m + 160)
  ArenaReady s ∧
  WorldTypedWith s S Nd ∧
  aa ∈ S ∧ ak ∈ S ∧ aa ≠ ak ∧
  hdr s aa 0 = 20 ∧ hdr s ak 0 = 52 ∧
  (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa) ∧
  (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ ak) ∧
  m % 8 = 0 ∧ Inside (m, 176) sourceBase (globN s "heap_ptr") ∧
  (∀ o ∈ worldOwned s S Nd, Disj (m, 176) o) ∧
  memW s (m + 40) < 2 ^ 63

theorem msgReadyAt_msgReady {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (h : MsgReadyAt s S Nd) : MsgReady s := by
  obtain ⟨hA, hW, haa_S, hak_S, haa_ne_ak, haa_klen, hak_klen, haa_loc, hak_loc,
    hm8, hm_in, hm_disj, hmgas⟩ := h
  exact msgReady_of_parts hA hW rfl rfl rfl haa_S hak_S haa_ne_ak haa_klen hak_klen
    haa_loc hak_loc hm_in hm8 hm_disj hmgas

theorem msgReadyAt_of_msgReady {F : Type} {s : PanSemStateFiniteExact 64 F} (h : MsgReady s) :
    ∃ S Nd, MsgReadyAt s S Nd := by
  obtain ⟨hA, S, Nd, hrest⟩ := msgReady_extract h
  exact ⟨S, Nd, hA, hrest⟩

theorem msgReadyAt_with_locals {F : Type} {s : PanSemStateFiniteExact 64 F}
    {locals : HolFiniteMapExact MlS (ValueHOL 64)} {k : Nat} {S Nd : List Nat}
    (hm : locals.lookup (ofString "msg") = s.locals.lookup (ofString "msg"))
    (h : MsgReadyAt s S Nd) :
    MsgReadyAt { s with locals := locals, clock := k } S Nd := by
  have hml := locN_congr s locals k "msg" hm
  unfold MsgReadyAt at h ⊢
  simp only [WorldTypedWith, tablesTyped_with_locals, arenaReady_with_locals] at h ⊢
  rw [hml]
  exact h

/-- Preserving `MsgReadyAt s S Nd` across ANY `WorldStep R gw keep Q` whose output regions `R s`
avoid `(locN s "msg", 176) :: worldTypedIvls s S Nd` (only for THAT `(S, Nd)`!) and have
8-byte-aligned zero-length bases! -/
theorem WorldStep.preserves_msgReadyAt {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)} {S Nd : List Nat}
    (hM : MsgReadyAt s S Nd)
    (hstep : WorldStep R gw keep Q s r post)
    (hR_z : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hR_all : IvlsDisj (R s) ((locN s "msg", 176) :: worldTypedIvls s S Nd)) :
    ∃ S0' Nd_post,
      let aa := memW s (locN s "msg" + 152)
      let ak := memW s (locN s "msg" + 160)
      MsgReadyAt { post with locals := s.locals } (S0' ++ [aa, ak]) Nd_post ∧
      Q s r post S0' Nd_post ∧
      ∀ t ∈ [aa, ak], htabFootprint post t = htabFootprint s t := by
  obtain ⟨hAs, hW, haa_S, hak_S, haa_ne_ak, haa_klen, hak_klen, haa_loc, hak_loc,
    hm8, hm_in, hm_disj, hmgas⟩ := hM
  set m := locN s "msg"
  set aa := memW s (m + 152)
  set ak := memW s (m + 160)
  have hR_m : ∀ x ∈ R s, Disj (m, 176) x := fun x hx => (hR_all x hx (m, 176) (by simp)).flip
  have hR_ti : IvlsDisj (R s) (worldTypedIvls s S Nd) :=
    fun x hx j hj => hR_all x hx j (List.mem_cons_of_mem _ hj)
  obtain ⟨hAp, hhp, _, _, hWS⟩ := hstep
  -- 1. Instantiate `hWS` at `(S, Nd)` to retain `Allocated post` on `htabFootprint post aa/ak`
  obtain ⟨S1', _, hsub1, hW1', _, _, _⟩ := hWS S Nd hW hR_ti
  have haa_S1' : aa ∈ S1' := hsub1 aa haa_S
  have hak_S1' : ak ∈ S1' := hsub1 ak hak_S
  -- 2. Peel `aa` and `ak` off `S` (`S0 := (S.erase aa).erase ak`) and instantiate `hWS` at `(S0, Nd)`
  let S_1 := S.erase aa
  let S0 := S_1.erase ak
  have hW_1 : WorldTypedWith s S_1 Nd := worldTypedWith_erase_local hW haa_loc
  have hW0 : WorldTypedWith s S0 Nd := worldTypedWith_erase_local hW_1 hak_loc
  have hsub0 : ∀ u ∈ S0, u ∈ S := fun u hu => List.mem_of_mem_erase (List.mem_of_mem_erase hu)
  have hsub_ti0 : ∀ i ∈ worldTypedIvls s S0 Nd, i ∈ worldTypedIvls s S Nd := by
    intro i hi; unfold worldTypedIvls at hi ⊢
    rcases List.mem_append.1 hi with h1 | hnd
    · apply List.mem_append.2; left
      rcases List.mem_append.1 h1 with h2 | hbal
      · apply List.mem_append.2; left
        rcases List.mem_append.1 h2 with h3 | hbo
        · apply List.mem_append.2; left
          rcases List.mem_append.1 h3 with h4 | hjr
          · apply List.mem_append.2; left
            rcases List.mem_append.1 h4 with htab | hrec
            · apply List.mem_append.2; left
              obtain ⟨u, hu0, hi_fp⟩ := List.mem_flatMap.1 htab
              exact List.mem_flatMap.2 ⟨u, hsub0 u hu0, hi_fp⟩
            · exact List.mem_append.2 (Or.inr hrec)
          · exact List.mem_append.2 (Or.inr hjr)
        · exact List.mem_append.2 (Or.inr hbo)
      · exact List.mem_append.2 (Or.inr hbal)
    · exact List.mem_append.2 (Or.inr hnd)
  have hsub_ow0 : ∀ j ∈ worldOwned s S0 Nd, j ∈ worldOwned s S Nd := by
    intro j hj; unfold worldOwned at hj ⊢
    rcases List.mem_append.1 hj with h1 | hnd
    · apply List.mem_append.2; left
      rcases List.mem_append.1 h1 with htab | hfix
      · apply List.mem_append.2; left
        obtain ⟨u, hu0, hj_fp⟩ := List.mem_flatMap.1 htab
        exact List.mem_flatMap.2 ⟨u, hsub0 u hu0, hj_fp⟩
      · exact List.mem_append.2 (Or.inr hfix)
    · exact List.mem_append.2 (Or.inr hnd)
  obtain ⟨S0', Nd0', _, hW0', hog0, hfr0, hQ0⟩ :=
    hWS S0 Nd hW0 (fun x hx i hi => hR_ti x hx i (hsub_ti0 i hi))
  obtain ⟨hT, _, _, hTr⟩ := hW
  have haa_not_S0 : aa ∉ S0 := by
    intro hm
    exact ((List.Nodup.mem_erase_iff hT.1).1 (List.mem_of_mem_erase hm)).1 rfl
  have hak_not_S0 : ak ∉ S0 := by
    intro hm
    exact ((List.Nodup.mem_erase_iff (hT.1.erase aa)).1 hm).1 rfl
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs.2
  obtain ⟨_, hp_hp, _, _, _⟩ := hAp.2
  have htab_surv : ∀ {t : Nat} (htS : t ∈ S) (htS1' : t ∈ S1') (ht0 : t ∉ S0),
      HtabWF post t ∧ htabFootprint post t = htabFootprint s t ∧ hdr post t 0 = hdr s t 0 ∧
      (∀ i ∈ htabFootprint post t, Allocated post i ∧ ∀ o ∈ worldOwned post S0' Nd0', Disj i o) := by
    intro t htS htS1' ht0
    have hwf_s := (hT.2.1 t htS).1
    have hdisj_ow0 : ∀ i ∈ htabFootprint s t, ∀ j ∈ worldOwned s S0 Nd, Disj i j := by
      intro i hi j hj
      unfold worldOwned at hj
      rcases List.mem_append.1 hj with h1 | hnd
      · rcases List.mem_append.1 h1 with htab | hfix
        · obtain ⟨u, hu0, hj_fp⟩ := List.mem_flatMap.1 htab
          exact hT.2.2.1 t htS u (hsub0 u hu0) (fun heq => ht0 (heq ▸ hu0)) i hi j hj_fp
        · exact ((hT.2.1 t htS).2 i hi).2 j hfix
      · exact ((hTr.2.1 j hnd).1 t htS i hi).flip
    have hunhit_t : ∀ i ∈ htabFootprint s t, IvlUnhit s post i := by
      intro i hi
      have hw := (hwf_s.1 i hi).2
      have hal_i := ((hT.2.1 t htS).2 i hi).1
      intro a ha8 hhit
      apply hfr0 a
      · intro j hj hcj
        rcases List.mem_append.1 hj with hj12 | hfg
        · rcases List.mem_append.1 hj12 with hj_ow | hj_R
          · exact not_cellHits_of_disj hw.1 hw.2.1 ha8 (worldOwned_zero_aligned hW0 j hj_ow) hhit (hdisj_ow0 i hi j hj_ow) hcj
          · have hi_ti : i ∈ worldTypedIvls s S Nd := by
              unfold worldTypedIvls
              apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
              apply List.mem_append.2; left; apply List.mem_append.2; left
              exact List.mem_flatMap.2 ⟨t, htS, hi⟩
            exact not_cellHits_of_disj hw.1 hw.2.1 ha8 (hR_z j hj_R) hhit (hR_ti j hj_R i hi_ti).flip hcj
        · simp only [List.mem_singleton] at hfg; subst hfg
          obtain ⟨hc1, hc2⟩ := hhit
          obtain ⟨hj1, hj2⟩ := hcj
          unfold freeGap at hj1 hj2; dsimp at hj1 hj2
          rcases hal_i with ⟨_, hhi_i⟩ | ⟨hlo_i, _⟩ <;> omega
      · intro ⟨hf1, hf2⟩
        obtain ⟨hc1, hc2⟩ := hhit
        unfold heapFree at hf1 hf2; dsimp at hf1 hf2
        rcases hal_i with ⟨_, hhi_i⟩ | ⟨hlo_i, _⟩ <;> omega
    have hwf_post : HtabWF post t := htabWF_congr_unhit hAs.1 hAp.1 hwf_s hunhit_t
    have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf_s.1 _ ht_fp).2.1
    have h264 : heapEnd ≤ 2 ^ 64 := by decide
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf_s.1 _ ht_fp).1.2; omega
    obtain ⟨hhdr_eq, hfp_eq⟩ := htabFootprint_eq_of_hdr_unhit ht8 hhi (hunhit_t _ ht_fp)
    refine ⟨hwf_post, hfp_eq, hhdr_eq 0 (by omega), fun i hi => ?_⟩
    have hal_post_i : Allocated post i := ((hW1'.1.2.1 t htS1').2 i hi).1
    rw [hfp_eq] at hi
    have hal_s_i : Allocated s i := ((hT.2.1 t htS).2 i hi).1
    refine ⟨hal_post_i, fun o ho => ?_⟩
    rcases hog0 o ho with rfl | ⟨j, hj0, hin_j⟩ | hfresh
    · exact disj_zero_right i
    · exact disj_of_inside_right hin_j (hdisj_ow0 i hi j hj0)
    · rcases hal_s_i with ⟨_, hhi_i⟩ | ⟨hlo_i, _⟩
      · exact Or.inr (Or.inr (Or.inl (Nat.le_trans hhi_i hfresh.1)))
      · exact Or.inr (Or.inr (Or.inr (by unfold Inside at hfresh; omega)))
  obtain ⟨hwf_aa, hfp_aa, hhdr_aa, hsurv_aa⟩ := htab_surv haa_S haa_S1' haa_not_S0
  obtain ⟨hwf_ak, hfp_ak, hhdr_ak, hsurv_ak⟩ := htab_surv hak_S hak_S1' hak_not_S0
  obtain ⟨_, haa_nz, haa_unass, hW_aa⟩ := adjoin_local_table hW0' hwf_aa hsurv_aa (hhdr_aa.trans haa_klen)
  have hsurv_ak2 : ∀ i ∈ htabFootprint post ak, Allocated post i ∧ ∀ o ∈ worldOwned post (S0' ++ [aa]) Nd0', Disj i o := by
    intro i hi
    refine ⟨(hsurv_ak i hi).1, fun o ho => ?_⟩
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · rw [List.flatMap_append] at htab
        rcases List.mem_append.1 htab with htab' | htab_aa
        · apply (hsurv_ak i hi).2 o
          unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htab')))
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at htab_aa
          rw [hfp_ak] at hi; rw [hfp_aa] at htab_aa
          exact hT.2.2.1 ak hak_S aa haa_S haa_ne_ak.symm i hi o htab_aa
      · apply (hsurv_ak i hi).2 o
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
    · apply (hsurv_ak i hi).2 o
      unfold worldOwned; exact List.mem_append.2 (Or.inr hnd)
  obtain ⟨_, hak_nz, hak_unass, hW_both⟩ := adjoin_local_table hW_aa hwf_ak hsurv_ak2 (hhdr_ak.trans hak_klen)
  have hassoc : (S0' ++ [aa]) ++ [ak] = S0' ++ [aa, ak] := by simp
  rw [hassoc] at hW_both
  -- 3. `(m, 176)` survives unhit and disjoint from `worldOwned post (S0' ++ [aa, ak]) Nd0'`
  obtain ⟨hm_in', hm_disj0', hm_u⟩ :=
    heap_ivl_survives_step hAs.2 hhp hog0 hfr0 (worldOwned_zero_aligned hW0) hR_z hm8 (by omega) hm_in
      (fun j hj => hm_disj j (hsub_ow0 j hj)) hR_m
  have hm_disj_both : ∀ o ∈ worldOwned post (S0' ++ [aa, ak]) Nd0', Disj (m, 176) o := by
    intro o ho
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · rw [List.flatMap_append] at htab
        rcases List.mem_append.1 htab with htab' | htab_loc
        · apply hm_disj0' o
          unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htab')))
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at htab_loc
          rcases htab_loc with haa_fp | hak_fp
          · rw [hfp_aa] at haa_fp
            exact hm_disj o (by unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨aa, haa_S, haa_fp⟩)))))
          · rw [hfp_ak] at hak_fp
            exact hm_disj o (by unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨ak, hak_S, hak_fp⟩)))))
      · apply hm_disj0' o
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
    · apply hm_disj0' o
      unfold worldOwned; exact List.mem_append.2 (Or.inr hnd)
  have hm_hi : m + 176 ≤ 2 ^ 64 := (ivl_allocated_bound hAs.2 (Or.inl hm_in)).2
  have hm152_post : memW post (m + 152) = aa :=
    memW_eq_of_ivlUnhit hm_u (by omega) hm_hi ⟨by omega, by omega⟩
  have hm160_post : memW post (m + 160) = ak :=
    memW_eq_of_ivlUnhit hm_u (by omega) hm_hi ⟨by omega, by omega⟩
  have hm40_post : memW post (m + 40) = memW s (m + 40) :=
    memW_eq_of_ivlUnhit hm_u (by omega) hm_hi ⟨by omega, by omega⟩
  refine ⟨S0', Nd0', ?_, hQ0, fun t ht => ?_⟩
  · unfold MsgReadyAt
    have hm_loc_eq : locN { post with locals := s.locals } "msg" = m := rfl
    rw [hm_loc_eq]
    change ArenaReady { post with locals := s.locals } ∧
      WorldTypedWith { post with locals := s.locals } (S0' ++ [aa, ak]) Nd0' ∧
      memW post (m + 152) ∈ S0' ++ [aa, ak] ∧
      memW post (m + 160) ∈ S0' ++ [aa, ak] ∧
      memW post (m + 152) ≠ memW post (m + 160) ∧
      hdr post (memW post (m + 152)) 0 = 20 ∧
      hdr post (memW post (m + 160)) 0 = 52 ∧
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ memW post (m + 152)) ∧
      (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ memW post (m + 160)) ∧
      m % 8 = 0 ∧
      Inside (m, 176) sourceBase (globN post "heap_ptr") ∧
      (∀ o ∈ worldOwned post (S0' ++ [aa, ak]) Nd0', Disj (m, 176) o) ∧
      memW post (m + 40) < 2 ^ 63
    rw [hm152_post, hm160_post, hm40_post]
    refine ⟨localsFree_arenaReady post s.locals post.clock hAp,
      by simp only [WorldTypedWith, tablesTyped_with_locals] at hW_both ⊢; exact hW_both,
      by simp, by simp, haa_ne_ak, hhdr_aa.trans haa_klen, hhdr_ak.trans hak_klen,
      haa_unass, hak_unass, hm8, hm_in', hm_disj_both, hmgas⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hfp_aa
    · exact hfp_ak

/-! ## 4. Lookup, Parameter, Hoare, Walk-Loop, and Straight-Line Combinators -/

theorem lookup_process_message_call :
    originalRuntimeCode.lookup (ofString "process_message_call") =
      some ((sourceFunctionEntry Guest.Software.guestFn_process_message_call).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 607 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_process_message_call) rfl

theorem lookup_process_message :
    originalRuntimeCode.lookup (ofString "process_message") =
      some ((sourceFunctionEntry Guest.Software.guestFn_process_message).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 588 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_process_message) rfl

theorem lookup_process_create_message :
    originalRuntimeCode.lookup (ofString "process_create_message") =
      some ((sourceFunctionEntry Guest.Software.guestFn_process_create_message).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 590 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_process_create_message) rfl

theorem lookup_process_unchecked_system_transaction :
    originalRuntimeCode.lookup (ofString "process_unchecked_system_transaction") =
      some ((sourceFunctionEntry Guest.Software.guestFn_process_unchecked_system_transaction).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 870 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_process_unchecked_system_transaction) rfl

theorem lookup_process_general_purpose_requests :
    originalRuntimeCode.lookup (ofString "process_general_purpose_requests") =
      some ((sourceFunctionEntry Guest.Software.guestFn_process_general_purpose_requests).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 877 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_process_general_purpose_requests) rfl

theorem lookup_alloc_fn :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ((sourceFunctionEntry Guest.Software.guestFn_alloc).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

theorem lookup_memcpy_fn :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ((sourceFunctionEntry Guest.Software.guestFn_memcpy).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

theorem lookup_memzero_fn :
    originalRuntimeCode.lookup (ofString "memzero") =
      some ((sourceFunctionEntry Guest.Software.guestFn_memzero).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memzero) rfl

theorem lookup_htab_new_fn :
    originalRuntimeCode.lookup (ofString "htab_new") =
      some ((sourceFunctionEntry Guest.Software.guestFn_htab_new).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 128 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_new) rfl

theorem lookup_extract_deposit_data_fn :
    originalRuntimeCode.lookup (ofString "extract_deposit_data") =
      some ((sourceFunctionEntry Guest.Software.guestFn_extract_deposit_data).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 841 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_extract_deposit_data) rfl

theorem worldTypedWith_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) :
    WorldTypedWith { s with locals := locals, clock := k } S Nd ↔ WorldTypedWith s S Nd := by
  simp only [WorldTypedWith, tablesTyped_with_locals]
  exact Iff.rfl

theorem callee_param_one_exp {F : Type} (state : PanSemStateFiniteExact 64 F) (fname p1 : MlS)
    (s1 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1)], body, ret))
    (e1 : ExpHOL 64) (v1 : ValueHOL 64)
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (he1 : evalAt state e1 = some v1)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    shapeEqHOL s1 (shapeOfHOLExact v1) = true ∧ callee.lookup p1 = some v1 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, he1, Option.some.injEq] at hargs
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
      obtain ⟨_, _, hsh⟩ := hcond
      simp only [List.zip] at hsh
      refine ⟨by simpa using hsh, ?_⟩
      simp [List.zip, List.foldl]
    · cases raw

theorem callee_param_two {F : Type} (state : PanSemStateFiniteExact 64 F) (fname p1 p2 : MlS)
    (s1 s2 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2)], body, ret))
    (e1 e2 : ExpHOL 64) (v1 v2 : ValueHOL 64)
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (he1 : evalAt state e1 = some v1) (he2 : evalAt state e2 = some v2)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    p1 ≠ p2 ∧ callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, he1, he2, Option.some.injEq] at hargs
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
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false] at hnd
      refine ⟨hnd.1, ?_, ?_⟩
      · simp [List.zip, List.foldl, hnd.1]
      · simp [List.zip, List.foldl]
    · cases raw

theorem callee_param_three {F : Type} (state : PanSemStateFiniteExact 64 F) (fname p1 p2 p3 : MlS)
    (s1 s2 s3 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2), (p3, s3)], body, ret))
    (e1 e2 e3 : ExpHOL 64) (v1 v2 v3 : ValueHOL 64)
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (he1 : evalAt state e1 = some v1) (he2 : evalAt state e2 = some v2) (he3 : evalAt state e3 = some v3)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, e3] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 ∧ callee.lookup p3 = some v3 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, he1, he2, he3, Option.some.injEq] at hargs
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
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        not_or, List.not_mem_nil, or_false] at hnd
      refine ⟨?_, ?_, ?_⟩
      · simp [List.zip, List.foldl, hnd.1.1, hnd.1.2]
      · simp [List.zip, List.foldl, hnd.2.1]
      · simp [List.zip, List.foldl]
    · cases raw

theorem callEntryOn_msgReady_same {fname : MlS} {e : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (hl : originalRuntimeCode.lookup fname = some e) (hp : e.1 = [(ofString "msg", .one)]) :
    CallEntryOn MsgReady MsgReady fname [.var .local (ofString "msg")] := by
  obtain ⟨ps, b, r⟩ := e
  dsimp only at hp
  subst hp
  intro F state values body' callee ret' hcode hP hargs hlook
  have hc := callee_param_one state fname (ofString "msg") .one b r (by rw [hcode]; exact hl) values
    body' callee ret' hargs hlook
  exact localsOnly_msgReady state callee (state.clock - 1)
    (fun n hn => by simp at hn; subst hn; exact hc) hP

theorem straight_guestInv (prog : ProgHOL 64) (hs : extStraightLine prog = true) :
    TerminatingProgBoundedOn GuestInv prog 0 :=
  TerminatingFunBoundedOn.of_unconditional_prog prog hs
where
  TerminatingFunBoundedOn.of_unconditional_prog (p : ProgHOL 64) (hp : extStraightLine p = true) :
      TerminatingProgBoundedOn GuestInv p 0 :=
    fun state hcode _ => TerminatingProgBounded.straight p hp state hcode

theorem straight_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (prog : ProgHOL 64) (hs : extStraightLine prog = true) :
    TerminatingProgBoundedOn P prog 0 :=
  fun state hcode _ => TerminatingProgBounded.straight prog hs state hcode

theorem Hoare.seq_fall {P R Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {first second : ProgHOL 64}
    (h1 : Hoare P first (fun r t => r = none → R t))
    (h2 : Hoare R second (fun r t => r = none → Q t)) :
    Hoare P (.seq first second) (fun r t => r = none → Q t) :=
  Hoare.seq ⟨fun s hc hP hnt => ⟨h1.run s hc hP hnt, fun hr h => absurd h hr⟩⟩ h2

theorem Hoare.dec_fall {P P' Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hname : ∀ n ∈ names, ofString n ≠ name)
    (hQ : LocalsOnly names Q)
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      evalAt s init = some v → P' (setVarHOLFinite name v s))
    (hbody : Hoare P' body (fun r t => r = none → Q t)) :
    Hoare P (.dec name shape init body) (fun r t => r = none → Q t) :=
  Hoare.dec hname hinit hbody
    (fun _ t locals hl h hr => hQ t locals t.clock hl (h hr))
    (fun _ _ hr => absurd hr (by simp))

theorem Hoare.ite_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hyes : Hoare (fun s => P s ∧ CondTrue cond s) yes (fun r t => r = none → Q t))
    (hno : Hoare (fun s => P s ∧ CondFalse cond s) no (fun r t => r = none → Q t)) :
    Hoare P (.ite cond yes no) (fun r t => r = none → Q t) :=
  Hoare.ite hyes hno (fun _ _ hr => absurd hr (by simp))

theorem Hoare.assign_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {kind : VarKind} {name : MlS} {source : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      evalAt s source = some v → Q (setKvarHOLFinite kind name v s)) :
    Hoare P (.assign kind name source) (fun r t => r = none → Q t) :=
  Hoare.assign (fun s v hP hv _ => h s v hP hv) (fun _ _ hr => absurd hr (by simp))

theorem Hoare.decCall_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {name fname : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hname : ∀ n ∈ names, ofString n ≠ name)
    (hQ : LocalsOnly names Q)
    (hres : DecCallResumeOn P R name fname arguments)
    (hcont : Hoare R cont (fun r t => r = none → Q t)) :
    Hoare P (.decCall name shape fname arguments cont) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.decCall name shape fname arguments cont) with ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst hr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with _ | values
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hrun; simp at hrun
      · rw [if_neg hz] at hrun
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨bres, bpost⟩
        rw [hb] at hrun hmeta
        dsimp only at hmeta
        cases bres with
        | none => simp at hrun
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hrun
            split at hrun
            · set resumed := setVarHOLFinite name v { bpost with locals := s.locals }
              have hresR : R resumed := hres s values body' callee ret' v bpost hcode hP hargs hl hb
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              rcases hc : evaluateHOLFiniteState resumed cont with ⟨cres, cpost⟩
              rw [hc] at hrun
              dsimp only at hrun
              obtain ⟨rfl, hpost_eq⟩ := Prod.mk.inj hrun
              have hQc0 := hcont.run resumed hresCode hresR (by rw [hc]; simp)
              rw [hc] at hQc0
              have hQc : Q cpost := hQc0 rfl
              dsimp only
              rw [← hpost_eq]
              exact hQ cpost _ cpost.clock
                (fun n hn => resVarEq_lookup_ne _ _ _ _ (hname n hn)) hQc
            · simp at hrun
          | _ => simp [emptyLocalsHOLFinite] at hrun

theorem Hoare.while_preserve {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {cond : ExpHOL 64} {body : ProgHOL 64}
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hbody : Hoare (fun s => P s ∧ CondTrue cond s) body
      (fun r t => (r = none ∨ r = some .continue ∨ r = some .break) → P t)) :
    Hoare P (.while cond body) (fun r t => r = none → P t) := by
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.while cond body) with ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst hr
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F),
      st.clock = k → st.code = originalRuntimeCode → P st →
      evaluateHOLFiniteState st (.while cond body) = (none, post) → P post from
    this s.clock s rfl hcode hP hrun
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk st_code hPst hst_run
    rw [evaluateHOLFiniteState_while_total] at hst_run
    split at hst_run
    · rename_i w hw
      split at hst_run
      · rename_i hwnz
        split at hst_run
        · simp at hst_run
        · dsimp only at hst_run
          rw [fixClockHOLFinite_evaluateState] at hst_run
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hmeta := (evaluateHOLFiniteState_metadata (decClockHOLFinite st) body).1
          have hct : CondTrue cond (decClockHOLFinite st) := by
            obtain ⟨_, hw', hwnz'⟩ := loopActive_decClock (s := st) ⟨w, hw, hwnz⟩
            refine ⟨_, ?_, hwnz'⟩
            rw [← evalHOLFinite_eq_toExact]
            exact hw'
          rcases bRun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r1, mid⟩
          rw [bRun] at hst_run hrem hmeta
          have hclk_lt : mid.clock < k := by
            change mid.clock ≤ st.clock - 1 at hrem
            omega
          have hb_nt : (evaluateHOLFiniteState (decClockHOLFinite st) body).1 ≠ some .timeOut := by
            intro hto
            rw [bRun] at hto; dsimp only at hto; subst hto
            simp at hst_run
          have hb_post := hbody.run (decClockHOLFinite st) st_code ⟨hdec st hPst, hct⟩ hb_nt
          rw [bRun] at hb_post
          dsimp only at hb_post
          cases r1 with
          | none =>
            exact ih mid.clock hclk_lt mid rfl (hmeta.trans st_code)
              (hb_post (Or.inl rfl)) hst_run
          | some r1' =>
            cases r1' with
            | «continue» =>
              exact ih mid.clock hclk_lt mid rfl (hmeta.trans st_code)
                (hb_post (Or.inr (Or.inl rfl))) hst_run
            | «break» =>
              simp at hst_run
              obtain ⟨_, rfl⟩ := hst_run
              exact hb_post (Or.inr (Or.inr rfl))
            | _ => simp at hst_run
      · simp at hst_run
        obtain ⟨_, rfl⟩ := hst_run
        exact hPst
    · simp at hst_run

theorem panMemStoresHOL_word_spec {F : Type} {s : PanSemStateFiniteExact 64 F}
    {x : BitVec 64} {w : HolWordLab 64} {mem' : BitVec 64 → HolWordLab 64}
    (hst : @panMemStoresHOL 64 _ x [w] s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem') :
    s.memaddrs x ∧ mem' x = w ∧ ∀ a : BitVec 64, a ≠ x → mem' a = s.memory a := by
  unfold panMemStoresHOL panMemStoreHOL at hst
  split_ifs at hst with hdom
  simp only [panMemStoresHOL, Option.some.injEq] at hst
  subst hst
  exact ⟨hdom, if_pos rfl, fun a hne => if_neg hne⟩

theorem panMemStoresHOL_frame {dom : BitVec 64 → Prop} {dec : DecidablePred dom} :
    ∀ (ws : List (HolWordLab 64)) (x : BitVec 64) (mem mem' : BitVec 64 → HolWordLab 64),
      @panMemStoresHOL 64 _ x ws dom dec mem = some mem' →
      ∀ a : BitVec 64, (∀ k, k < ws.length → a ≠ x + BitVec.ofNat 64 (8 * k)) → mem' a = mem a
  | [], _, mem, mem', hst, a, _ => by
    simp only [panMemStoresHOL, Option.some.injEq] at hst
    rw [← hst]
  | w :: ws, x, mem, mem', hst, a, hne => by
    unfold panMemStoresHOL panMemStoreHOL at hst
    split_ifs at hst with hdom
    have hbw : (panBytesInWord 64 : BitVec 64) = BitVec.ofNat 64 8 := by decide
    have ih := panMemStoresHOL_frame ws (x + panBytesInWord 64)
      (fun current => if current = x then w else mem current) mem' hst a (fun k hk => by
        have hk1 : k + 1 < (w :: ws).length := by simp; omega
        have hne1 := hne (k + 1) hk1
        rw [hbw]
        intro heq
        apply hne1
        rw [heq, BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega)
    rw [ih]
    exact if_neg (by simpa using hne 0 (by simp))

theorem panMemStoresHOL_nonempty_dom {dom : BitVec 64 → Prop} {dec : DecidablePred dom}
    {w : HolWordLab 64} {ws : List (HolWordLab 64)} {x : BitVec 64}
    {mem mem' : BitVec 64 → HolWordLab 64}
    (hst : @panMemStoresHOL 64 _ x (w :: ws) dom dec mem = some mem') :
    dom x := by
  unfold panMemStoresHOL panMemStoreHOL at hst
  split_ifs at hst with hdom
  exact hdom

theorem Hoare.store_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {dst src : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64) (v : ValueHOL 64)
      (mem' : BitVec 64 → HolWordLab 64),
      P s → evalAt s dst = some (.val (.word x)) → evalAt s src = some v →
      @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem' →
      Q { s with memory := mem' }) :
    Hoare P (.store dst src) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s _ hP _ hr => ?_⟩
  rw [evaluateHOLFiniteState_store] at hr ⊢
  revert hr
  split
  · rename_i x hx
    split
    · rename_i v hv
      rcases hm : @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
          (fun a => Classical.propDecidable (s.memaddrs a)) s.memory with _ | mem'
      · simp
      · intro _
        exact h s x v mem' hP hx hv hm
    · simp
  · simp

theorem TerminatingProgBoundedOn.seq_hoare_trans
    {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a) (hp : Hoare P first (fun r t => r = none → Q t))
    (h2 : TerminatingProgBoundedOn Q second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  have hmid := hp.run state hcode hP
  simp only [hr1] at hmeta hnt hmid ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) (hmid (by simp) rfl) hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    exact ⟨by omega, k1⟩

/-! ## 5. Proof 1: `gbody_process_message_call` -/

def MsgReadyWithOut : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_out : BitVec 64, ∃ S Nd : List Nat,
    MsgReadyAt s S Nd ∧
    s.locals.lookup (ofString "out") = some (.val (.word w_out)) ∧
    Disj (w_out.toNat, 96) (locN s "msg", 176) ∧
    IvlsDisj [(w_out.toNat, 96)] (worldTypedIvls s S Nd)

theorem msgReadyWithOut_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : MsgReadyWithOut s) : GuestInv s := by
  obtain ⟨_, _, _, hM, _⟩ := h
  exact hM.1.1

theorem resumeOn_alloc96_msgReady
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn MsgReady MsgReadyWithOut (ofString "out") (ofString "alloc") [.const 96#64] := by
  intro F state values body callee ret value post hcode hM hargs hl hrun
  obtain ⟨S, Nd, hMA⟩ := msgReadyAt_of_msgReady hM
  have hpc := callee_param_one_exp state (ofString "alloc") (ofString "n") .one _ _
    (by rw [hcode]; exact lookup_alloc_fn) (.const 96#64) (.val (.word 96#64)) values body callee ret rfl hargs hl
  have hn_loc : locN (callEntryStateHOLFinite state callee) "n" = 96 := by
    simp [locN, callEntryStateHOLFinite, hpc.2]
  have hstep := FunSpec.at_lookup wal state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) (msgReady_worldOK state hM))
    (by rw [hrun]; simp)
  rw [hrun] at hstep
  dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtal state hcode values body callee ret hl
    (localsFree_arenaReady state callee (state.clock - 1) hM.1)
    (by rw [hrun]; simp)
  rw [hrun] at hrt
  dsimp only at hrt
  obtain ⟨w_out, rfl, _, _, hfb⟩ := hrt value rfl
  rw [hn_loc] at hfb
  have hws_caller : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (fun _ r' post' S' Nd' => ∀ v', r' = some (.returned v') → ∃ w : BitVec 64,
        v' = .val (.word w) ∧ IvlsDisj [(w.toNat, 96)] (worldOwned post' S' Nd'))
      state (some (.returned (.val (.word w_out)))) post := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hws
    refine ⟨h1, h2, h3, h4, fun S_x Nd_x hW_x _ => ?_⟩
    obtain ⟨S_x', Nd_x', hsub_x, hW_x', hog_x, hfr_x, hQ_x⟩ :=
      h5 S_x Nd_x ((worldTypedWith_with_locals _ _ _ _ _).2 hW_x) (fun x hx => by simp at hx)
    refine ⟨S_x', Nd_x', hsub_x, hW_x', hog_x, hfr_x, fun v' hv' => ?_⟩
    obtain ⟨w, hw_eq, hav⟩ := hQ_x v' hv'
    dsimp only at hav
    rw [hn_loc] at hav
    exact ⟨w, hw_eq, hav⟩
  obtain ⟨S0', Nd_post, hMA_post, hQ0, hfp_eq⟩ :=
    WorldStep.preserves_msgReadyAt hMA hws_caller (fun j hj => by simp at hj) (fun x hx => by simp at hx)
  obtain ⟨w_out', hw_eq, hav0⟩ := hQ0 (.val (.word w_out)) rfl
  injection hw_eq with hw_eq'
  injection hw_eq' with hw_eq''
  subst hw_eq''
  set resumed := setVarHOLFinite (ofString "out") (.val (.word w_out)) { post with locals := state.locals }
  have hout_ne_msg : ofString "out" ≠ ofString "msg" := by decide
  have hMA_res : MsgReadyAt resumed (S0' ++ [memW state (locN state "msg" + 152), memW state (locN state "msg" + 160)]) Nd_post :=
    msgReadyAt_with_locals (s := { post with locals := state.locals })
      (by simp [HolFiniteMapExact.update, FUPDATE, hout_ne_msg]) hMA_post
  have hm_loc_eq : locN resumed "msg" = locN state "msg" := by
    rw [locN_setVar_ne _ "msg" (ofString "out") _ (by decide)]
    rfl
  have hm_in_s : Inside (locN state "msg", 176) sourceBase (globN state "heap_ptr") :=
    hMA.2.2.2.2.2.2.2.2.2.2.1
  have hout_disj_m : Disj (w_out.toNat, 96) (locN state "msg", 176) :=
    Or.inr (Or.inr (Or.inr (Nat.le_trans hm_in_s.2 hfb.2.1.1)))
  refine ⟨w_out, S0' ++ [memW state (locN state "msg" + 152), memW state (locN state "msg" + 160)], Nd_post,
    hMA_res, ?_, ?_, ?_⟩
  · simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · rw [hm_loc_eq]; exact hout_disj_m
  · intro x hx j hj
    simp only [List.mem_singleton] at hx; subst hx
    have hj_ow : j ∈ worldOwned post (S0' ++ [memW state (locN state "msg" + 152), memW state (locN state "msg" + 160)]) Nd_post :=
      worldTypedIvls_sub_worldOwned _ _ _ j hj
    unfold worldOwned at hj_ow
    rcases List.mem_append.1 hj_ow with h1 | hnd
    · rcases List.mem_append.1 h1 with htab | hfix
      · rw [List.flatMap_append] at htab
        rcases List.mem_append.1 htab with htab0 | htab_loc
        · apply hav0 (w_out.toNat, 96) (by simp) j
          unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htab0)))
        · obtain ⟨u, hu_loc, hj_fp⟩ := List.mem_flatMap.1 htab_loc
          rw [hfp_eq u hu_loc] at hj_fp
          have hu_S : u ∈ S := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_loc
            rcases hu_loc with rfl | rfl
            · exact hMA.2.2.1
            · exact hMA.2.2.2.1
          have hal_j : Allocated state j := ((hMA.2.1.1.2.1 u hu_S).2 j hj_fp).1
          have hsep : heapLimit ≤ scratchStart := by decide
          obtain ⟨_, h1_s, h2_s, h3_s, _⟩ := hMA.1.2
          obtain ⟨_, hp1, _⟩ := hws.1.2
          have hfb_in : Inside (w_out.toNat, 96) (globN state "heap_ptr") (globN post "heap_ptr") := hfb.2.1
          rcases hal_j with ⟨_, hhi_j⟩ | ⟨hlo_j, _⟩
          · exact Or.inr (Or.inr (Or.inr (Nat.le_trans hhi_j hfb_in.1)))
          · exact Or.inr (Or.inr (Or.inl (by unfold Inside at hfb_in; omega)))
      · apply hav0 (w_out.toNat, 96) (by simp) j
        unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
    · apply hav0 (w_out.toNat, 96) (by simp) j
      unfold worldOwned; exact List.mem_append.2 (Or.inr hnd)

theorem hoare_memzero96_msgReady
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero")) :
    Hoare MsgReadyWithOut
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "out"), .const 96#64])
      (fun r t => r = none → MsgReady t) := by
  refine ⟨fun {F} state hcode hMW _ hr => ?_⟩
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "out"), .const 96#64]) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  show MsgReady cpost
  obtain ⟨w_out, S, Nd, hMA, hout_lu, hout_dm, hout_dti⟩ := hMW
  rw [evaluateHOLFiniteState_call] at hcall
  have hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "out"), .const 96#64] = some [.val (.word w_out), .val (.word 96#64)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, hout_lu]
  rw [hargs] at hcall
  dsimp only at hcall
  rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "memzero")
      [.val (.word w_out), .val (.word 96#64)] with _ | ⟨body, callee, ret⟩
  · rw [hl] at hcall; simp at hcall
  · rw [hl] at hcall
    dsimp only at hcall
    by_cases hz : state.clock = 0
    · rw [if_pos hz] at hcall; simp at hcall
    · rw [if_neg hz] at hcall
      have hp2 := callee_param_two state (ofString "memzero") (ofString "dst") (ofString "n") .one .one _ _
        (by rw [hcode]; exact lookup_memzero_fn)
        (.var .local (ofString "out")) (.const 96#64) (.val (.word w_out)) (.val (.word 96#64))
        [.val (.word w_out), .val (.word 96#64)] body callee ret
        (by simp [evalAt, evalHOLExact, hout_lu]) rfl hargs hl
      have hdst : locN (callEntryStateHOLFinite state callee) "dst" = w_out.toNat := by
        simp [locN, callEntryStateHOLFinite, hp2.2.1]
      have hn : locN (callEntryStateHOLFinite state callee) "n" = 96 := by
        simp [locN, callEntryStateHOLFinite, hp2.2.2]
      rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
      rw [hrun] at hcall
      cases bres with
      | none => simp at hcall
      | some br =>
        cases br with
        | returned v =>
          dsimp only at hcall
          by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret = true
          · rw [if_pos hsh] at hcall
            obtain ⟨_, rfl⟩ := Prod.mk.inj hcall
            have hstep := FunSpec.at_lookup wmz state hcode _ body callee ret hl
              (localsFree_worldOK state callee (state.clock - 1) (msgReady_worldOK state (msgReadyAt_msgReady hMA)))
              (by rw [hrun]; simp)
            rw [hrun] at hstep
            dsimp only at hstep
            have hws := hstep (Or.inl ⟨v, rfl⟩)
            have hws_caller : WorldStep (fun _ => [(w_out.toNat, 96)]) []
                [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
                 ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
                NoExtra state (some (.returned v)) post := by
              obtain ⟨h1, h2, h3, h4, h5⟩ := hws
              refine ⟨h1, h2, h3, ?_, fun S_x Nd_x hW_x hD_x => ?_⟩
              · intro r_k hr_k hgnz k hk hnc
                apply h4 r_k hr_k hgnz k hk
                dsimp only
                rw [hdst, hn]; exact hnc
              · have h5' := h5 S_x Nd_x ((worldTypedWith_with_locals _ _ _ _ _).2 hW_x)
                  (by dsimp only; rw [hdst, hn]; exact hD_x)
                dsimp only at h5'
                rw [hdst, hn] at h5'
                exact h5'
            obtain ⟨_, _, hMA_post, _, _⟩ :=
              WorldStep.preserves_msgReadyAt hMA hws_caller
                (fun j hj => by simp at hj; subst hj; omega)
                (fun x hx j hj => by
                  simp only [List.mem_singleton] at hx; subst hx
                  rcases List.mem_cons.1 hj with rfl | hj_ti
                  · exact hout_dm
                  · exact hout_dti (w_out.toNat, 96) (by simp) j hj_ti)
            exact msgReadyAt_msgReady hMA_post
          · rw [if_neg hsh] at hcall; simp at hcall
        | _ => simp at hcall

theorem resumeOn_account_deployable_msgReady
    (wad : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "account_deployable"))
    (args : List (ExpHOL 64)) :
    DecCallResumeOn MsgReady MsgReady (ofString "dep") (ofString "account_deployable") args := by
  intro F state values body callee ret value post hcode hM _ hl hrun
  obtain ⟨S, Nd, hMA⟩ := msgReadyAt_of_msgReady hM
  have hstep := FunSpec.at_lookup wad state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) (msgReady_worldOK state hM))
    (by rw [hrun]; simp)
  rw [hrun] at hstep
  dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hws_caller : WorldStep
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra state (some (.returned value)) post := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hws
    refine ⟨h1, h2, h3, h4, fun S_x Nd_x hW_x hD_x => ?_⟩
    exact h5 S_x Nd_x ((worldTypedWith_with_locals _ _ _ _ _).2 hW_x) hD_x
  have hbuf_mem : ∀ gn ∈ ([("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64)] : List (String × Nat)),
      gn ∈ globalBuffers ∧ gn.1 ∉ typedRecords.map Prod.fst := by decide
  obtain ⟨_, _, hMA_post, _, _⟩ :=
    WorldStep.preserves_msgReadyAt hMA hws_caller
      (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · intro hz
          by_cases hk0 : globN state "keccak_pad" = 0
          · dsimp only; rw [hk0]
          · exfalso; have hz' : (if globN state "keccak_pad" = 0 then 0 else 136) = 0 := hz
            rw [if_neg hk0] at hz'; cases hz'
        · intro hz
          by_cases hk0 : globN state "keccak_st" = 0
          · dsimp only; rw [hk0]
          · exfalso; have hz' : (if globN state "keccak_st" = 0 then 0 else 200) = 0 := hz
            rw [if_neg hk0] at hz'; cases hz'
        · intro hz
          by_cases hk0 : globN state "mpt_nib_scratch" = 0
          · dsimp only; rw [hk0]
          · exfalso; have hz' : (if globN state "mpt_nib_scratch" = 0 then 0 else 64) = 0 := hz
            rw [if_neg hk0] at hz'; cases hz')
      (fun x hx j hj => by
        change x ∈ [bufferRegion state ("keccak_pad", 136), bufferRegion state ("keccak_st", 200),
          bufferRegion state ("mpt_nib_scratch", 64)] at hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        have hgn : ∃ gn ∈ ([("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64)] : List (String × Nat)),
            x = bufferRegion state gn := by
          rcases hx with rfl | rfl | rfl
          · exact ⟨("keccak_pad", 136), by simp, rfl⟩
          · exact ⟨("keccak_st", 200), by simp, rfl⟩
          · exact ⟨("mpt_nib_scratch", 64), by simp, rfl⟩
        obtain ⟨gn, hgn_in, rfl⟩ := hgn
        obtain ⟨hg, hu⟩ := hbuf_mem gn hgn_in
        rcases List.mem_cons.1 hj with rfl | hj_ti
        · have hx_ow : bufferRegion state gn ∈ worldOwned state S Nd := by
            unfold worldOwned fixedObjects
            apply List.mem_append.2; left; apply List.mem_append.2; right
            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
            exact List.mem_map.2 ⟨gn, hg, rfl⟩
          exact (hMA.2.2.2.2.2.2.2.2.2.2.2.1 _ hx_ow).flip
        · exact bufferRegion_disj hMA.2.1 gn hg hu j hj_ti)
  exact localsOnly_msgReady.setVar (by simp; decide) value _ (msgReadyAt_msgReady hMA_post)

theorem seq_ends_return_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    {p : ProgHOL 64} {e : ExpHOL 64} :
    (evaluateHOLFiniteState s (.seq p (.return e))).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s p with ⟨r, mid⟩
  cases r with
  | none => exact return_ne_none mid e
  | some _ => simp

theorem seq4_return_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p1 p2 p3 p4 : ProgHOL 64) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.seq p1 (.seq p2 (.seq p3 (.seq p4 (.return e)))))).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
  cases r1 with
  | some _ => simp
  | none =>
    dsimp only; rw [evaluateHOLFiniteState_seq_line780]
    rcases evaluateHOLFiniteState s1 p2 with ⟨r2, s2⟩
    cases r2 with
    | some _ => simp
    | none =>
      dsimp only; rw [evaluateHOLFiniteState_seq_line780]
      rcases evaluateHOLFiniteState s2 p3 with ⟨r3, s3⟩
      cases r3 with
      | some _ => simp
      | none => exact seq_ends_return_ne_none s3

theorem prove_gbody_process_message_call
    (had : TerminatingFunBoundedOn GuestInv (ofString "account_deployable") K.«account_deployable»)
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hfsg : TerminatingFunBoundedOn GuestInv (ofString "frame_state_gas_used") K.«frame_state_gas_used»)
    (hmz : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero»)
    (hpcm : TerminatingFunBoundedOn MsgReady (ofString "process_create_message") K.«process_create_message»)
    (hpm : TerminatingFunBoundedOn MsgReady (ofString "process_message") K.«process_message»)
    (wad : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "account_deployable"))
    (wal : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (wmz : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")])
      []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero"))
    (_zvmz : ZeroFills (ofString "memzero")) :
    TerminatingFunBoundedOn MsgReady (ofString "process_message_call") K.«process_message_call» := by
  refine ⟨_, _, _, lookup_process_message_call, ?_⟩
  simp only [InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  have hskip : Hoare MsgReady .skip (fun r t => r = none → MsgReady t) :=
    Hoare.skip fun _ h _ => h
  have hdep_guard : ∀ (cond : ExpHOL 64) (p1 p2 p3 p4 : ProgHOL 64) (e : ExpHOL 64),
      Hoare MsgReady (.ite cond (.seq p1 (.seq p2 (.seq p3 (.seq p4 (.return e))))) .skip)
        (fun r t => r = none → MsgReady t) := fun cond p1 p2 p3 p4 e =>
    Hoare.ite ⟨fun s _ _ _ h => absurd h (seq4_return_ne_none s p1 p2 p3 p4 e)⟩
      (Hoare.skip fun _ h _ => h.1) (fun _ _ h => absurd h (by simp))
  have hm_guest : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), MsgReady s → GuestInv s :=
    fun _ h => h.1.1
  have hentry_pcm : CallEntryOn MsgReady MsgReady (ofString "process_create_message")
      [.var .local (ofString "msg")] :=
    callEntryOn_msgReady_same lookup_process_create_message rfl
  have hentry_pm : CallEntryOn MsgReady MsgReady (ofString "process_message")
      [.var .local (ofString "msg")] :=
    callEntryOn_msgReady_same lookup_process_message rfl
  intro F state hcode hP
  exact TerminatingRunBounded.weaken
    ((TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)) hskip
      (TerminatingProgBoundedOn.decCall_on hal _ _ _
        (callEntryOn_of_imp localsFree_guestInv hm_guest _ _)
        (resumeOn_alloc96_msgReady wal rtal)
        (TerminatingProgBoundedOn.seq_hoare_trans
          (TerminatingProgBoundedOn.call_on hmz _ _
            (callEntryOn_of_imp localsFree_guestInv msgReadyWithOut_guestInv _ _))
          (hoare_memzero96_msgReady wmz)
          (TerminatingProgBoundedOn.dec_onLocals localsOnly_msgReady (ofString "frame") (by simp; decide) _ _
            (TerminatingProgBoundedOn.seq_guestInv_after
              (TerminatingProgBoundedOn.ite_on
                (TerminatingProgBoundedOn.decCall_on had _ _ _
                  (callEntryOn_of_imp localsFree_guestInv hm_guest _ _)
                  (resumeOn_account_deployable_msgReady wad _)
                  (TerminatingProgBoundedOn.seq_hoare
                    (TerminatingProgBoundedOn.ite_on
                      (TerminatingProgBoundedOn.of_clock
                        (seq_clock (fun s => clock_store s _ _)
                          (seq_clock (fun s => clock_store s _ _)
                            (seq_clock (fun s => clock_store s _ _)
                              (seq_clock (fun s => clock_store s _ _)
                                (fun s => clock_return s _))))))
                      (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                    (hdep_guard _ _ _ _ _ _)
                    (TerminatingProgBoundedOn.call_on hpcm _ _ hentry_pcm)))
                (TerminatingProgBoundedOn.call_on hpm _ _ hentry_pm))
              hm_guest
              (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                  (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                    (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                      (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                        (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                          (TerminatingProgBoundedOn.decCall_guestInv hfsg _ _ _
                            (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                              (TerminatingProgBoundedOn.seq_guestInv
                                (TerminatingProgBoundedOn.ite_on
                                  (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                    (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                      (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
                                        (TerminatingProgBoundedOn.seq_guestInv
                                          (TerminatingProgBoundedOn.ite_on
                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                                          (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))))))
                                  (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                                (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                  (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                    (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))))))))))))) state hcode hP)
    (by
      unfold K.«process_message_call»
      simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]
      omega)

/-! ## 6. Proof 2: `gbody_process_general_purpose_requests` -/

theorem lookup_requests_append_fn :
    originalRuntimeCode.lookup (ofString "requests_append") =
      some ((sourceFunctionEntry Guest.Software.guestFn_requests_append).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 876 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_requests_append) rfl

def ReqState (c : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ globN s "bo" ≠ 0 ∧ memW s (globN s "bo" + 64) ≤ c

theorem localsFree_reqState (c : Nat) : LocalsFree (ReqState c) := by
  intro F s locals k ⟨hW, hbo, hc⟩
  exact ⟨localsFree_worldOK s locals k hW, hbo, hc⟩

theorem reqState_mono {c1 c2 : Nat} (hle : c1 ≤ c2) {F : Type}
    {s : PanSemStateFiniteExact 64 F} (h : ReqState c1 s) : ReqState c2 s :=
  ⟨h.1, h.2.1, Nat.le_trans h.2.2 hle⟩

theorem reqState_reqRoom {c : Nat} (hc : c < 8) {F : Type}
    {s : PanSemStateFiniteExact 64 F} (h : ReqState c s) : ReqRoom s :=
  ⟨h.1, lt_of_le_of_lt h.2.2 hc⟩

theorem reqState_worldOK {c : Nat} {F : Type}
    {s : PanSemStateFiniteExact 64 F} (h : ReqState c s) : WorldOK s := h.1

theorem reqState_guestInv {c : Nat} {F : Type}
    {s : PanSemStateFiniteExact 64 F} (h : ReqState c s) : GuestInv s := h.1.1.1

def DepLoopInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_dep w_n w_cap : BitVec 64, ∃ S Nd : List Nat,
    WorldTypedWith s S Nd ∧
    ArenaReady s ∧
    globN s "bo" ≠ 0 ∧
    memW s (globN s "bo" + 64) = 0 ∧
    s.locals.lookup (ofString "dep") = some (.val (.word w_dep)) ∧
    s.locals.lookup (ofString "dep_n") = some (.val (.word w_n)) ∧
    s.locals.lookup (ofString "dep_cap") = some (.val (.word w_cap)) ∧
    w_n.toNat ≤ w_cap.toNat ∧
    w_dep.toNat % 8 = 0 ∧
    w_n.toNat % 8 = 0 ∧
    w_cap.toNat % 8 = 0 ∧
    Inside (w_dep.toNat, w_cap.toNat) sourceBase (globN s "heap_ptr") ∧
    IvlsDisj [(w_dep.toNat, w_cap.toNat)] (worldOwned s S Nd)

theorem depLoopInv_reqState0 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : DepLoopInv s) : ReqState 0 s := by
  obtain ⟨_, _, _, S, Nd, hW, hA, hbo, hc0, _⟩ := h
  exact ⟨⟨hA, S, (worldTyped_iff_with s S).2 ⟨Nd, hW⟩⟩, hbo, by omega⟩

theorem depLoopInv_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : DepLoopInv s) : GuestInv s :=
  (depLoopInv_reqState0 h).1.1.1

theorem localsOnly_depLoopInv : LocalsOnly ["dep", "dep_n", "dep_cap"] DepLoopInv := by
  intro F s locals k hl h
  obtain ⟨w_dep, w_n, w_cap, S, Nd, hW, hA, hbo, hc0, hlu_d, hlu_n, hlu_c, hle, hd8, hn8, hc8, hin, hdisj⟩ := h
  refine ⟨w_dep, w_n, w_cap, S, Nd,
    (worldTypedWith_with_locals s locals k S Nd).2 hW,
    localsFree_arenaReady s locals k hA,
    hbo, hc0,
    (hl "dep" (by simp)).trans hlu_d,
    (hl "dep_n" (by simp)).trans hlu_n,
    (hl "dep_cap" (by simp)).trans hlu_c,
    hle, hd8, hn8, hc8, hin, hdisj⟩

theorem evalAt_load_one_ordinary {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hg : GuestInv s) {addr : ExpHOL 64} {v : ValueHOL 64}
    (hev : evalAt s (.load .one addr) = some v) :
    ∃ a w : BitVec 64, evalAt s addr = some (.val (.word a)) ∧
      v = .val (.word w) ∧ a.toNat % 8 = 0 ∧ sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
  simp only [evalAt, evalHOLExact] at hev
  rcases ha : @evalHOLExact 64 F _ s.toExact (fun address => Classical.propDecidable (s.memaddrs address)) addr with _ | va
  · rw [ha] at hev; simp at hev
  · rw [ha] at hev
    cases va with
    | val wl =>
      cases wl with
      | word a =>
        simp only [memLoadHOLExact] at hev
        split_ifs at hev with _ hdom
        simp only [Option.some.injEq] at hev
        rw [hg.memaddrs, ordinaryDomain_iff] at hdom
        cases hmem : s.memory a with
        | word w =>
          rw [hmem] at hev
          exact ⟨a, w, ha, hev.symm, hdom.1, hdom.2.1, hdom.2.2⟩
    | rStruct _ => simp at hev
    | nStruct _ => simp at hev

theorem evalAt_add_panMul8 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base idx : MlS} {v : ValueHOL 64}
    (hev : evalAt s (.op .add [.var .local base, .panop .mul [.var .local idx, .const 8#64]]) = some v) :
    ∃ wb wi : BitVec 64,
      s.locals.lookup base = some (.val (.word wb)) ∧
      s.locals.lookup idx = some (.val (.word wi)) ∧
      v = .val (.word (wb + wi * 8#64)) := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hev
  rcases hb : s.locals.lookup base with _ | vb
  · simp [hb] at hev
  · rcases hi : s.locals.lookup idx with _ | vi
    · simp [hb, hi] at hev
    · cases vi with
      | rStruct _ => simp [hb, hi, valueIsWord] at hev
      | nStruct _ => simp [hb, hi, valueIsWord] at hev
      | val wli =>
        cases wli with
        | word wi =>
          cases vb with
          | rStruct _ => simp [hb, hi, valueIsWord, panOpHOL] at hev
          | nStruct _ => simp [hb, hi, valueIsWord, panOpHOL] at hev
          | val wlb =>
            cases wlb with
            | word wb =>
              simp only [hb, hi, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp,
                List.all, List.map, Option.map, Bool.and_self, if_true, Option.some.injEq] at hev
              refine ⟨wb, wi, rfl, rfl, ?_⟩
              rw [← hev]
              congr 2
              simp [BitVec.add_zero]

def walkRank (baseName idxName : String) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  min (heapEnd - (BitVec.ofNat 64 (locN s baseName) + BitVec.ofNat 64 (locN s idxName) * 8#64).toNat)
    31104957944

theorem walkRank_le (baseName idxName : String) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    walkRank baseName idxName s ≤ 31104957944 :=
  Nat.min_le_right _ _

theorem walkRank_step_lt {baseName idxName : String} {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {wb wi : BitVec 64}
    (hb_s : s.locals.lookup (ofString baseName) = some (.val (.word wb)))
    (hi_s : s.locals.lookup (ofString idxName) = some (.val (.word wi)))
    (hb_p : post.locals.lookup (ofString baseName) = some (.val (.word wb)))
    (hi_p : post.locals.lookup (ofString idxName) = some (.val (.word (wi + 1#64))))
    (hlo : sourceBase ≤ (wb + wi * 8#64).toNat)
    (hhi : (wb + wi * 8#64).toNat < heapEnd) :
    walkRank baseName idxName post < walkRank baseName idxName s := by
  unfold walkRank
  have hloc_bs : BitVec.ofNat 64 (locN s baseName) = wb := by simp [locN, hb_s]
  have hloc_is : BitVec.ofNat 64 (locN s idxName) = wi := by simp [locN, hi_s]
  have hloc_bp : BitVec.ofNat 64 (locN post baseName) = wb := by simp [locN, hb_p]
  have hloc_ip : BitVec.ofNat 64 (locN post idxName) = wi + 1#64 := by
    simp only [locN, hi_p, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hloc_bs, hloc_is, hloc_bp, hloc_ip]
  have hdom_le : heapEnd - (wb + wi * 8#64).toNat ≤ 31104957944 := by
    have hsb : sourceBase = 2701131776 := by decide
    have hhe : heapEnd = 33806089704 := by decide
    omega
  have hadd8 : wb + (wi + 1#64) * 8#64 = (wb + wi * 8#64) + 8#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  rw [hadd8]
  have h264 : heapEnd + 8 < 2 ^ 64 := by decide
  have htonat : ((wb + wi * 8#64) + 8#64).toNat = (wb + wi * 8#64).toNat + 8 := by
    rw [BitVec.toNat_add]
    change ((wb + wi * 8#64).toNat + 8) % 2 ^ 64 = (wb + wi * 8#64).toNat + 8
    exact Nat.mod_eq_of_lt (by omega)
  rw [htonat]
  omega

theorem dec_rls_reqsFresh_to_reqState0 :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      ReqsFresh s →
      evalAt s (.load .one (.op .add [.var .global (ofString "bo"), .const 72#64])) = some v →
      ReqState 0 (setVarHOLFinite (ofString "rls") v s) := by
  intro F s v ⟨hW, hc0⟩ hev
  obtain ⟨a, _, ha, _, _, hlo, _⟩ := evalAt_load_one_ordinary hW.1.1 hev
  have hbo_nz : globN s "bo" ≠ 0 := by
    intro hbo0
    simp only [evalAt, evalHOLExact, evalListHOLExact] at ha
    rcases hg : s.globals.lookup (ofString "bo") with _ | vb
    · simp [hg] at ha
    · cases vb with
      | rStruct _ => simp [hg, valueIsWord] at ha
      | nStruct _ => simp [hg, valueIsWord] at ha
      | val wlb =>
        cases wlb with
        | word wbo =>
          have hwbo0 : wbo.toNat = 0 := by simp [globN, hg] at hbo0; exact hbo0
          have hwbo_eq : wbo = 0#64 := BitVec.eq_of_toNat_eq hwbo0
          subst hwbo_eq
          simp only [hg, valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map,
            Option.map, Bool.and_self, if_true, Option.some.injEq, ValueHOL.val.injEq,
            HolWordLab.word.injEq] at ha
          have ha72 : a.toNat = 72 := by rw [← ha]; decide
          have hsb : sourceBase = 2701131776 := by decide
          omega
  exact localsFree_reqState 0 s _ s.clock ⟨hW, hbo_nz, by omega⟩

theorem resumeOn_init_dep_alloc
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn (ReqState 0)
      (fun s => ∃ w_dep : BitVec 64, ∃ S Nd : List Nat,
        WorldTypedWith s S Nd ∧ ArenaReady s ∧ globN s "bo" ≠ 0 ∧ memW s (globN s "bo" + 64) = 0 ∧
        s.locals.lookup (ofString "dep") = some (.val (.word w_dep)) ∧
        w_dep.toNat % 8 = 0 ∧
        Inside (w_dep.toNat, 8) sourceBase (globN s "heap_ptr") ∧
        IvlsDisj [(w_dep.toNat, 8)] (worldOwned s S Nd))
      (ofString "dep") (ofString "alloc") [.const 8#64] := by
  intro F state values body callee ret value post hcode ⟨hW, hbo_nz, hc0⟩ hargs hl hrun
  obtain ⟨hAs, S, hS⟩ := hW
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with state S).1 hS
  have hpc := callee_param_one_exp state (ofString "alloc") (ofString "n") .one _ _
    (by rw [hcode]; exact lookup_alloc_fn) (.const 8#64) (.val (.word 8#64)) values body callee ret rfl hargs hl
  have hn_loc : locN (callEntryStateHOLFinite state callee) "n" = 8 := by
    simp [locN, callEntryStateHOLFinite, hpc.2]
  have hstep := FunSpec.at_lookup wal state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) ⟨hAs, S, hS⟩) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  obtain ⟨hAp, _, hG, hRK, hWS⟩ := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtal state hcode values body callee ret hl
    (localsFree_arenaReady state callee (state.clock - 1) hAs) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_dep, rfl, _, _, hfb⟩ := hrt value rfl
  rw [hn_loc] at hfb
  obtain ⟨S', Nd', _, hWT', _, _, hQ⟩ :=
    hWS S Nd ((worldTypedWith_with_locals _ _ _ _ _).2 hWT) (fun x hx => by simp at hx)
  obtain ⟨w_dep', hw_eq, hav⟩ := hQ (.val (.word w_dep)) rfl
  injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
  dsimp only at hav
  rw [hn_loc] at hav
  have hbo_eq : globN post "bo" = globN state "bo" := by
    unfold globN; rw [← hG (ofString "bo") (by simp; decide)]; rfl
  have hc64_eq : memW post (globN state "bo" + 64) = memW state (globN state "bo" + 64) :=
    hRK ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) hbo_nz 64 (by simp)
      (fun i hi => by simp at hi)
  set resumed := setVarHOLFinite (ofString "dep") (.val (.word w_dep)) { post with locals := state.locals }
  refine ⟨w_dep, S', Nd', (worldTypedWith_with_locals post _ post.clock S' Nd').2 hWT',
    localsFree_arenaReady post _ post.clock hAp, ?_, ?_, ?_, hfb.1,
    ⟨Nat.le_trans hAs.2.1 hfb.2.1.1, hfb.2.1.2⟩, hav⟩
  · show globN post "bo" ≠ 0; rw [hbo_eq]; exact hbo_nz
  · show memW post (globN post "bo" + 64) = 0; rw [hbo_eq, hc64_eq]; omega
  · simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

def DepReallocMid : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_nd w_dep w_n w_cap : BitVec 64, ∃ S Nd : List Nat,
    WorldTypedWith s S Nd ∧
    ArenaReady s ∧
    globN s "bo" ≠ 0 ∧
    memW s (globN s "bo" + 64) = 0 ∧
    s.locals.lookup (ofString "nd") = some (.val (.word w_nd)) ∧
    s.locals.lookup (ofString "dep") = some (.val (.word w_dep)) ∧
    s.locals.lookup (ofString "dep_n") = some (.val (.word w_n)) ∧
    s.locals.lookup (ofString "dep_cap") = some (.val (.word w_cap)) ∧
    w_n.toNat + 192 ≤ (w_cap * 2#64 + 1024#64).toNat ∧
    w_nd.toNat % 8 = 0 ∧
    w_n.toNat % 8 = 0 ∧
    (w_cap * 2#64 + 1024#64).toNat % 8 = 0 ∧
    Inside (w_nd.toNat, (w_cap * 2#64 + 1024#64).toNat) sourceBase (globN s "heap_ptr") ∧
    IvlsDisj [(w_nd.toNat, (w_cap * 2#64 + 1024#64).toNat)] (worldOwned s S Nd)

theorem depReallocMid_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : DepReallocMid s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, hA, _⟩ := h
  exact hA.1

theorem resumeOn_realloc_dep
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn
      (fun s => DepLoopInv s ∧
        CondTrue (.cmp .lower (.var .local (ofString "dep_cap"))
          (.op .add [.var .local (ofString "dep_n"), .const 192#64])) s)
      DepReallocMid
      (ofString "nd") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "dep_cap"), .const 2#64], .const 1024#64]] := by
  intro F state values body callee ret value post hcode ⟨hInv, _⟩ hargs hl hrun
  have hW_state : WorldOK state := (depLoopInv_reqState0 hInv).1
  obtain ⟨w_dep, w_n, w_cap, S, Nd, hWT, hAs, hbo_nz, hc0, hlu_d, hlu_n, hlu_c, hle_nc, _, hn8, hc8, hin_old, _⟩ := hInv
  have hcap_bound : w_cap.toNat ≤ heapEnd - sourceBase := by
    have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
    have hlim_le : heapLimit ≤ heapEnd := by decide
    unfold Inside at hin_old
    omega
  have hdom_val : heapEnd - sourceBase = 31104957928 := by decide
  have hnew_cap_val : (w_cap * 2#64 + 1024#64).toNat = w_cap.toNat * 2 + 1024 := by
    have h264 : (31104957928 : Nat) * 2 + 1024 < 2 ^ 64 := by decide
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hround_eq : ((w_cap * 2#64 + 1024#64).toNat + 7) / 8 * 8 = (w_cap * 2#64 + 1024#64).toNat := by
    omega
  have harg_ev : evalAt state
      (.op .add [.panop .mul [.var .local (ofString "dep_cap"), .const 2#64], .const 1024#64]) =
      some (.val (.word (w_cap * 2#64 + 1024#64))) := by
    simp only [evalAt, evalHOLExact, evalListHOLExact, hlu_c, valueIsWord, valueWord, panOpHOL,
      wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, if_true, Option.some.injEq]
    simp [BitVec.add_zero]
  have hpc := callee_param_one_exp state (ofString "alloc") (ofString "n") .one _ _
    (by rw [hcode]; exact lookup_alloc_fn) _ (.val (.word (w_cap * 2#64 + 1024#64))) values body callee ret
    harg_ev hargs hl
  have hn_loc : locN (callEntryStateHOLFinite state callee) "n" = (w_cap * 2#64 + 1024#64).toNat := by
    simp [locN, callEntryStateHOLFinite, hpc.2]
  have hstep := FunSpec.at_lookup wal state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  obtain ⟨hAp, _, hG, hRK, hWS⟩ := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtal state hcode values body callee ret hl
    (localsFree_arenaReady state callee (state.clock - 1) hAs) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_nd, rfl, _, _, hfb⟩ := hrt value rfl
  rw [hn_loc] at hfb
  have hfb_in : Inside (w_nd.toNat, (w_cap * 2#64 + 1024#64).toNat)
      (globN (callEntryStateHOLFinite state callee) "heap_ptr") (globN post "heap_ptr") := by
    have := hfb.2.1; rw [hround_eq] at this; exact this
  obtain ⟨S', Nd', _, hWT', _, _, hQ⟩ :=
    hWS S Nd ((worldTypedWith_with_locals _ _ _ _ _).2 hWT) (fun x hx => by simp at hx)
  obtain ⟨w_nd', hw_eq, hav⟩ := hQ (.val (.word w_nd)) rfl
  injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
  dsimp only at hav
  rw [hn_loc, hround_eq] at hav
  have hbo_eq : globN post "bo" = globN state "bo" := by
    unfold globN; rw [← hG (ofString "bo") (by simp; decide)]; rfl
  have hc64_eq : memW post (globN state "bo" + 64) = memW state (globN state "bo" + 64) :=
    hRK ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) hbo_nz 64 (by simp)
      (fun i hi => by simp at hi)
  set resumed := setVarHOLFinite (ofString "nd") (.val (.word w_nd)) { post with locals := state.locals }
  refine ⟨w_nd, w_dep, w_n, w_cap, S', Nd',
    (worldTypedWith_with_locals post _ post.clock S' Nd').2 hWT',
    localsFree_arenaReady post _ post.clock hAp,
    by show globN post "bo" ≠ 0; rw [hbo_eq]; exact hbo_nz,
    by show memW post (globN post "bo" + 64) = 0; rw [hbo_eq, hc64_eq]; omega,
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by have hne : ofString "nd" ≠ ofString "dep" := by decide
       simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_d],
    by have hne : ofString "nd" ≠ ofString "dep_n" := by decide
       simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_n],
    by have hne : ofString "nd" ≠ ofString "dep_cap" := by decide
       simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_c],
    by omega, hfb.1, hn8, by omega,
    ⟨Nat.le_trans hAs.2.1 hfb_in.1, hfb_in.2⟩, hav⟩

def DepWriteReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_dep w_n w_cap : BitVec 64, ∃ S Nd : List Nat,
    WorldTypedWith s S Nd ∧
    ArenaReady s ∧
    globN s "bo" ≠ 0 ∧
    memW s (globN s "bo" + 64) = 0 ∧
    s.locals.lookup (ofString "dep") = some (.val (.word w_dep)) ∧
    s.locals.lookup (ofString "dep_n") = some (.val (.word w_n)) ∧
    s.locals.lookup (ofString "dep_cap") = some (.val (.word w_cap)) ∧
    w_n.toNat + 192 ≤ w_cap.toNat ∧
    w_dep.toNat % 8 = 0 ∧
    w_n.toNat % 8 = 0 ∧
    w_cap.toNat % 8 = 0 ∧
    Inside (w_dep.toNat, w_cap.toNat) sourceBase (globN s "heap_ptr") ∧
    IvlsDisj [(w_dep.toNat, w_cap.toNat)] (worldOwned s S Nd)

theorem depWriteReady_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : DepWriteReady s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, hA, _⟩ := h
  exact hA.1

theorem hoare_memcpy_dep_realloc
    (wmc : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memcpy")) :
    Hoare DepReallocMid
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "nd"), .var .local (ofString "dep"), .var .local (ofString "dep_n")])
        (.seq
          (.assign .local (ofString "dep") (.var .local (ofString "nd")))
          (.assign .local (ofString "dep_cap")
            (.op .add [.panop .mul [.var .local (ofString "dep_cap"), .const 2#64], .const 1024#64]))))
      (fun r t => r = none → DepWriteReady t) := by
  apply Hoare.seq_fall (R := DepReallocMid)
  · refine ⟨fun {F} state hcode hMid _ hr => ?_⟩
    rcases hcall : evaluateHOLFiniteState state
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "nd"), .var .local (ofString "dep"), .var .local (ofString "dep_n")]) with ⟨cres, cpost⟩
    have hr' : cres = none := by rw [hcall] at hr; exact hr
    subst hr'
    obtain ⟨w_nd, w_dep, w_n, w_cap, S, Nd, hWT, hAs, hbo_nz, hc0,
      hlu_nd, hlu_d, hlu_n, hlu_c, hle_192, hnd8, hn8, hncap8, hin_nd, hdisj_nd⟩ := hMid
    rw [evaluateHOLFiniteState_call] at hcall
    have hargs : evalListHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a))
        [.var .local (ofString "nd"), .var .local (ofString "dep"), .var .local (ofString "dep_n")] =
        some [.val (.word w_nd), .val (.word w_dep), .val (.word w_n)] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact, evalHOLExact, hlu_nd, hlu_d, hlu_n]
    rw [hargs] at hcall; dsimp only at hcall
    rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "memcpy")
        [.val (.word w_nd), .val (.word w_dep), .val (.word w_n)] with _ | ⟨body, callee, ret⟩
    · rw [hl] at hcall; simp at hcall
    · rw [hl] at hcall; dsimp only at hcall
      by_cases hz : state.clock = 0
      · rw [if_pos hz] at hcall; simp at hcall
      · rw [if_neg hz] at hcall
        have hp3 := callee_param_three state (ofString "memcpy")
          (ofString "dst") (ofString "src") (ofString "n") .one .one .one _ _
          (by rw [hcode]; exact lookup_memcpy_fn)
          (.var .local (ofString "nd")) (.var .local (ofString "dep")) (.var .local (ofString "dep_n"))
          (.val (.word w_nd)) (.val (.word w_dep)) (.val (.word w_n))
          [.val (.word w_nd), .val (.word w_dep), .val (.word w_n)] body callee ret
          (by simp [evalAt, evalHOLExact, hlu_nd])
          (by simp [evalAt, evalHOLExact, hlu_d])
          (by simp [evalAt, evalHOLExact, hlu_n]) hargs hl
        have hdst : locN (callEntryStateHOLFinite state callee) "dst" = w_nd.toNat := by
          simp [locN, callEntryStateHOLFinite, hp3.1]
        have hn_loc : locN (callEntryStateHOLFinite state callee) "n" = w_n.toNat := by
          simp [locN, callEntryStateHOLFinite, hp3.2.2]
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
        rw [hrun] at hcall
        cases bres with
        | none => simp at hcall
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hcall
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret = true
            · rw [if_pos hsh] at hcall
              obtain ⟨_, rfl⟩ := Prod.mk.inj hcall
              have hW_state : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hWT⟩⟩
              have hstep := FunSpec.at_lookup wmc state hcode _ body callee ret hl
                (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hrun]; simp)
              rw [hrun] at hstep; dsimp only at hstep
              obtain ⟨hAp, hhp, hG, hRK, hWS⟩ := hstep (Or.inl ⟨v, rfl⟩)
              have hin_sub : Inside (w_nd.toNat, w_n.toNat) w_nd.toNat (w_nd.toNat + (w_cap * 2#64 + 1024#64).toNat) :=
                ⟨le_rfl, by omega⟩
              have hdisj_R : IvlsDisj [(w_nd.toNat, w_n.toNat)] (worldTypedIvls state S Nd) := by
                intro x hx j hj
                simp only [List.mem_singleton] at hx; subst hx
                exact disj_of_inside_left (i' := (w_nd.toNat, (w_cap * 2#64 + 1024#64).toNat)) hin_sub
                  (hdisj_nd _ (by simp) j (worldTypedIvls_sub_worldOwned _ _ _ j hj))
              obtain ⟨S', Nd', _, hWT', hog, hfr, _⟩ :=
                hWS S Nd ((worldTypedWith_with_locals _ _ _ _ _).2 hWT)
                  (by dsimp only; rw [hdst, hn_loc]; exact hdisj_R)
              dsimp only at hog hfr
              rw [hdst, hn_loc] at hfr
              -- Show `(w_nd, new_cap)` is still disjoint from `worldOwned post S' Nd'` via `OwnedGrows`
              have hdisj_nd' : IvlsDisj [(w_nd.toNat, (w_cap * 2#64 + 1024#64).toNat)] (worldOwned post S' Nd') := by
                intro x hx o ho
                simp only [List.mem_singleton] at hx; subst hx
                rcases hog o ho with rfl | ⟨j, hj, hin_oj⟩ | hfresh
                · exact disj_zero_right _
                · exact disj_of_inside_right hin_oj (hdisj_nd _ (by simp) j hj)
                · exact Or.inr (Or.inr (Or.inl (Nat.le_trans hin_nd.2 hfresh.1)))
              have hbo_eq : globN post "bo" = globN state "bo" := by
                unfold globN; rw [← hG (ofString "bo") (by simp)]; rfl
              have hbo_rec : (globN state "bo", 88) ∈ worldOwned state S Nd := by
                have hr_in : ("bo", 88) ∈ typedRecords := by decide
                have hfix := typedRecord_mem_fixedObjects state hr_in
                rw [if_neg hbo_nz] at hfix
                unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
              have hbo8 : (globN state "bo") % 8 = 0 := by
                rcases worldOwned_zero_or_allocated hWT _ hbo_rec with h0 | ⟨_, _⟩
                · injection h0 with h0'; exact absurd h0' hbo_nz
                · have hfix := typedRecord_mem_fixedObjects state (show ("bo", 88) ∈ typedRecords by decide)
                  rw [if_neg hbo_nz] at hfix
                  rcases hWT.2.2.1.1 _ hfix with hz | ⟨_, hw⟩
                  · dsimp at hz; omega
                  · exact hw.1
              have hc64_eq : memW post (globN state "bo" + 64) = memW state (globN state "bo" + 64) := by
                apply hRK ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) hbo_nz 64 (by simp)
                intro i hi
                dsimp only at hi ⊢; rw [hdst, hn_loc] at hi
                change ¬ CellHits (globN state "bo" + 64) i
                simp only [List.mem_singleton] at hi; subst hi
                have hd_bo : Disj (w_nd.toNat, w_n.toNat) (globN state "bo", 88) :=
                  disj_of_inside_left (i' := (w_nd.toNat, (w_cap * 2#64 + 1024#64).toNat)) hin_sub
                    (hdisj_nd _ (by simp) _ hbo_rec)
                exact fun hch => not_cellHits_of_disj hnd8 hn8 (by omega) (by omega) hch hd_bo ⟨by omega, by omega⟩
              exact ⟨w_nd, w_dep, w_n, w_cap, S', Nd',
                (worldTypedWith_with_locals post _ post.clock S' Nd').2 hWT',
                localsFree_arenaReady post _ post.clock hAp,
                by show globN post "bo" ≠ 0; rw [hbo_eq]; exact hbo_nz,
                by show memW post (globN post "bo" + 64) = 0; rw [hbo_eq, hc64_eq]; omega,
                hlu_nd, hlu_d, hlu_n, hlu_c, hle_192, hnd8, hn8, hncap8,
                ⟨hin_nd.1, Nat.le_trans hin_nd.2 hhp⟩, hdisj_nd'⟩
            · rw [if_neg hsh] at hcall; simp at hcall
          | _ => simp at hcall
  · apply Hoare.seq_fall (R := fun s => ∃ w_nd w_n w_cap : BitVec 64, ∃ S Nd : List Nat,
        WorldTypedWith s S Nd ∧ ArenaReady s ∧ globN s "bo" ≠ 0 ∧ memW s (globN s "bo" + 64) = 0 ∧
        s.locals.lookup (ofString "dep") = some (.val (.word w_nd)) ∧
        s.locals.lookup (ofString "dep_n") = some (.val (.word w_n)) ∧
        s.locals.lookup (ofString "dep_cap") = some (.val (.word w_cap)) ∧
        w_n.toNat + 192 ≤ (w_cap * 2#64 + 1024#64).toNat ∧
        w_nd.toNat % 8 = 0 ∧ w_n.toNat % 8 = 0 ∧ (w_cap * 2#64 + 1024#64).toNat % 8 = 0 ∧
        Inside (w_nd.toNat, (w_cap * 2#64 + 1024#64).toNat) sourceBase (globN s "heap_ptr") ∧
        IvlsDisj [(w_nd.toNat, (w_cap * 2#64 + 1024#64).toNat)] (worldOwned s S Nd))
    · apply Hoare.assign_fall
      intro F s v hMid hv
      obtain ⟨w_nd, w_dep, w_n, w_cap, S, Nd, hWT, hAs, hbo_nz, hc0,
        hlu_nd, _, hlu_n, hlu_c, hle_192, hnd8, hn8, hncap8, hin_nd, hdisj_nd⟩ := hMid
      simp only [evalAt, evalHOLExact, hlu_nd, Option.some.injEq] at hv
      subst hv
      refine ⟨w_nd, w_n, w_cap, S, Nd,
        (worldTypedWith_with_locals s _ s.clock S Nd).2 hWT,
        localsFree_arenaReady s _ s.clock hAs, hbo_nz, hc0,
        by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
        by have hne : ofString "dep" ≠ ofString "dep_n" := by decide
           simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_n],
        by have hne : ofString "dep" ≠ ofString "dep_cap" := by decide
           simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_c],
        hle_192, hnd8, hn8, hncap8, hin_nd, hdisj_nd⟩
    · apply Hoare.assign_fall
      intro F s v hMid hv
      obtain ⟨w_nd, w_n, w_cap, S, Nd, hWT, hAs, hbo_nz, hc0,
        hlu_d, hlu_n, hlu_c, hle_192, hnd8, hn8, hncap8, hin_nd, hdisj_nd⟩ := hMid
      have hv_eq : v = .val (.word (w_cap * 2#64 + 1024#64)) := by
        simp only [evalAt, evalHOLExact, evalListHOLExact, hlu_c, valueIsWord, valueWord, panOpHOL,
          wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, if_true, Option.some.injEq] at hv
        rw [← hv]; simp [BitVec.add_zero]
      subst hv_eq
      refine ⟨w_nd, w_n, w_cap * 2#64 + 1024#64, S, Nd,
        (worldTypedWith_with_locals s _ s.clock S Nd).2 hWT,
        localsFree_arenaReady s _ s.clock hAs, hbo_nz, hc0,
        by have hne : ofString "dep_cap" ≠ ofString "dep" := by decide
           simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_d],
        by have hne : ofString "dep_cap" ≠ ofString "dep_n" := by decide
           simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_n],
        by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
        hle_192, hnd8, hn8, hncap8, hin_nd, hdisj_nd⟩

theorem hoare_skip_depWriteReady :
    Hoare
      (fun s => DepLoopInv s ∧
        CondFalse (.cmp .lower (.var .local (ofString "dep_cap"))
          (.op .add [.var .local (ofString "dep_n"), .const 192#64])) s)
      .skip
      (fun r t => r = none → DepWriteReady t) := by
  apply Hoare.skip
  intro F s ⟨hInv, hcf⟩ _
  obtain ⟨w_dep, w_n, w_cap, S, Nd, hWT, hAs, hbo_nz, hc0, hlu_d, hlu_n, hlu_c, hle_nc, hd8, hn8, hc8, hin, hdisj⟩ := hInv
  have hge_192 : w_n.toNat + 192 ≤ w_cap.toNat := by
    have hcap_bound : w_cap.toNat ≤ heapEnd - sourceBase := by
      have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
      have hlim_le : heapLimit ≤ heapEnd := by decide
      unfold Inside at hin; omega
    have hdom_val : heapEnd - sourceBase = 31104957928 := by decide
    have h264 : (31104957928 : Nat) + 192 < 2 ^ 64 := by decide
    have hadd_nat : (w_n + 192#64).toNat = w_n.toNat + 192 := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    unfold CondFalse at hcf
    simp only [evalHOLExact, evalListHOLExact, hlu_c, hlu_n, valueIsWord, valueWord, wordOpHOL,
      wordOp, List.all, List.map, Option.map, Bool.and_self, if_true, Option.some.injEq,
      ValueHOL.val.injEq, HolWordLab.word.injEq] at hcf
    have hfold_eq : List.foldr (fun left right : BitVec 64 => left + right) 0 [w_n, 192#64] = w_n + 192#64 := by
      simp [BitVec.add_zero]
    rw [hfold_eq] at hcf
    have hnlt : ¬ (w_cap < w_n + 192#64) := by
      intro hlt
      simp [wordCmpHOL, hlt] at hcf
    rw [BitVec.lt_def, hadd_nat] at hnlt
    omega
  exact ⟨w_dep, w_n, w_cap, S, Nd, hWT, hAs, hbo_nz, hc0, hlu_d, hlu_n, hlu_c, hge_192, hd8, hn8, hc8, hin, hdisj⟩

theorem hoare_extract_deposit_step
    (wed : WorldKeeps WorldOK (fun s => [(locN s "out", 192)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "extract_deposit_data"))
    (e1 e2 : ExpHOL 64) :
    Hoare DepWriteReady
      (.seq
        (.call (some (none, none)) (ofString "extract_deposit_data")
          [e1, e2, .op .add [.var .local (ofString "dep"), .var .local (ofString "dep_n")]])
        (.assign .local (ofString "dep_n") (.op .add [.var .local (ofString "dep_n"), .const 192#64])))
      (fun r t => r = none → DepLoopInv t) := by
  apply Hoare.seq_fall (R := DepWriteReady)
  · refine ⟨fun {F} state hcode hWR _ hr => ?_⟩
    rcases hcall : evaluateHOLFiniteState state
        (.call (some (none, none)) (ofString "extract_deposit_data")
          [e1, e2, .op .add [.var .local (ofString "dep"), .var .local (ofString "dep_n")]]) with ⟨cres, cpost⟩
    have hr' : cres = none := by rw [hcall] at hr; exact hr
    subst hr'
    obtain ⟨w_dep, w_n, w_cap, S, Nd, hWT, hAs, hbo_nz, hc0,
      hlu_d, hlu_n, hlu_c, hge_192, hd8, hn8, hc8, hin_dep, hdisj_dep⟩ := hWR
    have h264 : heapEnd < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
    have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
    have hout_nat : (w_dep + w_n).toNat = w_dep.toNat + w_n.toNat := by
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt (by unfold Inside at hin_dep; omega)
    have he3 : evalAt state (.op .add [.var .local (ofString "dep"), .var .local (ofString "dep_n")]) =
        some (.val (.word (w_dep + w_n))) := by
      simp only [evalAt, evalHOLExact, evalListHOLExact, hlu_d, hlu_n, valueIsWord, valueWord,
        wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, if_true, Option.some.injEq]
      simp [BitVec.add_zero]
    rw [evaluateHOLFiniteState_call] at hcall
    rcases hargs : evalListHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a))
        [e1, e2, .op .add [.var .local (ofString "dep"), .var .local (ofString "dep_n")]] with _ | values
    · rw [hargs] at hcall; simp at hcall
    · rw [hargs] at hcall; dsimp only at hcall
      have hargs_ex := hargs
      rw [evalListHOLFinite_eq_toExact] at hargs_ex
      rcases he1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
      · simp [evalListHOLExact, he1] at hargs_ex
      · rcases he2 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e2 with _ | v2
        · simp [evalListHOLExact, he1, he2] at hargs_ex
        · rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "extract_deposit_data") values with _ | ⟨body, callee, ret⟩
          · rw [hl] at hcall; simp at hcall
          · rw [hl] at hcall; dsimp only at hcall
            by_cases hz : state.clock = 0
            · rw [if_pos hz] at hcall; simp at hcall
            · rw [if_neg hz] at hcall
              have hp3 := callee_param_three state (ofString "extract_deposit_data")
                (ofString "data") (ofString "n") (ofString "out") .one .one .one _ _
                (by rw [hcode]; exact lookup_extract_deposit_data_fn)
                e1 e2 (.op .add [.var .local (ofString "dep"), .var .local (ofString "dep_n")])
                v1 v2 (.val (.word (w_dep + w_n))) values body callee ret he1 he2 he3 hargs hl
              have hout_loc : locN (callEntryStateHOLFinite state callee) "out" = w_dep.toNat + w_n.toNat := by
                simp [locN, callEntryStateHOLFinite, hp3.2.2, hout_nat]
              rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
              rw [hrun] at hcall
              cases bres with
              | none => simp at hcall
              | some br =>
                cases br with
                | returned v =>
                  dsimp only at hcall
                  by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret = true
                  · rw [if_pos hsh] at hcall
                    obtain ⟨_, rfl⟩ := Prod.mk.inj hcall
                    have hW_state : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hWT⟩⟩
                    have hstep := FunSpec.at_lookup wed state hcode _ body callee ret hl
                      (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hrun]; simp)
                    rw [hrun] at hstep; dsimp only at hstep
                    obtain ⟨hAp, hhp, hG, hRK, hWS⟩ := hstep (Or.inl ⟨v, rfl⟩)
                    have hin_sub : Inside (w_dep.toNat + w_n.toNat, 192) w_dep.toNat (w_dep.toNat + w_cap.toNat) :=
                      ⟨by omega, by omega⟩
                    have hdisj_R : IvlsDisj [(w_dep.toNat + w_n.toNat, 192)] (worldTypedIvls state S Nd) := by
                      intro x hx j hj
                      simp only [List.mem_singleton] at hx; subst hx
                      exact disj_of_inside_left (i' := (w_dep.toNat, w_cap.toNat)) hin_sub
                        (hdisj_dep _ (by simp) j (worldTypedIvls_sub_worldOwned _ _ _ j hj))
                    obtain ⟨S', Nd', _, hWT', hog, _, _⟩ :=
                      hWS S Nd ((worldTypedWith_with_locals _ _ _ _ _).2 hWT)
                        (by dsimp only; rw [hout_loc]; exact hdisj_R)
                    have hdisj_dep' : IvlsDisj [(w_dep.toNat, w_cap.toNat)] (worldOwned post S' Nd') := by
                      intro x hx o ho
                      simp only [List.mem_singleton] at hx; subst hx
                      rcases hog o ho with rfl | ⟨j, hj, hin_oj⟩ | hfresh
                      · exact disj_zero_right _
                      · exact disj_of_inside_right hin_oj (hdisj_dep _ (by simp) j hj)
                      · exact Or.inr (Or.inr (Or.inl (Nat.le_trans hin_dep.2 hfresh.1)))
                    have hbo_eq : globN post "bo" = globN state "bo" := by
                      unfold globN; rw [← hG (ofString "bo") (by simp; decide)]; rfl
                    have hbo_rec : (globN state "bo", 88) ∈ worldOwned state S Nd := by
                      have hfix := typedRecord_mem_fixedObjects state (show ("bo", 88) ∈ typedRecords by decide)
                      rw [if_neg hbo_nz] at hfix
                      unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
                    have hbo8 : (globN state "bo") % 8 = 0 := by
                      have hfix := typedRecord_mem_fixedObjects state (show ("bo", 88) ∈ typedRecords by decide)
                      rw [if_neg hbo_nz] at hfix
                      rcases hWT.2.2.1.1 _ hfix with hz | ⟨_, hw⟩
                      · dsimp at hz; omega
                      · exact hw.1
                    have hc64_eq : memW post (globN state "bo" + 64) = memW state (globN state "bo" + 64) := by
                      apply hRK ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) hbo_nz 64 (by simp)
                      intro i hi
                      dsimp only at hi ⊢; rw [hout_loc] at hi
                      change ¬ CellHits (globN state "bo" + 64) i
                      simp only [List.mem_singleton] at hi; subst hi
                      have hd_bo : Disj (w_dep.toNat + w_n.toNat, 192) (globN state "bo", 88) :=
                        disj_of_inside_left (i' := (w_dep.toNat, w_cap.toNat)) hin_sub
                          (hdisj_dep _ (by simp) _ hbo_rec)
                      exact fun hch => not_cellHits_of_disj (by omega) (by omega) (by omega) (by omega) hch hd_bo ⟨by omega, by omega⟩
                    exact ⟨w_dep, w_n, w_cap, S', Nd',
                      (worldTypedWith_with_locals post _ post.clock S' Nd').2 hWT',
                      localsFree_arenaReady post _ post.clock hAp,
                      by show globN post "bo" ≠ 0; rw [hbo_eq]; exact hbo_nz,
                      by show memW post (globN post "bo" + 64) = 0; rw [hbo_eq, hc64_eq]; omega,
                      hlu_d, hlu_n, hlu_c, hge_192, hd8, hn8, hc8,
                      ⟨hin_dep.1, Nat.le_trans hin_dep.2 hhp⟩, hdisj_dep'⟩
                  · rw [if_neg hsh] at hcall; simp at hcall
                | _ => simp at hcall
  · apply Hoare.assign_fall
    intro F s v hWR hv
    obtain ⟨w_dep, w_n, w_cap, S, Nd, hWT, hAs, hbo_nz, hc0,
      hlu_d, hlu_n, hlu_c, hge_192, hd8, hn8, hc8, hin_dep, hdisj_dep⟩ := hWR
    have h264 : heapEnd < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
    have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
    have hv_eq : v = .val (.word (w_n + 192#64)) := by
      simp only [evalAt, evalHOLExact, evalListHOLExact, hlu_n, valueIsWord, valueWord,
        wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, if_true, Option.some.injEq] at hv
      rw [← hv]; simp [BitVec.add_zero]
    subst hv_eq
    have hn_new_nat : (w_n + 192#64).toNat = w_n.toNat + 192 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by unfold Inside at hin_dep; omega)
    refine ⟨w_dep, w_n + 192#64, w_cap, S, Nd,
      (worldTypedWith_with_locals s _ s.clock S Nd).2 hWT,
      localsFree_arenaReady s _ s.clock hAs, hbo_nz, hc0,
      by have hne : ofString "dep_n" ≠ ofString "dep" := by decide
         simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_d],
      by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
      by have hne : ofString "dep_n" ≠ ofString "dep_cap" := by decide
         simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_c],
      by omega, hd8, by omega, hc8, hin_dep, hdisj_dep⟩

theorem resumeOn_memeq_depLoopInv
    (rmq : ReadOnlyFn (ofString "memeq")) (name : MlS)
    (hname : ∀ n ∈ ["dep", "dep_n", "dep_cap"], ofString n ≠ name)
    (args : List (ExpHOL 64)) :
    DecCallResumeOn DepLoopInv DepLoopInv name (ofString "memeq") args := by
  intro F state values body callee ret value post hcode hInv _ hl hrun
  have hro := FunSpec.at_lookup rmq state hcode values body callee ret hl
    (localsFree_guestInv state callee (state.clock - 1) (depLoopInv_guestInv hInv))
    (by rw [hrun]; simp)
  rw [hrun] at hro; dsimp only at hro
  have heq := hro (Or.inl ⟨value, rfl⟩)
  have hpost_eq : { post with locals := state.locals } = { state with clock := post.clock } := by
    rw [heq]; rfl
  rw [hpost_eq]
  exact localsOnly_depLoopInv.setVar hname value _
    (localsOnly_depLoopInv state state.locals post.clock (fun _ _ => rfl) hInv)

theorem hoare_dep_inner_after_isdep
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (wed : WorldKeeps WorldOK (fun s => [(locN s "out", 192)]) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "extract_deposit_data"))
    (wmc : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memcpy"))
    (rmq : ReadOnlyFn (ofString "memeq")) :
    Hoare DepLoopInv
      (.ite (.cmp .notEqual (.var .local (ofString "isdep")) (.const 0#64))
        (.ite (.cmp .lower (.const 0#64) (.load .one (.op .add [.var .local (ofString "log"), .const 16#64])))
          (.decCall (ofString "sig") .one (ofString "memeq")
            [.load .one (.op .add [.var .local (ofString "log"), .const 8#64]),
             .var .global (ofString "deposit_event_signature_hash"), .const 32#64]
            (.ite (.cmp .notEqual (.var .local (ofString "sig")) (.const 0#64))
              (.seq
                (.ite (.cmp .lower (.var .local (ofString "dep_cap"))
                  (.op .add [.var .local (ofString "dep_n"), .const 192#64]))
                  (.decCall (ofString "nd") .one (ofString "alloc")
                    [.op .add [.panop .mul [.var .local (ofString "dep_cap"), .const 2#64], .const 1024#64]]
                    (.seq
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "nd"), .var .local (ofString "dep"), .var .local (ofString "dep_n")])
                      (.seq
                        (.assign .local (ofString "dep") (.var .local (ofString "nd")))
                        (.assign .local (ofString "dep_cap")
                          (.op .add [.panop .mul [.var .local (ofString "dep_cap"), .const 2#64], .const 1024#64])))))
                  .skip)
                (.seq
                  (.call (some (none, none)) (ofString "extract_deposit_data")
                    [.load .one (.op .add [.var .local (ofString "log"), .const 24#64]),
                     .load .one (.op .add [.var .local (ofString "log"), .const 32#64]),
                     .op .add [.var .local (ofString "dep"), .var .local (ofString "dep_n")]])
                  (.assign .local (ofString "dep_n") (.op .add [.var .local (ofString "dep_n"), .const 192#64]))))
              .skip))
          .skip)
        .skip)
      (fun r t => r = none → DepLoopInv t) := by
  apply Hoare.ite_fall
  · apply Hoare.mono _ (fun _ h => h.1)
    apply Hoare.ite_fall
    · apply Hoare.mono _ (fun _ h => h.1)
      apply Hoare.decCall_fall (by simp; decide) localsOnly_depLoopInv
        (resumeOn_memeq_depLoopInv rmq (ofString "sig") (by simp; decide) _)
      apply Hoare.ite_fall
      · apply Hoare.mono _ (fun _ h => h.1)
        apply Hoare.seq_fall (R := DepWriteReady)
        · apply Hoare.ite_fall
          · exact Hoare.decCall_fall
              (names := ["dep", "dep_n", "dep_cap"]) (by simp; decide)
              (by
                intro F s locals k hl hWR
                obtain ⟨w_d, w_n, w_c, S, Nd, hWT, hA, hbo, hc0, hld, hln, hlc, hge, hd8, hn8, hc8, hin, hdj⟩ := hWR
                exact ⟨w_d, w_n, w_c, S, Nd,
                  (worldTypedWith_with_locals s locals k S Nd).2 hWT,
                  localsFree_arenaReady s locals k hA, hbo, hc0,
                  (hl "dep" (by simp)).trans hld,
                  (hl "dep_n" (by simp)).trans hln,
                  (hl "dep_cap" (by simp)).trans hlc,
                  hge, hd8, hn8, hc8, hin, hdj⟩)
              (resumeOn_realloc_dep wal rtal)
              (hoare_memcpy_dep_realloc wmc)
          · exact hoare_skip_depWriteReady
        · exact hoare_extract_deposit_step wed _ _
      · exact Hoare.skip fun _ h _ => h.1
    · exact Hoare.skip fun _ h _ => h.1
  · exact Hoare.skip fun _ h _ => h.1

theorem bounded_dep_inner_after_isdep
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hed : TerminatingFunBoundedOn GuestInv (ofString "extract_deposit_data") K.«extract_deposit_data»)
    (hmc : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (hmq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (wmc : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memcpy"))
    (rmq : ReadOnlyFn (ofString "memeq")) :
    TerminatingProgBoundedOn DepLoopInv
      (.ite (.cmp .notEqual (.var .local (ofString "isdep")) (.const 0#64))
        (.ite (.cmp .lower (.const 0#64) (.load .one (.op .add [.var .local (ofString "log"), .const 16#64])))
          (.decCall (ofString "sig") .one (ofString "memeq")
            [.load .one (.op .add [.var .local (ofString "log"), .const 8#64]),
             .var .global (ofString "deposit_event_signature_hash"), .const 32#64]
            (.ite (.cmp .notEqual (.var .local (ofString "sig")) (.const 0#64))
              (.seq
                (.ite (.cmp .lower (.var .local (ofString "dep_cap"))
                  (.op .add [.var .local (ofString "dep_n"), .const 192#64]))
                  (.decCall (ofString "nd") .one (ofString "alloc")
                    [.op .add [.panop .mul [.var .local (ofString "dep_cap"), .const 2#64], .const 1024#64]]
                    (.seq
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "nd"), .var .local (ofString "dep"), .var .local (ofString "dep_n")])
                      (.seq
                        (.assign .local (ofString "dep") (.var .local (ofString "nd")))
                        (.assign .local (ofString "dep_cap")
                          (.op .add [.panop .mul [.var .local (ofString "dep_cap"), .const 2#64], .const 1024#64])))))
                  .skip)
                (.seq
                  (.call (some (none, none)) (ofString "extract_deposit_data")
                    [.load .one (.op .add [.var .local (ofString "log"), .const 24#64]),
                     .load .one (.op .add [.var .local (ofString "log"), .const 32#64]),
                     .op .add [.var .local (ofString "dep"), .var .local (ofString "dep_n")]])
                  (.assign .local (ofString "dep_n") (.op .add [.var .local (ofString "dep_n"), .const 192#64]))))
              .skip))
          .skip)
        .skip)
      (Nat.max (Nat.max ((K.«memeq» + 1) + Nat.max (Nat.max ((K.«alloc» + 1) + (K.«memcpy» + 1)) 0 + (K.«extract_deposit_data» + 1)) 0) 0) 0) := by
  intro F state hcode hInv
  exact TerminatingRunBounded.weaken
    ((TerminatingProgBoundedOn.ite_on
      (TerminatingProgBoundedOn.ite_on
        (TerminatingProgBoundedOn.decCall_on hmq _ _ _
          (callEntryOn_of_imp localsFree_guestInv (fun _ h => depLoopInv_guestInv h) _ _)
          (resumeOn_memeq_depLoopInv rmq (ofString "sig") (by simp; decide) _)
          (TerminatingProgBoundedOn.ite_on
            (TerminatingProgBoundedOn.seq_hoare_trans
              (TerminatingProgBoundedOn.ite_cond_on
                (TerminatingProgBoundedOn.decCall_on hal _ _ _
                  (callEntryOn_of_imp (P := fun s => DepLoopInv s ∧
                    CondTrue (.cmp .lower (.var .local (ofString "dep_cap"))
                      (.op .add [.var .local (ofString "dep_n"), .const 192#64])) s)
                    localsFree_guestInv (fun _ h => depLoopInv_guestInv h.1) _ _)
                  (resumeOn_realloc_dep wal rtal)
                  (TerminatingProgBoundedOn.seq_guestInv_after
                    (TerminatingProgBoundedOn.call_on hmc _ _
                      (callEntryOn_of_imp localsFree_guestInv (fun _ h => depReallocMid_guestInv h) _ _))
                    (fun _ h => depReallocMid_guestInv h)
                    (TerminatingProgBoundedOn.seq_guestInv
                      (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                      (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _)))))
                (TerminatingProgBoundedOn.of_clock (P := fun s => DepLoopInv s ∧
                  CondFalse (.cmp .lower (.var .local (ofString "dep_cap"))
                    (.op .add [.var .local (ofString "dep_n"), .const 192#64])) s)
                  (fun s => clock_skip s)))
              (Hoare.ite_fall
                (Hoare.decCall_fall
                  (names := ["dep", "dep_n", "dep_cap"]) (by simp; decide)
                  (by
                    intro F2 s2 locals2 k2 hl2 hWR2
                    obtain ⟨w_d, w_n, w_c, S, Nd, hWT, hA, hbo, hc0, hld, hln, hlc, hge, hd8, hn8, hc8, hin, hdj⟩ := hWR2
                    exact ⟨w_d, w_n, w_c, S, Nd,
                      (worldTypedWith_with_locals s2 locals2 k2 S Nd).2 hWT,
                      localsFree_arenaReady s2 locals2 k2 hA, hbo, hc0,
                      (hl2 "dep" (by simp)).trans hld,
                      (hl2 "dep_n" (by simp)).trans hln,
                      (hl2 "dep_cap" (by simp)).trans hlc,
                      hge, hd8, hn8, hc8, hin, hdj⟩)
                  (resumeOn_realloc_dep wal rtal)
                  (hoare_memcpy_dep_realloc wmc))
                hoare_skip_depWriteReady)
              (TerminatingProgBoundedOn.seq_guestInv_after
                (TerminatingProgBoundedOn.call_on hed _ _
                  (callEntryOn_of_imp localsFree_guestInv (fun _ h => depWriteReady_guestInv h) _ _))
                (fun _ h => depWriteReady_guestInv h)
                (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))))
            (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s))))
        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
      (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s))) state hcode hInv)
    (by simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]; omega)

theorem walk_loop_general {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {baseName idxName elemName : String}
    {tail : ProgHOL 64} {B : Nat}
    (hP : LocalsOnly names P)
    (hP_guest : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (helem_not_names : ∀ n ∈ names, ofString n ≠ ofString elemName)
    (helem_ne_base : ofString elemName ≠ ofString baseName)
    (helem_ne_idx : ofString elemName ≠ ofString idxName)
    (htail_step : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (wb wi : BitVec 64),
      s.code = originalRuntimeCode → P s →
      s.locals.lookup (ofString baseName) = some (.val (.word wb)) →
      s.locals.lookup (ofString idxName) = some (.val (.word wi)) →
      ((evaluateHOLFiniteState s tail).1 = none ∨
       (evaluateHOLFiniteState s tail).1 = some .continue ∨
       (evaluateHOLFiniteState s tail).1 = some .break) →
      P (evaluateHOLFiniteState s tail).2 ∧
      (evaluateHOLFiniteState s tail).2.locals.lookup (ofString baseName) = some (.val (.word wb)) ∧
      (evaluateHOLFiniteState s tail).2.locals.lookup (ofString idxName) = some (.val (.word (wi + 1#64))))
    (htail_bound : TerminatingProgBoundedOn P tail B) :
    ∀ (limitName : String),
      Hoare P
        (.while (.cmp .less (.var .local (ofString idxName)) (.var .local (ofString limitName)))
          (.dec (ofString elemName) .one
            (.load .one (.op .add [.var .local (ofString baseName),
              .panop .mul [.var .local (ofString idxName), .const 8#64]]))
            tail))
        (fun r t => r = none → P t) ∧
      TerminatingProgBoundedOn P
        (.while (.cmp .less (.var .local (ofString idxName)) (.var .local (ofString limitName)))
          (.dec (ofString elemName) .one
            (.load .one (.op .add [.var .local (ofString baseName),
              .panop .mul [.var .local (ofString idxName), .const 8#64]]))
            tail))
        ((31104957944 + 1) * (B + 1)) := by
  intro limitName
  set body := ProgHOL.dec (ofString elemName) .one
    (.load .one (.op .add [.var .local (ofString baseName),
      .panop .mul [.var .local (ofString idxName), .const 8#64]]))
    tail
  have hstep_common : ∀ {F : Type} (st : PanSemStateFiniteExact 64 F),
      st.code = originalRuntimeCode → P st →
      ((evaluateHOLFiniteState st body).1 = none ∨
       (evaluateHOLFiniteState st body).1 = some .continue ∨
       (evaluateHOLFiniteState st body).1 = some .break) →
      P (evaluateHOLFiniteState st body).2 ∧
      walkRank baseName idxName (evaluateHOLFiniteState st body).2 < walkRank baseName idxName st := by
    intro F st hcode hPst hflow
    set out := evaluateHOLFiniteState st body with hrun_def
    have hrun : evaluateHOLFiniteState st body = (out.1, out.2) := by simp [hrun_def]
    rcases out with ⟨res, post⟩
    dsimp only at hflow hrun ⊢
    have hfl : Flowing res := by
      rcases hflow with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    have hrun_dec := hrun
    rw [evaluateHOLFiniteState_dec_total] at hrun_dec
    dsimp only at hrun_dec
    rcases he : @evalHOLExact 64 F _ st.toExact
        (fun a => Classical.propDecidable (st.memaddrs a))
        (.load .one (.op .add [.var .local (ofString baseName),
          .panop .mul [.var .local (ofString idxName), .const 8#64]])) with _ | val
    · rw [he] at hrun_dec; simp at hrun_dec; obtain ⟨rfl, _⟩ := hrun_dec; rcases hfl with h | h | h <;> simp at h
    · rw [he] at hrun_dec; dsimp only at hrun_dec
      by_cases hsh : shapeEqHOL .one (shapeOfHOLExact val) = true
      · rw [if_pos hsh] at hrun_dec
        obtain ⟨a, _, ha, _, _, hlo, hhi⟩ := evalAt_load_one_ordinary (hP_guest st hPst) he
        obtain ⟨wb, wi, hb_st, hi_st, ha_eq⟩ := evalAt_add_panMul8 ha
        injection ha_eq with ha_eq'; injection ha_eq' with ha_eq''; subst ha_eq''
        set s1 := setVarHOLFinite (ofString elemName) val st
        have hPs1 : P s1 := hP.setVar helem_not_names val st hPst
        have hb_s1 : s1.locals.lookup (ofString baseName) = some (.val (.word wb)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, helem_ne_base, hb_st]
        have hi_s1 : s1.locals.lookup (ofString idxName) = some (.val (.word wi)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, helem_ne_idx, hi_st]
        obtain ⟨hres_eq, hpost_eq⟩ := Prod.mk.inj hrun_dec
        have htail_fl : (evaluateHOLFiniteState s1 tail).1 = none ∨
            (evaluateHOLFiniteState s1 tail).1 = some .continue ∨
            (evaluateHOLFiniteState s1 tail).1 = some .break := by
          rw [hres_eq]; exact hflow
        obtain ⟨hP_t, hb_t, hi_t⟩ := htail_step s1 wb wi hcode hPs1 hb_s1 hi_s1 htail_fl
        rw [← hpost_eq]
        refine ⟨?_, ?_⟩
        · exact hP (evaluateHOLFiniteState s1 tail).2
            (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 tail).2.locals
              (ofString elemName, st.locals.lookup (ofString elemName)))
            (evaluateHOLFiniteState s1 tail).2.clock
            (fun n hn => resVarEq_lookup_ne _ _ _ _ (helem_not_names n hn)) hP_t
        · apply walkRank_step_lt hb_st hi_st
          · rw [PanRunBounded.resVarEq_lookup, if_neg helem_ne_base.symm]; exact hb_t
          · rw [PanRunBounded.resVarEq_lookup, if_neg helem_ne_idx.symm]; exact hi_t
          · exact hlo
          · exact hhi
      · rw [if_neg hsh] at hrun_dec; simp at hrun_dec; obtain ⟨rfl, _⟩ := hrun_dec; rcases hfl with h | h | h <;> simp at h
  refine ⟨?_, ?_⟩
  · exact Hoare.while_preserve hP.decClock
      ⟨fun st hcode ⟨hPst, _⟩ _ hfl => (hstep_common st hcode hPst hfl).1⟩
  · exact TerminatingProgBoundedOn.mono_bound
      (TerminatingProgBoundedOn.while_rank (walkRank baseName idxName)
        hP.decClock
        (TerminatingProgBoundedOn.dec_onLocals hP (ofString elemName) helem_not_names _ _ htail_bound)
        (fun s _ _ _ => walkRank_le baseName idxName s)
        (fun s hcode hPs _ hfl =>
          hstep_common (decClockHOLFinite s) hcode (hP.decClock s hPs)
            (hfl.elim Or.inl (fun h => Or.inr (Or.inl h)))))
      (by omega)

theorem walk_seq_inc_step {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {baseName idxName : String} {mid : ProgHOL 64}
    (hP : LocalsOnly names P)
    (hidx_not_names : ∀ n ∈ names, ofString n ≠ ofString idxName)
    (hidx_ne_base : ofString idxName ≠ ofString baseName)
    (hav_base : avoidsLocal (ofString baseName) mid = true)
    (hav_idx : avoidsLocal (ofString idxName) mid = true)
    (hmid_no_cont : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s mid).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s mid).1 ≠ some .break)
    (hmid_hoare : Hoare P mid (fun r t => r = none → P t)) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (wb wi : BitVec 64),
      s.code = originalRuntimeCode → P s →
      s.locals.lookup (ofString baseName) = some (.val (.word wb)) →
      s.locals.lookup (ofString idxName) = some (.val (.word wi)) →
      ((evaluateHOLFiniteState s (.seq mid (.assign .local (ofString idxName)
        (.op .add [.var .local (ofString idxName), .const 1#64])))).1 = none ∨
       (evaluateHOLFiniteState s (.seq mid (.assign .local (ofString idxName)
        (.op .add [.var .local (ofString idxName), .const 1#64])))).1 = some .continue ∨
       (evaluateHOLFiniteState s (.seq mid (.assign .local (ofString idxName)
        (.op .add [.var .local (ofString idxName), .const 1#64])))).1 = some .break) →
      P (evaluateHOLFiniteState s (.seq mid (.assign .local (ofString idxName)
        (.op .add [.var .local (ofString idxName), .const 1#64])))).2 ∧
      (evaluateHOLFiniteState s (.seq mid (.assign .local (ofString idxName)
        (.op .add [.var .local (ofString idxName), .const 1#64])))).2.locals.lookup (ofString baseName) =
          some (.val (.word wb)) ∧
      (evaluateHOLFiniteState s (.seq mid (.assign .local (ofString idxName)
        (.op .add [.var .local (ofString idxName), .const 1#64])))).2.locals.lookup (ofString idxName) =
          some (.val (.word (wi + 1#64))) := by
  intro F s wb wi hcode hPs hb_s hi_s hflow
  set out := evaluateHOLFiniteState s (.seq mid (.assign .local (ofString idxName)
    (.op .add [.var .local (ofString idxName), .const 1#64]))) with hout
  have hrun : evaluateHOLFiniteState s (.seq mid (.assign .local (ofString idxName)
    (.op .add [.var .local (ofString idxName), .const 1#64]))) = (out.1, out.2) := by simp [hout]
  rcases out with ⟨res, post⟩
  dsimp only at hflow hrun ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hrun
  rcases hm_run : evaluateHOLFiniteState s mid with ⟨mres, s2⟩
  rw [hm_run] at hrun
  cases mres with
  | some mr =>
    dsimp only at hrun
    obtain ⟨rfl, _⟩ := Prod.mk.inj hrun
    rcases hflow with h | h | h
    · simp at h
    · exact absurd (by rw [hm_run]; exact h) (hmid_no_cont s).1
    · exact absurd (by rw [hm_run]; exact h) (hmid_no_cont s).2
  | none =>
    dsimp only at hrun
    have hPs2 : P s2 := by
      have hh := hmid_hoare.run s hcode hPs (by rw [hm_run]; simp)
      rw [hm_run] at hh; exact hh rfl
    have hb_s2 : s2.locals.lookup (ofString baseName) = some (.val (.word wb)) := by
      have hav := evaluate_avoidsLocal_flowing (ofString baseName) mid hav_base s
        (by rw [hm_run]; exact Or.inl rfl)
      rw [hm_run] at hav; exact hav.trans hb_s
    have hi_s2 : s2.locals.lookup (ofString idxName) = some (.val (.word wi)) := by
      have hav := evaluate_avoidsLocal_flowing (ofString idxName) mid hav_idx s
        (by rw [hm_run]; exact Or.inl rfl)
      rw [hm_run] at hav; exact hav.trans hi_s
    rw [evaluateHOLFiniteState_assign] at hrun
    have hass_ev : @evalHOLExact 64 F _ s2.toExact
        (fun a => Classical.propDecidable (s2.memaddrs a))
        (.op .add [.var .local (ofString idxName), .const 1#64]) =
        some (.val (.word (wi + 1#64))) := by
      simp only [evalHOLExact, evalListHOLExact, hi_s2, valueIsWord, valueWord, wordOpHOL,
        wordOp, List.all, List.map, Option.map, Bool.and_self, if_true, Option.some.injEq]
      simp [BitVec.add_zero]
    rw [hass_ev] at hrun; dsimp only at hrun
    have hvalid : isValidValueHOLFinite s2 .local (ofString idxName) (.val (.word (wi + 1#64))) = true := by
      simp [isValidValueHOLFinite, lookupKvarHOLFinite, hi_s2, shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hvalid] at hrun
    obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hrun
    rw [← hpost_eq]
    exact ⟨hP.setVar hidx_not_names _ s2 hPs2,
      by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hidx_ne_base, hb_s2],
      by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩

theorem walk_dec_step {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {baseName idxName : String}
    {name : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {cont : ProgHOL 64}
    (hP : LocalsOnly names P)
    (hname_not_names : ∀ n ∈ names, ofString n ≠ name)
    (hname_ne_base : name ≠ ofString baseName)
    (hname_ne_idx : name ≠ ofString idxName)
    (hcont : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (wb wi : BitVec 64),
      s.code = originalRuntimeCode → P s →
      s.locals.lookup (ofString baseName) = some (.val (.word wb)) →
      s.locals.lookup (ofString idxName) = some (.val (.word wi)) →
      ((evaluateHOLFiniteState s cont).1 = none ∨
       (evaluateHOLFiniteState s cont).1 = some .continue ∨
       (evaluateHOLFiniteState s cont).1 = some .break) →
      P (evaluateHOLFiniteState s cont).2 ∧
      (evaluateHOLFiniteState s cont).2.locals.lookup (ofString baseName) = some (.val (.word wb)) ∧
      (evaluateHOLFiniteState s cont).2.locals.lookup (ofString idxName) = some (.val (.word (wi + 1#64)))) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (wb wi : BitVec 64),
      s.code = originalRuntimeCode → P s →
      s.locals.lookup (ofString baseName) = some (.val (.word wb)) →
      s.locals.lookup (ofString idxName) = some (.val (.word wi)) →
      ((evaluateHOLFiniteState s (.dec name sh init cont)).1 = none ∨
       (evaluateHOLFiniteState s (.dec name sh init cont)).1 = some .continue ∨
       (evaluateHOLFiniteState s (.dec name sh init cont)).1 = some .break) →
      P (evaluateHOLFiniteState s (.dec name sh init cont)).2 ∧
      (evaluateHOLFiniteState s (.dec name sh init cont)).2.locals.lookup (ofString baseName) =
          some (.val (.word wb)) ∧
      (evaluateHOLFiniteState s (.dec name sh init cont)).2.locals.lookup (ofString idxName) =
          some (.val (.word (wi + 1#64))) := by
  intro F s wb wi hcode hPs hb_s hi_s hflow
  set out := evaluateHOLFiniteState s (.dec name sh init cont) with hout
  have hrun : evaluateHOLFiniteState s (.dec name sh init cont) = (out.1, out.2) := by simp [hout]
  rcases out with ⟨res, post⟩
  dsimp only at hflow hrun ⊢
  have hfl : Flowing res := by
    rcases hflow with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  rw [evaluateHOLFiniteState_dec_total] at hrun
  dsimp only at hrun
  rcases he : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) init with _ | val
  · rw [he] at hrun; simp at hrun; obtain ⟨rfl, _⟩ := hrun; rcases hfl with h | h | h <;> simp at h
  · rw [he] at hrun; dsimp only at hrun
    split_ifs at hrun with hsh
    · set s1 := setVarHOLFinite name val s
      have hb_s1 : s1.locals.lookup (ofString baseName) = some (.val (.word wb)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hname_ne_base, hb_s]
      have hi_s1 : s1.locals.lookup (ofString idxName) = some (.val (.word wi)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hname_ne_idx, hi_s]
      obtain ⟨hres_eq, hpost_eq⟩ := Prod.mk.inj hrun
      have hc_fl : (evaluateHOLFiniteState s1 cont).1 = none ∨
          (evaluateHOLFiniteState s1 cont).1 = some .continue ∨
          (evaluateHOLFiniteState s1 cont).1 = some .break := by
        rw [hres_eq]; exact hflow
      obtain ⟨hP_c, hb_c, hi_c⟩ := hcont s1 wb wi hcode (hP.setVar hname_not_names val s hPs) hb_s1 hi_s1 hc_fl
      rw [← hpost_eq]
      refine ⟨?_, ?_, ?_⟩
      · exact hP (evaluateHOLFiniteState s1 cont).2
          (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 cont).2.locals
            (name, s.locals.lookup name))
          (evaluateHOLFiniteState s1 cont).2.clock
          (fun n hn => resVarEq_lookup_ne _ _ _ _ (hname_not_names n hn)) hP_c
      · rw [PanRunBounded.resVarEq_lookup, if_neg hname_ne_base.symm]; exact hb_c
      · rw [PanRunBounded.resVarEq_lookup, if_neg hname_ne_idx.symm]; exact hi_c
    · simp at hrun; obtain ⟨rfl, _⟩ := hrun; rcases hfl with h | h | h <;> simp at h

theorem walk_decCall_step {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {baseName idxName : String}
    {name fname : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hP : LocalsOnly names P)
    (hname_not_names : ∀ n ∈ names, ofString n ≠ name)
    (hname_ne_base : name ≠ ofString baseName)
    (hname_ne_idx : name ≠ ofString idxName)
    (hres : DecCallResumeOn P P name fname args)
    (hcont : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (wb wi : BitVec 64),
      s.code = originalRuntimeCode → P s →
      s.locals.lookup (ofString baseName) = some (.val (.word wb)) →
      s.locals.lookup (ofString idxName) = some (.val (.word wi)) →
      ((evaluateHOLFiniteState s cont).1 = none ∨
       (evaluateHOLFiniteState s cont).1 = some .continue ∨
       (evaluateHOLFiniteState s cont).1 = some .break) →
      P (evaluateHOLFiniteState s cont).2 ∧
      (evaluateHOLFiniteState s cont).2.locals.lookup (ofString baseName) = some (.val (.word wb)) ∧
      (evaluateHOLFiniteState s cont).2.locals.lookup (ofString idxName) = some (.val (.word (wi + 1#64)))) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (wb wi : BitVec 64),
      s.code = originalRuntimeCode → P s →
      s.locals.lookup (ofString baseName) = some (.val (.word wb)) →
      s.locals.lookup (ofString idxName) = some (.val (.word wi)) →
      ((evaluateHOLFiniteState s (.decCall name sh fname args cont)).1 = none ∨
       (evaluateHOLFiniteState s (.decCall name sh fname args cont)).1 = some .continue ∨
       (evaluateHOLFiniteState s (.decCall name sh fname args cont)).1 = some .break) →
      P (evaluateHOLFiniteState s (.decCall name sh fname args cont)).2 ∧
      (evaluateHOLFiniteState s (.decCall name sh fname args cont)).2.locals.lookup (ofString baseName) =
          some (.val (.word wb)) ∧
      (evaluateHOLFiniteState s (.decCall name sh fname args cont)).2.locals.lookup (ofString idxName) =
          some (.val (.word (wi + 1#64))) := by
  intro F s wb wi hcode hPs hb_s hi_s hflow
  set out := evaluateHOLFiniteState s (.decCall name sh fname args cont) with hout
  have hrun : evaluateHOLFiniteState s (.decCall name sh fname args cont) = (out.1, out.2) := by simp [hout]
  rcases out with ⟨res, post⟩
  dsimp only at hflow hrun ⊢
  have hfl : Flowing res := by
    rcases hflow with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hargs] at hrun; simp at hrun; obtain ⟨rfl, _⟩ := hrun; rcases hfl with h | h | h <;> simp at h
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hrun; simp at hrun; obtain ⟨rfl, _⟩ := hrun; rcases hfl with h | h | h <;> simp at h
    · rw [hl] at hrun; dsimp only at hrun
      split_ifs at hrun with hz
      · simp at hrun; obtain ⟨rfl, _⟩ := hrun; rcases hfl with h | h | h <;> simp at h
      · have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').1
        rcases hb_run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨bres, bpost⟩
        rw [hb_run] at hrun hmeta
        dsimp only at hmeta
        cases bres with
        | none => simp at hrun; obtain ⟨rfl, _⟩ := hrun; rcases hfl with h | h | h <;> simp at h
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hrun
            split_ifs at hrun with hsh
            · set resumed := setVarHOLFinite name v { bpost with locals := s.locals }
              have hresP : P resumed := hres s values body' callee ret' v bpost hcode hPs hargs hl hb_run
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              have hb_res : resumed.locals.lookup (ofString baseName) = some (.val (.word wb)) := by
                simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hname_ne_base, hb_s]
              have hi_res : resumed.locals.lookup (ofString idxName) = some (.val (.word wi)) := by
                simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hname_ne_idx, hi_s]
              obtain ⟨hres_eq, hpost_eq⟩ := Prod.mk.inj hrun
              have hc_fl : (evaluateHOLFiniteState resumed cont).1 = none ∨
                  (evaluateHOLFiniteState resumed cont).1 = some .continue ∨
                  (evaluateHOLFiniteState resumed cont).1 = some .break := by
                rw [hres_eq]; exact hflow
              obtain ⟨hP_c, hb_c, hi_c⟩ := hcont resumed wb wi hresCode hresP hb_res hi_res hc_fl
              rw [← hpost_eq]
              refine ⟨?_, ?_, ?_⟩
              · exact hP (evaluateHOLFiniteState resumed cont).2
                  (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState resumed cont).2.locals
                    (name, s.locals.lookup name))
                  (evaluateHOLFiniteState resumed cont).2.clock
                  (fun n hn => resVarEq_lookup_ne _ _ _ _ (hname_not_names n hn)) hP_c
              · rw [PanRunBounded.resVarEq_lookup, if_neg hname_ne_base.symm]; exact hb_c
              · rw [PanRunBounded.resVarEq_lookup, if_neg hname_ne_idx.symm]; exact hi_c
            · simp at hrun; obtain ⟨rfl, _⟩ := hrun; rcases hfl with h | h | h <;> simp at h
          | _ => simp at hrun; obtain ⟨rfl, _⟩ := hrun; rcases hfl with h | h | h <;> simp at h

theorem no_cont_break_seq {p1 p2 : ProgHOL 64}
    (h1 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s p1).1 ≠ some .continue ∧ (evaluateHOLFiniteState s p1).1 ≠ some .break)
    (h2 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s p2).1 ≠ some .continue ∧ (evaluateHOLFiniteState s p2).1 ≠ some .break) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s (.seq p1 p2)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s (.seq p1 p2)).1 ≠ some .break := by
  intro F s
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
  cases r1 with
  | none => exact h2 s1
  | some _ =>
    have := h1 s
    rw [hr1] at this
    exact this

theorem no_cont_break_ite {cond : ExpHOL 64} {p1 p2 : ProgHOL 64}
    (h1 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s p1).1 ≠ some .continue ∧ (evaluateHOLFiniteState s p1).1 ≠ some .break)
    (h2 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s p2).1 ≠ some .continue ∧ (evaluateHOLFiniteState s p2).1 ≠ some .break) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s (.ite cond p1 p2)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s (.ite cond p1 p2)).1 ≠ some .break := by
  intro F s
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact h2 s
    · exact h1 s
  · simp

theorem no_cont_break_dec {name : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s body).1 ≠ some .continue ∧ (evaluateHOLFiniteState s body).1 ≠ some .break) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s (.dec name sh init body)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s (.dec name sh init body)).1 ≠ some .break := by
  intro F s
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · split
    · exact hb _
    · simp

theorem no_cont_break_decCall {name fname : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s cont).1 ≠ some .continue ∧ (evaluateHOLFiniteState s cont).1 ≠ some .break) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s (.decCall name sh fname args cont)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s (.decCall name sh fname args cont)).1 ≠ some .break := by
  intro F s
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
    · simp
    · dsimp only
      split_ifs with hz
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨bres, _⟩
        cases bres with
        | none => simp
        | some br =>
          cases br with
          | returned _ =>
            dsimp only; split_ifs
            · exact hc _
            · simp
          | _ => simp

theorem no_cont_break_call (ret : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (hnone : ∀ h, ret ≠ some (none, some h) ∧ ∀ d, ret ≠ some (d, some h))
    (fname : MlS) (args : List (ExpHOL 64)) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s (.call ret fname args)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s (.call ret fname args)).1 ≠ some .break := by
  intro F s
  cases ret with
  | none =>
    rw [evaluateHOLFiniteState_call]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
    · simp
    · dsimp only
      rcases lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, rsh⟩
      · simp
      · dsimp only
        split_ifs with hz
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨bres, _⟩
          cases bres with
          | none => simp
          | some br =>
            cases br with
            | returned _ => dsimp only; split_ifs <;> simp
            | _ => simp
  | some p =>
    rcases p with ⟨dest, hdl⟩
    cases hdl with
    | some h => exact absurd rfl ((hnone h).2 dest)
    | none =>
      rw [evaluateHOLFiniteState_call]
      rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
      · simp
      · dsimp only
        rcases lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, rsh⟩
        · simp
        · dsimp only
          split_ifs with hz
          · simp
          · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨bres, _⟩
            cases bres with
            | none => simp
            | some br =>
              cases br with
              | returned _ =>
                cases dest with
                | none => dsimp only; split_ifs <;> simp
                | some kv => dsimp only; split_ifs <;> simp
              | _ => simp

theorem no_cont_break_assign (k : VarKind) (name : MlS) (e : ExpHOL 64) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s (.assign k name e)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s (.assign k name e)).1 ≠ some .break := by
  intro F s
  rw [evaluateHOLFiniteState_assign]
  split
  · simp
  · split <;> simp

theorem no_cont_break_skip :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s .skip).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s .skip).1 ≠ some .break := by
  intro F s; simp

theorem no_cont_break_while (cond : ExpHOL 64) (body : ProgHOL 64) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .break := by
  intro F s
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      (evaluateHOLFiniteState st (.while cond body)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState st (.while cond body)).1 ≠ some .break from
    this s.clock s rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          set bOut := evaluateHOLFiniteState (decClockHOLFinite st) body with hbOut
          have bRun : evaluateHOLFiniteState (decClockHOLFinite st) body = (bOut.1, bOut.2) := by simp [hbOut]
          rcases bOut with ⟨r1, mid⟩
          dsimp only at hrem bRun ⊢
          have hlt : mid.clock < k := by change mid.clock ≤ st.clock - 1 at hrem; omega
          cases r1 with
          | none => exact ih mid.clock hlt mid rfl
          | some r1' =>
            cases r1' with
            | «continue» => exact ih mid.clock hlt mid rfl
            | «break» => simp
            | _ => simp
      · simp
    · simp

def noContBreak : ProgHOL 64 → Bool
  | .skip => true
  | .annot _ _ => true
  | .assign _ _ _ => true
  | .store _ _ => true
  | .store32 _ _ => true
  | .storeByte _ _ => true
  | .return _ => true
  | .raise _ _ => true
  | .while _ _ => true
  | .call (some (_, none)) _ _ => true
  | .call none _ _ => true
  | .seq p1 p2 => noContBreak p1 && noContBreak p2
  | .ite _ p1 p2 => noContBreak p1 && noContBreak p2
  | .dec _ _ _ b => noContBreak b
  | .decCall _ _ _ _ c => noContBreak c
  | _ => false

theorem noContBreak_sound : ∀ (p : ProgHOL 64), noContBreak p = true →
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s p).1 ≠ some .continue ∧
      (evaluateHOLFiniteState s p).1 ≠ some .break
  | .skip, _, _, s => no_cont_break_skip s
  | .annot _ _, _, _, _ => by simp
  | .assign k n e, _, _, s => no_cont_break_assign k n e s
  | .store a v, _, _, s => by
    rw [evaluateHOLFiniteState_store]
    repeat' split
    all_goals simp
  | .store32 a v, _, _, s => by
    rw [evaluateHOLFiniteState_store32]
    repeat' split
    all_goals simp
  | .storeByte a v, _, _, s => by
    rw [evaluateHOLFiniteState_storeByte]
    repeat' split
    all_goals simp
  | .return e, _, _, s => by
    rw [evaluateHOLFiniteState_return]
    repeat' split
    all_goals simp
  | .raise n e, _, _, s => by
    rw [evaluateHOLFiniteState_raise]
    repeat' split
    all_goals (try simp)
    all_goals (split_ifs <;> simp)
  | .while c b, _, _, s => no_cont_break_while c b s
  | .call none fn args, _, _, s => no_cont_break_call none (by intro h; simp) fn args s
  | .call (some (d, none)) fn args, _, _, s => no_cont_break_call (some (d, none)) (by intro h; simp) fn args s
  | .call (some (_, some _)) _ _, h, _, _ => by simp [noContBreak] at h
  | .seq p1 p2, h, _, s => by
    simp only [noContBreak, Bool.and_eq_true] at h
    exact no_cont_break_seq (noContBreak_sound p1 h.1) (noContBreak_sound p2 h.2) s
  | .ite c p1 p2, h, _, s => by
    simp only [noContBreak, Bool.and_eq_true] at h
    exact no_cont_break_ite (noContBreak_sound p1 h.1) (noContBreak_sound p2 h.2) s
  | .dec _ _ _ b, h, _, s => no_cont_break_dec (noContBreak_sound b h) s
  | .decCall _ _ _ _ c, h, _, s => no_cont_break_decCall (noContBreak_sound c h) s
  | .break, h, _, _ => by simp [noContBreak] at h
  | .continue, h, _, _ => by simp [noContBreak] at h
  | .primitive _ _ _, h, _, _ => by simp [noContBreak] at h
  | .extCall _ _ _ _ _, h, _, _ => by simp [noContBreak] at h
  | .shMemLoad _ _ _ _, h, _, _ => by simp [noContBreak] at h
  | .shMemStore _ _ _, h, _, _ => by simp [noContBreak] at h

theorem hoare_ite_requests_append {c : Nat} (hc : c < 8)
    (wra : WorldKeeps ReqRoom (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 72, 80])]
      ReqCountInc (ofString "requests_append"))
    (cond : ExpHOL 64) (args : List (ExpHOL 64)) :
    Hoare (ReqState c) (.ite cond (.call (some (none, none)) (ofString "requests_append") args) .skip)
      (fun r t => r = none → ReqState (c + 1) t) := by
  apply Hoare.ite_fall
  · apply Hoare.mono _ (fun _ h => h.1)
    exact Hoare.call0 wra
      (callEntryOn_of_imp (fun s locals k ⟨hW, hr⟩ => ⟨localsFree_worldOK s locals k hW, hr⟩)
        (fun _ h => reqState_reqRoom hc h) _ _)
      (fun s _ post v _ ⟨hW, hbo_nz, hc_le⟩ hq _ => by
        have hws := hq (Or.inl ⟨v, rfl⟩)
        obtain ⟨hAp, _, hG, _, hWS⟩ := hws
        obtain ⟨_, S, hS⟩ := hW
        obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with s S).1 hS
        obtain ⟨S', Nd', _, hWT', _, _, hinc⟩ :=
          hWS S Nd ((worldTypedWith_with_locals _ _ _ _ _).2 hWT) (fun x hx => by simp at hx)
        have hbo_eq : globN post "bo" = globN s "bo" := by
          unfold globN; rw [← hG (ofString "bo") (by simp; decide)]; rfl
        have hinc' : memW post (globN s "bo" + 64) = memW s (globN s "bo" + 64) + 1 := hinc
        refine localsFree_reqState (c + 1) post s.locals post.clock
          ⟨⟨hAp, S', (worldTyped_iff_with post S').2 ⟨Nd', hWT'⟩⟩, ?_, ?_⟩
        · rw [hbo_eq]; exact hbo_nz
        · rw [hbo_eq, hinc']; omega)
      (fun _ _ hr _ h => absurd h hr)
  · exact Hoare.skip fun _ h _ => reqState_mono (Nat.le_succ c) h.1

theorem resumeOn_process_checked_sys_tx {c : Nat}
    (wpcs : WorldKeeps WorldOK
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
                 (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
                 (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
                 (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
                 (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
                 (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
                 (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
                 (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
                 (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
                 (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
                 (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "process_checked_system_transaction"))
    (name : MlS) (args : List (ExpHOL 64)) :
    DecCallResumeOn (ReqState c) (ReqState c) name (ofString "process_checked_system_transaction") args := by
  intro F state values body callee ret value post hcode ⟨hW, hbo_nz, hc_le⟩ _ hl hrun
  obtain ⟨hAs, S, hS⟩ := hW
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with state S).1 hS
  have hstep := FunSpec.at_lookup wpcs state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) ⟨hAs, S, hS⟩) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  obtain ⟨hAp, _, hG, hRK, hWS⟩ := hstep (Or.inl ⟨value, rfl⟩)
  have hdisj_R : ∀ {F2 : Type} (st : PanSemStateFiniteExact 64 F2),
      WorldTypedWith st S Nd →
      IvlsDisj
        [(globN st "b2_v", if globN st "b2_v" = 0 then 0 else 128),
         (globN st "bal_key_buf", if globN st "bal_key_buf" = 0 then 0 else 64),
         (globN st "bn_expw", if globN st "bn_expw" = 0 then 0 else 352),
         (globN st "bn_gamma", if globN st "bn_gamma" = 0 then 0 else 384),
         (globN st "evm_key_buf", if globN st "evm_key_buf" = 0 then 0 else 32),
         (globN st "keccak_pad", if globN st "keccak_pad" = 0 then 0 else 136),
         (globN st "keccak_st", if globN st "keccak_st" = 0 then 0 else 200),
         (globN st "mpt_nib_scratch", if globN st "mpt_nib_scratch" = 0 then 0 else 64),
         (globN st "pre_hdr_buf", if globN st "pre_hdr_buf" = 0 then 0 else 96),
         (globN st "rmd_h", if globN st "rmd_h" = 0 then 0 else 40),
         (globN st "rmd_pad", if globN st "rmd_pad" = 0 then 0 else 128),
         (globN st "rmd_x", if globN st "rmd_x" = 0 then 0 else 128),
         (globN st "sha_pad", if globN st "sha_pad" = 0 then 0 else 128),
         (globN st "sha_st", if globN st "sha_st" = 0 then 0 else 64),
         (globN st "sk_buf", if globN st "sk_buf" = 0 then 0 else 52),
         (globN st "u256_ws", if globN st "u256_ws" = 0 then 0 else 640)]
        (worldTypedIvls st S Nd) := by
    intro F2 st hWT_st i hi j hj
    change i ∈ [bufferRegion st ("b2_v", 128), bufferRegion st ("bal_key_buf", 64),
      bufferRegion st ("bn_expw", 352), bufferRegion st ("bn_gamma", 384),
      bufferRegion st ("evm_key_buf", 32), bufferRegion st ("keccak_pad", 136),
      bufferRegion st ("keccak_st", 200), bufferRegion st ("mpt_nib_scratch", 64),
      bufferRegion st ("pre_hdr_buf", 96), bufferRegion st ("rmd_h", 40),
      bufferRegion st ("rmd_pad", 128), bufferRegion st ("rmd_x", 128),
      bufferRegion st ("sha_pad", 128), bufferRegion st ("sha_st", 64),
      bufferRegion st ("sk_buf", 52), bufferRegion st ("u256_ws", 640)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bufferRegion_disj_le hWT_st ("b2_v", 128) (by decide) (by decide) 128 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("bal_key_buf", 64) (by decide) (by decide) 64 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("bn_expw", 352) (by decide) (by decide) 352 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("bn_gamma", 384) (by decide) (by decide) 384 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("evm_key_buf", 32) (by decide) (by decide) 32 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("keccak_pad", 136) (by decide) (by decide) 136 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("keccak_st", 200) (by decide) (by decide) 200 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("mpt_nib_scratch", 64) (by decide) (by decide) 64 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("pre_hdr_buf", 96) (by decide) (by decide) 96 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("rmd_h", 40) (by decide) (by decide) 40 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("rmd_pad", 128) (by decide) (by decide) 128 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("rmd_x", 128) (by decide) (by decide) 128 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("sha_pad", 128) (by decide) (by decide) 128 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("sha_st", 64) (by decide) (by decide) 64 le_rfl j hj
    · exact bufferRegion_disj_le hWT_st ("sk_buf", 64) (by decide) (by decide) 52 (by decide) j hj
    · exact bufferRegion_disj_le hWT_st ("u256_ws", 640) (by decide) (by decide) 640 le_rfl j hj
  have hWT_entry := (worldTypedWith_with_locals state callee (state.clock - 1) S Nd).2 hWT
  obtain ⟨S', Nd', _, hWT', _, _, _⟩ := hWS S Nd hWT_entry (hdisj_R _ hWT_entry)
  have hbo_eq : globN post "bo" = globN state "bo" := by
    unfold globN; rw [← hG (ofString "bo") (by simp; decide)]; rfl
  have hbo_ti : (globN state "bo", 88) ∈ worldTypedIvls state S Nd := by
    unfold worldTypedIvls
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; left; apply List.mem_append.2; right
    have hr_in : ("bo", 88) ∈ typedRecords := by decide
    have hm : (globN state "bo", if globN state "bo" = 0 then 0 else 88) ∈
        typedRecords.map (fun r => (globN state r.1, if globN state r.1 = 0 then 0 else r.2)) :=
      List.mem_map.2 ⟨("bo", 88), hr_in, rfl⟩
    rw [if_neg hbo_nz] at hm
    exact hm
  have hbo8 : (globN state "bo") % 8 = 0 := by
    have hfix := typedRecord_mem_fixedObjects state (show ("bo", 88) ∈ typedRecords by decide)
    rw [if_neg hbo_nz] at hfix
    rcases hWT.2.2.1.1 _ hfix with hz | ⟨_, hw⟩
    · dsimp at hz; omega
    · exact hw.1
  have hc64_eq : memW post (globN state "bo" + 64) = memW state (globN state "bo" + 64) := by
    apply hRK ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) hbo_nz 64 (by simp)
    intro i hi
    dsimp only at hi ⊢
    change ¬ CellHits (globN state "bo" + 64) i
    have hi_z : i.2 = 0 → i.1 % 8 = 0 := by
      change i ∈ [bufferRegion state ("b2_v", 128), bufferRegion state ("bal_key_buf", 64),
        bufferRegion state ("bn_expw", 352), bufferRegion state ("bn_gamma", 384),
        bufferRegion state ("evm_key_buf", 32), bufferRegion state ("keccak_pad", 136),
        bufferRegion state ("keccak_st", 200), bufferRegion state ("mpt_nib_scratch", 64),
        bufferRegion state ("pre_hdr_buf", 96), bufferRegion state ("rmd_h", 40),
        bufferRegion state ("rmd_pad", 128), bufferRegion state ("rmd_x", 128),
        bufferRegion state ("sha_pad", 128), bufferRegion state ("sha_st", 64),
        bufferRegion state ("sk_buf", 52), bufferRegion state ("u256_ws", 640)] at hi
      have hbuf0 : ∀ (g : String) (sz : Nat), sz ≠ 0 →
          (bufferRegion state (g, sz)).2 = 0 → (bufferRegion state (g, sz)).1 % 8 = 0 := by
        intro g sz hsz hz
        unfold bufferRegion at hz ⊢
        dsimp only at hz ⊢
        by_cases hg0 : globN state g = 0
        · rw [hg0]
        · rw [if_neg hg0] at hz; exact absurd hz hsz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hbuf0 _ _ (by omega)
    have hd_bo : Disj i (globN state "bo", 88) := hdisj_R state hWT i hi _ hbo_ti
    exact fun hch => not_cellHits_of_disj (by omega) (by omega) (by omega) hi_z ⟨by omega, by omega⟩ hd_bo.flip hch
  exact LocalsOnly.setVar (LocalsOnly.of_localsFree (localsFree_reqState c)) (by simp) value _
    (localsFree_reqState c post state.locals post.clock
      ⟨⟨hAp, S', (worldTyped_iff_with post S').2 ⟨Nd', hWT'⟩⟩,
       by rw [hbo_eq]; exact hbo_nz,
       by rw [hbo_eq, hc64_eq]; exact hc_le⟩)

theorem dec_zero_on {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (name : MlS) {body : ProgHOL 64} {K : Nat}
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (setVarHOLFinite name (.val (.word 0#64)) s))
    (hbody : TerminatingProgBoundedOn Q body K) :
    TerminatingProgBoundedOn P (.dec name .one (.const 0#64) body) K := by
  intro F s hcode hP
  unfold TerminatingRunBounded; dsimp only; intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  have hc0_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0#64) =
      some (.val (.word 0#64)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hnt ⊢
  rw [hc0_ev] at hnt ⊢; dsimp only at hnt ⊢; rw [if_pos hsh0] at hnt ⊢
  have hb := hbody (setVarHOLFinite name (.val (.word 0#64)) s) hcode (hstep s hP) hnt
  simpa [setVarHOLFinite] using hb

theorem dec_eval_on {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (name : MlS) (sh : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {K : Nat}
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      P s → evalAt s init = some v → Q (setVarHOLFinite name v s))
    (hbody : TerminatingProgBoundedOn Q body K) :
    TerminatingProgBoundedOn P (.dec name sh init body) K := by
  intro F state hcode hP
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  rcases he : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) init with _ | val
  · intro _; exact ⟨Nat.le_add_right state.clock K, Nat.le_refl _⟩
  · dsimp only
    split <;> intro hnt
    · have hb := hbody (setVarHOLFinite name val state) hcode (hstep state val hP he)
        (by simpa [setVarHOLFinite] using hnt)
      simpa [setVarHOLFinite] using hb
    · exact ⟨Nat.le_add_right state.clock K, Nat.le_refl _⟩

theorem prove_gbody_process_general_purpose_requests
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hed : TerminatingFunBoundedOn GuestInv (ofString "extract_deposit_data") K.«extract_deposit_data»)
    (hmc : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (hmq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (hpcs : TerminatingFunBoundedOn WorldOK (ofString "process_checked_system_transaction") K.«process_checked_system_transaction»)
    (hra : TerminatingFunBoundedOn GuestInv (ofString "requests_append") K.«requests_append»)
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (wed : WorldKeeps WorldOK (fun s => [(locN s "out", 192)]) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "extract_deposit_data"))
    (wmc : WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memcpy"))
    (rmq : ReadOnlyFn (ofString "memeq"))
    (wpcs : WorldKeeps WorldOK
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
                 (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
                 (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
                 (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
                 (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
                 (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
                 (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
                 (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
                 (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
                 (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
                 (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "process_checked_system_transaction"))
    (wra : WorldKeeps ReqRoom (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 72, 80])]
      ReqCountInc (ofString "requests_append")) :
    TerminatingFunBoundedOn ReqsFresh (ofString "process_general_purpose_requests")
      K.«process_general_purpose_requests» := by
  refine ⟨_, _, _, lookup_process_general_purpose_requests, ?_⟩
  simp only [InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, List.map_cons, List.map_nil]
  -- Inner loop (`j < nl`)
  obtain ⟨hinner_hoare, hinner_bound⟩ :=
    walk_loop_general localsOnly_depLoopInv (fun _ h => depLoopInv_guestInv h)
      (elemName := "log") (baseName := "lp") (idxName := "j")
      (by simp; decide) (by decide) (by decide)
      (walk_decCall_step localsOnly_depLoopInv (by simp; decide) (by decide) (by decide)
        (resumeOn_memeq_depLoopInv rmq (ofString "isdep") (by simp; decide)
          [.load .one (.op .add [.var .local (ofString "log"), .const 0#64]),
           .var .global (ofString "deposit_contract_address"), .const 20#64])
        (walk_seq_inc_step localsOnly_depLoopInv (by simp; decide) (by decide)
          (by decide) (by decide) (noContBreak_sound _ (by decide))
          (hoare_dep_inner_after_isdep wal rtal wed wmc rmq)))
      (TerminatingProgBoundedOn.decCall_on hmq (ofString "isdep") .one
        [.load .one (.op .add [.var .local (ofString "log"), .const 0#64]),
         .var .global (ofString "deposit_contract_address"), .const 20#64]
        (callEntryOn_of_imp localsFree_guestInv (fun _ h => depLoopInv_guestInv h) _ _)
        (resumeOn_memeq_depLoopInv rmq (ofString "isdep") (by simp; decide) _)
        (TerminatingProgBoundedOn.seq_guestInv_after
          (bounded_dep_inner_after_isdep hal hed hmc hmq wal rtal wmc rmq)
          (fun _ h => depLoopInv_guestInv h)
          (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))))
      "nl"
  -- Outer loop (`i < nr`)
  obtain ⟨houter_hoare, houter_bound⟩ :=
    walk_loop_general localsOnly_depLoopInv (fun _ h => depLoopInv_guestInv h)
      (elemName := "logs") (baseName := "rp") (idxName := "i")
      (by simp; decide) (by decide) (by decide)
      (walk_dec_step (name := ofString "nl") (sh := .one)
        (init := .load .one (.op .add [.var .local (ofString "logs"), .const 8#64]))
        localsOnly_depLoopInv (by simp; decide) (by decide) (by decide)
        (walk_dec_step (name := ofString "lp") (sh := .one)
          (init := .load .one (.op .add [.var .local (ofString "logs"), .const 0#64]))
          localsOnly_depLoopInv (by simp; decide) (by decide) (by decide)
          (walk_dec_step (name := ofString "j") (sh := .one) (init := .const 0#64)
            localsOnly_depLoopInv (by simp; decide) (by decide) (by decide)
            (walk_seq_inc_step localsOnly_depLoopInv (by simp; decide) (by decide)
              (by decide) (by decide) (noContBreak_sound _ (by decide))
              hinner_hoare))))
      (TerminatingProgBoundedOn.dec_onLocals localsOnly_depLoopInv (ofString "nl") (by simp; decide) .one
        (.load .one (.op .add [.var .local (ofString "logs"), .const 8#64]))
        (TerminatingProgBoundedOn.dec_onLocals localsOnly_depLoopInv (ofString "lp") (by simp; decide) .one
          (.load .one (.op .add [.var .local (ofString "logs"), .const 0#64]))
          (TerminatingProgBoundedOn.dec_onLocals localsOnly_depLoopInv (ofString "j") (by simp; decide) .one (.const 0#64)
            (TerminatingProgBoundedOn.seq_guestInv_after
              hinner_bound
              (fun _ h => depLoopInv_guestInv h)
              (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))))))
      "nr"
  -- Post-loop tail: `ReqState 0` -> `ReqState 1` -> ... -> `ReqState 5`
  have hite_ra_bound : ∀ (c : Nat) (cond : ExpHOL 64) (args : List (ExpHOL 64)),
      TerminatingProgBoundedOn (ReqState c)
        (.ite cond (.call (some (none, none)) (ofString "requests_append") args) .skip)
        (Nat.max (K.«requests_append» + 1) 0) :=
    fun c cond args =>
      TerminatingProgBoundedOn.ite_on
        (TerminatingProgBoundedOn.call_on hra _ _
          (callEntryOn_of_imp localsFree_guestInv (fun _ h => reqState_guestInv h) _ _))
        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s))
  -- Assemble the full body from `ReqsFresh`:
  -- First `dec "rls"` transitions `ReqsFresh` -> `ReqState 0` when init succeeds!
  set P_dep0 : ∀ {F2 : Type}, PanSemStateFiniteExact 64 F2 → Prop :=
    fun s => ∃ w_dep : BitVec 64, ∃ S Nd : List Nat,
      WorldTypedWith s S Nd ∧ ArenaReady s ∧ globN s "bo" ≠ 0 ∧ memW s (globN s "bo" + 64) = 0 ∧
      s.locals.lookup (ofString "dep") = some (.val (.word w_dep)) ∧
      w_dep.toNat % 8 = 0 ∧
      Inside (w_dep.toNat, 8) sourceBase (globN s "heap_ptr") ∧
      IvlsDisj [(w_dep.toNat, 8)] (worldOwned s S Nd)
  set P_dep1 : ∀ {F2 : Type}, PanSemStateFiniteExact 64 F2 → Prop :=
    fun s => ∃ w_dep : BitVec 64, ∃ S Nd : List Nat,
      WorldTypedWith s S Nd ∧ ArenaReady s ∧ globN s "bo" ≠ 0 ∧ memW s (globN s "bo" + 64) = 0 ∧
      s.locals.lookup (ofString "dep") = some (.val (.word w_dep)) ∧
      s.locals.lookup (ofString "dep_n") = some (.val (.word 0#64)) ∧
      w_dep.toNat % 8 = 0 ∧
      Inside (w_dep.toNat, 8) sourceBase (globN s "heap_ptr") ∧
      IvlsDisj [(w_dep.toNat, 8)] (worldOwned s S Nd)
  intro F state hcode hRF hnt
  exact TerminatingRunBounded.weaken
    (K' := K.«process_general_purpose_requests»)
    ((dec_eval_on (P := ReqsFresh) (Q := ReqState 0)
      (ofString "rls") .one (.load .one (.op .add [.var .global (ofString "bo"), .const 72#64]))
      dec_rls_reqsFresh_to_reqState0
      (TerminatingProgBoundedOn.dec_on (localsFree_reqState 0)
        (ofString "nr") .one (.load .one (.op .add [.var .local (ofString "rls"), .const 8#64]))
        (TerminatingProgBoundedOn.dec_on (localsFree_reqState 0)
          (ofString "rp") .one (.load .one (.op .add [.var .local (ofString "rls"), .const 0#64]))
          (TerminatingProgBoundedOn.decCall_on hal (ofString "dep") .one [.const 8#64]
            (callEntryOn_of_imp localsFree_guestInv (fun _ h => reqState_guestInv h) _ _)
            (resumeOn_init_dep_alloc wal rtal)
            (dec_zero_on (P := P_dep0) (Q := P_dep1) (ofString "dep_n")
              (fun s2 hP0 => by
                obtain ⟨w_dep, S, Nd, hWT, hA, hbo, hc0, hld, hd8, hin, hdj⟩ := hP0
                exact ⟨w_dep, S, Nd,
                  (worldTypedWith_with_locals s2 _ s2.clock S Nd).2 hWT,
                  localsFree_arenaReady s2 _ s2.clock hA, hbo, hc0,
                  by have hne : ofString "dep_n" ≠ ofString "dep" := by decide
                     simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hld],
                  by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
                  hd8, hin, hdj⟩)
              (dec_zero_on (P := P_dep1) (Q := DepLoopInv) (ofString "dep_cap")
                (fun s2 hP1 => by
                  obtain ⟨w_dep, S, Nd, hWT, hA, hbo, hc0, hld, hln, hd8, hin, _⟩ := hP1
                  exact ⟨w_dep, 0#64, 0#64, S, Nd,
                    (worldTypedWith_with_locals s2 _ s2.clock S Nd).2 hWT,
                    localsFree_arenaReady s2 _ s2.clock hA, hbo, hc0,
                    by have hne : ofString "dep_cap" ≠ ofString "dep" := by decide
                       simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hld],
                    by have hne : ofString "dep_cap" ≠ ofString "dep_n" := by decide
                       simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hln],
                    by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
                    by decide, hd8, by decide, by decide,
                    ⟨hin.1, by change w_dep.toNat + 0 ≤ globN s2 "heap_ptr"; unfold Inside at hin; omega⟩,
                    fun x hx _ _ => by simp only [List.mem_singleton] at hx; subst hx; exact Or.inl rfl⟩)
                (TerminatingProgBoundedOn.dec_onLocals localsOnly_depLoopInv (ofString "i") (by simp; decide) .one (.const 0#64)
                  (TerminatingProgBoundedOn.seq_hoare_trans
                    houter_bound
                    ⟨fun s3 hc3 hI3 hnt3 hr3 => depLoopInv_reqState0 (houter_hoare.run s3 hc3 hI3 hnt3 hr3)⟩
                    (TerminatingProgBoundedOn.seq_hoare_trans
                      (hite_ra_bound 0 _ _)
                      (hoare_ite_requests_append (c := 0) (by omega) wra _ _)
                      (TerminatingProgBoundedOn.decCall_on hpcs (ofString "o1") .one _
                        (callEntryOn_of_imp localsFree_worldOK (fun _ h => reqState_worldOK h) _ _)
                        (resumeOn_process_checked_sys_tx (c := 1) wpcs _ _)
                        (TerminatingProgBoundedOn.seq_hoare_trans
                          (hite_ra_bound 1 _ _)
                          (hoare_ite_requests_append (c := 1) (by omega) wra _ _)
                          (TerminatingProgBoundedOn.decCall_on hpcs (ofString "o2") .one _
                            (callEntryOn_of_imp localsFree_worldOK (fun _ h => reqState_worldOK h) _ _)
                            (resumeOn_process_checked_sys_tx (c := 2) wpcs _ _)
                            (TerminatingProgBoundedOn.seq_hoare_trans
                              (hite_ra_bound 2 _ _)
                              (hoare_ite_requests_append (c := 2) (by omega) wra _ _)
                              (TerminatingProgBoundedOn.decCall_on hpcs (ofString "o3") .one _
                                (callEntryOn_of_imp localsFree_worldOK (fun _ h => reqState_worldOK h) _ _)
                                (resumeOn_process_checked_sys_tx (c := 3) wpcs _ _)
                                (TerminatingProgBoundedOn.seq_hoare_trans
                                  (hite_ra_bound 3 _ _)
                                  (hoare_ite_requests_append (c := 3) (by omega) wra _ _)
                                  (TerminatingProgBoundedOn.decCall_on hpcs (ofString "o4") .one _
                                    (callEntryOn_of_imp localsFree_worldOK (fun _ h => reqState_worldOK h) _ _)
                                    (resumeOn_process_checked_sys_tx (c := 4) wpcs _ _)
                                    (TerminatingProgBoundedOn.seq_guestInv_after
                                      (hite_ra_bound 4 _ _)
                                      (fun _ h => reqState_guestInv h)
                                      (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))))))))))))))
      state hcode hRF)
    (by
      unfold K.«process_general_purpose_requests»
      simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]
      omega)
    hnt

/-! ## 7. Proof 3: `gbody_process_unchecked_system_transaction` -/

theorem lookup_state_fresh_tx_fn :
    originalRuntimeCode.lookup (ofString "state_fresh_tx") =
      some ((sourceFunctionEntry Guest.Software.guestFn_state_fresh_tx).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 355 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_state_fresh_tx) rfl

theorem lookup_ext_code_of_fn :
    originalRuntimeCode.lookup (ofString "ext_code_of") =
      some ((sourceFunctionEntry Guest.Software.guestFn_ext_code_of).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 543 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ext_code_of) rfl

theorem lookup_te_new_fn :
    originalRuntimeCode.lookup (ofString "te_new") =
      some ((sourceFunctionEntry Guest.Software.guestFn_te_new).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 869 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_te_new) rfl

theorem lookup_msg_new_fn :
    originalRuntimeCode.lookup (ofString "msg_new") =
      some ((sourceFunctionEntry Guest.Software.guestFn_msg_new).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 465 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_msg_new) rfl

theorem callee_param_zero {F : Type} (state : PanSemStateFiniteExact 64 F) (fname : MlS)
    (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([], body, ret))
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    values = [] ∧ body' = body ∧ ret' = ret := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, Option.some.injEq] at hargs
  subst hargs
  exact ⟨rfl,
    lookupCodeHOLFinite_installed_body state.code.lookup fname [] body body' ret ret' [] callee hl hlook,
    lookupCodeHOLFinite_installed_return state fname [] body body' ret ret' [] callee hl hlook⟩

/-- Word-shaped entry parameters and global buffers read by inline stores in
`process_unchecked_system_transaction`. All actual callers (`execute_block`,
`process_checked_system_transaction`) pass 1-word values and run after `mem_init`/`fork_init`
where every global holds a word (`GlobalWord`). -/
def WordSysTxArgs {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (∃ w : BitVec 64, s.locals.lookup (ofString "target") = some (.val (.word w))) ∧
  (∃ w : BitVec 64, s.locals.lookup (ofString "data") = some (.val (.word w))) ∧
  (∃ w : BitVec 64, s.locals.lookup (ofString "data_n") = some (.val (.word w))) ∧
  (∃ w : BitVec 64, s.globals.lookup (ofString "vm_system_address") = some (.val (.word w))) ∧
  (∃ w : BitVec 64, s.globals.lookup (ofString "be") = some (.val (.word w)))

/-- WorldOK together with word-shaped locals `target`, `data`, `data_n` and word-shaped globals
`vm_system_address`, `be`. -/
def SysTxEntry : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ WordSysTxArgs s

theorem sysTxEntry_worldOK {F : Type} {s : PanSemStateFiniteExact 64 F} (h : SysTxEntry s) : WorldOK s :=
  h.1

theorem sysTxEntry_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : SysTxEntry s) : GuestInv s :=
  h.1.1.1

theorem localsOnly_sysTxEntry : LocalsOnly ["target", "data", "data_n"] SysTxEntry := by
  intro F s locals k hl ⟨hW, ⟨ht, hd, hdn, hvsa, hbe⟩⟩
  refine ⟨localsFree_worldOK s locals k hW, ?_, ?_, ?_, hvsa, hbe⟩
  · obtain ⟨w, hw⟩ := ht; exact ⟨w, (hl "target" (by simp)).trans hw⟩
  · obtain ⟨w, hw⟩ := hd; exact ⟨w, (hl "data" (by simp)).trans hw⟩
  · obtain ⟨w, hw⟩ := hdn; exact ⟨w, (hl "data_n" (by simp)).trans hw⟩

theorem wordSysTxArgs_preserved_of_globalsKept {gw : List String} {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    (hG : GlobalsKept gw (callEntryStateHOLFinite s callee) post)
    (hvsa_notin : ofString "vm_system_address" ∉ gw.map ofString)
    (hbe_notin : ofString "be" ∉ gw.map ofString)
    (hargs : WordSysTxArgs s) :
    WordSysTxArgs { post with locals := s.locals } := by
  obtain ⟨ht, hd, hdn, ⟨wv, hwv⟩, ⟨wb, hwb⟩⟩ := hargs
  refine ⟨ht, hd, hdn, ⟨wv, ?_⟩, ⟨wb, ?_⟩⟩
  · dsimp only; rw [← hG (ofString "vm_system_address") hvsa_notin]; exact hwv
  · dsimp only; rw [← hG (ofString "be") hbe_notin]; exact hwb

/-- After `te_new` and stores into `te`: `SysTxEntry` plus `te` is a 200-byte heap block disjoint from `worldOwned`. -/
def SysTxAfterTe : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_te : BitVec 64, ∃ S Nd : List Nat,
    WorldTypedWith s S Nd ∧
    ArenaReady s ∧
    WordSysTxArgs s ∧
    s.locals.lookup (ofString "te") = some (.val (.word w_te)) ∧
    w_te.toNat % 8 = 0 ∧
    Inside (w_te.toNat, 200) sourceBase (globN s "heap_ptr") ∧
    IvlsDisj [(w_te.toNat, 200)] (worldOwned s S Nd)

theorem sysTxAfterTe_sysTxEntry {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : SysTxAfterTe s) : SysTxEntry s := by
  obtain ⟨_, S, Nd, hWT, hA, hargs, _⟩ := h
  exact ⟨⟨hA, S, (worldTyped_iff_with s S).2 ⟨Nd, hWT⟩⟩, hargs⟩

theorem sysTxAfterTe_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : SysTxAfterTe s) : GuestInv s :=
  (sysTxAfterTe_sysTxEntry h).1.1.1

theorem resumeOn_te_new
    (wte : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ w => [(w, 200)])) (ofString "te_new"))
    (rtte : Returns ArenaReady (fun s post m => FreshBlock s post m 200 ∧
      ∀ k, k < 25 → memW post (m + 8 * k) = 0) (ofString "te_new")) :
    DecCallResumeOn SysTxEntry SysTxAfterTe (ofString "te") (ofString "te_new") [] := by
  intro F state values body callee ret value post hcode ⟨hW, hargs_w⟩ _ hl hrun
  obtain ⟨hAs, S, hS⟩ := hW
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with state S).1 hS
  have hstep := FunSpec.at_lookup wte state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) ⟨hAs, S, hS⟩) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  obtain ⟨hAp, _, hG, _, hWS⟩ := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtte state hcode values body callee ret hl
    (localsFree_arenaReady state callee (state.clock - 1) hAs) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_te, rfl, _, _, hfb, _⟩ := hrt value rfl
  obtain ⟨S', Nd', _, hWT', _, _, hQ⟩ :=
    hWS S Nd ((worldTypedWith_with_locals _ _ _ _ _).2 hWT) (fun x hx => by simp at hx)
  obtain ⟨w_te', hw_eq, hav⟩ := hQ (.val (.word w_te)) rfl
  injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
  have hargs_post := wordSysTxArgs_preserved_of_globalsKept hG (by simp; decide) (by simp; decide) hargs_w
  set resumed := setVarHOLFinite (ofString "te") (.val (.word w_te)) { post with locals := state.locals }
  refine ⟨w_te, S', Nd',
    (worldTypedWith_with_locals post _ post.clock S' Nd').2 hWT',
    localsFree_arenaReady post _ post.clock hAp,
    ?_, ?_, hfb.1, ⟨Nat.le_trans hAs.2.1 hfb.2.1.1, hfb.2.1.2⟩, hav⟩
  · obtain ⟨⟨wt, hwt⟩, ⟨wd, hwd⟩, ⟨wdn, hwdn⟩, hvsa, hbe⟩ := hargs_post
    refine ⟨⟨wt, ?_⟩, ⟨wd, ?_⟩, ⟨wdn, ?_⟩, hvsa, hbe⟩
    · have hne : ofString "te" ≠ ofString "target" := by decide
      simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]; exact hwt
    · have hne : ofString "te" ≠ ofString "data" := by decide
      simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]; exact hwd
    · have hne : ofString "te" ≠ ofString "data_n" := by decide
      simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]; exact hwdn
  · simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem evalAt_load_comb4_len {F : Type} {s : PanSemStateFiniteExact 64 F}
    {addr : ExpHOL 64} {v : ValueHOL 64}
    (hev : evalAt s (.load (.comb [.one, .one, .one, .one]) addr) = some v) :
    (flattenHOL v).length = 4 := by
  simp only [evalAt, evalHOLExact] at hev
  split_ifs at hev with hwf
  rcases ha : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addr with _ | va
  · rw [ha] at hev; simp at hev
  · rw [ha] at hev
    cases va with
    | rStruct _ => simp at hev
    | nStruct _ => simp at hev
    | val wl =>
      cases wl with
      | word a =>
        dsimp only at hev
        have hone : ∀ {b : BitVec 64} {v1 : ValueHOL 64},
            @memLoadHOLExact 64 _ .one b s.memaddrs (fun x => Classical.propDecidable (s.memaddrs x))
              s.memory s.structs = some v1 → (flattenHOL v1).length = 1 := by
          intro b v1 h1
          unfold memLoadHOLExact at h1
          split_ifs at h1
          simp only [Option.some.injEq] at h1
          subst h1
          simp [flattenHOL]
        unfold memLoadHOLExact at hev
        rcases hm0 : @memLoadsHOLExact 64 _ [.one, .one, .one, .one] a s.memaddrs
            (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | vs0
        · rw [hm0] at hev; simp at hev
        · rw [hm0] at hev
          simp only [Option.some.injEq] at hev
          subst hev
          unfold memLoadsHOLExact at hm0
          rcases hl1 : @memLoadHOLExact 64 _ .one a s.memaddrs
              (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | v1
          · rw [hl1] at hm0; simp at hm0
          · rw [hl1] at hm0
            rcases hm1 : @memLoadsHOLExact 64 _ [.one, .one, .one] _ s.memaddrs
                (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | vs1
            · rw [hm1] at hm0; simp at hm0
            · rw [hm1] at hm0
              simp only [Option.some.injEq] at hm0
              subst hm0
              unfold memLoadsHOLExact at hm1
              rcases hl2 : @memLoadHOLExact 64 _ .one _ s.memaddrs
                  (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | v2
              · rw [hl2] at hm1; simp at hm1
              · rw [hl2] at hm1
                rcases hm2 : @memLoadsHOLExact 64 _ [.one, .one] _ s.memaddrs
                    (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | vs2
                · rw [hm2] at hm1; simp at hm1
                · rw [hm2] at hm1
                  simp only [Option.some.injEq] at hm1
                  subst hm1
                  unfold memLoadsHOLExact at hm2
                  rcases hl3 : @memLoadHOLExact 64 _ .one _ s.memaddrs
                      (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | v3
                  · rw [hl3] at hm2; simp at hm2
                  · rw [hl3] at hm2
                    rcases hm3 : @memLoadsHOLExact 64 _ [.one] _ s.memaddrs
                        (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | vs3
                    · rw [hm3] at hm2; simp at hm2
                    · rw [hm3] at hm2
                      simp only [Option.some.injEq] at hm2
                      subst hm2
                      unfold memLoadsHOLExact at hm3
                      rcases hl4 : @memLoadHOLExact 64 _ .one _ s.memaddrs
                          (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | v4
                      · rw [hl4] at hm3; simp at hm3
                      · rw [hl4] at hm3
                        rcases hm4 : @memLoadsHOLExact 64 _ [] _ s.memaddrs
                            (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | vs4
                        · rw [hm4] at hm3; simp at hm3
                        · rw [hm4] at hm3
                          simp only [Option.some.injEq] at hm3
                          subst hm3
                          unfold memLoadsHOLExact at hm4
                          simp only [Option.some.injEq] at hm4
                          subst hm4
                          have c1 := hone hl1
                          have c2 := hone hl2
                          have c3 := hone hl3
                          have c4 := hone hl4
                          conv_lhs => unfold flattenHOL
                          simp [c1, c2, c3, c4]

theorem store_in_block_preserves_worldTypedWith {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {base sz off : Nat} {w_base x : BitVec 64} {v : ValueHOL 64}
    {mem' : BitVec 64 → HolWordLab 64}
    (hWT : WorldTypedWith s S Nd) (hAs : ArenaReady s)
    (hbase_lu : w_base.toNat = base)
    (hbase8 : base % 8 = 0) (hsz8 : sz % 8 = 0) (hoff8 : off % 8 = 0)
    (hin_blk : Inside (base, sz) sourceBase (globN s "heap_ptr"))
    (hdisj_blk : IvlsDisj [(base, sz)] (worldOwned s S Nd))
    (hx_eq : x = w_base + BitVec.ofNat 64 off)
    (hoff_fit : off + 8 * (flattenHOL v).length ≤ sz)
    (hst : @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem') :
    ArenaReady { s with memory := mem' } ∧
    WorldTypedWith { s with memory := mem' } S Nd ∧
    worldOwned { s with memory := mem' } S Nd = worldOwned s S Nd ∧
    worldRoleSlots { s with memory := mem' } = worldRoleSlots s ∧
    journalRoleSlots { s with memory := mem' } = journalRoleSlots s ∧
    (∀ t ∈ S, hdr { s with memory := mem' } t 0 = hdr s t 0) := by
  have h264 : heapEnd < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hx_nat : x.toNat = base + off := by
    rw [hx_eq, BitVec.toNat_add, hbase_lu, BitVec.toNat_ofNat]
    have hoff_lt : off < 2 ^ 64 := by unfold Inside at hin_blk; omega
    rw [Nat.mod_eq_of_lt hoff_lt]
    exact Nat.mod_eq_of_lt (by unfold Inside at hin_blk; omega)
  have hframe : FrameOutside s { s with memory := mem' } [(base, sz)] (0, 0) := by
    intro a hkeep _
    apply panMemStoresHOL_frame (flattenHOL v) x s.memory mem' hst a
    intro k hk h_eq
    apply hkeep (base, sz) (by simp)
    have ha_nat : a.toNat = base + off + 8 * k := by
      rw [h_eq, BitVec.toNat_add, hx_nat, BitVec.toNat_ofNat]
      have hk_lt : 8 * k < 2 ^ 64 := by unfold Inside at hin_blk; omega
      rw [Nat.mod_eq_of_lt hk_lt]
      exact Nat.mod_eq_of_lt (by unfold Inside at hin_blk; omega)
    unfold CellHits
    rw [ha_nat]
    exact ⟨by omega, by omega⟩
  exact worldTypedWith_store_range_disj (post := { s with memory := mem' }) hAs hbase8 hsz8 hin_blk.1
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, hframe⟩ hWT
    (fun j hj => (hdisj_blk (base, sz) (by simp) j (worldTypedIvls_sub_worldOwned _ _ _ j hj)).flip)

theorem hoare_call_state_fresh_tx
    (wsf : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr", "journal_n", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "state_fresh_tx")) :
    Hoare SysTxEntry (.call (some (none, none)) (ofString "state_fresh_tx") [])
      (fun r t => r = none → SysTxEntry t) := by
  refine Hoare.call0 wsf
    (callEntryOn_of_imp localsFree_worldOK (fun _ h => h.1) _ _)
    (fun s callee post v _ ⟨hW, hargs⟩ hq _ => ?_)
    (fun _ _ hr _ h => absurd h hr)
  have hws := hq (Or.inl ⟨v, rfl⟩)
  exact ⟨localsFree_worldOK post s.locals post.clock (hws.worldOK_nil (localsFree_worldOK s callee (s.clock - 1) hW)),
    wordSysTxArgs_preserved_of_globalsKept hws.2.2.1 (by simp; decide) (by simp; decide) hargs⟩

theorem resumeOn_ext_code_of_sysTx
    (wext : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "ext_code_of")) :
    DecCallResumeOn SysTxEntry SysTxEntry (ofString "code") (ofString "ext_code_of")
      [.var .local (ofString "target")] := by
  intro F state values body callee ret value post hcode ⟨hW, hargs⟩ _ hl hrun
  obtain ⟨hAs, S, hS⟩ := hW
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with state S).1 hS
  have hstep := FunSpec.at_lookup wext state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) ⟨hAs, S, hS⟩) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hW_post : WorldOK post := by
    apply hws.worldOK
    refine ⟨S, Nd, (worldTypedWith_with_locals _ _ _ _ _).2 hWT, ?_⟩
    intro i hi j hj
    change i ∈ [bufferRegion state ("keccak_pad", 136), bufferRegion state ("keccak_st", 200),
      bufferRegion state ("mpt_nib_scratch", 64), bufferRegion state ("sk_buf", 52)] at hi
    change j ∈ worldTypedIvls state S Nd at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact bufferRegion_disj_le hWT ("keccak_pad", 136) (by decide) (by decide) 136 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("keccak_st", 200) (by decide) (by decide) 200 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("mpt_nib_scratch", 64) (by decide) (by decide) 64 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("sk_buf", 64) (by decide) (by decide) 52 (by decide) j hj
  have hargs_post := wordSysTxArgs_preserved_of_globalsKept hws.2.2.1 (by simp; decide) (by simp; decide) hargs
  exact localsOnly_sysTxEntry.setVar (by simp; decide) value _
    ⟨localsFree_worldOK post state.locals post.clock hW_post, hargs_post⟩

theorem evalAt_add_local_const {F : Type} {s : PanSemStateFiniteExact 64 F}
    {name : MlS} {w : BitVec 64} {off : Nat} {x : BitVec 64}
    (hl : s.locals.lookup name = some (.val (.word w)))
    (hev : evalAt s (.op .add [.var .local name, .const (BitVec.ofNat 64 off)]) = some (.val (.word x))) :
    x = w + BitVec.ofNat 64 off := by
  simp only [evalAt, evalHOLExact, evalListHOLExact, hl, valueIsWord, valueWord,
    wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
    Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hev
  rw [← hev]
  simp [BitVec.add_zero]

theorem evalAt_word_src_len_le_one {F : Type} {s : PanSemStateFiniteExact 64 F}
    {src : ExpHOL 64} {v : ValueHOL 64}
    (hsrc : (∃ w : BitVec 64, evalAt s src = some (.val (.word w))) ∨
      (∀ u : ValueHOL 64, evalAt s src = some u → (flattenHOL u).length ≤ 1))
    (hev : evalAt s src = some v) :
    (flattenHOL v).length ≤ 1 := by
  rcases hsrc with ⟨w, hw⟩ | hlen
  · rw [hev] at hw; injection hw with hw'; subst hw'; simp [flattenHOL]
  · exact hlen v hev

theorem evalAt_rfield_len_le_one {F : Type} {s : PanSemStateFiniteExact 64 F}
    {idx : Nat} { v : ValueHOL 64 }
    (hcode_sh : ∀ vc, s.locals.lookup (ofString "code") = some vc →
      shapeEqHOL (shapeOfHOLExact vc) (.comb [.one, .one]) = true) :
    evalAt s (.rfield idx (.var .local (ofString "code"))) = some v →
    (flattenHOL v).length ≤ 1 := by
  intro hev
  simp only [evalAt, evalHOLExact] at hev
  rcases hc : s.locals.lookup (ofString "code") with _ | vc
  · rw [hc] at hev; simp at hev
  · rw [hc] at hev
    have hsh := (shapeEqHOL_eq_true _ _).1 (hcode_sh vc hc)
    cases vc with
    | val _ => simp [shapeOfHOLExact] at hsh
    | nStruct _ _ => simp [shapeOfHOLExact] at hsh
    | rStruct vs =>
      simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh
      rcases vs with _ | ⟨v0, _ | ⟨v1, _ | _⟩⟩ <;> simp at hsh
      rcases hsh with ⟨hv0, hv1⟩
      have hone_len : ∀ u : ValueHOL 64, shapeOfHOLExact u = .one → (flattenHOL u).length ≤ 1 := by
        intro u hu
        cases u with
        | val wl => cases wl; simp [flattenHOL]
        | rStruct _ => simp [shapeOfHOLExact] at hu
        | nStruct _ _ => simp [shapeOfHOLExact] at hu
      rcases idx with _ | ⟨_ | _⟩
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hev; subst hev; exact hone_len v0 hv0
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hev
        subst hev; exact hone_len v1 hv1
      · simp at hev

/-- Re-include local `"code"` having shape `.comb [.one, .one]` in `SysTxEntry` after `ext_code_of`! -/
def SysTxEntryCode : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => SysTxEntry s ∧
    ∃ a b : BitVec 64, s.locals.lookup (ofString "code") = some (.rStruct [.val (.word a), .val (.word b)])

theorem sysTxEntryCode_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : SysTxEntryCode s) : GuestInv s :=
  sysTxEntry_guestInv h.1

theorem resumeOn_ext_code_of_sysTxCode
    (wext : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "ext_code_of")) :
    ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
      (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
      (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode → SysTxEntry state →
      evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        [.var .local (ofString "target")] = some values →
      lookupCodeHOLFinite state.code.lookup (ofString "ext_code_of") values = some (body, callee, returnShape) →
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (some (.returned value), post) →
      shapeEqHOL (shapeOfHOLExact value) (.comb [.one, .one]) = true →
      SysTxEntryCode (setVarHOLFinite (ofString "code") value { post with locals := state.locals }) := by
  intro F state values body callee ret value post hcode hP hargs hl hrun hsh
  have hbase := resumeOn_ext_code_of_sysTx wext state values body callee ret value post hcode hP hargs hl hrun
  have hsh_eq := (shapeEqHOL_eq_true _ _).1 hsh
  cases value with
  | val _ => simp [shapeOfHOLExact] at hsh_eq
  | nStruct _ _ => simp [shapeOfHOLExact] at hsh_eq
  | rStruct vs =>
    simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh_eq
    rcases vs with _ | ⟨v0, _ | ⟨v1, _ | _⟩⟩ <;> simp at hsh_eq
    rcases hsh_eq with ⟨hv0, hv1⟩
    cases v0 with
    | rStruct _ => simp [shapeOfHOLExact] at hv0
    | nStruct _ _ => simp [shapeOfHOLExact] at hv0
    | val wl0 =>
      cases wl0 with
      | word a =>
        cases v1 with
        | rStruct _ => simp [shapeOfHOLExact] at hv1
        | nStruct _ _ => simp [shapeOfHOLExact] at hv1
        | val wl1 =>
          cases wl1 with
          | word b =>
            exact ⟨hbase, a, b, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩

/-- Variant of `decCall_on` whose continuation guard may also use the `decCall` shape check
`shapeEqHOL (shapeOfHOLExact value) shape = true`! -/
theorem decCall_on_shaped
    {P Pc Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {B Bc : Nat}
    (hf : TerminatingFunBoundedOn Pc fname B)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {continuation : ProgHOL 64}
    (hentry : CallEntryOn P Pc fname arguments)
    (hres : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
      (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
      (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode → P state →
      evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        arguments = some values →
      lookupCodeHOLFinite state.code.lookup fname values = some (body, callee, returnShape) →
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
        (some (.returned value), post) →
      shapeEqHOL (shapeOfHOLExact value) shape = true →
      Q (setVarHOLFinite name value { post with locals := state.locals }))
    (hcont : TerminatingProgBoundedOn Q continuation Bc) :
    TerminatingProgBoundedOn P (.decCall name shape fname arguments continuation) (B + Bc + 1) := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hf
  intro F state hcode hP hnt
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    _ | values
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · simp only [hl] at hnt ⊢
      obtain ⟨hbb, hrunBound⟩ := callee_body_bound hlook hbody hentry state hcode hP values body'
        callee ret' hargs hl
      subst hbb
      by_cases hz : state.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee)
          body').1
        have hresQ := hres state values body' callee ret'
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt hmeta ⊢
        change post.code = state.code at hmeta
        have bodyClock (hsafe : res ≠ some .timeOut) :
            state.clock - 1 ≤ post.clock + B ∧ post.clock ≤ state.clock - 1 := by
          have hb := hrunBound (by rw [hrun]; exact hsafe)
          rw [hrun] at hb
          exact hb
        cases res with
        | none =>
          obtain ⟨hs, hk⟩ := bodyClock (by simp)
          exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
        | some r =>
          cases r with
          | returned value =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact value) shape &&
                shapeEqHOL (shapeOfHOLExact value) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt ⊢
              set resumed := setVarHOLFinite name value { post with locals := state.locals }
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              have hsh1 : shapeEqHOL (shapeOfHOLExact value) shape = true := (Bool.and_eq_true _ _ ▸ hsh).1
              have hresInv : Q resumed := hresQ value post hcode hP hargs hl hrun hsh1
              obtain ⟨hsc, hkc⟩ := hcont resumed hresCode hresInv hnt
              change post.clock ≤ (evaluateHOLFiniteState resumed continuation).2.clock + Bc at hsc
              change (evaluateHOLFiniteState resumed continuation).2.clock ≤ post.clock at hkc
              exact ⟨by omega, by omega⟩
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
              exact ⟨by omega, by omega⟩
          | timeOut => simp at hnt
          | «break» =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | «continue» =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | _ =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩

def SysTxAfterTeCode : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => SysTxAfterTe s ∧
    ∃ a b : BitVec 64, s.locals.lookup (ofString "code") = some (.rStruct [.val (.word a), .val (.word b)])

theorem sysTxAfterTeCode_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : SysTxAfterTeCode s) : GuestInv s :=
  sysTxAfterTe_guestInv h.1

theorem resumeOn_te_new_code
    (wte : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ w => [(w, 200)])) (ofString "te_new"))
    (rtte : Returns ArenaReady (fun s post m => FreshBlock s post m 200 ∧
      ∀ k, k < 25 → memW post (m + 8 * k) = 0) (ofString "te_new")) :
    DecCallResumeOn SysTxEntryCode SysTxAfterTeCode (ofString "te") (ofString "te_new") [] := by
  intro F state values body callee ret value post hcode ⟨hP, a, b, hcode_lu⟩ hargs hl hrun
  refine ⟨resumeOn_te_new wte rtte state values body callee ret value post hcode hP hargs hl hrun, a, b, ?_⟩
  have hne : ofString "te" ≠ ofString "code" := by decide
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hcode_lu]

theorem hoare_store_te
    (off : Nat) (hoff8 : off % 8 = 0) (src : ExpHOL 64)
    (hlen : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      SysTxAfterTeCode s → evalAt s src = some v → off + 8 * (flattenHOL v).length ≤ 200) :
    Hoare SysTxAfterTeCode
      (.store (.op .add [.var .local (ofString "te"), .const (BitVec.ofNat 64 off)]) src)
      (fun r t => r = none → SysTxAfterTeCode t) := by
  apply Hoare.store_fall
  intro F s x v mem' hS hx hv hst
  have hfit := hlen s v hS hv
  obtain ⟨⟨w_te, S, Nd, hWT, hAs, hargs, hte_lu, hte8, hin_te, hdisj_te⟩, a, b, hcode_lu⟩ := hS
  have hx_eq := evalAt_add_local_const hte_lu hx
  obtain ⟨hAp, hWT', howned', _, _, _⟩ :=
    store_in_block_preserves_worldTypedWith hWT hAs rfl hte8 (by omega) hoff8 hin_te hdisj_te hx_eq hfit hst
  exact ⟨⟨w_te, S, Nd, hWT', hAp, hargs, hte_lu, hte8, hin_te, by rw [howned']; exact hdisj_te⟩, a, b, hcode_lu⟩

/-- After `msg_new`: `m` is a 176-byte heap block disjoint from `worldOwned`, and once `m+40 := 30000000`
is stored, `hasGas` tracks `memW s (m + 40) < 2 ^ 63`. -/
def SysTxAfterMsg (hasGas : Bool) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_m a b : BitVec 64, ∃ S Nd : List Nat,
    WorldTypedWith s S Nd ∧
    ArenaReady s ∧
    WordSysTxArgs s ∧
    (∃ w_te : BitVec 64, s.locals.lookup (ofString "te") = some (.val (.word w_te))) ∧
    s.locals.lookup (ofString "code") = some (.rStruct [.val (.word a), .val (.word b)]) ∧
    s.locals.lookup (ofString "m") = some (.val (.word w_m)) ∧
    w_m.toNat % 8 = 0 ∧
    Inside (w_m.toNat, 176) sourceBase (globN s "heap_ptr") ∧
    IvlsDisj [(w_m.toNat, 176)] (worldOwned s S Nd) ∧
    (hasGas = true → memW s (w_m.toNat + 40) < 2 ^ 63)

theorem sysTxAfterMsg_guestInv {hasGas : Bool} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : SysTxAfterMsg hasGas s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, hA, _⟩ := h
  exact hA.1

theorem resumeOn_msg_new
    (wmsg : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ w => [(w, 176)])) (ofString "msg_new"))
    (rtmsg : Returns ArenaReady (fun s post m => FreshBlock s post m 176 ∧
      ∀ k, k < 22 → memW post (m + 8 * k) = 0) (ofString "msg_new")) :
    DecCallResumeOn SysTxAfterTeCode (SysTxAfterMsg false) (ofString "m") (ofString "msg_new") [] := by
  intro F state values body callee ret value post hcode ⟨⟨w_te, S, Nd, hWT, hAs, hargs_w, hte_lu, _, _, _⟩, a, b, hcode_lu⟩ _ hl hrun
  have hstep := FunSpec.at_lookup wmsg state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hWT⟩⟩)
    (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  obtain ⟨hAp, _, hG, _, hWS⟩ := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtmsg state hcode values body callee ret hl
    (localsFree_arenaReady state callee (state.clock - 1) hAs) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_m, rfl, _, _, hfb, _⟩ := hrt value rfl
  obtain ⟨S', Nd', _, hWT', _, _, hQ⟩ :=
    hWS S Nd ((worldTypedWith_with_locals _ _ _ _ _).2 hWT) (fun x hx => by simp at hx)
  obtain ⟨w_m', hw_eq, hav⟩ := hQ (.val (.word w_m)) rfl
  injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
  have hargs_post := wordSysTxArgs_preserved_of_globalsKept hG (by simp; decide) (by simp; decide) hargs_w
  set resumed := setVarHOLFinite (ofString "m") (.val (.word w_m)) { post with locals := state.locals }
  refine ⟨w_m, a, b, S', Nd',
    (worldTypedWith_with_locals post _ post.clock S' Nd').2 hWT',
    localsFree_arenaReady post _ post.clock hAp,
    ?_, ?_, ?_, ?_, hfb.1, ⟨Nat.le_trans hAs.2.1 hfb.2.1.1, hfb.2.1.2⟩, hav, fun h => by cases h⟩
  · obtain ⟨⟨wt, hwt⟩, ⟨wd, hwd⟩, ⟨wdn, hwdn⟩, hvsa, hbe⟩ := hargs_post
    refine ⟨⟨wt, ?_⟩, ⟨wd, ?_⟩, ⟨wdn, ?_⟩, hvsa, hbe⟩
    · have hne : ofString "m" ≠ ofString "target" := by decide
      simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]; exact hwt
    · have hne : ofString "m" ≠ ofString "data" := by decide
      simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]; exact hwd
    · have hne : ofString "m" ≠ ofString "data_n" := by decide
      simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]; exact hwdn
  · refine ⟨w_te, ?_⟩
    have hne : ofString "m" ≠ ofString "te" := by decide
    simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hte_lu]
  · have hne : ofString "m" ≠ ofString "code" := by decide
    simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hcode_lu]
  · simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem hoare_store_msg_other
    {hasGas : Bool} (off : Nat) (hoff8 : off % 8 = 0) (hoff_ne40 : hasGas = true → off ≠ 40)
    (src : ExpHOL 64)
    (hlen : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      SysTxAfterMsg hasGas s → evalAt s src = some v → (flattenHOL v).length = 1)
    (hoff_lt : off + 8 ≤ 176) :
    Hoare (SysTxAfterMsg hasGas)
      (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 off)]) src)
      (fun r t => r = none → SysTxAfterMsg hasGas t) := by
  apply Hoare.store_fall
  intro F s x v mem' hM hx hv hst
  have hv_len := hlen s v hM hv
  obtain ⟨w_m, a, b, S, Nd, hWT, hAs, hargs, hte, hcode_lu, hm_lu, hm8, hin_m, hdisj_m, hgas⟩ := hM
  have hx_eq := evalAt_add_local_const hm_lu hx
  obtain ⟨hAp, hWT', howned', _, _, _⟩ :=
    store_in_block_preserves_worldTypedWith hWT hAs rfl hm8 (by omega) hoff8 hin_m hdisj_m hx_eq
      (by rw [hv_len]; omega) hst
  refine ⟨w_m, a, b, S, Nd, hWT', hAp, hargs, hte, hcode_lu, hm_lu, hm8, hin_m,
    by rw [howned']; exact hdisj_m, fun hg => ?_⟩
  have hne40 := hoff_ne40 hg
  have h264 : heapEnd < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hm40_eq : memW ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) (w_m.toNat + 40) =
      memW s (w_m.toNat + 40) := by
    unfold memW
    dsimp only
    rw [panMemStoresHOL_frame (flattenHOL v) x s.memory mem' hst (BitVec.ofNat 64 (w_m.toNat + 40)) ?_]
    intro k hk h_eq
    rw [hv_len] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    have hoff_lt264 : off < 2 ^ 64 := by omega
    have hlhs : (BitVec.ofNat 64 (w_m.toNat + 40)).toNat = w_m.toNat + 40 := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by unfold Inside at hin_m; omega)
    have hrhs : (x + BitVec.ofNat 64 (8 * 0)).toNat = w_m.toNat + off := by
      rw [hx_eq, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hoff_lt264, Nat.mod_eq_of_lt (by unfold Inside at hin_m; omega)]
    have := congrArg BitVec.toNat h_eq
    omega
  rw [hm40_eq]
  exact hgas hg

theorem hoare_store_msg_gas :
    Hoare (SysTxAfterMsg false)
      (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 40)])
        (.const (BitVec.ofNat 64 30000000)))
      (fun r t => r = none → SysTxAfterMsg true t) := by
  apply Hoare.store_fall
  intro F s x v mem' hM hx hv hst
  obtain ⟨w_m, a, b, S, Nd, hWT, hAs, hargs, hte, hcode_lu, hm_lu, hm8, hin_m, hdisj_m, _⟩ := hM
  have hx_eq := evalAt_add_local_const hm_lu hx
  have hv_eq := evalAt_const s (BitVec.ofNat 64 30000000) v hv
  subst hv_eq
  obtain ⟨hAp, hWT', howned', _, _, _⟩ :=
    store_in_block_preserves_worldTypedWith hWT hAs rfl hm8 (by omega) (by omega) hin_m hdisj_m hx_eq
      (by simp [flattenHOL]) hst
  refine ⟨w_m, a, b, S, Nd, hWT', hAp, hargs, hte, hcode_lu, hm_lu, hm8, hin_m,
    by rw [howned']; exact hdisj_m, fun _ => ?_⟩
  have hfl : flattenHOL (.val (.word (BitVec.ofNat 64 30000000)) : ValueHOL 64) =
      [.word (BitVec.ofNat 64 30000000)] := by unfold flattenHOL; rfl
  rw [hfl] at hst
  have hst_w := panMemStoresHOL_word_spec (s := s) (x := x) (w := .word (BitVec.ofNat 64 30000000)) hst
  have h264 : heapEnd < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have h40_lt : 40 < 2 ^ 64 := by decide
  have hbv_eq : BitVec.ofNat 64 (w_m.toNat + 40) = x := by
    apply BitVec.eq_of_toNat_eq
    rw [hx_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold Inside at hin_m; omega),
      BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h40_lt,
      Nat.mod_eq_of_lt (by unfold Inside at hin_m; omega)]
  unfold memW
  dsimp only
  rw [hbv_eq, hst_w.2.1]
  decide

/-- After `aa := htab_new(20, 8)`: `aa` is in `S`, `hdr s aa 0 = 20`, local to world/journal. -/
def SysTxAfterAa (stored : Bool) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_m w_aa : BitVec 64, ∃ S Nd : List Nat,
    WorldTypedWith s S Nd ∧
    ArenaReady s ∧
    s.locals.lookup (ofString "m") = some (.val (.word w_m)) ∧
    s.locals.lookup (ofString "aa") = some (.val (.word w_aa)) ∧
    w_m.toNat % 8 = 0 ∧
    Inside (w_m.toNat, 176) sourceBase (globN s "heap_ptr") ∧
    IvlsDisj [(w_m.toNat, 176)] (worldOwned s S Nd) ∧
    memW s (w_m.toNat + 40) < 2 ^ 63 ∧
    w_aa.toNat ∈ S ∧
    hdr s w_aa.toNat 0 = 20 ∧
    (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ w_aa.toNat) ∧
    (stored = true → memW s (w_m.toNat + 152) = w_aa.toNat)

theorem sysTxAfterAa_guestInv {stored : Bool} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : SysTxAfterAa stored s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, hA, _⟩ := h
  exact hA.1

theorem resumeOn_htab_new_aa
    (hnspec : type_of% @htab_new_spec) :
    DecCallResumeOn (SysTxAfterMsg true) (SysTxAfterAa false) (ofString "aa") (ofString "htab_new")
      [.const (BitVec.ofNat 64 20), .const (BitVec.ofNat 64 8)] := by
  intro F state values body callee ret value post hcode hM hargs hl hrun
  obtain ⟨w_m, _, _, S, Nd, hWT, hAs, _, _, _, hm_lu, hm8, hin_m, hdisj_m, hgas⟩ := hM
  have hpc := callee_param_two state (ofString "htab_new") (ofString "key_len") (ofString "cap")
    .one .one _ _ (by rw [hcode]; exact lookup_htab_new_fn)
    (.const (BitVec.ofNat 64 20)) (.const (BitVec.ofNat 64 8))
    (.val (.word (BitVec.ofNat 64 20))) (.val (.word (BitVec.ofNat 64 8)))
    values body callee ret rfl rfl hargs hl
  have hkl : locN (callEntryStateHOLFinite state callee) "key_len" = 20 := by
    simp [locN, callEntryStateHOLFinite, hpc.2.1]
  have hcp : locN (callEntryStateHOLFinite state callee) "cap" = 8 := by
    simp [locN, callEntryStateHOLFinite, hpc.2.2]
  have hnr : HtabNewReady (callEntryStateHOLFinite state callee) :=
    ⟨localsFree_arenaReady state callee (state.clock - 1) hAs,
      by rw [hkl]; decide, by rw [hcp]; decide⟩
  have hbe_eq : post.be = state.be := by
    have hm := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
    rw [hrun] at hm; exact hm.2.2.1
  have hout := FunSpec.at_lookup hnspec state hcode values body callee ret hl hnr (by rw [hrun]; simp)
  rw [hrun] at hout; dsimp only at hout
  obtain ⟨w_aa, rfl, hAp, hag, hwf_aa, _, hklen_aa, hfp_aa, hfr, hg_kept⟩ := hout value rfl
  rw [hkl] at hklen_aa
  have hg_kept_s : GlobalsKept ["heap_ptr", "scratch_ptr"] state post := hg_kept
  have hag_s : AllocatorGrows state post := hag
  obtain ⟨_, _, haa_unass, hWT_ext, _, _, _, hb_surv⟩ :=
    worldTypedWith_htab_new hAs hWT hAp hag_s hwf_aa hfp_aa hfr hbe_eq hg_kept_s
  obtain ⟨hin_m', hdisj_m_fn, hunhit_m⟩ :=
    hb_surv (w_m.toNat, 176) hm8 (by omega) hin_m (fun j hj => hdisj_m (w_m.toNat, 176) (by simp) j hj)
  have h264 : heapEnd < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hm40_eq : memW post (w_m.toNat + 40) = memW state (w_m.toNat + 40) :=
    memW_eq_of_ivlUnhit hunhit_m (by omega) (by unfold Inside at hin_m; omega) ⟨by dsimp; omega, by dsimp; omega⟩
  set resumed := setVarHOLFinite (ofString "aa") (.val (.word w_aa)) { post with locals := state.locals }
  have hne : ofString "aa" ≠ ofString "m" := by decide
  refine ⟨w_m, w_aa, S ++ [w_aa.toNat], Nd,
    (worldTypedWith_with_locals post _ post.clock _ Nd).2 hWT_ext,
    localsFree_arenaReady post _ post.clock hAp,
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hm_lu],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    hm8, hin_m',
    fun o ho j hj => by simp only [List.mem_singleton] at ho; subst ho; exact hdisj_m_fn j hj,
    by change memW post (w_m.toNat + 40) < 2 ^ 63; rw [hm40_eq]; exact hgas rfl,
    List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)),
    hklen_aa, haa_unass, fun h => by cases h⟩

theorem hoare_store_msg_aa :
    Hoare (SysTxAfterAa false)
      (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 152)])
        (.var .local (ofString "aa")))
      (fun r t => r = none → SysTxAfterAa true t) := by
  apply Hoare.store_fall
  intro F s x v mem' hM hx hv hst
  obtain ⟨w_m, w_aa, S, Nd, hWT, hAs, hm_lu, haa_lu, hm8, hin_m, hdisj_m, hgas,
    haa_S, haa_klen, haa_unass, _⟩ := hM
  have hx_eq := evalAt_add_local_const hm_lu hx
  have hv_eq : v = .val (.word w_aa) := by
    simp only [evalAt, evalHOLExact, haa_lu, Option.some.injEq] at hv
    exact hv.symm
  subst hv_eq
  obtain ⟨hAp, hWT', howned', hwrs', hjr', hhdr'⟩ :=
    store_in_block_preserves_worldTypedWith hWT hAs rfl hm8 (by omega) (by omega) hin_m hdisj_m hx_eq
      (by simp [flattenHOL]) hst
  have hfl : flattenHOL (.val (.word w_aa) : ValueHOL 64) = [.word w_aa] := by unfold flattenHOL; rfl
  rw [hfl] at hst
  have hst_w := panMemStoresHOL_word_spec (s := s) (x := x) (w := .word w_aa) hst
  have h264 : heapEnd < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have h152_lt : 152 < 2 ^ 64 := by decide
  have hm40_eq : memW ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) (w_m.toNat + 40) =
      memW s (w_m.toNat + 40) := by
    unfold memW; dsimp only
    rw [hst_w.2.2]
    intro heq
    have hlhs : (BitVec.ofNat 64 (w_m.toNat + 40)).toNat = w_m.toNat + 40 := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by unfold Inside at hin_m; omega)
    have hrhs : x.toNat = w_m.toNat + 152 := by
      rw [hx_eq, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h152_lt,
        Nat.mod_eq_of_lt (by unfold Inside at hin_m; omega)]
    have := congrArg BitVec.toNat heq; omega
  have hbv152 : BitVec.ofNat 64 (w_m.toNat + 152) = x := by
    apply BitVec.eq_of_toNat_eq
    rw [hx_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold Inside at hin_m; omega),
      BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h152_lt,
      Nat.mod_eq_of_lt (by unfold Inside at hin_m; omega)]
  refine ⟨w_m, w_aa, S, Nd, hWT', hAp, hm_lu, haa_lu, hm8, hin_m,
    by rw [howned']; exact hdisj_m,
    by rw [hm40_eq]; exact hgas,
    haa_S, by rw [hhdr' _ haa_S]; exact haa_klen,
    by rw [hwrs', hjr']; exact haa_unass,
    fun _ => ?_⟩
  unfold memW; dsimp only; rw [hbv152, hst_w.2.1]

/-- After `ak := htab_new(52, 8)` and storing `ak` at `m+160`. -/
def SysTxAfterAk (stored : Bool) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_m w_aa w_ak : BitVec 64, ∃ S Nd : List Nat,
    WorldTypedWith s S Nd ∧
    ArenaReady s ∧
    s.locals.lookup (ofString "m") = some (.val (.word w_m)) ∧
    s.locals.lookup (ofString "ak") = some (.val (.word w_ak)) ∧
    w_m.toNat % 8 = 0 ∧
    Inside (w_m.toNat, 176) sourceBase (globN s "heap_ptr") ∧
    IvlsDisj [(w_m.toNat, 176)] (worldOwned s S Nd) ∧
    memW s (w_m.toNat + 40) < 2 ^ 63 ∧
    memW s (w_m.toNat + 152) = w_aa.toNat ∧
    w_aa.toNat ∈ S ∧ w_ak.toNat ∈ S ∧ w_aa.toNat ≠ w_ak.toNat ∧
    hdr s w_aa.toNat 0 = 20 ∧ hdr s w_ak.toNat 0 = 52 ∧
    (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ w_aa.toNat) ∧
    (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ w_ak.toNat) ∧
    (stored = true → memW s (w_m.toNat + 160) = w_ak.toNat)

theorem sysTxAfterAk_guestInv {stored : Bool} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : SysTxAfterAk stored s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, hA, _⟩ := h
  exact hA.1

theorem resumeOn_htab_new_ak
    (hnspec : type_of% @htab_new_spec) :
    DecCallResumeOn (SysTxAfterAa true) (SysTxAfterAk false) (ofString "ak") (ofString "htab_new")
      [.const (BitVec.ofNat 64 52), .const (BitVec.ofNat 64 8)] := by
  intro F state values body callee ret value post hcode hM hargs hl hrun
  obtain ⟨w_m, w_aa, S, Nd, hWT, hAs, hm_lu, _, hm8, hin_m, hdisj_m, hgas,
    haa_S, haa_klen, haa_unass, hm152⟩ := hM
  have hpc := callee_param_two state (ofString "htab_new") (ofString "key_len") (ofString "cap")
    .one .one _ _ (by rw [hcode]; exact lookup_htab_new_fn)
    (.const (BitVec.ofNat 64 52)) (.const (BitVec.ofNat 64 8))
    (.val (.word (BitVec.ofNat 64 52))) (.val (.word (BitVec.ofNat 64 8)))
    values body callee ret rfl rfl hargs hl
  have hkl : locN (callEntryStateHOLFinite state callee) "key_len" = 52 := by
    simp [locN, callEntryStateHOLFinite, hpc.2.1]
  have hcp : locN (callEntryStateHOLFinite state callee) "cap" = 8 := by
    simp [locN, callEntryStateHOLFinite, hpc.2.2]
  have hnr : HtabNewReady (callEntryStateHOLFinite state callee) :=
    ⟨localsFree_arenaReady state callee (state.clock - 1) hAs,
      by rw [hkl]; decide, by rw [hcp]; decide⟩
  have hbe_eq : post.be = state.be := by
    have hm := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
    rw [hrun] at hm; exact hm.2.2.1
  have hout := FunSpec.at_lookup hnspec state hcode values body callee ret hl hnr (by rw [hrun]; simp)
  rw [hrun] at hout; dsimp only at hout
  obtain ⟨w_ak, rfl, hAp, hag, hwf_ak, _, hklen_ak, hfp_ak, hfr, hg_kept⟩ := hout value rfl
  rw [hkl] at hklen_ak
  have hg_kept_s : GlobalsKept ["heap_ptr", "scratch_ptr"] state post := hg_kept
  have hag_s : AllocatorGrows state post := hag
  obtain ⟨hak_not_S, _, hak_unass, hWT_ext, hwrs_eq, hjr_eq, hhdr_S, hb_surv⟩ :=
    worldTypedWith_htab_new hAs hWT hAp hag_s hwf_ak hfp_ak hfr hbe_eq hg_kept_s
  obtain ⟨hin_m', hdisj_m_fn, hunhit_m⟩ :=
    hb_surv (w_m.toNat, 176) hm8 (by omega) hin_m (fun j hj => hdisj_m (w_m.toNat, 176) (by simp) j hj)
  have h264 : heapEnd < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hm40_eq : memW post (w_m.toNat + 40) = memW state (w_m.toNat + 40) :=
    memW_eq_of_ivlUnhit hunhit_m (by omega) (by unfold Inside at hin_m; omega) ⟨by dsimp; omega, by dsimp; omega⟩
  have hm152_eq : memW post (w_m.toNat + 152) = memW state (w_m.toNat + 152) :=
    memW_eq_of_ivlUnhit hunhit_m (by omega) (by unfold Inside at hin_m; omega) ⟨by dsimp; omega, by dsimp; omega⟩
  have haa_ne_ak : w_aa.toNat ≠ w_ak.toNat := fun heq => hak_not_S (heq ▸ haa_S)
  set resumed := setVarHOLFinite (ofString "ak") (.val (.word w_ak)) { post with locals := state.locals }
  have hne : ofString "ak" ≠ ofString "m" := by decide
  refine ⟨w_m, w_aa, w_ak, S ++ [w_ak.toNat], Nd,
    (worldTypedWith_with_locals post _ post.clock _ Nd).2 hWT_ext,
    localsFree_arenaReady post _ post.clock hAp,
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hm_lu],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    hm8, hin_m',
    fun o ho j hj => by simp only [List.mem_singleton] at ho; subst ho; exact hdisj_m_fn j hj,
    by change memW post (w_m.toNat + 40) < 2 ^ 63; rw [hm40_eq]; exact hgas,
    by change memW post (w_m.toNat + 152) = w_aa.toNat; rw [hm152_eq]; exact hm152 rfl,
    List.mem_append.2 (Or.inl haa_S),
    List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)),
    haa_ne_ak,
    by change hdr post w_aa.toNat 0 = 20; rw [hhdr_S _ haa_S]; exact haa_klen,
    hklen_ak,
    by change ∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ w_aa.toNat
       rw [hwrs_eq, hjr_eq]; exact haa_unass,
    hak_unass,
    fun h => by cases h⟩

theorem hoare_store_msg_ak :
    Hoare (SysTxAfterAk false)
      (.store (.op .add [.var .local (ofString "m"), .const (BitVec.ofNat 64 160)])
        (.var .local (ofString "ak")))
      (fun r t => r = none → SysTxAfterAk true t) := by
  apply Hoare.store_fall
  intro F s x v mem' hM hx hv hst
  obtain ⟨w_m, w_aa, w_ak, S, Nd, hWT, hAs, hm_lu, hak_lu, hm8, hin_m, hdisj_m, hgas,
    hm152, haa_S, hak_S, haa_ne_ak, haa_klen, hak_klen, haa_unass, hak_unass, _⟩ := hM
  have hx_eq := evalAt_add_local_const hm_lu hx
  have hv_eq : v = .val (.word w_ak) := by
    simp only [evalAt, evalHOLExact, hak_lu, Option.some.injEq] at hv
    exact hv.symm
  subst hv_eq
  obtain ⟨hAp, hWT', howned', hwrs', hjr', hhdr'⟩ :=
    store_in_block_preserves_worldTypedWith hWT hAs rfl hm8 (by omega) (by omega) hin_m hdisj_m hx_eq
      (by simp [flattenHOL]) hst
  have hfl : flattenHOL (.val (.word w_ak) : ValueHOL 64) = [.word w_ak] := by unfold flattenHOL; rfl
  rw [hfl] at hst
  have hst_w := panMemStoresHOL_word_spec (s := s) (x := x) (w := .word w_ak) hst
  have h264 : heapEnd < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have h160_lt : 160 < 2 ^ 64 := by decide
  have hm_ne : ∀ (off : Nat), off < 160 →
      memW ({ s with memory := mem' } : PanSemStateFiniteExact 64 F) (w_m.toNat + off) =
        memW s (w_m.toNat + off) := by
    intro off hoff
    unfold memW; dsimp only
    rw [hst_w.2.2]
    intro heq
    have hlhs : (BitVec.ofNat 64 (w_m.toNat + off)).toNat = w_m.toNat + off := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by unfold Inside at hin_m; omega)
    have hrhs : x.toNat = w_m.toNat + 160 := by
      rw [hx_eq, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h160_lt,
        Nat.mod_eq_of_lt (by unfold Inside at hin_m; omega)]
    have := congrArg BitVec.toNat heq; omega
  have hbv160 : BitVec.ofNat 64 (w_m.toNat + 160) = x := by
    apply BitVec.eq_of_toNat_eq
    rw [hx_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold Inside at hin_m; omega),
      BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h160_lt,
      Nat.mod_eq_of_lt (by unfold Inside at hin_m; omega)]
  refine ⟨w_m, w_aa, w_ak, S, Nd, hWT', hAp, hm_lu, hak_lu, hm8, hin_m,
    by rw [howned']; exact hdisj_m,
    by rw [hm_ne 40 (by omega)]; exact hgas,
    by rw [hm_ne 152 (by omega)]; exact hm152,
    haa_S, hak_S, haa_ne_ak,
    by rw [hhdr' _ haa_S]; exact haa_klen,
    by rw [hhdr' _ hak_S]; exact hak_klen,
    by rw [hwrs', hjr']; exact haa_unass,
    by rw [hwrs', hjr']; exact hak_unass,
    fun _ => ?_⟩
  unfold memW; dsimp only; rw [hbv160, hst_w.2.1]

theorem callEntryOn_pmc_sysTx :
    CallEntryOn (SysTxAfterAk true) MsgReady (ofString "process_message_call")
      [.var .local (ofString "m")] := by
  intro F state values body callee ret hcode hM hargs hlook
  obtain ⟨w_m, w_aa, w_ak, S, Nd, hWT, hAs, hm_lu, _, hm8, hin_m, hdisj_m, hgas,
    hm152, haa_S, hak_S, haa_ne_ak, haa_klen, hak_klen, haa_unass, hak_unass, hm160⟩ := hM
  have hpc := callee_param_one_exp state (ofString "process_message_call") (ofString "msg") .one _ _
    (by rw [hcode]; exact lookup_process_message_call)
    (.var .local (ofString "m")) (.val (.word w_m)) values body callee ret hm_lu hargs hlook
  have hmsg_loc : locN (callEntryStateHOLFinite state callee) "msg" = w_m.toNat := by
    simp [locN, callEntryStateHOLFinite, hpc.2]
  exact msgReady_of_parts
    (localsFree_arenaReady state callee (state.clock - 1) hAs)
    ((worldTypedWith_with_locals state callee (state.clock - 1) S Nd).2 hWT)
    hmsg_loc hm152 (hm160 rfl) haa_S hak_S haa_ne_ak haa_klen hak_klen haa_unass hak_unass
    hin_m hm8 (fun o ho => hdisj_m (w_m.toNat, 176) (by simp) o ho) hgas

theorem resumeOn_pmc_sysTx
    (wpmc : WorldKeepsIn MsgReady (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => [(locN s "msg", 176),
                 (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
                 (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
                 (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
                 (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
                 (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
                 (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
                 (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
                 (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
                 (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
                 (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetMessageOutput (ofString "process_message_call")) :
    DecCallResumeOn (SysTxAfterAk true) WorldOK (ofString "out") (ofString "process_message_call")
      [.var .local (ofString "m")] := by
  intro F state values body callee ret value post hcode hM hargs hl hrun
  have hMR := callEntryOn_pmc_sysTx state values body callee ret hcode hM hargs hl
  obtain ⟨w_m, w_aa, w_ak, S, Nd, hWT, hAs, hm_lu, _, hm8, hin_m, hdisj_m, hgas,
    hm152, haa_S, hak_S, _, _, _, _, _, hm160⟩ := hM
  have hpc := callee_param_one_exp state (ofString "process_message_call") (ofString "msg") .one _ _
    (by rw [hcode]; exact lookup_process_message_call)
    (.var .local (ofString "m")) (.val (.word w_m)) values body callee ret hm_lu hargs hl
  have hmsg_loc : locN (callEntryStateHOLFinite state callee) "msg" = w_m.toNat := by
    simp [locN, callEntryStateHOLFinite, hpc.2]
  have hstep := FunSpec.at_lookup wpmc state hcode values body callee ret hl hMR (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hwsi := hstep (Or.inl ⟨value, rfl⟩)
  have hW_post : WorldOK post := by
    apply hwsi.worldOK
    refine ⟨S, Nd, (worldTypedWith_with_locals state callee (state.clock - 1) S Nd).2 hWT, ?_, ?_⟩
    · intro t ht
      change t ∈ [memW (callEntryStateHOLFinite state callee) (locN (callEntryStateHOLFinite state callee) "msg" + 152),
        memW (callEntryStateHOLFinite state callee) (locN (callEntryStateHOLFinite state callee) "msg" + 160)] at ht
      rw [hmsg_loc] at ht
      change t ∈ [memW state (w_m.toNat + 152), memW state (w_m.toNat + 160)] at ht
      rw [hm152, hm160 rfl] at ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact haa_S
      · exact hak_S
    · intro i hi j hj
      change i ∈ [(locN (callEntryStateHOLFinite state callee) "msg", 176),
        bufferRegion state ("b2_v", 128), bufferRegion state ("bn_expw", 352),
        bufferRegion state ("bn_gamma", 384), bufferRegion state ("evm_key_buf", 32),
        bufferRegion state ("keccak_pad", 136), bufferRegion state ("keccak_st", 200),
        bufferRegion state ("mpt_nib_scratch", 64), bufferRegion state ("pre_hdr_buf", 96),
        bufferRegion state ("rmd_h", 40), bufferRegion state ("rmd_pad", 128),
        bufferRegion state ("rmd_x", 128), bufferRegion state ("sha_pad", 128),
        bufferRegion state ("sha_st", 64), bufferRegion state ("sk_buf", 52),
        bufferRegion state ("u256_ws", 640)] at hi
      rw [hmsg_loc] at hi
      change j ∈ worldTypedIvls state S Nd at hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hdisj_m (w_m.toNat, 176) (by simp) j (worldTypedIvls_sub_worldOwned _ _ _ j hj)
      · exact bufferRegion_disj_le hWT ("b2_v", 128) (by decide) (by decide) 128 le_rfl j hj
      · exact bufferRegion_disj_le hWT ("bn_expw", 352) (by decide) (by decide) 352 le_rfl j hj
      · exact bufferRegion_disj_le hWT ("bn_gamma", 384) (by decide) (by decide) 384 le_rfl j hj
      · exact bufferRegion_disj_le hWT ("evm_key_buf", 32) (by decide) (by decide) 32 le_rfl j hj
      · exact bufferRegion_disj_le hWT ("keccak_pad", 136) (by decide) (by decide) 136 le_rfl j hj
      · exact bufferRegion_disj_le hWT ("keccak_st", 200) (by decide) (by decide) 200 le_rfl j hj
      · exact bufferRegion_disj_le hWT ("mpt_nib_scratch", 64) (by decide) (by decide) 64 le_rfl j hj
      · exact bufferRegion_disj_le hWT ("pre_hdr_buf", 96) (by decide) (by decide) 96 le_rfl j hj
      · exact bufferRegion_disj_le hWT ("rmd_h", 40) (by decide) (by decide) 40 le_rfl j hj
      · exact bufferRegion_disj_le hWT ("rmd_pad", 128) (by decide) (by decide) 128 le_rfl j hj
      · exact bufferRegion_disj_le hWT ("rmd_x", 128) (by decide) (by decide) 128 le_rfl j hj
      · exact bufferRegion_disj_le hWT ("sha_pad", 128) (by decide) (by decide) 128 le_rfl j hj
      · exact bufferRegion_disj_le hWT ("sha_st", 64) (by decide) (by decide) 64 le_rfl j hj
      · exact bufferRegion_disj_le hWT ("sk_buf", 64) (by decide) (by decide) 52 (by decide) j hj
      · exact bufferRegion_disj_le hWT ("u256_ws", 640) (by decide) (by decide) 640 le_rfl j hj
  exact LocalsOnly.setVar (LocalsOnly.of_localsFree localsFree_worldOK) (by simp) value _
    (localsFree_worldOK post state.locals post.clock hW_post)

/-- Full genuine body composition for `process_unchecked_system_transaction` under `SysTxEntry`
(`WorldOK` + 1-word entry parameters `target`, `data`, `data_n` and 1-word globals
`vm_system_address`, `be`). -/
theorem bounded_process_unchecked_system_transaction_wordArgs
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hext : TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of»)
    (hfmr : TerminatingFunBoundedOn GuestInv (ofString "frame_mem_release") K.«frame_mem_release»)
    (hhn : TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new»)
    (hitb : TerminatingFunBoundedOn WorldOK (ofString "incorporate_tx_into_block") K.«incorporate_tx_into_block»)
    (hmc : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (hmn : TerminatingFunBoundedOn GuestInv (ofString "msg_new") K.«msg_new»)
    (hpmc : TerminatingFunBoundedOn MsgReady (ofString "process_message_call") K.«process_message_call»)
    (hsr : TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release»)
    (hsf : TerminatingFunBoundedOn GuestInv (ofString "state_fresh_tx") K.«state_fresh_tx»)
    (hte : TerminatingFunBoundedOn GuestInv (ofString "te_new") K.«te_new»)
    (wext : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "ext_code_of"))
    (hnspec : type_of% @htab_new_spec)
    (wmn : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ w => [(w, 176)])) (ofString "msg_new"))
    (rtmn : Returns ArenaReady (fun s post m => FreshBlock s post m 176 ∧
      ∀ k, k < 22 → memW post (m + 8 * k) = 0) (ofString "msg_new"))
    (wpmc : WorldKeepsIn MsgReady (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => [(locN s "msg", 176),
                 (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
                 (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
                 (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
                 (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
                 (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
                 (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
                 (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
                 (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
                 (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
                 (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetMessageOutput (ofString "process_message_call"))
    (wsf : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr", "journal_n", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "state_fresh_tx"))
    (wte : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ w => [(w, 200)])) (ofString "te_new"))
    (rtte : Returns ArenaReady (fun s post m => FreshBlock s post m 200 ∧
      ∀ k, k < 25 → memW post (m + 8 * k) = 0) (ofString "te_new")) :
    TerminatingProgBoundedOn SysTxEntry
      (sourceFunctionEntry Guest.Software.guestFn_process_unchecked_system_transaction).2.2.1
      K.«process_unchecked_system_transaction» := by
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_process_unchecked_system_transaction,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.call_on hsf _ _
        (callEntryOn_of_imp localsFree_guestInv (fun _ h => sysTxEntry_guestInv h) _ _))
      (hoare_call_state_fresh_tx wsf)
      (decCall_on_shaped hext (ofString "code") (.comb [.one, .one]) [.var .local (ofString "target")]
        (callEntryOn_of_imp localsFree_guestInv (fun _ h => sysTxEntry_guestInv h) _ _)
        (resumeOn_ext_code_of_sysTxCode wext)
        (TerminatingProgBoundedOn.decCall_on hte (ofString "te") .one []
          (callEntryOn_of_imp localsFree_guestInv (fun _ h => sysTxEntryCode_guestInv h) _ _)
          (resumeOn_te_new_code wte rtte)
          (TerminatingProgBoundedOn.seq_hoare
            (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
            (hoare_store_te 0 (by omega) (.var .global (ofString "vm_system_address")) (fun s v hS hv => by
              obtain ⟨⟨_, _, _, _, _, ⟨_, _, _, ⟨wv, hwv⟩, _⟩, _⟩, _⟩ := hS
              simp only [evalAt, evalHOLExact, hwv, Option.some.injEq] at hv
              subst hv; simp [flattenHOL]))
            (TerminatingProgBoundedOn.seq_hoare
              (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
              (hoare_store_te 8 (by omega) (.var .local (ofString "target")) (fun s v hS hv => by
                obtain ⟨⟨_, _, _, _, _, ⟨⟨wt, hwt⟩, _⟩, _⟩, _⟩ := hS
                simp only [evalAt, evalHOLExact, hwt, Option.some.injEq] at hv
                subst hv; simp [flattenHOL]))
              (TerminatingProgBoundedOn.seq_hoare
                (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                (hoare_store_te 48 (by omega)
                  (.load (.comb [.one, .one, .one, .one]) (.op .add [.var .global (ofString "be"), .const (BitVec.ofNat 64 48)]))
                  (fun s v _ hv => by
                    rw [evalAt_load_comb4_len hv]; omega))
                (TerminatingProgBoundedOn.seq_hoare
                  (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                  (hoare_store_te 80 (by omega) (.const (BitVec.ofNat 64 30000000)) (fun s v _ hv => by
                    rw [evalAt_const s _ v hv]; simp [flattenHOL]))
                  (TerminatingProgBoundedOn.seq_hoare
                    (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                    (hoare_store_te 88 (by omega)
                      (.panop .mul [.const (BitVec.ofNat 64 97920), .const (BitVec.ofNat 64 16)])
                      (fun s v _ hv => by
                        simp only [evalAt, evalHOLExact, evalListHOLExact, valueIsWord, valueWord,
                          panOpHOL, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
                          Option.some.injEq] at hv
                        subst hv; simp [flattenHOL]))
                    (TerminatingProgBoundedOn.decCall_on hmn (ofString "m") .one []
                      (callEntryOn_of_imp localsFree_guestInv (fun _ h => sysTxAfterTeCode_guestInv h) _ _)
                      (resumeOn_msg_new wmn rtmn)
                      (TerminatingProgBoundedOn.seq_hoare
                        (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                        (hoare_store_msg_other 0 (by omega) (fun h => by cases h) (.var .global (ofString "be"))
                          (fun s v hM hv => by
                            obtain ⟨_, _, _, _, _, _, _, ⟨_, _, _, _, ⟨wb, hwb⟩⟩, _⟩ := hM
                            simp only [evalAt, evalHOLExact, hwb, Option.some.injEq] at hv
                            subst hv; simp [flattenHOL]) (by omega))
                        (TerminatingProgBoundedOn.seq_hoare
                          (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                          (hoare_store_msg_other 8 (by omega) (fun h => by cases h) (.var .local (ofString "te"))
                            (fun s v hM hv => by
                              obtain ⟨_, _, _, _, _, _, _, _, ⟨wte0, hwte0⟩, _⟩ := hM
                              simp only [evalAt, evalHOLExact, hwte0, Option.some.injEq] at hv
                              subst hv; simp [flattenHOL]) (by omega))
                          (TerminatingProgBoundedOn.seq_hoare
                            (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                            (hoare_store_msg_other 16 (by omega) (fun h => by cases h) (.var .global (ofString "vm_system_address"))
                              (fun s v hM hv => by
                                obtain ⟨_, _, _, _, _, _, _, ⟨_, _, _, ⟨wv, hwv⟩, _⟩, _⟩ := hM
                                simp only [evalAt, evalHOLExact, hwv, Option.some.injEq] at hv
                                subst hv; simp [flattenHOL]) (by omega))
                            (TerminatingProgBoundedOn.seq_hoare
                              (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                              (hoare_store_msg_other 24 (by omega) (fun h => by cases h) (.var .local (ofString "target"))
                                (fun s v hM hv => by
                                  obtain ⟨_, _, _, _, _, _, _, ⟨⟨wt, hwt⟩, _⟩, _⟩ := hM
                                  simp only [evalAt, evalHOLExact, hwt, Option.some.injEq] at hv
                                  subst hv; simp [flattenHOL]) (by omega))
                              (TerminatingProgBoundedOn.seq_hoare
                                (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                (hoare_store_msg_other 32 (by omega) (fun h => by cases h) (.var .local (ofString "target"))
                                  (fun s v hM hv => by
                                    obtain ⟨_, _, _, _, _, _, _, ⟨⟨wt, hwt⟩, _⟩, _⟩ := hM
                                    simp only [evalAt, evalHOLExact, hwt, Option.some.injEq] at hv
                                    subst hv; simp [flattenHOL]) (by omega))
                                (TerminatingProgBoundedOn.seq_hoare_trans
                                  (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                  hoare_store_msg_gas
                                  (TerminatingProgBoundedOn.seq_hoare
                                    (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                    (hoare_store_msg_other 48 (by omega) (fun _ => by omega)
                                      (.panop .mul [.const (BitVec.ofNat 64 97920), .const (BitVec.ofNat 64 16)])
                                      (fun s v _ hv => by
                                        simp only [evalAt, evalHOLExact, evalListHOLExact, valueIsWord, valueWord,
                                          panOpHOL, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
                                          Option.some.injEq] at hv
                                        subst hv; simp [flattenHOL]) (by omega))
                                    (TerminatingProgBoundedOn.seq_hoare
                                      (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                      (hoare_store_msg_other 88 (by omega) (fun _ => by omega) (.var .local (ofString "data"))
                                        (fun s v hM hv => by
                                          obtain ⟨_, _, _, _, _, _, _, ⟨_, ⟨wd, hwd⟩, _⟩, _⟩ := hM
                                          simp only [evalAt, evalHOLExact, hwd, Option.some.injEq] at hv
                                          subst hv; simp [flattenHOL]) (by omega))
                                      (TerminatingProgBoundedOn.seq_hoare
                                        (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                        (hoare_store_msg_other 96 (by omega) (fun _ => by omega) (.var .local (ofString "data_n"))
                                          (fun s v hM hv => by
                                            obtain ⟨_, _, _, _, _, _, _, ⟨_, _, ⟨wdn, hwdn⟩, _⟩, _⟩ := hM
                                            simp only [evalAt, evalHOLExact, hwdn, Option.some.injEq] at hv
                                            subst hv; simp [flattenHOL]) (by omega))
                                        (TerminatingProgBoundedOn.seq_hoare
                                          (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                          (hoare_store_msg_other 104 (by omega) (fun _ => by omega) (.var .local (ofString "target"))
                                            (fun s v hM hv => by
                                              obtain ⟨_, _, _, _, _, _, _, ⟨⟨wt, hwt⟩, _⟩, _⟩ := hM
                                              simp only [evalAt, evalHOLExact, hwt, Option.some.injEq] at hv
                                              subst hv; simp [flattenHOL]) (by omega))
                                          (TerminatingProgBoundedOn.seq_hoare
                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                            (hoare_store_msg_other 112 (by omega) (fun _ => by omega) (.rfield 0 (.var .local (ofString "code")))
                                              (fun s v hM hv => by
                                                obtain ⟨_, a, b, _, _, _, _, _, _, hcode_lu, _⟩ := hM
                                                simp only [evalAt, evalHOLExact, hcode_lu, List.getElem?_cons_zero, Option.some.injEq] at hv
                                                subst hv; simp [flattenHOL]) (by omega))
                                            (TerminatingProgBoundedOn.seq_hoare
                                              (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                              (hoare_store_msg_other 120 (by omega) (fun _ => by omega) (.rfield 1 (.var .local (ofString "code")))
                                               (fun s v hM hv => by
                                                  obtain ⟨_, a, b, _, _, _, _, _, _, hcode_lu, _⟩ := hM
                                                  simp only [evalAt, evalHOLExact, hcode_lu, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hv
                                                  subst hv; simp [flattenHOL]) (by omega))
                                              (TerminatingProgBoundedOn.decCall_on hhn (ofString "aa") .one _
                                                (callEntryOn_of_imp localsFree_guestInv (fun _ h => sysTxAfterMsg_guestInv h) _ _)
                                                (resumeOn_htab_new_aa hnspec)
                                                (TerminatingProgBoundedOn.seq_hoare_trans
                                                  (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                  hoare_store_msg_aa
                                                  (TerminatingProgBoundedOn.decCall_on hhn (ofString "ak") .one _
                                                    (callEntryOn_of_imp localsFree_guestInv (fun _ h => sysTxAfterAa_guestInv h) _ _)
                                                    (resumeOn_htab_new_ak hnspec)
                                                    (TerminatingProgBoundedOn.seq_hoare_trans
                                                      (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                      hoare_store_msg_ak
                                                      (TerminatingProgBoundedOn.seq_hoare
                                                        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s))
                                                        (Hoare.skip fun _ h _ => h)
                                                        (TerminatingProgBoundedOn.decCall_on hpmc (ofString "out") .one [.var .local (ofString "m")]
                                                          callEntryOn_pmc_sysTx
                                                          (resumeOn_pmc_sysTx wpmc)
                                                          (TerminatingProgBoundedOn.seq_hoare
                                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s))
                                                            (Hoare.skip fun _ h _ => h)
                                                            (TerminatingProgBoundedOn.seq_guestInv_after
                                                              (TerminatingProgBoundedOn.call_on hitb _ _
                                                                (callEntryOn_of_localsFree localsFree_worldOK _ _))
                                                              worldOK_guestInv
                                                              (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
                                                                (TerminatingProgBoundedOn.seq_guestInv
                                                                  (TerminatingProgBoundedOn.ite_on
                                                                    (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
                                                                      (TerminatingProgBoundedOn.seq_guestInv
                                                                        (TerminatingProgBoundedOn.ite_on
                                                                          (TerminatingProgBoundedOn.decCall_guestInv hal _ _ _
                                                                            (TerminatingProgBoundedOn.seq_guestInv
                                                                              (TerminatingProgBoundedOn.call_guestInv hmc _ _)
                                                                              (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))))
                                                                          (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                                                                        (TerminatingProgBoundedOn.seq_guestInv
                                                                          (TerminatingProgBoundedOn.call_guestInv hsr _ _)
                                                                          (TerminatingProgBoundedOn.call_guestInv hfmr _ _))))
                                                                    (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                                                                  (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))))))))))))))))))))))))))))))) ?_
  unfold K.«process_unchecked_system_transaction»
  simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]
  omega

/-! ### R10 unguarded global-shape corner case (`not_wk_state_fresh_tx_r10`)

In R10 (`664524baaf`), `FunSpec` (`C00.lean:38`) added the entry parameter shape witness
`∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, s.locals, retShape)`,
which enforces 1-word local parameter shapes on `FunSpec`, while `TerminatingFunBoundedOn WorldOK`
(`Defs.lean:164`) and `WorldOK` (`MemoryViews.lean:602`) omit both `lookupCodeHOLFinite` and
`GlobalWord` (`globN` maps `.rStruct` globals to `0`).

Consequently:
- For `process_unchecked_system_transaction` under well-shaped 1-word entry parameters and globals
  (`WordSysTxArgs`), `bounded_process_unchecked_system_transaction_wordArgs` above proves the full
  relational `WorldOK`/`MsgReady` Hoare & clock bound genuinely from the callee hypotheses.
- For the malformed `¬ WordSysTxArgs` case, `wk_state_fresh_tx` (`WorldKeeps WorldOK ... "state_fresh_tx"`,
  zero parameters `params = []`) is itself refuted by a state `s₀` where `bs` holds a 2751-word
  `.rStruct`: `globN s₀ "bs" = 0` so `WorldOK s₀` holds trivially with `S = []`, `Nd = []`, and
  `state_fresh_tx` allocates `ts` at `scratchStart - 22000` and executes `store (ts + 0) bs`, writing
  2751 words across `heapLimit = scratchStart` into `scratchStart` (`[scratch_ptr, scratchEnd)`),
  outside `worldOwned s₀ [] [] ++ [freeGap s₀]` and `heapFree s₀`, violating `FrameOutside` on
  normal return (`return 0`). -/

section StateFreshTxCornerCase

private theorem sftx_nm1 : (ofString "bs" = ofString "heap_ptr") = False := by
  simp only [eq_iff_iff, iff_false]; decide
private theorem sftx_nm2 : (ofString "frame_mem_ptr" = ofString "heap_ptr") = False := by
  simp only [eq_iff_iff, iff_false]; decide
private theorem sftx_nm3 : (ofString "scratch_ptr" = ofString "heap_ptr") = False := by
  simp only [eq_iff_iff, iff_false]; decide
private theorem sftx_nm4 : (ofString "bs" = ofString "frame_mem_ptr") = False := by
  simp only [eq_iff_iff, iff_false]; decide
private theorem sftx_nm5 : (ofString "scratch_ptr" = ofString "frame_mem_ptr") = False := by
  simp only [eq_iff_iff, iff_false]; decide
private theorem sftx_nm6 : (ofString "bs" = ofString "scratch_ptr") = False := by
  simp only [eq_iff_iff, iff_false]; decide
private theorem sftx_nm7 : (ofString "ts" = ofString "heap_ptr") = False := by
  simp only [eq_iff_iff, iff_false]; decide
private theorem sftx_nm8 : (ofString "ts" = ofString "frame_mem_ptr") = False := by
  simp only [eq_iff_iff, iff_false]; decide
private theorem sftx_nm9 : (ofString "ts" = ofString "scratch_ptr") = False := by
  simp only [eq_iff_iff, iff_false]; decide
private theorem sftx_nm10 : (ofString "ts" = ofString "bs") = False := by
  simp only [eq_iff_iff, iff_false]; decide
private theorem sftx_nm11 : (ofString "journal_n" = ofString "heap_ptr") = False := by
  simp only [eq_iff_iff, iff_false]; decide
private theorem sftx_nm12 : (ofString "journal_n" = ofString "frame_mem_ptr") = False := by
  simp only [eq_iff_iff, iff_false]; decide
private theorem sftx_nm13 : (ofString "journal_n" = ofString "scratch_ptr") = False := by
  simp only [eq_iff_iff, iff_false]; decide
private theorem sftx_nm14 : (ofString "journal_n" = ofString "bs") = False := by
  simp only [eq_iff_iff, iff_false]; decide
private theorem sftx_nm15 : (ofString "journal_n" = ofString "ts") = False := by
  simp only [eq_iff_iff, iff_false]; decide

private def cxHpInit : Nat := scratchStart - 22000

private def cxBsVal : ValueHOL 64 :=
  .rStruct (List.replicate 2751 (.val (.word 99#64)))

private def cxSftxGlobals : HolFiniteMapExact MlS (ValueHOL 64) :=
  ((((((HolFiniteMapExact.empty.update
      (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 cxHpInit)))).update
    (ofString "frame_mem_ptr", .val (.word (BitVec.ofNat 64 scratchStart)))).update
    (ofString "scratch_ptr", .val (.word (BitVec.ofNat 64 scratchStart)))).update
    (ofString "ts", .val (.word 0#64))).update
    (ofString "journal_n", .val (.word 0#64))).update
    (ofString "bs", cxBsVal))

private noncomputable def cxSftxState : PanSemStateFiniteExact 64 Guest.HostMemory :=
  { sourceInitialState [] with
    locals := HolFiniteMapExact.empty
    globals := cxSftxGlobals
    code := originalRuntimeCode
    memory := fun _ => .word 0
    clock := 1000 }

private theorem cxSftx_globN_hp : globN cxSftxState "heap_ptr" = cxHpInit := by
  simp [cxSftxState, cxSftxGlobals, globN, HolFiniteMapExact.lookup_update, FUPDATE,
    sftx_nm1, sftx_nm2, sftx_nm3, sftx_nm7, sftx_nm11, cxHpInit]
  decide

private theorem cxSftx_globN_fm : globN cxSftxState "frame_mem_ptr" = scratchStart := by
  simp [cxSftxState, cxSftxGlobals, globN, HolFiniteMapExact.lookup_update, FUPDATE,
    sftx_nm4, sftx_nm5, sftx_nm8, sftx_nm12]
  decide

private theorem cxSftx_globN_sc : globN cxSftxState "scratch_ptr" = scratchStart := by
  simp [cxSftxState, cxSftxGlobals, globN, HolFiniteMapExact.lookup_update, FUPDATE,
    sftx_nm6, sftx_nm9, sftx_nm13]
  decide

private theorem cxSftx_globN_other (g : String)
    (h1 : ofString g ≠ ofString "heap_ptr")
    (h2 : ofString g ≠ ofString "frame_mem_ptr")
    (h3 : ofString g ≠ ofString "scratch_ptr") :
    globN cxSftxState g = 0 := by
  have hb1 : (ofString "heap_ptr" == ofString g) = false := beq_false_of_ne h1.symm
  have hb2 : (ofString "frame_mem_ptr" == ofString g) = false := beq_false_of_ne h2.symm
  have hb3 : (ofString "scratch_ptr" == ofString g) = false := beq_false_of_ne h3.symm
  unfold globN cxSftxState cxSftxGlobals
  dsimp only
  simp only [HolFiniteMapExact.lookup_update, FUPDATE, hb1, hb2, hb3, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> simp [cxBsVal, HolFiniteMapExact.empty]

private theorem cxSftx_gb_ne (gn : String × Nat) (hgn : gn ∈ globalBuffers) :
    ofString gn.1 ≠ ofString "heap_ptr" ∧
    ofString gn.1 ≠ ofString "frame_mem_ptr" ∧
    ofString gn.1 ≠ ofString "scratch_ptr" := by
  revert gn hgn; decide

private theorem cxSftx_worldTypedWith : WorldTypedWith cxSftxState [] [] := by
  have ho := fun g h1 h2 h3 => cxSftx_globN_other g h1 h2 h3
  have hws0 : globN cxSftxState "ws" = 0 := ho "ws" (by decide) (by decide) (by decide)
  have hbs0 : globN cxSftxState "bs" = 0 := ho "bs" (by decide) (by decide) (by decide)
  have hts0 : globN cxSftxState "ts" = 0 := ho "ts" (by decide) (by decide) (by decide)
  have hbo0 : globN cxSftxState "bo" = 0 := ho "bo" (by decide) (by decide) (by decide)
  have hba0 : globN cxSftxState "bal_accounts" = 0 := ho "bal_accounts" (by decide) (by decide) (by decide)
  have hbia0 : globN cxSftxState "bal_idx_accts" = 0 := ho "bal_idx_accts" (by decide) (by decide) (by decide)
  have hbis0 : globN cxSftxState "bal_idx_stor" = 0 := ho "bal_idx_stor" (by decide) (by decide) (by decide)
  have hjn0 : globN cxSftxState "journal_n" = 0 := ho "journal_n" (by decide) (by decide) (by decide)
  have hjc0 : globN cxSftxState "journal_cap" = 0 := ho "journal_cap" (by decide) (by decide) (by decide)
  have hbrec0 : balRecords cxSftxState = [] := by unfold balRecords; simp [hba0]
  have hbo_obj : blockOutObjects cxSftxState = [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)] := by
    unfold blockOutObjects; simp [hbo0]
  have hbal_obj : balObjects cxSftxState = [] := by unfold balObjects; simp [hbrec0]
  have hgb_zero : ∀ gn ∈ globalBuffers,
      (globN cxSftxState gn.1, if globN cxSftxState gn.1 = 0 then 0 else gn.2) = (0, 0) := by
    intro gn hgn
    have hne := cxSftx_gb_ne gn hgn
    have hz := ho gn.1 hne.1 hne.2.1 hne.2.2
    simp [hz]
  have hfix_all_zero : ∀ i ∈ fixedObjects cxSftxState, i = (0, 0) := by
    intro i hi
    unfold fixedObjects at hi
    rcases List.mem_append.1 hi with h1 | hbal
    · rcases List.mem_append.1 h1 with h2 | hbo
      · rcases List.mem_append.1 h2 with hbuf | hjr
        · obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hbuf
          exact hgb_zero gn hgn
        · simp only [List.mem_singleton] at hjr; subst hjr; simp [hjc0]
      · rw [hbo_obj] at hbo
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbo
        rcases hbo with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rw [hbal_obj] at hbal; simp at hbal
  have hwrs0 : worldRoleSlots cxSftxState = [] := by
    unfold worldRoleSlots recRoles nestRoles
    simp [hws0, hbs0, hts0, hba0, hbia0, hbis0, hbrec0]
  have hjrs0 : journalRoleSlots cxSftxState = [] := by
    unfold journalRoleSlots; simp [hjn0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨List.nodup_nil, (by simp), (by simp),
      by simp [hws0], by simp [hbs0], by simp [hts0],
      fun g hg => ?_, by simp [hbs0], by simp [hts0],
      by simp [hbrec0], by simp [hbo0],
      by unfold RolesOK; simp [hwrs0, hjrs0]⟩
    simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact Or.inl hba0
    · exact Or.inl hbia0
    · exact Or.inl hbis0
  · exact ⟨by simp [hjn0, hjc0], by rw [hjc0]; decide, Or.inl hjc0, by simp [hjn0]⟩
  · refine ⟨fun i hi => Or.inl (by rw [hfix_all_zero i hi]), ?_⟩
    rw [List.pairwise_iff_forall_sublist]
    intro a b hsub
    have ha : a ∈ fixedObjects cxSftxState := hsub.subset (by simp)
    rw [hfix_all_zero a ha]
    exact Or.inl rfl
  · exact ⟨⟨by simp, by simp⟩, by simp [nodeExtents], by simp [hws0]⟩

private theorem cxSftx_arenaReady : ArenaReady cxSftxState := by
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  unfold ArenaOK
  rw [cxSftx_globN_hp, cxSftx_globN_fm, cxSftx_globN_sc]
  unfold cxHpInit
  decide

private theorem cxSftx_worldOK : WorldOK cxSftxState :=
  ⟨cxSftx_arenaReady, [], (worldTyped_iff_with cxSftxState []).2 ⟨[], cxSftx_worldTypedWith⟩⟩

private theorem cxSftx_lookup_entry :
    lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "state_fresh_tx") [] =
      some ((sourceFunctionEntry Guest.Software.guestFn_state_fresh_tx).2.2.1,
        cxSftxState.locals,
        (sourceFunctionEntry Guest.Software.guestFn_state_fresh_tx).2.2.2) := by
  have hcode : originalRuntimeCode.lookup (ofString "state_fresh_tx") =
      some ([], (sourceFunctionEntry Guest.Software.guestFn_state_fresh_tx).2.2.1,
        (sourceFunctionEntry Guest.Software.guestFn_state_fresh_tx).2.2.2) :=
    lookup_state_fresh_tx_fn
  exact pan_zero_arg_lookup originalRuntimeCode.lookup (ofString "state_fresh_tx") _ _ hcode

/-- Exact deterministic step for `alloc(n)` when `p % 8 = 0`, `n % 8 = 0`, and `p + n ≤ heapLimit`. -/
private theorem eval_alloc_aligned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p n : Nat)
    (_hcode : s.code = originalRuntimeCode)
    (_hclk : 2 ≤ s.clock)
    (hp8 : p % 8 = 0) (hn8 : n % 8 = 0) (hfit : p + n ≤ scratchStart)
    (hp_lu : s.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 p)))) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word (BitVec.ofNat 64 n)))))
        (sourceFnBody Guest.Software.guestFn_alloc) =
        (some (.returned (.val (.word (BitVec.ofNat 64 p)))), post) ∧
      post.globals = s.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (p + n)))) ∧
      post.memory = s.memory ∧
      post.memaddrs = s.memaddrs ∧
      post.shMemaddrs = s.shMemaddrs ∧
      post.code = s.code ∧
      post.structs = s.structs ∧
      post.eshapes = s.eshapes ∧
      post.be = s.be ∧
      post.ffi = s.ffi ∧
      post.baseAddr = s.baseAddr ∧
      post.topAddr = s.topAddr ∧
      post.clock = s.clock - 1 := by
  have h264 : scratchStart < 2 ^ 64 := by decide
  have hcmax : cMax = BitVec.ofNat 64 scratchStart := rfl
  set wp := BitVec.ofNat 64 p
  set wn := BitVec.ofNat 64 n
  set wq := BitVec.ofNat 64 (p + n)
  let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word wn)))
  have hbody_eq : sourceFnBody Guest.Software.guestFn_alloc =
      .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip)
              (.seq
                (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  have hwp_nat : wp.toNat = p := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hwn_nat : wn.toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hwq_nat : wq.toNat = p + n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hcmax_nat : cMax.toNat = scratchStart := by decide
  have hq_eq : (wp + (wn + 7)) &&& ((0 : BitVec 64) - 8) = wq := by
    apply BitVec.eq_of_toNat_eq
    rw [GuestTrapAndLookup.and_neg8_toNat, hwq_nat]
    have h7 : (7 : BitVec 64).toNat = 7 := rfl
    have hn7 : (wn + 7).toNat = n + 7 := by rw [BitVec.toNat_add, hwn_nat, h7]; omega
    have hsum : (wp + (wn + 7)).toNat = p + n + 7 := by rw [BitVec.toNat_add, hwp_nat, hn7]; omega
    rw [hsum]
    omega
  have hcmp1 : ¬ ((cMax - wp).toNat < wn.toNat) := by
    rw [BitVec.toNat_sub_of_le, hcmax_nat, hwp_nat, hwn_nat]
    · omega
    · rw [BitVec.le_def, hwp_nat, hcmax_nat]; omega
  have hcmp2 : ¬ (cMax.toNat < wq.toNat) := by rw [hcmax_nat, hwq_nat]; omega
  have hp_entry : entry.globals.lookup (ofString "heap_ptr") = some (.val (.word wp)) := hp_lu
  have hn_entry : entry.locals.lookup (ofString "n") = some (.val (.word wn)) := by
    simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  set pState := setVarHOLFinite (ofString "p") (.val (.word wp)) entry
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word wn)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_entry,
      show ofString "p" ≠ ofString "n" by decide]
  set qState := setVarHOLFinite (ofString "q") (.val (.word wq)) pState
  have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word wq)) := by
    simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
      show ofString "q" ≠ ofString "p" by decide]
  refine ⟨{ emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word wq)) qState) with
      locals := HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word wq)) qState)).locals
          (ofString "q", pState.locals.lookup (ofString "q")))
        (ofString "p", entry.locals.lookup (ofString "p")) }, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]
  have hp_ev : @evalHOLExact 64 F _ entry.toExact
      (fun a => Classical.propDecidable (entry.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word wp)) := hp_entry
  dsimp only
  rw [hp_ev]
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word wp))) = true := by simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only; rw [if_pos hsh_p]
  rw [evaluateHOLFiniteState_seq_line780]
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
        (.var .local (ofString "n"))) = some (.val (.word 0#64)) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    change some (ValueHOL.val (HolWordLab.word (if (cMax - wp).toNat < wn.toNat then 1 else 0))) = _
    rw [if_neg hcmp1]; rfl
  have hite1 : evaluateHOLFiniteState pState
      (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
          (.var .local (ofString "n")))
        (.call (some (none, none)) (ofString "trap_with") [.const 1])
        .skip) = (none, pState) := by
    rw [evaluateHOLFiniteState_ite, hev1]; simp [evaluateHOLFiniteState_skip]
  rw [hite1]; dsimp only
  rw [evaluateHOLFiniteState_dec_total]
  have hq_ev : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
        .op .sub [.const 0, .const 8]]) = some (.val (.word wq)) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
      wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
    exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) ((alloc_q_word_eq wp wn).trans hq_eq)
  dsimp only; rw [hq_ev]
  have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word wq))) = true := by simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only; rw [if_pos hsh_q]
  rw [evaluateHOLFiniteState_seq_line780]
  have hev2 : @evalHOLExact 64 F _ qState.toExact
      (fun a => Classical.propDecidable (qState.memaddrs a))
      (.cmp .lower (.const cMax) (.var .local (ofString "q"))) = some (.val (.word 0#64)) := by
    simp only [evalHOLExact, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    rw [if_neg hcmp2]; rfl
  have hite2 : evaluateHOLFiniteState qState
      (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
        (.call (some (none, none)) (ofString "trap_with") [.const 1])
        .skip) = (none, qState) := by
    rw [evaluateHOLFiniteState_ite, hev2]; simp [evaluateHOLFiniteState_skip]
  rw [hite2]; dsimp only
  have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word wp)) := hp_entry
  have heval_end : evaluateHOLFiniteState qState
      (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
        (.return (.var .local (ofString "p")))) =
      (some (.returned (.val (.word wp))),
        emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word wq)) qState)) := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
    simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
      shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
      evaluateHOLFiniteState_return]
  rw [heval_end]

/-- Corollary: `decCall name .one "alloc" [e] cont` with `evalAt s e = some (.val (.word (BitVec.ofNat 64 n)))`. -/
private theorem eval_decCall_alloc_aligned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (name : MlS) (e : ExpHOL 64) (cont : ProgHOL 64)
    (p n : Nat)
    (hcode : s.code = originalRuntimeCode) (hclk : 2 ≤ s.clock)
    (hp8 : p % 8 = 0) (hn8 : n % 8 = 0) (hfit : p + n ≤ scratchStart)
    (hp_lu : s.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 p))))
    (he_ev : evalAt s e = some (.val (.word (BitVec.ofNat 64 n)))) :
    let s' : PanSemStateFiniteExact 64 F :=
      setVarHOLFinite name (.val (.word (BitVec.ofNat 64 p)))
        { s with
          globals := s.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (p + n)))),
          clock := s.clock - 1 }
    evaluateHOLFiniteState s (.decCall name .one (ofString "alloc") [e] cont) =
      ((evaluateHOLFiniteState s' cont).1,
        { (evaluateHOLFiniteState s' cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s' cont).2.locals
            (name, s.locals.lookup name) }) := by
  dsimp only
  obtain ⟨post, hrun, hg, hm, hma, hsh, hc, hst, hes, hbe, hffi, hba, hta, hck⟩ :=
    eval_alloc_aligned s p n hcode hclk hp8 hn8 hfit hp_lu
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e] =
      some [.val (.word (BitVec.ofNat 64 n))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp only [evalListHOLExact, evalAt] at he_ev ⊢
    rw [he_ev]
  have hlook : lookupCodeHOLFinite s.code.lookup (ofString "alloc") [.val (.word (BitVec.ofNat 64 n))] =
      some (sourceFnBody Guest.Software.guestFn_alloc,
        HolFiniteMapExact.empty.update (ofString "n", .val (.word (BitVec.ofNat 64 n))), .one) := by
    rw [hcode]
    exact pan_one_word_lookup originalRuntimeCode.lookup (ofString "alloc") (ofString "n") _ _ lookup_alloc
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]
  dsimp only
  rw [hlook]
  dsimp only
  rw [if_neg (by omega), hrun]
  dsimp only
  have hsh_ok : (shapeEqHOL (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 p)) : ValueHOL 64)) .one &&
      shapeEqHOL (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 p)) : ValueHOL 64)) .one) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  rw [if_pos hsh_ok]
  have hst_eq : ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F) =
      { s with
        globals := s.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (p + n)))),
        clock := s.clock - 1 } := by
    cases post; cases s
    dsimp only at hg hm hma hsh hc hst hes hbe hffi hba hta hck ⊢
    subst hg hm hma hsh hc hst hes hbe hffi hba hta hck
    rfl
  rw [hst_eq]

/-- Corollary: `call (some (some (.global, g), none)) "alloc" [.const (BitVec.ofNat 64 n)]` when `g` holds a word. -/
private theorem eval_call_global_alloc_aligned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (g : MlS) (wg : BitVec 64) (p n : Nat)
    (hcode : s.code = originalRuntimeCode) (hclk : 2 ≤ s.clock)
    (hp8 : p % 8 = 0) (hn8 : n % 8 = 0) (hfit : p + n ≤ scratchStart)
    (hp_lu : s.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 p))))
    (hg_lu : s.globals.lookup g = some (.val (.word wg))) :
    evaluateHOLFiniteState s
        (.call (some (some (.global, g), none)) (ofString "alloc") [.const (BitVec.ofNat 64 n)]) =
      (none,
        setGlobalHOLFinite g (.val (.word (BitVec.ofNat 64 p)))
          { s with
            globals := s.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (p + n)))),
            clock := s.clock - 1 }) := by
  obtain ⟨post, hrun, hg, hm, hma, hsh, hc, hst, hes, hbe, hffi, hba, hta, hck⟩ :=
    eval_alloc_aligned s p n hcode hclk hp8 hn8 hfit hp_lu
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const (BitVec.ofNat 64 n)] = some [.val (.word (BitVec.ofNat 64 n))] := rfl
  have hlook : lookupCodeHOLFinite s.code.lookup (ofString "alloc") [.val (.word (BitVec.ofNat 64 n))] =
      some (sourceFnBody Guest.Software.guestFn_alloc,
        HolFiniteMapExact.empty.update (ofString "n", .val (.word (BitVec.ofNat 64 n))), .one) := by
    rw [hcode]
    exact pan_one_word_lookup originalRuntimeCode.lookup (ofString "alloc") (ofString "n") _ _ lookup_alloc
  rw [evaluateHOLFiniteState_call, hargs]
  dsimp only
  rw [hlook]
  dsimp only
  rw [if_neg (by omega), hrun]
  dsimp only
  have hsh_ok : shapeEqHOL (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 p)) : ValueHOL 64)) .one = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  have hval_ok : isValidValueHOLExact s.toExact .global g (.val (.word (BitVec.ofNat 64 p))) = true := by
    simp [isValidValueHOLExact, lookupKvarHOLExact, hg_lu, shapeOfHOLExact, shapeEqHOL]
  rw [if_pos hsh_ok, if_pos hval_ok]
  have hst_eq : ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F) =
      { s with
        globals := s.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (p + n)))),
        clock := s.clock - 1 } := by
    cases post; cases s
    dsimp only at hg hm hma hsh hc hst hes hbe hffi hba hta hck ⊢
    subst hg hm hma hsh hc hst hes hbe hffi hba hta hck
    rfl
  rw [hst_eq]
  rfl

/-- Exact deterministic step for `htab_new(klen, cap)` with `cap ≥ 2`: advances `heap_ptr` by
`88 + (cap + 1) * ((klen + 7) / 8 * 8) + (cap + 1) * 32 + (cap + 1) * 8`, returns `BitVec.ofNat 64 p`,
and leaves all cells outside `[p, p + total)` unchanged. -/
private theorem eval_htab_new_body_frame {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p klen cap : Nat)
    (hcode : s.code = originalRuntimeCode) (hdom_s : s.memaddrs = ordinaryDomain)
    (hclk : 20 ≤ s.clock)
    (hp_lo : sourceBase ≤ p) (hp8 : p % 8 = 0)
    (hklen : klen ∈ ([20, 32, 52] : List Nat))
    (hcap : cap ∈ ([16, 64] : List Nat))
    (hfit : p + (88 + (cap + 1) * ((klen + 7) / 8 * 8 + 40)) ≤ scratchStart)
    (hp_lu : s.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 p)))) :
    let total := 88 + (cap + 1) * ((klen + 7) / 8 * 8 + 40)
    let entry := callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "key_len", .val (.word (BitVec.ofNat 64 klen)))).update
        (ofString "cap", .val (.word (BitVec.ofNat 64 cap))))
    let out := evaluateHOLFiniteState entry (sourceFunctionEntry Guest.Software.guestFn_htab_new).2.2.1
    out.1 = some (.returned (.val (.word (BitVec.ofNat 64 p)))) ∧
    out.2.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (p + total)))) ∧
    (∀ k : MlS, k ≠ ofString "heap_ptr" → out.2.globals.lookup k = s.globals.lookup k) ∧
    out.2.memaddrs = s.memaddrs ∧
    out.2.code = s.code ∧
    20 + out.2.clock ≥ s.clock ∧
    out.2.clock < s.clock ∧
    ∀ a : BitVec 64, scratchStart ≤ a.toNat → out.2.memory a = s.memory a := by
  dsimp only
  set total := 88 + (cap + 1) * ((klen + 7) / 8 * 8 + 40)
  set stride := (klen + 7) / 8 * 8
  set sz1 := (cap + 1) * stride
  set sz2 := (cap + 1) * 32
  set sz3 := (cap + 1) * 8
  have htot_eq : 88 + sz1 + sz2 + sz3 = total := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hklen hcap
    rcases hklen with rfl | rfl | rfl <;> rcases hcap with rfl | rfl <;> decide
  have htot_pos : 88 < total := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hklen hcap
    rcases hklen with rfl | rfl | rfl <;> rcases hcap with rfl | rfl <;> decide
  have hstride8 : stride % 8 = 0 := by dsimp [stride]; omega
  have hsz1_8 : sz1 % 8 = 0 := by
    have : 8 ∣ stride := Nat.dvd_of_mod_eq_zero hstride8
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left_of_dvd this _)
  have hsz2_8 : sz2 % 8 = 0 := by dsimp [sz2]; omega
  have hsz3_8 : sz3 % 8 = 0 := by dsimp [sz3]; omega
  have h264 : scratchStart < 2 ^ 64 ∧ scratchStart ≤ heapEnd := ⟨by decide, by decide⟩
  set entry := callEntryStateHOLFinite s
    ((HolFiniteMapExact.empty.update (ofString "key_len", .val (.word (BitVec.ofNat 64 klen)))).update
      (ofString "cap", .val (.word (BitVec.ofNat 64 cap))))
  have hentry_code : entry.code = originalRuntimeCode := hcode
  have hentry_clk : entry.clock = s.clock - 1 := rfl
  have hentry_hp : entry.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 p))) := hp_lu
  have hbody : (sourceFunctionEntry Guest.Software.guestFn_htab_new).2.2.1 =
      .decCall (ofString "t") .one (ofString "alloc") [.const 88#64]
        (.dec (ofString "stride") .one
          (.op .and [.op .add [.var .local (ofString "key_len"), .const 7#64],
            .op .sub [.const 0#64, .const 8#64]])
          (.dec (ofString "ncap") .one (.var .local (ofString "cap"))
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "ncap")) (.const 2#64))
                (.assign .local (ofString "ncap") (.const 2#64))
                .skip)
              (.seq
                (.store (.op .add [.var .local (ofString "t"), .const 0#64]) (.var .local (ofString "key_len")))
                (.seq
                  (.store (.op .add [.var .local (ofString "t"), .const 8#64]) (.var .local (ofString "stride")))
                  (.seq
                    (.store (.op .add [.var .local (ofString "t"), .const 16#64]) (.var .local (ofString "cap")))
                    (.seq
                      (.store (.op .add [.var .local (ofString "t"), .const 24#64]) (.const 0#64))
                      (.decCall (ofString "keys") .one (ofString "alloc")
                        [.panop .mul [.op .add [.var .local (ofString "ncap"), .const 1#64], .var .local (ofString "stride")]]
                        (.seq
                          (.store (.op .add [.var .local (ofString "t"), .const 32#64]) (.var .local (ofString "keys")))
                          (.decCall (ofString "nodes") .one (ofString "alloc")
                            [.panop .mul [.op .add [.var .local (ofString "ncap"), .const 1#64], .const 32#64]]
                            (.seq
                              (.store (.op .add [.var .local (ofString "t"), .const 40#64]) (.var .local (ofString "nodes")))
                              (.decCall (ofString "order") .one (ofString "alloc")
                                [.panop .mul [.op .add [.var .local (ofString "ncap"), .const 1#64], .const 8#64]]
                                (.seq
                                  (.store (.op .add [.var .local (ofString "t"), .const 48#64]) (.var .local (ofString "order")))
                                  (.seq
                                    (.store (.op .add [.var .local (ofString "t"), .const 56#64]) (.const 0#64))
                                    (.seq
                                      (.store (.op .add [.var .local (ofString "t"), .const 64#64]) (.const 1#64))
                                      (.seq
                                        (.store (.op .add [.var .local (ofString "t"), .const 72#64]) (.const 0#64))
                                        (.seq
                                          (.store (.op .add [.var .local (ofString "t"), .const 80#64]) (.var .local (ofString "ncap")))
                                          (.return (.var .local (ofString "t")))))))))))))))))))) := rfl
  rw [hbody]
  -- 1st alloc: 88 bytes at `p`
  rw [eval_decCall_alloc_aligned entry (ofString "t") (.const 88#64) _ p 88
    hentry_code (by omega) hp8 (by omega) (by omega) hentry_hp rfl]
  dsimp only
  set s1 := setVarHOLFinite (ofString "t") (.val (.word (BitVec.ofNat 64 p)))
    { entry with
      globals := entry.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (p + 88)))),
      clock := entry.clock - 1 }
  -- Helper for evaluating stride & mul expressions on concrete small `klen ∈ [20, 32, 52]`, `cap ∈ [16, 64]`
  have hklen_lu1 : s1.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 klen))) := by
    simp [s1, entry, callEntryStateHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show (ofString "t" == ofString "key_len") = false by decide,
      show (ofString "cap" == ofString "key_len") = false by decide]
  have hcap_lu1 : s1.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 cap))) := by
    simp [s1, entry, callEntryStateHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show (ofString "t" == ofString "cap") = false by decide]
  have hstride_ev : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.op .and [.op .add [.var .local (ofString "key_len"), .const 7#64], .op .sub [.const 0#64, .const 8#64]]) =
      some (.val (.word (BitVec.ofNat 64 stride))) := by
    simp only [evalHOLExact, evalListHOLExact, hklen_lu1, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, Option.some.injEq,
      ValueHOL.val.injEq, HolWordLab.word.injEq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hklen
    rcases hklen with rfl | rfl | rfl <;> (dsimp [stride]; decide)
  rw [evaluateHOLFiniteState_dec_total]; dsimp only; rw [hstride_ev]; dsimp only
  have hsh_one : ∀ w : BitVec 64, shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true :=
    fun _ => by simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos (hsh_one _)]; dsimp only
  set s2 := setVarHOLFinite (ofString "stride") (.val (.word (BitVec.ofNat 64 stride))) s1
  have hcap_ev2 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
      (.var .local (ofString "cap")) = some (.val (.word (BitVec.ofNat 64 cap))) := by
    simp [evalHOLExact, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hcap_lu1,
      show (ofString "stride" == ofString "cap") = false by decide]
  rw [evaluateHOLFiniteState_dec_total]; dsimp only; rw [hcap_ev2]; dsimp only
  rw [if_pos (hsh_one _)]; dsimp only
  set s3 := setVarHOLFinite (ofString "ncap") (.val (.word (BitVec.ofNat 64 cap))) s2
  -- `ite (ncap < 2)` -> false (`skip`)
  have hncap_lu3 : s3.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 cap))) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hite_ncap : evaluateHOLFiniteState s3
      (.ite (.cmp .lower (.var .local (ofString "ncap")) (.const 2#64))
        (.assign .local (ofString "ncap") (.const 2#64)) .skip) = (none, s3) := by
    rw [evaluateHOLFiniteState_ite]
    have hc_ev : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
        (.cmp .lower (.var .local (ofString "ncap")) (.const 2#64)) = some (.val (.word 0#64)) := by
      simp only [evalHOLExact, hncap_lu3, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq,
        ValueHOL.val.injEq, HolWordLab.word.injEq]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcap
      rcases hcap with rfl | rfl <;> decide
    rw [hc_ev]; simp [evaluateHOLFiniteState_skip]
  rw [evaluateHOLFiniteState_seq_line780, hite_ncap]; dsimp only
  -- Helper for aligned header store at `t + off` (`off < 88`, `off % 8 = 0`)
  have hdom_hdr : ∀ off : Nat, off < 88 → off % 8 = 0 →
      ordinaryDomain (BitVec.ofNat 64 p + BitVec.ofNat 64 off) := by
    intro off hoff hoff8
    have hp_lt : p < 2 ^ 64 := by omega
    have hoff_lt : off < 2 ^ 64 := by omega
    have hpo_lt : p + off < 2 ^ 64 := by omega
    rw [ordinaryDomain_iff, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hp_lt, Nat.mod_eq_of_lt hoff_lt, Nat.mod_eq_of_lt hpo_lt]
    exact ⟨by omega, by omega, by omega⟩
  have hhdr_lt_sc : ∀ off : Nat, off < 88 → ∀ a : BitVec 64, scratchStart ≤ a.toNat →
      a ≠ BitVec.ofNat 64 p + BitVec.ofNat 64 off := by
    intro off hoff a ha heq
    have hp_lt : p < 2 ^ 64 := by omega
    have hoff_lt : off < 2 ^ 64 := by omega
    have hpo_lt : p + off < 2 ^ 64 := by omega
    have : (BitVec.ofNat 64 p + BitVec.ofNat 64 off).toNat = p + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hp_lt, Nat.mod_eq_of_lt hoff_lt, Nat.mod_eq_of_lt hpo_lt]
    rw [heq, this] at ha; omega
  -- Generic header-word store step:
  have hstep_store : ∀ (st : PanSemStateFiniteExact 64 F) (off : Nat) (src : ExpHOL 64) (wv : BitVec 64) (rest : ProgHOL 64),
      off < 88 → off % 8 = 0 → st.memaddrs = ordinaryDomain →
      st.locals.lookup (ofString "t") = some (.val (.word (BitVec.ofNat 64 p))) →
      evalAt st src = some (.val (.word wv)) →
      ∃ st' : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState st (.seq (.store (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 off)]) src) rest) =
          evaluateHOLFiniteState st' rest ∧
        st'.locals = st.locals ∧ st'.globals = st.globals ∧ st'.code = st.code ∧
        st'.memaddrs = st.memaddrs ∧ st'.clock = st.clock ∧
        (∀ a : BitVec 64, scratchStart ≤ a.toNat → st'.memory a = st.memory a) := by
    intro st off src wv rest hoff hoff8 hma ht_lu hsrc
    have hdst : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 off)]) =
        some (.val (.word (BitVec.ofNat 64 p + BitVec.ofNat 64 off))) := by
      simp [evalHOLExact, evalListHOLExact, ht_lu, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero]
    have hdom_a : st.memaddrs (BitVec.ofNat 64 p + BitVec.ofNat 64 off) := by
      rw [hma]; exact hdom_hdr off hoff hoff8
    refine ⟨{ st with memory := fun cur => if cur = BitVec.ofNat 64 p + BitVec.ofNat 64 off then .word wv else st.memory cur },
      ?_, rfl, rfl, rfl, rfl, rfl, fun a ha => if_neg (hhdr_lt_sc off hoff a ha)⟩
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store]
    simp only [evalAt] at hsrc
    simp [hdst, hsrc, flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom_a]
  -- Lookups in `s3`
  have ht_s3 : s3.locals.lookup (ofString "t") = some (.val (.word (BitVec.ofNat 64 p))) := by
    simp [s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show (ofString "ncap" == ofString "t") = false by decide,
      show (ofString "stride" == ofString "t") = false by decide]
  have hklen_s3 : s3.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 klen))) := by
    simp [s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hklen_lu1,
      show (ofString "ncap" == ofString "key_len") = false by decide,
      show (ofString "stride" == ofString "key_len") = false by decide]
  have hstride_s3 : s3.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 stride))) := by
    simp [s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show (ofString "ncap" == ofString "stride") = false by decide]
  have hcap_s3 : s3.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 cap))) := by
    simp [s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hcap_lu1,
      show (ofString "ncap" == ofString "cap") = false by decide,
      show (ofString "stride" == ofString "cap") = false by decide]
  -- 4 header stores: t+0, t+8, t+16, t+24
  obtain ⟨s4, heq4, hl4, hg4, hc4, hm4, hck4, hfr4⟩ :=
    hstep_store s3 0 (.var .local (ofString "key_len")) (BitVec.ofNat 64 klen) _ (by omega) (by omega) hdom_s ht_s3 hklen_s3
  rw [heq4]
  obtain ⟨s5, heq5, hl5, hg5, hc5, hm5, hck5, hfr5⟩ :=
    hstep_store s4 8 (.var .local (ofString "stride")) (BitVec.ofNat 64 stride) _ (by omega) (by omega)
      (hm4.trans hdom_s) (hl4.symm ▸ ht_s3) (show evalAt s4 (.var .local (ofString "stride")) = _ by simp [evalAt, evalHOLExact, hl4, hstride_s3])
  rw [heq5]
  obtain ⟨s6, heq6, hl6, hg6, hc6, hm6, hck6, hfr6⟩ :=
    hstep_store s5 16 (.var .local (ofString "cap")) (BitVec.ofNat 64 cap) _ (by omega) (by omega)
      (hm5.trans (hm4.trans hdom_s)) (by rw [hl5, hl4]; exact ht_s3)
      (show evalAt s5 (.var .local (ofString "cap")) = _ by simp [evalAt, evalHOLExact, hl5, hl4, hcap_s3])
  rw [heq6]
  obtain ⟨s7, heq7, hl7, hg7, hc7, hm7, hck7, hfr7⟩ :=
    hstep_store s6 24 (.const 0#64) 0#64 _ (by omega) (by omega)
      (hm6.trans (hm5.trans (hm4.trans hdom_s))) (by rw [hl6, hl5, hl4]; exact ht_s3) rfl
  rw [heq7]
  have hl7_eq : s7.locals = s3.locals := by rw [hl7, hl6, hl5, hl4]
  have hg7_eq : s7.globals = s1.globals := by rw [hg7, hg6, hg5, hg4]; rfl
  have hc7_eq : s7.code = originalRuntimeCode := by rw [hc7, hc6, hc5, hc4]; exact hentry_code
  have hm7_eq : s7.memaddrs = ordinaryDomain := by rw [hm7, hm6, hm5, hm4]; exact hdom_s
  have hck7_eq : s7.clock = s.clock - 2 := by
    rw [hck7, hck6, hck5, hck4]; change entry.clock - 1 = s.clock - 2; omega
  -- 2nd alloc: `keys := alloc((ncap + 1) * stride)` at `p + 88`
  have hsz1_ev : evalAt s7 (.panop .mul [.op .add [.var .local (ofString "ncap"), .const 1#64], .var .local (ofString "stride")]) =
      some (.val (.word (BitVec.ofNat 64 sz1))) := by
    have hn_lu : s7.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 cap))) := hl7_eq ▸ hncap_lu3
    have hs_lu : s7.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 stride))) := hl7_eq ▸ hstride_s3
    simp only [evalAt, evalHOLExact, evalListHOLExact, hn_lu, hs_lu, wordOpHOL, wordOp, panOpHOL,
      valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hklen hcap
    rcases hklen with rfl | rfl | rfl <;> rcases hcap with rfl | rfl <;> decide
  have hhp7 : s7.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (p + 88)))) := by
    rw [hg7_eq]; simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [eval_decCall_alloc_aligned s7 (ofString "keys") _ _ (p + 88) sz1
    hc7_eq (by omega) (by omega) hsz1_8 (by omega) hhp7 hsz1_ev]
  dsimp only
  set s8 := setVarHOLFinite (ofString "keys") (.val (.word (BitVec.ofNat 64 (p + 88))))
    { s7 with
      globals := s7.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (p + 88 + sz1)))),
      clock := s7.clock - 1 }
  -- Store `t + 32 := keys`
  have ht_s8 : s8.locals.lookup (ofString "t") = some (.val (.word (BitVec.ofNat 64 p))) := by
    simp [s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl7_eq, ht_s3,
      show (ofString "keys" == ofString "t") = false by decide]
  have hkeys_s8 : evalAt s8 (.var .local (ofString "keys")) = some (.val (.word (BitVec.ofNat 64 (p + 88)))) := by
    simp [evalAt, evalHOLExact, s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨s9, heq9, hl9, hg9, hc9, hm9, hck9, hfr9⟩ :=
    hstep_store s8 32 (.var .local (ofString "keys")) (BitVec.ofNat 64 (p + 88)) _ (by omega) (by omega) hm7_eq ht_s8 hkeys_s8
  rw [heq9]
  -- 3rd alloc: `nodes := alloc((ncap + 1) * 32)` at `p + 88 + sz1`
  have hncap_s9 : s9.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 cap))) := by
    rw [hl9]; simp [s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl7_eq, hncap_lu3,
      show (ofString "keys" == ofString "ncap") = false by decide]
  have hsz2_ev : evalAt s9 (.panop .mul [.op .add [.var .local (ofString "ncap"), .const 1#64], .const 32#64]) =
      some (.val (.word (BitVec.ofNat 64 sz2))) := by
    simp only [evalAt, evalHOLExact, evalListHOLExact, hncap_s9, wordOpHOL, wordOp, panOpHOL,
      valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcap
    rcases hcap with rfl | rfl <;> decide
  have hhp9 : s9.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (p + 88 + sz1)))) := by
    rw [hg9]; simp [s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hck9_eq : s9.clock = s.clock - 3 := by
    rw [hck9]; change s7.clock - 1 = s.clock - 3; omega
  rw [eval_decCall_alloc_aligned s9 (ofString "nodes") _ _ (p + 88 + sz1) sz2
    (hc9.trans hc7_eq) (by omega) (by omega) hsz2_8 (by omega) hhp9 hsz2_ev]
  dsimp only
  set s10 := setVarHOLFinite (ofString "nodes") (.val (.word (BitVec.ofNat 64 (p + 88 + sz1))))
    { s9 with
      globals := s9.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (p + 88 + sz1 + sz2)))),
      clock := s9.clock - 1 }
  -- Store `t + 40 := nodes`
  have ht_s10 : s10.locals.lookup (ofString "t") = some (.val (.word (BitVec.ofNat 64 p))) := by
    simp [s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl9, ht_s8,
      show (ofString "nodes" == ofString "t") = false by decide]
  have hnodes_s10 : evalAt s10 (.var .local (ofString "nodes")) = some (.val (.word (BitVec.ofNat 64 (p + 88 + sz1)))) := by
    simp [evalAt, evalHOLExact, s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨s11, heq11, hl11, hg11, hc11, hm11, hck11, hfr11⟩ :=
    hstep_store s10 40 (.var .local (ofString "nodes")) (BitVec.ofNat 64 (p + 88 + sz1)) _ (by omega) (by omega)
      (hm9.trans hm7_eq) ht_s10 hnodes_s10
  rw [heq11]
  -- 4th alloc: `order := alloc((ncap + 1) * 8)` at `p + 88 + sz1 + sz2`
  have hncap_s11 : s11.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 cap))) := by
    rw [hl11]; simp [s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hncap_s9,
      show (ofString "nodes" == ofString "ncap") = false by decide]
  have hsz3_ev : evalAt s11 (.panop .mul [.op .add [.var .local (ofString "ncap"), .const 1#64], .const 8#64]) =
      some (.val (.word (BitVec.ofNat 64 sz3))) := by
    simp only [evalAt, evalHOLExact, evalListHOLExact, hncap_s11, wordOpHOL, wordOp, panOpHOL,
      valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcap
    rcases hcap with rfl | rfl <;> decide
  have hhp11 : s11.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (p + 88 + sz1 + sz2)))) := by
    rw [hg11]; simp [s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hck11_eq : s11.clock = s.clock - 4 := by
    rw [hck11]; change s9.clock - 1 = s.clock - 4; omega
  rw [eval_decCall_alloc_aligned s11 (ofString "order") _ _ (p + 88 + sz1 + sz2) sz3
    (hc11.trans (hc9.trans hc7_eq)) (by omega)
    (by omega) hsz3_8 (by omega) hhp11 hsz3_ev]
  dsimp only
  set s12 := setVarHOLFinite (ofString "order") (.val (.word (BitVec.ofNat 64 (p + 88 + sz1 + sz2))))
    { s11 with
      globals := s11.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (p + 88 + sz1 + sz2 + sz3)))),
      clock := s11.clock - 1 }
  -- Final 5 header stores: t+48, t+56, t+64, t+72, t+80, then `return t`
  have ht_s12 : s12.locals.lookup (ofString "t") = some (.val (.word (BitVec.ofNat 64 p))) := by
    simp [s12, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl11, ht_s10,
      show (ofString "order" == ofString "t") = false by decide]
  have hncap_s12 : s12.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 cap))) := by
    simp [s12, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hncap_s11,
      show (ofString "order" == ofString "ncap") = false by decide]
  have horder_s12 : evalAt s12 (.var .local (ofString "order")) = some (.val (.word (BitVec.ofNat 64 (p + 88 + sz1 + sz2)))) := by
    simp [evalAt, evalHOLExact, s12, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨s13, heq13, hl13, hg13, hc13, hm13, hck13, hfr13⟩ :=
    hstep_store s12 48 (.var .local (ofString "order")) (BitVec.ofNat 64 (p + 88 + sz1 + sz2)) _ (by omega) (by omega)
      (hm11.trans (hm9.trans hm7_eq)) ht_s12 horder_s12
  rw [heq13]
  obtain ⟨s14, heq14, hl14, hg14, hc14, hm14, hck14, hfr14⟩ :=
    hstep_store s13 56 (.const 0#64) 0#64 _ (by omega) (by omega)
      (hm13.trans (hm11.trans (hm9.trans hm7_eq))) (hl13.symm ▸ ht_s12) rfl
  rw [heq14]
  obtain ⟨s15, heq15, hl15, hg15, hc15, hm15, hck15, hfr15⟩ :=
    hstep_store s14 64 (.const 1#64) 1#64 _ (by omega) (by omega)
      (hm14.trans (hm13.trans (hm11.trans (hm9.trans hm7_eq)))) (by rw [hl14, hl13]; exact ht_s12) rfl
  rw [heq15]
  obtain ⟨s16, heq16, hl16, hg16, hc16, hm16, hck16, hfr16⟩ :=
    hstep_store s15 72 (.const 0#64) 0#64 _ (by omega) (by omega)
      (hm15.trans (hm14.trans (hm13.trans (hm11.trans (hm9.trans hm7_eq)))))
      (by rw [hl15, hl14, hl13]; exact ht_s12) rfl
  rw [heq16]
  obtain ⟨s17, heq17, hl17, hg17, hc17, hm17, hck17, hfr17⟩ :=
    hstep_store s16 80 (.var .local (ofString "ncap")) (BitVec.ofNat 64 cap) _ (by omega) (by omega)
      (hm16.trans (hm15.trans (hm14.trans (hm13.trans (hm11.trans (hm9.trans hm7_eq))))))
      (by rw [hl16, hl15, hl14, hl13]; exact ht_s12)
      (show evalAt s16 (.var .local (ofString "ncap")) = _ by
        simp [evalAt, evalHOLExact, hl16, hl15, hl14, hl13, hncap_s12])
  rw [heq17]
  -- Evaluate `.return (.var .local "t")`
  have ht_s17 : @evalHOLExact 64 F _ s17.toExact (fun a => Classical.propDecidable (s17.memaddrs a))
      (.var .local (ofString "t")) = some (.val (.word (BitVec.ofNat 64 p))) := by
    simp [evalHOLExact, hl17, hl16, hl15, hl14, hl13, ht_s12]
  have hret_ev : evaluateHOLFiniteState s17 (.return (.var .local (ofString "t"))) =
      (some (.returned (.val (.word (BitVec.ofNat 64 p)))), emptyLocalsHOLFinite s17) := by
    rw [evaluateHOLFiniteState_return, ht_s17]
    simp [shapeOfHOLExact]
  rw [hret_ev]
  dsimp only
  have htot_p : p + 88 + sz1 + sz2 + sz3 = p + total := by omega
  have hck17_eq : (emptyLocalsHOLFinite s17).clock = s.clock - 5 := by
    change s17.clock = s.clock - 5
    rw [hck17, hck16, hck15, hck14, hck13]
    change s11.clock - 1 = s.clock - 5
    omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, by rw [hck17_eq]; omega, by rw [hck17_eq]; omega, ?_⟩
  · change s17.globals.lookup (ofString "heap_ptr") = _
    rw [hg17, hg16, hg15, hg14, hg13]
    simp [s12, setVarHOLFinite, htot_p, HolFiniteMapExact.lookup_update, FUPDATE]
  · intro k hk
    have hb : (ofString "heap_ptr" == k) = false := beq_false_of_ne hk.symm
    change s17.globals.lookup k = _
    rw [hg17, hg16, hg15, hg14, hg13]
    simp [s12, setVarHOLFinite, hg11, s10, hg9, s8, hg7_eq, s1, entry, callEntryStateHOLFinite,
      HolFiniteMapExact.lookup_update, FUPDATE, hb]
  · change s17.memaddrs = _
    rw [hm17, hm16, hm15, hm14, hm13]
    change s11.memaddrs = s.memaddrs
    rw [hm11]
    change s9.memaddrs = s.memaddrs
    rw [hm9]
    change s7.memaddrs = s.memaddrs
    rw [hm7_eq, hdom_s]
  · change s17.code = _
    rw [hc17, hc16, hc15, hc14, hc13]
    change s11.code = s.code
    rw [hc11]
    change s9.code = s.code
    rw [hc9]
    change s7.code = s.code
    rw [hc7_eq, hcode]
  · intro a ha
    change s17.memory a = s.memory a
    rw [hfr17 a ha, hfr16 a ha, hfr15 a ha, hfr14 a ha, hfr13 a ha]
    change s11.memory a = s.memory a
    rw [hfr11 a ha]
    change s9.memory a = s.memory a
    rw [hfr9 a ha]
    change s7.memory a = s.memory a
    rw [hfr7 a ha, hfr6 a ha, hfr5 a ha, hfr4 a ha]
    rfl

private theorem eval_decCall_htab_new_frame {F : Type}
    (s : PanSemStateFiniteExact 64 F) (cont : ProgHOL 64) (p klen cap : Nat)
    (hcode : s.code = originalRuntimeCode) (hdom_s : s.memaddrs = ordinaryDomain)
    (hclk : 20 ≤ s.clock) (hp_lo : sourceBase ≤ p) (hp8 : p % 8 = 0)
    (hklen : klen ∈ ([20, 32, 52] : List Nat)) (hcap : cap ∈ ([16, 64] : List Nat))
    (hfit : p + (88 + (cap + 1) * ((klen + 7) / 8 * 8 + 40)) ≤ scratchStart)
    (hp_lu : s.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 p)))) :
    ∃ s' : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s
        (.decCall (ofString "t") .one (ofString "htab_new")
          [.const (BitVec.ofNat 64 klen), .const (BitVec.ofNat 64 cap)] cont) =
        ((evaluateHOLFiniteState s' cont).1,
          { (evaluateHOLFiniteState s' cont).2 with
            locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s' cont).2.locals
              (ofString "t", s.locals.lookup (ofString "t")) }) ∧
      s'.locals.lookup (ofString "t") = some (.val (.word (BitVec.ofNat 64 p))) ∧
      s'.globals.lookup (ofString "heap_ptr") =
        some (.val (.word (BitVec.ofNat 64 (p + (88 + (cap + 1) * ((klen + 7) / 8 * 8 + 40)))))) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s'.globals.lookup k = s.globals.lookup k) ∧
      s'.memaddrs = s.memaddrs ∧ s'.code = s.code ∧
      s.clock ≤ s'.clock + 20 ∧ s'.clock < s.clock ∧
      (∀ a : BitVec 64, scratchStart ≤ a.toNat → s'.memory a = s.memory a) := by
  have hcode_hn : originalRuntimeCode.lookup (ofString "htab_new") =
      some ([(ofString "key_len", .one), (ofString "cap", .one)],
        (sourceFunctionEntry Guest.Software.guestFn_htab_new).2.2.1, .one) := lookup_htab_new_fn
  have hlook : lookupCodeHOLFinite s.code.lookup (ofString "htab_new")
      [.val (.word (BitVec.ofNat 64 klen)), .val (.word (BitVec.ofNat 64 cap))] =
      some ((sourceFunctionEntry Guest.Software.guestFn_htab_new).2.2.1,
        (HolFiniteMapExact.empty.update (ofString "key_len", .val (.word (BitVec.ofNat 64 klen)))).update
          (ofString "cap", .val (.word (BitVec.ofNat 64 cap))), .one) := by
    rw [hcode]
    exact pan_two_word_lookup originalRuntimeCode.lookup (ofString "htab_new")
      (ofString "key_len") (ofString "cap") _ _ _ (by decide) hcode_hn
  have hstep := eval_htab_new_body_frame s p klen cap hcode hdom_s hclk hp_lo hp8 hklen hcap hfit hp_lu
  dsimp only at hstep
  set entry := callEntryStateHOLFinite s
    ((HolFiniteMapExact.empty.update (ofString "key_len", .val (.word (BitVec.ofNat 64 klen)))).update
      (ofString "cap", .val (.word (BitVec.ofNat 64 cap))))
  rcases hrun : evaluateHOLFiniteState entry (sourceFunctionEntry Guest.Software.guestFn_htab_new).2.2.1 with ⟨res, post⟩
  rw [hrun] at hstep
  dsimp only at hstep
  obtain ⟨rfl, hhp, hg_other, hma, hc, hck_lo, hck_hi, hmem_fr⟩ := hstep
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const (BitVec.ofNat 64 klen), .const (BitVec.ofNat 64 cap)] =
      some [.val (.word (BitVec.ofNat 64 klen)), .val (.word (BitVec.ofNat 64 cap))] := rfl
  set resumed := setVarHOLFinite (ofString "t") (.val (.word (BitVec.ofNat 64 p))) { post with locals := s.locals }
  refine ⟨resumed, ?_,
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
    hhp, hg_other, hma, hc, by dsimp [resumed, setVarHOLFinite]; omega,
    by dsimp [resumed, setVarHOLFinite]; omega, hmem_fr⟩
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]
  dsimp only; rw [hlook]; dsimp only
  rw [if_neg (by omega), hrun]; dsimp only
  have hsh_ok : (shapeEqHOL (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 p)) : ValueHOL 64)) .one &&
      shapeEqHOL (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 p)) : ValueHOL 64)) .one) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  rw [if_pos hsh_ok]

private theorem eval_call_local_htab_new_frame {F : Type}
    (s : PanSemStateFiniteExact 64 F) (wt_prev : BitVec 64) (p klen cap : Nat)
    (hcode : s.code = originalRuntimeCode) (hdom_s : s.memaddrs = ordinaryDomain)
    (hclk : 20 ≤ s.clock) (hp_lo : sourceBase ≤ p) (hp8 : p % 8 = 0)
    (hklen : klen ∈ ([20, 32, 52] : List Nat)) (hcap : cap ∈ ([16, 64] : List Nat))
    (hfit : p + (88 + (cap + 1) * ((klen + 7) / 8 * 8 + 40)) ≤ scratchStart)
    (hp_lu : s.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 p))))
    (ht_lu : s.locals.lookup (ofString "t") = some (.val (.word wt_prev))) :
    ∃ s' : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s
        (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new")
          [.const (BitVec.ofNat 64 klen), .const (BitVec.ofNat 64 cap)]) =
        (none, s') ∧
      s'.locals.lookup (ofString "t") = some (.val (.word (BitVec.ofNat 64 p))) ∧
      s'.globals.lookup (ofString "heap_ptr") =
        some (.val (.word (BitVec.ofNat 64 (p + (88 + (cap + 1) * ((klen + 7) / 8 * 8 + 40)))))) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s'.globals.lookup k = s.globals.lookup k) ∧
      s'.memaddrs = s.memaddrs ∧ s'.code = s.code ∧
      s.clock ≤ s'.clock + 20 ∧ s'.clock < s.clock ∧
      (∀ a : BitVec 64, scratchStart ≤ a.toNat → s'.memory a = s.memory a) := by
  have hcode_hn : originalRuntimeCode.lookup (ofString "htab_new") =
      some ([(ofString "key_len", .one), (ofString "cap", .one)],
        (sourceFunctionEntry Guest.Software.guestFn_htab_new).2.2.1, .one) := lookup_htab_new_fn
  have hlook : lookupCodeHOLFinite s.code.lookup (ofString "htab_new")
      [.val (.word (BitVec.ofNat 64 klen)), .val (.word (BitVec.ofNat 64 cap))] =
      some ((sourceFunctionEntry Guest.Software.guestFn_htab_new).2.2.1,
        (HolFiniteMapExact.empty.update (ofString "key_len", .val (.word (BitVec.ofNat 64 klen)))).update
          (ofString "cap", .val (.word (BitVec.ofNat 64 cap))), .one) := by
    rw [hcode]
    exact pan_two_word_lookup originalRuntimeCode.lookup (ofString "htab_new")
      (ofString "key_len") (ofString "cap") _ _ _ (by decide) hcode_hn
  have hstep := eval_htab_new_body_frame s p klen cap hcode hdom_s hclk hp_lo hp8 hklen hcap hfit hp_lu
  dsimp only at hstep
  set entry := callEntryStateHOLFinite s
    ((HolFiniteMapExact.empty.update (ofString "key_len", .val (.word (BitVec.ofNat 64 klen)))).update
      (ofString "cap", .val (.word (BitVec.ofNat 64 cap))))
  rcases hrun : evaluateHOLFiniteState entry (sourceFunctionEntry Guest.Software.guestFn_htab_new).2.2.1 with ⟨res, post⟩
  rw [hrun] at hstep
  dsimp only at hstep
  obtain ⟨rfl, hhp, hg_other, hma, hc, hck_lo, hck_hi, hmem_fr⟩ := hstep
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const (BitVec.ofNat 64 klen), .const (BitVec.ofNat 64 cap)] =
      some [.val (.word (BitVec.ofNat 64 klen)), .val (.word (BitVec.ofNat 64 cap))] := rfl
  set resumed := setVarHOLFinite (ofString "t") (.val (.word (BitVec.ofNat 64 p))) { post with locals := s.locals }
  refine ⟨resumed, ?_,
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
    hhp, hg_other, hma, hc, by dsimp [resumed, setVarHOLFinite]; omega,
    by dsimp [resumed, setVarHOLFinite]; omega, hmem_fr⟩
  rw [evaluateHOLFiniteState_call, hargs]
  dsimp only; rw [hlook]; dsimp only
  rw [if_neg (by omega), hrun]; dsimp only
  have hsh_ok : shapeEqHOL (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 p)) : ValueHOL 64)) .one = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  have hval_ok : isValidValueHOLExact s.toExact .local (ofString "t") (.val (.word (BitVec.ofNat 64 p))) = true := by
    simp [isValidValueHOLExact, lookupKvarHOLExact, ht_lu, shapeOfHOLExact, shapeEqHOL]
  rw [if_pos hsh_ok, if_pos hval_ok]; rfl

private theorem panMemStoresHOL_replicate_99 (k : Nat) :
    ∀ (x : BitVec 64) (mem : BitVec 64 → HolWordLab 64),
      x.toNat % 8 = 0 → sourceBase ≤ x.toNat → x.toNat + 8 * k ≤ heapEnd →
      ∃ mem' : BitVec 64 → HolWordLab 64,
        @panMemStoresHOL 64 _ x (List.replicate k (.word 99#64)) ordinaryDomain
          (fun a => Classical.propDecidable (ordinaryDomain a)) mem = some mem' ∧
        (1 ≤ k → mem' (BitVec.ofNat 64 (x.toNat + 8 * (k - 1))) = .word 99#64) := by
  induction k with
  | zero =>
    intro x mem _ _ _
    exact ⟨mem, rfl, fun h => by omega⟩
  | succ k ih =>
    intro x mem hx8 hlo hhi
    have h264 : heapEnd < 2 ^ 64 := by decide
    have hdom_x : ordinaryDomain x := (ordinaryDomain_iff x).2 ⟨hx8, hlo, by omega⟩
    have hbw : (panBytesInWord 64 : BitVec 64) = 8#64 := rfl
    have hx8_nat : (x + 8#64).toNat = x.toNat + 8 := by
      rw [BitVec.toNat_add]; change (x.toNat + 8) % 2 ^ 64 = x.toNat + 8
      exact Nat.mod_eq_of_lt (by omega)
    rcases k with _ | k'
    · refine ⟨fun cur => if cur = x then .word 99#64 else mem cur, ?_, fun _ => ?_⟩
      · simp [List.replicate, panMemStoresHOL, panMemStoreHOL, hdom_x]
      · have h_eq : BitVec.ofNat 64 (x.toNat + 8 * 0) = x := by
          apply BitVec.eq_of_toNat_eq
          rw [Nat.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        dsimp only
        rw [h_eq, if_pos rfl]
    · obtain ⟨mem', hst', hlast⟩ :=
        ih (x + 8#64) (fun cur => if cur = x then .word 99#64 else mem cur)
          (by rw [hx8_nat]; omega) (by rw [hx8_nat]; omega) (by rw [hx8_nat]; omega)
      refine ⟨mem', ?_, fun _ => ?_⟩
      · simp only [List.replicate_succ, panMemStoresHOL, panMemStoreHOL, hdom_x, ↓reduceIte, hbw]
        exact hst'
      · have hlast' := hlast (by omega)
        rw [hx8_nat] at hlast'
        have h_idx : x.toNat + 8 + 8 * (k' + 1 - 1) = x.toNat + 8 * (k' + 1 + 1 - 1) := by omega
        rw [← h_idx]
        exact hlast'

private theorem flattenHOL_cxBsVal :
    flattenHOL cxBsVal = List.replicate 2751 (.word 99#64) := by
  unfold cxBsVal
  have h1 : flattenHOL (.val (.word 99#64) : ValueHOL 64) = [.word 99#64] := by unfold flattenHOL; rfl
  have hlist : ∀ n : Nat,
      (List.map flattenHOL (List.replicate n (.val (.word 99#64) : ValueHOL 64))).flatten =
        List.replicate n (.word 99#64) := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih =>
      simp only [List.replicate_succ, List.map_cons, List.flatten_cons, h1, List.singleton_append]
      exact congrArg (HolWordLab.word 99#64 :: ·) ih
  conv_lhs => unfold flattenHOL
  exact hlist 2751

private theorem cxSftx_runs_and_writes_scratchStart :
    let out := evaluateHOLFiniteState cxSftxState
      (sourceFunctionEntry Guest.Software.guestFn_state_fresh_tx).2.2.1
    out.1 = some (.returned (.val (.word 0#64))) ∧
    out.2.memory (BitVec.ofNat 64 scratchStart) = .word 99#64 := by
  dsimp only
  have hbody : (sourceFunctionEntry Guest.Software.guestFn_state_fresh_tx).2.2.1 =
      .seq (.call (some (some (.global, ofString "ts"), none)) (ofString "alloc") [.const 72#64])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 0#64]) (.var .global (ofString "bs")))
      (.decCall (ofString "t") .one (ofString "htab_new") [.const 20#64, .const 64#64]
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 8#64]) (.var .local (ofString "t")))
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20#64, .const 64#64])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 16#64]) (.var .local (ofString "t")))
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 52#64, .const 64#64])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 24#64]) (.var .local (ofString "t")))
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20#64, .const 16#64])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 32#64]) (.var .local (ofString "t")))
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 52#64, .const 16#64])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 40#64]) (.var .local (ofString "t")))
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 32#64, .const 16#64])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 48#64]) (.var .local (ofString "t")))
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20#64, .const 16#64])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 56#64]) (.var .local (ofString "t")))
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 52#64, .const 16#64])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 64#64]) (.var .local (ofString "t")))
      (.seq (.assign .global (ofString "journal_n") (.const 0#64))
      (.return (.const 0#64)))))))))))))))))))) := rfl
  rw [hbody]
  have hhp0 : cxSftxState.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (BitVec.ofNat 64 cxHpInit))) := by
    simp [cxSftxState, cxSftxGlobals, HolFiniteMapExact.lookup_update, FUPDATE,
      sftx_nm1, sftx_nm2, sftx_nm3, sftx_nm7, sftx_nm11]
  have hts0_lu : cxSftxState.globals.lookup (ofString "ts") = some (.val (.word 0#64)) := by
    simp [cxSftxState, cxSftxGlobals, HolFiniteMapExact.lookup_update, FUPDATE,
      show (ofString "bs" == ofString "ts") = false by decide,
      show (ofString "journal_n" == ofString "ts") = false by decide]
  -- 1. `ts := alloc(72)`
  rw [evaluateHOLFiniteState_seq_line780,
    eval_call_global_alloc_aligned cxSftxState (ofString "ts") 0#64 cxHpInit 72
      rfl (by decide) (by unfold cxHpInit; decide) (by omega) (by unfold cxHpInit; decide) hhp0 hts0_lu]
  dsimp only
  set st1 := setGlobalHOLFinite (ofString "ts") (.val (.word (BitVec.ofNat 64 cxHpInit)))
    { cxSftxState with
      globals := cxSftxState.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (cxHpInit + 72)))),
      clock := cxSftxState.clock - 1 }
  -- 2. `store (ts + 0) bs` (writes 2751 words of `99#64` from `cxHpInit` up to `cxHpInit + 22000 = scratchStart`!)
  have hts_st1 : st1.globals.lookup (ofString "ts") = some (.val (.word (BitVec.ofNat 64 cxHpInit))) := by
    simp [st1, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hbs_st1 : st1.globals.lookup (ofString "bs") = some cxBsVal := by
    simp [st1, setGlobalHOLFinite, cxSftxState, cxSftxGlobals, HolFiniteMapExact.lookup_update, FUPDATE,
      show (ofString "ts" == ofString "bs") = false by decide,
      show (ofString "heap_ptr" == ofString "bs") = false by decide]
  have hdst0 : @evalHOLExact 64 _ _ st1.toExact (fun a => Classical.propDecidable (st1.memaddrs a))
      (.op .add [.var .global (ofString "ts"), .const 0#64]) =
      some (.val (.word (BitVec.ofNat 64 cxHpInit))) := by
    simp [evalHOLExact, evalListHOLExact, hts_st1, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero]
  have hsrc_bs : @evalHOLExact 64 _ _ st1.toExact (fun a => Classical.propDecidable (st1.memaddrs a))
      (.var .global (ofString "bs")) = some cxBsVal := hbs_st1
  have hts_nat : (BitVec.ofNat 64 cxHpInit).toNat = cxHpInit := by
    unfold cxHpInit; decide
  obtain ⟨mem_bs, hst_bs, hmem_bs_last⟩ :=
    panMemStoresHOL_replicate_99 2751 (BitVec.ofNat 64 cxHpInit) st1.memory
      (by rw [hts_nat]; unfold cxHpInit; decide)
      (by rw [hts_nat]; unfold cxHpInit; decide)
      (by rw [hts_nat]; unfold cxHpInit; decide)
  have hsc_eq : cxHpInit + 8 * (2751 - 1) = scratchStart := by unfold cxHpInit; decide
  have hmem_bs_sc : mem_bs (BitVec.ofNat 64 scratchStart) = .word 99#64 := by
    rw [← hsc_eq, ← hts_nat]; exact hmem_bs_last (by omega)
  rw [evaluateHOLFiniteState_seq_line780]
  have hstore_bs_ev : evaluateHOLFiniteState st1
      (.store (.op .add [.var .global (ofString "ts"), .const 0#64]) (.var .global (ofString "bs"))) =
      (none, { st1 with memory := mem_bs }) := by
    rw [evaluateHOLFiniteState_store, hdst0, hsrc_bs]
    dsimp only
    rw [flattenHOL_cxBsVal]
    have hma_st1 : st1.memaddrs = ordinaryDomain := rfl
    have hst_bs' : @panMemStoresHOL 64 _ (BitVec.ofNat 64 cxHpInit) (List.replicate 2751 (.word 99#64))
        st1.memaddrs (fun a => Classical.propDecidable (st1.memaddrs a)) st1.memory = some mem_bs := hst_bs
    rw [hst_bs']
  rw [hstore_bs_ev]; dsimp only
  set st2 : PanSemStateFiniteExact 64 Guest.HostMemory := { st1 with memory := mem_bs }
  -- Helper for `store (ts + off) t` (`off ∈ [8, 16, 24, 32, 40, 48, 56, 64]`):
  have hts_store_step : ∀ (st : PanSemStateFiniteExact 64 Guest.HostMemory) (off : Nat) (wt : BitVec 64) (rest : ProgHOL 64),
      off < 72 → off % 8 = 0 → st.memaddrs = ordinaryDomain →
      st.globals.lookup (ofString "ts") = some (.val (.word (BitVec.ofNat 64 cxHpInit))) →
      st.locals.lookup (ofString "t") = some (.val (.word wt)) →
      st.memory (BitVec.ofNat 64 scratchStart) = .word 99#64 →
      ∃ st' : PanSemStateFiniteExact 64 Guest.HostMemory,
        evaluateHOLFiniteState st (.seq (.store (.op .add [.var .global (ofString "ts"), .const (BitVec.ofNat 64 off)]) (.var .local (ofString "t"))) rest) =
          evaluateHOLFiniteState st' rest ∧
        st'.locals = st.locals ∧ st'.globals = st.globals ∧ st'.code = st.code ∧
        st'.memaddrs = st.memaddrs ∧ st'.clock = st.clock ∧
        st'.memory (BitVec.ofNat 64 scratchStart) = .word 99#64 := by
    intro st off wt rest hoff hoff8 hma hts_g ht_l hm_sc
    have h264 : scratchStart < 2 ^ 64 ∧ scratchStart ≤ heapEnd := ⟨by decide, by decide⟩
    have hhp_lo : sourceBase ≤ cxHpInit ∧ cxHpInit + 72 < scratchStart ∧ cxHpInit % 8 = 0 := by
      unfold cxHpInit; decide
    have hcx_lt : cxHpInit < 2 ^ 64 := by omega
    have hoff_lt : off < 2 ^ 64 := by omega
    have hcxo_lt : cxHpInit + off < 2 ^ 64 := by omega
    have hdom_a : st.memaddrs (BitVec.ofNat 64 cxHpInit + BitVec.ofNat 64 off) := by
      rw [hma, ordinaryDomain_iff, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hcx_lt, Nat.mod_eq_of_lt hoff_lt, Nat.mod_eq_of_lt hcxo_lt]
      exact ⟨by omega, by omega, by omega⟩
    have hne_sc : BitVec.ofNat 64 scratchStart ≠ BitVec.ofNat 64 cxHpInit + BitVec.ofNat 64 off := by
      intro heq
      have hlhs : (BitVec.ofNat 64 scratchStart).toNat = scratchStart := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h264.1]
      have hrhs : (BitVec.ofNat 64 cxHpInit + BitVec.ofNat 64 off).toNat = cxHpInit + off := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hcx_lt, Nat.mod_eq_of_lt hoff_lt, Nat.mod_eq_of_lt hcxo_lt]
      have := congrArg BitVec.toNat heq; omega
    refine ⟨{ st with memory := fun cur => if cur = BitVec.ofNat 64 cxHpInit + BitVec.ofNat 64 off then .word wt else st.memory cur },
      ?_, rfl, rfl, rfl, rfl, rfl, by dsimp only; rw [if_neg hne_sc]; exact hm_sc⟩
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store]
    have hdst : @evalHOLExact 64 _ _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.op .add [.var .global (ofString "ts"), .const (BitVec.ofNat 64 off)]) =
        some (.val (.word (BitVec.ofNat 64 cxHpInit + BitVec.ofNat 64 off))) := by
      simp [evalHOLExact, evalListHOLExact, hts_g, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hsrc : @evalHOLExact 64 _ _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.var .local (ofString "t")) = some (.val (.word wt)) := ht_l
    simp [hdst, hsrc, flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom_a]
  -- Helper for `call "t" := htab_new(klen, cap); store (ts + off) t` step!
  have hcall_and_store : ∀ (st : PanSemStateFiniteExact 64 Guest.HostMemory) (wt_prev : BitVec 64)
      (p klen cap off : Nat) (rest : ProgHOL 64),
      st.code = originalRuntimeCode → st.memaddrs = ordinaryDomain →
      20 ≤ st.clock → sourceBase ≤ p → p % 8 = 0 →
      klen ∈ ([20, 32, 52] : List Nat) → cap ∈ ([16, 64] : List Nat) →
      off < 72 → off % 8 = 0 →
      p + (88 + (cap + 1) * ((klen + 7) / 8 * 8 + 40)) ≤ scratchStart →
      st.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 p))) →
      st.globals.lookup (ofString "ts") = some (.val (.word (BitVec.ofNat 64 cxHpInit))) →
      st.globals.lookup (ofString "journal_n") = some (.val (.word 0#64)) →
      st.locals.lookup (ofString "t") = some (.val (.word wt_prev)) →
      st.memory (BitVec.ofNat 64 scratchStart) = .word 99#64 →
      ∃ st'' : PanSemStateFiniteExact 64 Guest.HostMemory,
        evaluateHOLFiniteState st
          (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new")
              [.const (BitVec.ofNat 64 klen), .const (BitVec.ofNat 64 cap)])
            (.seq (.store (.op .add [.var .global (ofString "ts"), .const (BitVec.ofNat 64 off)]) (.var .local (ofString "t"))) rest)) =
          evaluateHOLFiniteState st'' rest ∧
        st''.code = originalRuntimeCode ∧ st''.memaddrs = ordinaryDomain ∧
        st.clock ≤ st''.clock + 20 ∧
        st''.globals.lookup (ofString "heap_ptr") =
          some (.val (.word (BitVec.ofNat 64 (p + (88 + (cap + 1) * ((klen + 7) / 8 * 8 + 40)))))) ∧
        st''.globals.lookup (ofString "ts") = some (.val (.word (BitVec.ofNat 64 cxHpInit))) ∧
        st''.globals.lookup (ofString "journal_n") = some (.val (.word 0#64)) ∧
        st''.locals.lookup (ofString "t") = some (.val (.word (BitVec.ofNat 64 p))) ∧
        st''.memory (BitVec.ofNat 64 scratchStart) = .word 99#64 := by
    intro st wt_prev p klen cap off rest hc hma hck hplo hp8 hkl hcp hoff hoff8 hfit hhp hts hjn ht hm_sc
    obtain ⟨st1', hcall, ht1, hhp1, hg_o1, hma1, hc1, hck1, _, hfr1⟩ :=
      eval_call_local_htab_new_frame st wt_prev p klen cap hc hma hck hplo hp8 hkl hcp hfit hhp ht
    have h264 : scratchStart < 2 ^ 64 := by decide
    have hsc_nat : (BitVec.ofNat 64 scratchStart).toNat = scratchStart := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h264]
    have hm_sc1 : st1'.memory (BitVec.ofNat 64 scratchStart) = .word 99#64 := by
      rw [hfr1 _ (by rw [hsc_nat]), hm_sc]
    have hts1 : st1'.globals.lookup (ofString "ts") = some (.val (.word (BitVec.ofNat 64 cxHpInit))) := by
      rw [hg_o1 _ (by decide)]; exact hts
    have hjn1 : st1'.globals.lookup (ofString "journal_n") = some (.val (.word 0#64)) := by
      rw [hg_o1 _ (by decide)]; exact hjn
    obtain ⟨st2', hst_eq, hl2, hg2, hc2, hma2, hck2, hm_sc2⟩ :=
      hts_store_step st1' off (BitVec.ofNat 64 p) rest hoff hoff8 (hma1.trans hma) hts1 ht1 hm_sc1
    refine ⟨st2', ?_, hc2.trans (hc1.trans hc), hma2.trans (hma1.trans hma),
      by rw [hck2]; exact hck1, hg2 ▸ hhp1, hg2 ▸ hts1, hg2 ▸ hjn1, hl2 ▸ ht1, hm_sc2⟩
    rw [evaluateHOLFiniteState_seq_line780, hcall]; dsimp only; exact hst_eq
  -- Initial `decCall "t" := htab_new(20, 64)` from `st2`:
  have hhp_st2 : st2.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cxHpInit + 72)))) := by
    simp [st2, st1, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show (ofString "ts" == ofString "heap_ptr") = false by decide]
  have hts_st2 : st2.globals.lookup (ofString "ts") = some (.val (.word (BitVec.ofNat 64 cxHpInit))) := hts_st1
  have hjn_st2 : st2.globals.lookup (ofString "journal_n") = some (.val (.word 0#64)) := by
    simp [st2, st1, setGlobalHOLFinite, cxSftxState, cxSftxGlobals, HolFiniteMapExact.lookup_update, FUPDATE,
      show (ofString "ts" == ofString "journal_n") = false by decide,
      show (ofString "heap_ptr" == ofString "journal_n") = false by decide,
      show (ofString "bs" == ofString "journal_n") = false by decide]
  have hck_st2 : st2.clock = 999 := rfl
  obtain ⟨u1, hdec1, ht_u1, hhp_u1, hg_u1, hma_u1, hc_u1, hck_u1, _, hfr_u1⟩ :=
    eval_decCall_htab_new_frame st2 _ (cxHpInit + 72) 20 64 rfl rfl (by rw [hck_st2]; omega)
      (by unfold cxHpInit; decide) (by unfold cxHpInit; decide) (by simp) (by simp)
      (by unfold cxHpInit; decide) hhp_st2
  rw [hdec1]; dsimp only
  have hsc_nat : (BitVec.ofNat 64 scratchStart).toNat = scratchStart := by decide
  have hm_st2 : st2.memory (BitVec.ofNat 64 scratchStart) = .word 99#64 := hmem_bs_sc
  have hm_u1 : u1.memory (BitVec.ofNat 64 scratchStart) = .word 99#64 := by
    rw [hfr_u1 _ (by rw [hsc_nat]), hm_st2]
  obtain ⟨v1, heqv1, hl_v1, hg_v1, hc_v1, hma_v1, hck_v1, hm_v1⟩ :=
    hts_store_step u1 8 (BitVec.ofNat 64 (cxHpInit + 72)) _ (by omega) (by omega) hma_u1
      (by rw [hg_u1 _ (by decide)]; exact hts_st2) ht_u1 hm_u1
  rw [heqv1]
  obtain ⟨v2, heqv2, hc_v2, hma_v2, hck_v2, hhp_v2, hts_v2, hjn_v2, ht_v2, hm_v2⟩ :=
    hcall_and_store v1 _ _ 20 64 16 _ (hc_v1.trans hc_u1) (hma_v1.trans hma_u1)
      (by omega) (by unfold cxHpInit; decide) (by unfold cxHpInit; decide) (by simp) (by simp)
      (by omega) (by omega) (by unfold cxHpInit; decide)
      (hg_v1 ▸ hhp_u1) (by rw [hg_v1, hg_u1 _ (by decide)]; exact hts_st2)
      (by rw [hg_v1, hg_u1 _ (by decide)]; exact hjn_st2) (hl_v1 ▸ ht_u1) hm_v1
  rw [heqv2]
  obtain ⟨v3, heqv3, hc_v3, hma_v3, hck_v3, hhp_v3, hts_v3, hjn_v3, ht_v3, hm_v3⟩ :=
    hcall_and_store v2 _ _ 52 64 24 _ hc_v2 hma_v2
      (by omega) (by unfold cxHpInit; decide) (by unfold cxHpInit; decide) (by simp) (by simp)
      (by omega) (by omega) (by unfold cxHpInit; decide) hhp_v2 hts_v2 hjn_v2 ht_v2 hm_v2
  rw [heqv3]
  obtain ⟨v4, heqv4, hc_v4, hma_v4, hck_v4, hhp_v4, hts_v4, hjn_v4, ht_v4, hm_v4⟩ :=
    hcall_and_store v3 _ _ 20 16 32 _ hc_v3 hma_v3
      (by omega) (by unfold cxHpInit; decide) (by unfold cxHpInit; decide) (by simp) (by simp)
      (by omega) (by omega) (by unfold cxHpInit; decide) hhp_v3 hts_v3 hjn_v3 ht_v3 hm_v3
  rw [heqv4]
  obtain ⟨v5, heqv5, hc_v5, hma_v5, hck_v5, hhp_v5, hts_v5, hjn_v5, ht_v5, hm_v5⟩ :=
    hcall_and_store v4 _ _ 52 16 40 _ hc_v4 hma_v4
      (by omega) (by unfold cxHpInit; decide) (by unfold cxHpInit; decide) (by simp) (by simp)
      (by omega) (by omega) (by unfold cxHpInit; decide) hhp_v4 hts_v4 hjn_v4 ht_v4 hm_v4
  rw [heqv5]
  obtain ⟨v6, heqv6, hc_v6, hma_v6, hck_v6, hhp_v6, hts_v6, hjn_v6, ht_v6, hm_v6⟩ :=
    hcall_and_store v5 _ _ 32 16 48 _ hc_v5 hma_v5
      (by omega) (by unfold cxHpInit; decide) (by unfold cxHpInit; decide) (by simp) (by simp)
      (by omega) (by omega) (by unfold cxHpInit; decide) hhp_v5 hts_v5 hjn_v5 ht_v5 hm_v5
  rw [heqv6]
  obtain ⟨v7, heqv7, hc_v7, hma_v7, hck_v7, hhp_v7, hts_v7, hjn_v7, ht_v7, hm_v7⟩ :=
    hcall_and_store v6 _ _ 20 16 56 _ hc_v6 hma_v6
      (by omega) (by unfold cxHpInit; decide) (by unfold cxHpInit; decide) (by simp) (by simp)
      (by omega) (by omega) (by unfold cxHpInit; decide) hhp_v6 hts_v6 hjn_v6 ht_v6 hm_v6
  rw [heqv7]
  obtain ⟨v8, heqv8, hc_v8, hma_v8, hck_v8, hhp_v8, hts_v8, hjn_v8, ht_v8, hm_v8⟩ :=
    hcall_and_store v7 _ _ 52 16 64 _ hc_v7 hma_v7
      (by omega) (by unfold cxHpInit; decide) (by unfold cxHpInit; decide) (by simp) (by simp)
      (by omega) (by omega) (by unfold cxHpInit; decide) hhp_v7 hts_v7 hjn_v7 ht_v7 hm_v7
  rw [heqv8]
  -- Final `assign .global "journal_n" 0; return 0`
  have htail_ev : evaluateHOLFiniteState v8
      (.seq (.assign .global (ofString "journal_n") (.const 0#64)) (.return (.const 0#64))) =
      (some (.returned (.val (.word 0#64))),
        emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "journal_n") (.val (.word 0#64)) v8)) := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
    simp [evalHOLExact, isValidValueHOLExact, lookupKvarHOLExact, hjn_v8,
      shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
      evaluateHOLFiniteState_return]
  rw [htail_ev]
  exact ⟨rfl, hm_v8⟩

theorem not_wk_state_fresh_tx_r10 :
    ¬ WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr", "journal_n", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "state_fresh_tx") := by
  rintro ⟨params, body, retShape, hlook, hspec⟩
  have hcode : originalRuntimeCode.lookup (ofString "state_fresh_tx") =
      some ([], (sourceFunctionEntry Guest.Software.guestFn_state_fresh_tx).2.2.1,
        (sourceFunctionEntry Guest.Software.guestFn_state_fresh_tx).2.2.2) :=
    lookup_state_fresh_tx_fn
  rw [hcode] at hlook
  injection hlook with h1
  rcases Prod.mk.inj h1 with ⟨rfl, h2⟩
  rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
  obtain ⟨hret, hm_sc⟩ := cxSftx_runs_and_writes_scratchStart
  have hws := hspec cxSftxState rfl cxSftx_worldOK ⟨[], cxSftx_lookup_entry⟩
    (by rw [hret]; simp) (Or.inl ⟨_, hret⟩)
  obtain ⟨_, _, _, _, _, hfr, _⟩ := hws.2.2.2.2 [] [] cxSftx_worldTypedWith (fun x hx => by simp at hx)
  have hsc_nat : (BitVec.ofNat 64 scratchStart).toNat = scratchStart := by decide
  have hmem_eq := hfr (BitVec.ofNat 64 scratchStart)
    (fun i hi hch => by
      have ho := fun g h1 h2 h3 => cxSftx_globN_other g h1 h2 h3
      have hbo0 : globN cxSftxState "bo" = 0 := ho "bo" (by decide) (by decide) (by decide)
      have hba0 : globN cxSftxState "bal_accounts" = 0 := ho "bal_accounts" (by decide) (by decide) (by decide)
      have hjc0 : globN cxSftxState "journal_cap" = 0 := ho "journal_cap" (by decide) (by decide) (by decide)
      have hi_z : i.2 = 0 := by
        rcases List.mem_append.1 hi with h1 | hfg
        · rcases List.mem_append.1 h1 with hwo | hr0
          · unfold worldOwned at hwo
            rcases List.mem_append.1 hwo with htf | hne
            · rcases List.mem_append.1 htf with htab | hfix
              · simp at htab
              · unfold fixedObjects at hfix
                rcases List.mem_append.1 hfix with hf1 | hbal
                · rcases List.mem_append.1 hf1 with hf2 | hbo
                  · rcases List.mem_append.1 hf2 with hbuf | hjr
                    · obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hbuf
                      have hne := cxSftx_gb_ne gn hgn
                      simp [ho gn.1 hne.1 hne.2.1 hne.2.2]
                    · simp only [List.mem_singleton] at hjr; subst hjr; simp [hjc0]
                  · unfold blockOutObjects at hbo; simp [hbo0] at hbo
                    rcases hbo with rfl | rfl | rfl | rfl | rfl | rfl | rfl
                    all_goals rfl
                · unfold balObjects balRecords at hbal; simp [hba0] at hbal
            · simp [nodeExtents] at hne
          · simp at hr0
        · simp only [List.mem_singleton] at hfg; subst hfg
          unfold freeGap; rw [cxSftx_globN_fm, cxSftx_globN_sc]; dsimp; omega
      have hi_al : i.1 % 8 = 0 := by
        rcases List.mem_append.1 hi with h1 | hfg
        · rcases List.mem_append.1 h1 with hwo | hr0
          · exact worldOwned_zero_aligned cxSftx_worldTypedWith i hwo hi_z
          · simp at hr0
        · simp only [List.mem_singleton] at hfg; subst hfg
          unfold freeGap; rw [cxSftx_globN_fm]; decide
      obtain ⟨hc1, hc2⟩ := hch
      rw [hsc_nat] at hc1 hc2
      have hsc8 : scratchStart % 8 = 0 := by decide
      omega)
    (fun hcf => by
      obtain ⟨_, hc2⟩ := hcf
      unfold heapFree at hc2
      dsimp only at hc2
      rw [hsc_nat, cxSftx_globN_hp] at hc2
      have hhl : heapLimit = scratchStart := rfl
      have hinit_le : cxHpInit ≤ scratchStart := by unfold cxHpInit; decide
      omega)
  rw [hm_sc] at hmem_eq
  have hm0 : cxSftxState.memory (BitVec.ofNat 64 scratchStart) = .word 0 := rfl
  rw [hm0] at hmem_eq
  injection hmem_eq with h99
  exact absurd h99 (by decide)

end StateFreshTxCornerCase

theorem prove_gbody_process_unchecked_system_transaction
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hext : TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of»)
    (hfmr : TerminatingFunBoundedOn GuestInv (ofString "frame_mem_release") K.«frame_mem_release»)
    (hhn : TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new»)
    (hitb : TerminatingFunBoundedOn WorldOK (ofString "incorporate_tx_into_block") K.«incorporate_tx_into_block»)
    (hmc : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (hmn : TerminatingFunBoundedOn GuestInv (ofString "msg_new") K.«msg_new»)
    (hpmc : TerminatingFunBoundedOn MsgReady (ofString "process_message_call") K.«process_message_call»)
    (hsr : TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release»)
    (hsf : TerminatingFunBoundedOn GuestInv (ofString "state_fresh_tx") K.«state_fresh_tx»)
    (hte : TerminatingFunBoundedOn GuestInv (ofString "te_new") K.«te_new»)
    (wext : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "ext_code_of"))
    (hnspec : type_of% @htab_new_spec)
    (wmn : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ w => [(w, 176)])) (ofString "msg_new"))
    (rtmn : Returns ArenaReady (fun s post m => FreshBlock s post m 176 ∧
      ∀ k, k < 22 → memW post (m + 8 * k) = 0) (ofString "msg_new"))
    (wpmc : WorldKeepsIn MsgReady (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => [(locN s "msg", 176),
                 (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
                 (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
                 (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
                 (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
                 (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
                 (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
                 (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
                 (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
                 (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
                 (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetMessageOutput (ofString "process_message_call"))
    (wsf : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr", "journal_n", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "state_fresh_tx"))
    (wte : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ w => [(w, 200)])) (ofString "te_new"))
    (rtte : Returns ArenaReady (fun s post m => FreshBlock s post m 200 ∧
      ∀ k, k < 25 → memW post (m + 8 * k) = 0) (ofString "te_new")) :
    TerminatingFunBoundedOn WorldOK (ofString "process_unchecked_system_transaction") K.«process_unchecked_system_transaction» := by
  refine ⟨_, _, _, lookup_process_unchecked_system_transaction, ?_⟩
  intro F state hcode hW
  by_cases hargs : WordSysTxArgs state
  · exact bounded_process_unchecked_system_transaction_wordArgs
      hal hext hfmr hhn hitb hmc hmn hpmc hsr hsf hte
      wext hnspec wmn rtmn wpmc wsf wte rtte state hcode ⟨hW, hargs⟩
  · exact absurd wsf not_wk_state_fresh_tx_r10

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodySysTxReqs
