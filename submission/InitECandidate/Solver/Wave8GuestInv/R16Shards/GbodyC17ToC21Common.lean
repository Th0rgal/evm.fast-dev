import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07
import InitECandidate.Solver.GuestTrapOutcomes

/-! Helper lemmas and body proofs for `gbody_process_message_call`,
`gbody_process_unchecked_system_transaction`, and `gbody_process_general_purpose_requests`
on R10 (`ContractParts/C17.lean`).
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.GbodyC17ToC21Common

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
  obtain ⟨_, _, _, _, _, hs_hp8, _, hs_sc8, _⟩ := hAs
  obtain ⟨_, _, _, _, _, hp_hp8, _, hp_sc8, _⟩ := hAp
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
    exact arenaOK_congr hpost.2.2.2.2.2.1 hAs.2
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
    exact arenaOK_congr hpost.2.2.2.2.2.1 hAs.2
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
  obtain ⟨hs_lo, hs_hp, hs_fm, hs_sc, hs_end, hs_hp8, hs_fm8, hs_sc8, _⟩ := hAs.2
  obtain ⟨hp_lo, hp_hp, hp_fm, hp_sc, hp_end, hp_hp8, hp_fm8, hp_sc8, _⟩ := hAp.2
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


end InitECandidate.Solver.Wave8GuestInv.R16Shards.GbodyC17ToC21Common
