import InitECandidate.Solver.Wave8GuestInv.Primitives
import InitECandidate.Solver.GuestTrapOutcomes
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

/-! Core W1 world-frame and execution-effect infrastructure for Shards P26 + P27 + P28. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

abbrev stdKeep : List (String × List Nat) :=
  [("ws", [0, 8, 16, 24, 32]),
   ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
   ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
   ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]

def coreWorldGlobals : List String :=
  ["ws", "bs", "ts", "bo", "bal_accounts", "bal_idx_accts", "bal_idx_stor",
   "journal", "journal_cap", "journal_n"]

/-! ## 1. Ordinary domain & interval geometry -/

theorem addresses_iff (b : BitVec 64) (n : Nat) (x : BitVec 64) :
    Flapjack.Compiler.Backend.StackRemove.addresses b n x ↔
      ∃ i, i < n ∧ x = b + BitVec.ofNat 64 (8 * i) := by
  induction n generalizing b with
  | zero => simp [Flapjack.Compiler.Backend.StackRemove.addresses]
  | succ n ih =>
    simp only [Flapjack.Compiler.Backend.StackRemove.addresses,
      Flapjack.Compiler.Backend.StackRemove.bytesInWord]
    rw [ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · refine ⟨i + 1, by omega, ?_⟩
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
    · rintro ⟨i, hi, rfl⟩
      rcases i with _ | i
      · left; simp
      · right; refine ⟨i, by omega, ?_⟩
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

theorem ordinaryDomain_eq : ordinaryDomain =
    Flapjack.Compiler.Backend.StackRemove.addresses (BitVec.ofNat 64 2701131776) 3888119741 := by
  have h1 : (BitVec.ofNat 64 sourceBase) = BitVec.ofNat 64 2701131776 := rfl
  have h2 : (stackStart - sourceBase) / 8 - globalsWords = 3888119741 := by decide
  unfold ordinaryDomain; rw [h1, h2]

theorem addresses_iff_nat (b : BitVec 64) (n : Nat) (hb : b.toNat + 8 * n ≤ 2 ^ 64)
    (x : BitVec 64) :
    Flapjack.Compiler.Backend.StackRemove.addresses b n x ↔
      b.toNat ≤ x.toNat ∧ x.toNat < b.toNat + 8 * n ∧ (x.toNat - b.toNat) % 8 = 0 := by
  rw [addresses_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have : (b + BitVec.ofNat 64 (8 * i)).toNat = b.toNat + 8 * i := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [this]; omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(x.toNat - b.toNat) / 8, by omega, ?_⟩
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem sourceBase_val : sourceBase = 2701131776 := rfl
theorem heapLimit_val : heapLimit = 2952790016 := rfl
theorem scratchStart_val : scratchStart = 2952790016 := rfl
theorem scratchEnd_val : scratchEnd = 2965299200 := rfl
theorem heapEnd_val : heapEnd = 33806089704 := by decide

theorem ordinaryDomain_iff (x : BitVec 64) :
    ordinaryDomain x ↔ x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
  have hb : (BitVec.ofNat 64 2701131776).toNat = 2701131776 := rfl
  rw [ordinaryDomain_eq, addresses_iff_nat _ _ (by rw [hb]; decide), hb, sourceBase_val, heapEnd_val]
  omega

theorem wordAt_of_ordinary {F : Type} {s : PanSemStateFiniteExact 64 F} (hg : GuestInv s)
    {a : Nat} (ha8 : a % 8 = 0) (hlo : sourceBase ≤ a) (hhi : a < heapEnd) :
    WordAt s a := by
  have ha_lt : a < 2 ^ 64 := by rw [heapEnd_val] at hhi; omega
  rcases hm : s.memory (BitVec.ofNat 64 a) with ⟨w⟩
  refine ⟨w, ?_, hm⟩
  rw [hg.memaddrs, ordinaryDomain_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  exact ⟨ha8, hlo, hhi⟩

theorem wordsOK_of_inside_heap {F : Type} {s : PanSemStateFiniteExact 64 F} (hg : GuestInv s)
    {p len : Nat} (hp8 : p % 8 = 0) (hl8 : len % 8 = 0)
    (hlo : sourceBase ≤ p) (hhi : p + len ≤ heapEnd) :
    WordsOK s (p, len) := by
  refine ⟨hp8, hl8, fun k hk => ?_⟩
  exact wordAt_of_ordinary hg (by omega) (by omega) (by omega)

theorem wordsOK_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) {i : Ivl} (hw : WordsOK s i) :
    WordsOK post i := by
  refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
  obtain ⟨_, hdom, _⟩ := hw.2.2 k hk
  rcases hm : post.memory (BitVec.ofNat 64 (i.1 + 8 * k)) with ⟨w⟩
  refine ⟨w, ?_, hm⟩
  rw [hgP.memaddrs, ← hgS.memaddrs]; exact hdom

theorem disj_zero_left (j : Ivl) : Disj (0, 0) j := Or.inl rfl
theorem disj_zero_right (i : Ivl) : Disj i (0, 0) := Or.inr (Or.inl rfl)

theorem disj_of_inside_left {i i' j : Ivl} (hin : Inside i i'.1 (i'.1 + i'.2))
    (hd : Disj i' j) : Disj i j := by
  rcases hin with ⟨h1, h2⟩
  rcases hd with h0 | h0 | hle | hge
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl h0)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem disj_of_inside_right {i j j' : Ivl} (hin : Inside j j'.1 (j'.1 + j'.2))
    (hd : Disj i j') : Disj i j :=
  Disj.flip (disj_of_inside_left hin (Disj.flip hd))

theorem disj_allocated_fresh_heap {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaOK s) (hp : ArenaOK post) {i f : Ivl}
    (hi : Allocated s i) (hf : Inside f (globN s "heap_ptr") (globN post "heap_ptr")) :
    Disj f i := by
  rcases hi with hi | hi
  · exact Or.inr (Or.inr (Or.inr (Nat.le_trans hi.2 hf.1)))
  · have hsep : heapLimit ≤ scratchStart := by decide
    exact Or.inr (Or.inr (Or.inl (Nat.le_trans hf.2 (Nat.le_trans hp.2.1
      (Nat.le_trans hsep (Nat.le_trans hs.2.2.1 (Nat.le_trans hs.2.2.2.1 hi.1)))))))

theorem disj_allocated_heapFree {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : ArenaOK s) {i : Ivl} (hi : Allocated s i) :
    Disj i (heapFree s) := by
  unfold heapFree
  rcases hi with hi | hi
  · exact Or.inr (Or.inr (Or.inl hi.2))
  · have hsep : heapLimit ≤ scratchStart := by decide
    have := hs.1; have := hs.2.1; have := hs.2.2.1; have := hs.2.2.2.1; have := hi.1
    exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))

theorem disj_allocated_freeGap {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : ArenaOK s) {i : Ivl} (hi : Allocated s i) :
    Disj i (freeGap s) := by
  unfold freeGap
  rcases hi with hi | hi
  · have hsep : heapLimit ≤ scratchStart := by decide
    have := hs.2.1; have := hs.2.2.1; have := hi.2
    exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
  · have := hs.2.2.2.1; have := hi.1
    exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))

/-- Non-empty cell hit: `0 < i.2 ∧ CellHits a i`. Every actual word or byte store into `i`
requires `0 < i.2`, avoiding vacuous hits on unaligned zero-length intervals `(p, 0)`. -/
def CellHitsPos (a : Nat) (i : Ivl) : Prop := 0 < i.2 ∧ CellHits a i

theorem not_cellHitsPos_of_disj {a : Nat} {i j : Ivl}
    (ha : a ≥ i.1 ∧ a + 8 ≤ i.1 + i.2) (hd : Disj i j) : ¬ CellHitsPos a j := by
  rintro ⟨hjpos, hc1, hc2⟩
  rcases hd with h0 | h0 | h1 | h2 <;> omega

theorem not_cellHits_of_disj_aligned {a : Nat} {i j : Ivl}
    (ha8 : a % 8 = 0) (hj1 : j.1 % 8 = 0)
    (ha : a ≥ i.1 ∧ a + 8 ≤ i.1 + i.2) (hd : Disj i j) : ¬ CellHits a j := by
  rintro ⟨hc1, hc2⟩
  rcases hd with h0 | h0 | h1 | h2 <;> omega

theorem ivl_allocated_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {i : Ivl} (hal : Allocated s i) :
    i.1 + i.2 ≤ heapEnd ∧ i.1 + i.2 ≤ 2 ^ 64 := by
  have h1 : heapLimit ≤ heapEnd := by decide
  have h2 : scratchEnd ≤ heapEnd := by decide
  have h3 : heapEnd < 2 ^ 64 := by decide
  rcases hal with ⟨_, hi⟩ | ⟨_, hi⟩
  · have := hA.2.1; omega
  · have := hA.2.2.2.2.1; omega

theorem globN_eq_of_lookup {F : Type} {s post : PanSemStateFiniteExact 64 F} {name : String}
    (h : s.globals.lookup (ofString name) = post.globals.lookup (ofString name)) :
    globN post name = globN s name := by
  unfold globN; rw [← h]

theorem mem_low_eq_of_domain_writes {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hd : ∀ a : BitVec 64, post.memory a ≠ s.memory a → s.memaddrs a)
    (hg : GuestInv s) {k : Nat} (hk : k < sourceBase) :
    memW post k = memW s k := by
  by_cases heq : post.memory (BitVec.ofNat 64 k) = s.memory (BitVec.ofNat 64 k)
  · unfold memW; rw [heq]
  · have hdom := hd (BitVec.ofNat 64 k) heq
    rw [hg.memaddrs, ordinaryDomain_iff] at hdom
    have hlt : k < 2 ^ 64 := by rw [sourceBase_val] at hk; omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at hdom
    omega

/-! ## 2. Unhit intervals & sub-object congruence -/

def IvlUnhit {F : Type} (s post : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  ∀ a : BitVec 64, a.toNat % 8 = 0 → CellHits a.toNat i → post.memory a = s.memory a

theorem ivlUnhit_of_cellHitsPos {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hi1 : i.1 % 8 = 0) (hi2 : i.2 % 8 = 0)
    (hfr : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
      (∃ j ∈ keep, CellHitsPos a.toNat j) ∨ CellHitsPos a.toNat fresh)
    (hk : ∀ j ∈ keep, Disj i j) (hf : Disj i fresh) :
    IvlUnhit s post i := by
  intro a ha8 hhit
  have hin : i.1 ≤ a.toNat ∧ a.toNat + 8 ≤ i.1 + i.2 := by
    unfold CellHits at hhit; omega
  by_contra hne
  rcases hfr a hne with ⟨j, hj, hcj⟩ | hcf
  · exact not_cellHitsPos_of_disj hin (hk j hj) hcj
  · exact not_cellHitsPos_of_disj hin hf hcf

theorem ivlUnhit_of_frameOutside_aligned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hi_pos : i.2 ≠ 0)
    (hfr : FrameOutside s post keep fresh)
    (hk_al : ∀ j ∈ keep, j.1 % 8 = 0 ∧ j.2 % 8 = 0)
    (hf_al : fresh.1 % 8 = 0 ∧ fresh.2 % 8 = 0)
    (hk : ∀ j ∈ keep, Disj i j) (hf : Disj i fresh) :
    IvlUnhit s post i := by
  intro a ha8 hhit
  obtain ⟨hi1, hi2⟩ := hhit
  apply hfr a
  · intro j hj hcj
    obtain ⟨hj1, hj2⟩ := hk_al j hj
    obtain ⟨hc1, hc2⟩ := hcj
    have hin : j.1 ≤ a.toNat ∧ a.toNat + 8 ≤ j.1 + j.2 := by omega
    rcases hk j hj with h0 | h0 | h1 | h2 <;> omega
  · intro hcf
    obtain ⟨hf1, hf2⟩ := hf_al
    obtain ⟨hc1, hc2⟩ := hcf
    have hin : fresh.1 ≤ a.toNat ∧ a.toNat + 8 ≤ fresh.1 + fresh.2 := by omega
    rcases hf with h0 | h0 | h1 | h2 <;> omega

theorem memW_eq_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {i : Ivl} (hu : IvlUnhit s post i) {a : Nat}
    (ha8 : a % 8 = 0) (hhi : i.1 + i.2 ≤ 2 ^ 64) (hin : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) :
    memW post a = memW s a := by
  have ha_lt : a < 2 ^ 64 := by omega
  have hmem := hu (BitVec.ofNat 64 a)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; exact ha8)
    (by unfold CellHits; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega)
  unfold memW; rw [hmem]

theorem memB_eq_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {i : Ivl} (hu : IvlUnhit s post i) (hbe : post.be = s.be)
    {a : Nat} (hhi : i.1 + i.2 ≤ 2 ^ 64) (hin : i.1 ≤ a ∧ a < i.1 + i.2) :
    memB post a = memB s a := by
  have ha_lt : a < 2 ^ 64 := by omega
  let c := panByteAlignHOL (BitVec.ofNat 64 a)
  have hc_nat : c.toNat = a / 8 * 8 := by
    rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  have hmem := hu c (by rw [hc_nat]; omega) (by unfold CellHits; rw [hc_nat]; omega)
  unfold memB
  change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 a) v post.be).toNat) =
         (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 a) v s.be).toNat)
  rw [hmem, hbe]

theorem freeChain_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {nodes ncap : Nat} (hn8 : nodes % 8 = 0) (hhi : nodes + (ncap + 1) * 32 ≤ 2 ^ 64)
    (hu : IvlUnhit s post (nodes, (ncap + 1) * 32)) :
    ∀ (Fr : List Nat) (head : Nat),
      (∀ f ∈ Fr, 1 ≤ f ∧ f ≤ ncap) →
      (FreeChain post nodes head Fr ↔ FreeChain s nodes head Fr)
  | [], _, _ => Iff.rfl
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

/-! ## 3. `NodeHeap`, `TablesTyped`, `FixedTyped`, `JournalTyped` W1 congruence -/

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
    (hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88))
    (hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i) :
    blockOutObjects post = blockOutObjects s ∧
    (globN post "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat), memW post (globN post "bo" + k) ≠ 0 →
      LstOK post (memW post (globN post "bo" + k))) := by
  by_cases hbo : globN s "bo" = 0
  · refine ⟨?_, fun hp => absurd (hbo_eq.trans hbo) hp⟩
    simp [blockOutObjects, hbo_eq, hbo]
  · have hbo_words : ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
        memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := fun k hk => by
      have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simpa [hbo_eq] using rec_word_eq_of_unhit hA hF "bo" 88 (by simp [typedRecords]) hbo_eq hbo (hu_bo hbo) hk_in.1 hk_in.2
    have hlst_hdr : ∀ k ∈ ([40, 72] : List Nat), memW s (globN s "bo" + k) ≠ 0 →
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
        have hu := hu_bo_lst _ hmem_bo rfl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        rcases hoff with rfl | rfl | rfl <;>
          exact memW_eq_of_ivlUnhit hu (by omega) hhi ⟨by omega, by omega⟩
    constructor
    · unfold blockOutObjects
      simp only [hbo_eq, hbo, false_or,
        hbo_words 24 (by simp), hbo_words 32 (by simp), hbo_words 40 (by simp),
        hbo_words 56 (by simp), hbo_words 72 (by simp), hbo_words 80 (by simp)]
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
      have hk_eq : memW post (globN s "bo" + k) = memW s (globN s "bo" + k) :=
        hbo_words k (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> simp)
      rw [hk_eq] at hknz ⊢
      unfold LstOK
      rw [hlst_hdr k hk hknz 8 (by simp), hlst_hdr k hk hknz 16 (by simp)]
      exact hbo_lst_ok hbo k hk hknz

theorem balRecords_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S : List Nat} (hT : TablesTyped s S)
    (hbal_eq : globN post "bal_accounts" = globN s "bal_accounts")
    (hu : globN s "bal_accounts" ≠ 0 → ∀ i ∈ htabFootprint s (globN s "bal_accounts"), IvlUnhit s post i) :
    balRecords post = balRecords s := by
  unfold balRecords; rw [hbal_eq]
  by_cases hbal : globN s "bal_accounts" = 0
  · simp [hbal]
  · simp only [hbal, ↓reduceIte]
    have hmem_S : globN s "bal_accounts" ∈ S := by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hbal
      · exact hm
    exact htabValues_eq_of_unhit (hT.2.1 _ hmem_S).1 (hu hbal)

theorem balObjects_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hbal_eq : globN post "bal_accounts" = globN s "bal_accounts")
    (hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i)
    (hlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
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
  have had_props : ∀ ad ∈ balRecords s,
      (∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off)) ∧
      htabValues post (memW s ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat),
        memW s (ad + k) ≠ 0 →
        memW post (memW s (ad + k)) = memW s (memW s (ad + k)) ∧
        memW post (memW s (ad + k) + 8) = memW s (memW s (ad + k) + 8) ∧
        memW post (memW s (ad + k) + 16) = memW s (memW s (ad + k) + 16)) ∧
      (∀ l ∈ htabValues s (memW s ad),
        l ≠ 0 →
        memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16)) := by
    intro ad had
    have had_bal : (ad, 40) ∈ balObjects s := by
      unfold balObjects; exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
    rcases hF.1 _ (hmem_fix_of_bal _ had_bal) with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (ivl_allocated_bound hA hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hoff_eq : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off) := by
      intro off hoff
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
        exact memW_eq_of_ivlUnhit (hu_bal _ had_bal (by simp)) (by omega) hhi_ad ⟨by omega, by omega⟩
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hvals_ad : htabValues post (memW s ad) = htabValues s (memW s ad) :=
      htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_tab _ had_T.1)
    have hlst_eq : ∀ l, (l, 24) ∈ balObjects s →
        memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16) := by
      intro l hl_bal
      rcases hF.1 _ (hmem_fix_of_bal _ hl_bal) with h0 | ⟨hal_l, hw_l⟩
      · simp at h0
      have hhi_l := (ivl_allocated_bound hA hal_l).2
      have hl8 : l % 8 = 0 := hw_l.1
      have hul := hu_bal _ hl_bal (by simp)
      refine ⟨?_, ?_, ?_⟩
      · simpa using memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
      · exact memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
      · exact memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
    refine ⟨hoff_eq, hvals_ad, ?_, ?_⟩
    · intro k hk hnz
      apply hlst_eq
      unfold balObjects
      refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> simp [lstObjects, hnz]
    · intro l hl hnz
      apply hlst_eq
      unfold balObjects
      refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
      apply List.mem_cons_of_mem
      apply List.mem_append.2; right
      exact List.mem_flatMap.2 ⟨l, hl, by simp [lstObjects, hnz]⟩
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
    have hlst_congr : ∀ k esz, k ∈ ([16, 24, 32] : List Nat) →
        lstObjects post (memW s (ad + k)) esz = lstObjects s (memW s (ad + k)) esz := by
      intro k esz hk
      by_cases hkz : memW s (ad + k) = 0
      · simp [lstObjects, hkz]
      · obtain ⟨hc0, _, hc16⟩ := hklst k hk hkz
        simp [lstObjects, hkz, hc0, hc16]
    have htail : (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
      rw [h0, hvals_ad]
      apply List.flatMap_congr
      intro l hl
      by_cases hlz : l = 0
      · simp [lstObjects, hlz]
      · obtain ⟨hl0, _, hl16⟩ := hllst l hl hlz
        simp [lstObjects, hlz, hl0, hl16]
    rw [htail, h16, h24, h32, hlst_congr 16 40 (by simp), hlst_congr 24 16 (by simp), hlst_congr 32 24 (by simp)]
  · intro ad had
    rw [hrecs] at had
    obtain ⟨hoff_eq, hvals_ad, hklst, hllst⟩ := had_props ad had
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h8 := hoff_eq 8 (by simp)
    refine ⟨h0, h8, by rw [h0, hvals_ad], ?_, ?_⟩
    · intro k hk
      have hk_in : k ∈ ([0, 8, 16, 24, 32] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl <;> simp
      rw [hoff_eq k hk_in]
      by_cases hkz : memW s (ad + k) = 0
      · unfold LstOK; rw [hkz]; simp [hlow.1, hlow.2]; simpa [LstOK, hkz] using had_T.2.2.1 k hk
      · obtain ⟨_, hk8, hk16⟩ := hklst k hk hkz
        unfold LstOK; rw [hk8, hk16]; exact had_T.2.2.1 k hk
    · intro l hl
      rw [h0, hvals_ad] at hl
      by_cases hlz : l = 0
      · unfold LstOK; rw [hlz]; simp [hlow.1, hlow.2]; simpa [LstOK, hlz] using had_T.2.2.2 l hl
      · obtain ⟨_, hl8, hl16⟩ := hllst l hl hlz
        unfold LstOK; rw [hl8, hl16]; exact had_T.2.2.2 l hl

theorem worldRoleSlots_eq_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g)
    (hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80))
    (hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72))
    (hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i)
    (hlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
    worldRoleSlots post = worldRoleSlots s := by
  have hws_g : globN post "ws" = globN s "ws" := hcore "ws" (by decide)
  have hbs_g : globN post "bs" = globN s "bs" := hcore "bs" (by decide)
  have hts_g : globN post "ts" = globN s "ts" := hcore "ts" (by decide)
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hcore "bal_accounts" (by decide)
  have hbia_g : globN post "bal_idx_accts" = globN s "bal_idx_accts" := hcore "bal_idx_accts" (by decide)
  have hbis_g : globN post "bal_idx_stor" = globN s "bal_idx_stor" := hcore "bal_idx_stor" (by decide)
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
      simp only [hws_g] at hw; simp [hw]
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
      simp only [hbs_g] at hw; simp [hw]
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
      simp only [hts_g] at hw; simp [hw]
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
  have hbal_part := (balObjects_eq_of_unhit hA hT hF hba_g hu_tab hu_bal hlow).2
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
    (hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g)
    (hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72))
    (hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap")) :
    journalRoleSlots post = journalRoleSlots s ∧ JournalTyped post S' := by
  have hts_g : globN post "ts" = globN s "ts" := hcore "ts" (by decide)
  have hj_g : globN post "journal" = globN s "journal" := hcore "journal" (by decide)
  have hjc_g : globN post "journal_cap" = globN s "journal_cap" := hcore "journal_cap" (by decide)
  have hjn_g : globN post "journal_n" = globN s "journal_n" := hcore "journal_n" (by decide)
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

theorem nodeHeap_congr_bytes {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post)
    (hag : AllocatorGrows s post)
    {Nd : List Nat} (hN : NodeHeap s Nd)
    (hu_rec : ∀ n ∈ Nd, IvlUnhit s post (nodeIvl s n))
    (hu_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k)) :
    NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hn_props : ∀ n ∈ Nd,
      memW post n = memW s n ∧
      nodeIvl post n = nodeIvl s n ∧
      (∀ k, k < nodeSize (memW s n) / 8 → memW post (n + 8 * k) = memW s (n + 8 * k)) ∧
      nodePath post n = nodePath s n ∧
      ((memW s n = 1 ∨ memW s n = 2) → KeyIn post Nd (memW post (n + 32)) (memW post (n + 40))) := by
    intro n hn
    obtain ⟨hk3, hal_n, hin_n, hw_n, _, _, hkey_n, _, _, _⟩ := hN.1 n hn
    have hhi_n : n + nodeSize (memW s n) ≤ 2 ^ 64 := by
      have := hin_n.2; dsimp [nodeIvl] at this; omega
    have hn8 : n % 8 = 0 := hw_n.1
    have hu_n : IvlUnhit s post (n, nodeSize (memW s n)) := hu_rec n hn
    have hsz_ge32 : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
    have hw_k : ∀ k, k < nodeSize (memW s n) / 8 → memW post (n + 8 * k) = memW s (n + 8 * k) := by
      intro k hk
      have hsz8 : nodeSize (memW s n) % 8 = 0 := by unfold nodeSize; split_ifs <;> omega
      exact memW_eq_of_ivlUnhit hu_n (by omega) hhi_n ⟨by omega, by omega⟩
    have hw0 : memW post n = memW s n := by simpa using hw_k 0 (by omega)
    have hivl_eq : nodeIvl post n = nodeIvl s n := by simp [nodeIvl, hw0]
    have hpath_eq : nodePath post n = nodePath s n := by
      by_cases h12 : memW s n = 1 ∨ memW s n = 2
      · have hsz_ge56 : 56 ≤ nodeSize (memW s n) := by
          unfold nodeSize; rcases h12 with h1 | h2 <;> simp [*]
        have hw32 : memW post (n + 32) = memW s (n + 32) := hw_k 4 (by omega)
        have hw40 : memW post (n + 40) = memW s (n + 40) := hw_k 5 (by omega)
        unfold nodePath; rw [hw0, hw32, hw40]
      · unfold nodePath; rw [hw0]; simp [h12]
    exact ⟨hw0, hivl_eq, hw_k, hpath_eq, fun h12 => by
      have hsz_ge56 : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize; rcases h12 with h1 | h2 <;> simp [*]
      have hw32 : memW post (n + 32) = memW s (n + 32) := hw_k 4 (by omega)
      have hw40 : memW post (n + 40) = memW s (n + 40) := hw_k 5 (by omega)
      rw [hw32, hw40]
      by_cases hlen0 : memW s (n + 40) = 0
      · exact Or.inl hlen0
      · rcases hkey_n h12 with h0 | ⟨hnib, hal_p, hin_p, hdisj_p⟩
        · exact Or.inl h0
        · right
          refine ⟨fun k hk => ?_, hag.allocated hal_p, hin_p, ?_⟩
          · rw [hu_byte n hn h12 hlen0 k hk]; exact hnib k hk
          · intro m hm
            have hhm_hi : m + nodeSize (memW s m) ≤ 2 ^ 64 := by
              have := (hN.1 m hm).2.2.1.2; dsimp [nodeIvl] at this; omega
            have hm8 : m % 8 = 0 := (hN.1 m hm).2.2.2.1.1
            have hu_m : IvlUnhit s post (m, nodeSize (memW s m)) := hu_rec m hm
            have hsz_m : 32 ≤ nodeSize (memW s m) := by unfold nodeSize; split_ifs <;> omega
            have hwm : memW post m = memW s m := memW_eq_of_ivlUnhit hu_m hm8 hhm_hi ⟨by omega, by omega⟩
            have hm_ivl : nodeIvl post m = nodeIvl s m := by simp [nodeIvl, hwm]
            rw [hm_ivl]; exact hdisj_p m hm⟩
  constructor
  · refine ⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩
    · obtain ⟨hk3, hal_n, hin_n, hw_n, hext, hbr, _, h16_lt, h1_56, h3_168⟩ := hN.1 n hn
      obtain ⟨hw0, hivl_eq, hw_k, _, hkey_post⟩ := hn_props n hn
      have hsz_ge32 : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
      have hw16 : memW post (n + 16) = memW s (n + 16) := hw_k 2 (by omega)
      rw [hw0, hivl_eq, hw16]
      refine ⟨hk3, hag.allocated hal_n, hin_n, wordsOK_transfer hgS hgP hw_n, ?_, ?_, hkey_post, h16_lt, ?_, ?_⟩
      · intro h2
        have hsz : nodeSize (memW s n) = 56 := by unfold nodeSize; simp [h2]
        have hw48 := hw_k 6 (by omega)
        simpa only [Nat.mul_succ, Nat.mul_zero] using (by rw [hw48]; exact hext h2 : RootIn Nd (memW post (n + 48)))
      · intro h3 i hi
        have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
        have hw_ch := hw_k (4 + i) (by omega)
        have hadd : n + 8 * (4 + i) = n + 32 + 8 * i := by omega
        rw [← hadd, hw_ch, hadd]; exact hbr h3 i hi
      · intro h1
        have hsz : nodeSize (memW s n) = 64 := by unfold nodeSize; simp [h1]
        have hw56 : memW post (n + 56) = memW s (n + 56) := hw_k 7 (by omega)
        rw [hw56]; exact h1_56 h1
      · intro h3
        have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
        have hw168 : memW post (n + 168) = memW s (n + 168) := hw_k 21 (by omega)
        rw [hw168]; exact h3_168 h3
    · rw [(hn_props n hn).2.1, (hn_props m hm).2.1]
      exact hN.2 n hn m hm hne
  · unfold nodeExtents
    apply List.flatMap_congr
    intro n hn
    rw [(hn_props n hn).2.1, (hn_props n hn).2.2.2.1]

/-- Master W1 congruence supporting fresh rebindings of untyped `globalBuffers`! -/
theorem worldTypedWith_congr_w1 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hag : AllocatorGrows s post)
    (hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g)
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i)
    (hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80))
    (hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72))
    (hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88))
    (hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap"))
    (hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i)
    (hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i)
    (hu_nd_rec : ∀ n ∈ Nd, IvlUnhit s post (nodeIvl s n))
    (hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k))
    (hlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16)
    (hF_post : FixedTyped post)
    (hfix_new : ∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o = (0, 0) ∨
      Inside o (globN s "heap_ptr") (globN post "heap_ptr")) :
    WorldTypedWith post S Nd ∧
    OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd) ∧
    nodeExtents post Nd = nodeExtents s Nd ∧
    (∀ t ∈ S, htabFootprint post t = htabFootprint s t) := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hW
  have hbo_g : globN post "bo" = globN s "bo" := hcore "bo" (by decide)
  have hws_g : globN post "ws" = globN s "ws" := hcore "ws" (by decide)
  have hbs_g : globN post "bs" = globN s "bs" := hcore "bs" (by decide)
  have hts_g : globN post "ts" = globN s "ts" := hcore "ts" (by decide)
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hcore "bal_accounts" (by decide)
  have hbo_part := blockOutObjects_eq_of_bo_unhit hAs.2 hF hbo_g hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst
  have hbal_part := balObjects_eq_of_unhit hAs.2 hT hF hba_g hu_tab hu_bal hlow
  have hjr_part := journalRoleSlots_eq_of_unhit hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hcore hu_ts hu_jr
  have hwrs_eq := worldRoleSlots_eq_of_unhit hAs.2 hT hF hcore hu_tab hu_ws hu_bs hu_ts hu_bal hlow
  have hnd_part := nodeHeap_congr_bytes hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  have htab_fp_hdr : ∀ t ∈ S, (∀ k, k < 11 → hdr post t k = hdr s t k) ∧ htabFootprint post t = htabFootprint s t := by
    have h264_he : heapEnd ≤ 2 ^ 64 := by decide
    intro t ht
    have hwf := (hT.2.1 t ht).1
    have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; dsimp at this; omega
    exact htabFootprint_eq_of_hdr_unhit ht8 hhi (hu_tab t ht _ ht_fp)
  have hdisj_alloc_new : ∀ i : Ivl, Allocated s i → ∀ j ∈ fixedObjects post,
      (∀ k ∈ fixedObjects s, Disj i k) → Disj i j := by
    intro i hal j hj hold
    rcases hfix_new j hj with hj_old | rfl | hj_fr
    · exact hold j hj_old
    · exact disj_zero_right i
    · exact Disj.flip (disj_allocated_fresh_heap hAs.2 hAp.2 hal hj_fr)
  have hT_post : TablesTyped post S := by
    obtain ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, hboT, hroles⟩ := hT
    refine ⟨hndS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_part.2, ?_⟩
    · intro t ht
      rw [(htab_fp_hdr t ht).2]
      refine ⟨htabWF_congr_unhit hAs.1 hAp.1 (hTt t ht).1 (hu_tab t ht), fun i hi => ?_⟩
      obtain ⟨hal_i, hdf_i⟩ := (hTt t ht).2 i hi
      exact ⟨hag.allocated hal_i, fun j hj => hdisj_alloc_new i hal_i j hj hdf_i⟩
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
      have hg_core : g ∈ coreWorldGlobals := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;> decide
      rw [hcore g hg_core]; exact hgR g hg
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
      have ho_alloc : o.2 = 0 ∨ Allocated s o := by
        unfold nodeExtents at ho
        obtain ⟨n, hn, hni⟩ := List.mem_flatMap.1 ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hni
        rcases hni with rfl | rfl
        · exact Or.inr (hTr.1.1 n hn).2.1
        · unfold nodePath
          split_ifs with hp
          · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hp.1 with h0 | ⟨_, hal, _, _⟩
            · exact absurd h0 hp.2
            · exact Or.inr hal
          · exact Or.inl rfl
      refine ⟨fun t ht i hi => ?_, fun j hj => ?_⟩
      · rw [(htab_fp_hdr t ht).2] at hi
        exact (hTr.2.1 o ho).1 t ht i hi
      · rcases ho_alloc with ho0 | hal_o
        · exact Or.inl ho0
        · exact hdisj_alloc_new o hal_o j hj (hTr.2.1 o ho).2
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
  refine ⟨⟨hT_post, hjr_part.2, hF_post, hTr_post⟩, ?_, hnd_part.2, fun t ht => (htab_fp_hdr t ht).2⟩
  intro o ho
  unfold worldOwned at ho
  rcases List.mem_append.1 ho with h12 | hnd
  · rcases List.mem_append.1 h12 with htab | hfix
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 htab
      rw [(htab_fp_hdr t ht).2] at hfp
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold worldOwned
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, ht, hfp⟩))
    · rcases hfix_new o hfix with hold | rfl | hfr
      · refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_right _ hold)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hfr)
  · rw [hnd_part.2] at hnd
    refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
    unfold worldOwned
    exact List.mem_append_right _ hnd

/-! ## 4. `FixedTyped` preservation under fresh aligned global-buffer rebindings -/

/-- A newly assigned global buffer interval in `post`: either unchanged from `s`, or `0`, or
allocated inside `[heap_ptr s, heap_ptr post)` with `8 ∣ base`, `8 ∣ sz`, and pairwise disjoint
from every other newly assigned global buffer! -/
def FreshBufsOK {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  (∀ gn ∈ globalBuffers,
    globN post gn.1 = globN s gn.1 ∨
    globN post gn.1 = 0 ∨
    ((globN post gn.1) % 8 = 0 ∧
     Inside (globN post gn.1, gn.2) (globN s "heap_ptr") (globN post "heap_ptr"))) ∧
  (globalBuffers.Pairwise fun a b =>
    (globN post a.1 ≠ globN s a.1 ∧ globN post a.1 ≠ 0) →
    (globN post b.1 ≠ globN s b.1 ∧ globN post b.1 ≠ 0) →
    Disj (globN post a.1, a.2) (globN post b.1, b.2))

theorem fixedTyped_of_freshBufsOK {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hag : AllocatorGrows s post)
    (hF : FixedTyped s)
    (hj_eq : globN post "journal" = globN s "journal")
    (hjc_eq : globN post "journal_cap" = globN s "journal_cap")
    (hbo_eq : blockOutObjects post = blockOutObjects s)
    (hbal_eq : balObjects post = balObjects s)
    (hbuf : FreshBufsOK s post) :
    FixedTyped post ∧
    (∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o = (0, 0) ∨
      Inside o (globN s "heap_ptr") (globN post "heap_ptr")) := by
  let rest_s := [(if globN s "journal_cap" = 0 then 0 else globN s "journal",
      32 * globN s "journal_cap")] ++ blockOutObjects s ++ balObjects s
  let rest_p := [(if globN post "journal_cap" = 0 then 0 else globN post "journal",
      32 * globN post "journal_cap")] ++ blockOutObjects post ++ balObjects post
  have hrest_eq : rest_p = rest_s := by
    simp only [rest_p, rest_s, hj_eq, hjc_eq, hbo_eq, hbal_eq]
  have hfix_s : fixedObjects s = (globalBuffers.map (bufferRegion s)) ++ rest_s := by
    simp only [fixedObjects, rest_s, List.append_assoc]; rfl
  have hfix_p : fixedObjects post = (globalBuffers.map (bufferRegion post)) ++ rest_p := by
    simp only [fixedObjects, rest_p, List.append_assoc]; rfl
  have hgb8 : ∀ gn ∈ globalBuffers, gn.2 % 8 = 0 := by decide
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hitem : ∀ gn ∈ globalBuffers,
      bufferRegion post gn = bufferRegion s gn ∨
      bufferRegion post gn = (0, 0) ∨
      ((bufferRegion post gn).1 % 8 = 0 ∧ (bufferRegion post gn).2 % 8 = 0 ∧
       Inside (bufferRegion post gn) (globN s "heap_ptr") (globN post "heap_ptr")) := by
    intro gn hgn
    rcases hbuf.1 gn hgn with heq | hz | ⟨ha8, hin⟩
    · left; simp [bufferRegion, heq]
    · right; left; simp [bufferRegion, hz]
    · by_cases h0 : globN post gn.1 = 0
      · right; left; simp [bufferRegion, h0]
      · right; right; simp [bufferRegion, h0]; exact ⟨ha8, hgb8 gn hgn, hin⟩
  have hnew_prop : ∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o = (0, 0) ∨
      Inside o (globN s "heap_ptr") (globN post "heap_ptr") := by
    intro o ho
    rw [hfix_p, hrest_eq] at ho
    rcases List.mem_append.1 ho with hmb | hmr
    · obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hmb
      rcases hitem gn hgn with heq | hz | ⟨_, _, hin⟩
      · left; rw [hfix_s, heq]; exact List.mem_append_left _ (List.mem_map.2 ⟨gn, hgn, rfl⟩)
      · right; left; exact hz
      · right; right; exact hin
    · left; rw [hfix_s]; exact List.mem_append_right _ hmr
  refine ⟨⟨?_, ?_⟩, hnew_prop⟩
  · intro i hi
    rw [hfix_p, hrest_eq] at hi
    rcases List.mem_append.1 hi with hmb | hmr
    · obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hmb
      rcases hitem gn hgn with heq | hz | ⟨ha8, hsz8, hin⟩
      · rw [heq]
        have hm_s : bufferRegion s gn ∈ fixedObjects s := by
          rw [hfix_s]; exact List.mem_append_left _ (List.mem_map.2 ⟨gn, hgn, rfl⟩)
        rcases hF.1 _ hm_s with h0 | ⟨hal, hw⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hAs.1 hAp.1 hw⟩
      · rw [hz]; exact Or.inl rfl
      · right
        have hlo : sourceBase ≤ (bufferRegion post gn).1 := le_trans hAs.2.1 hin.1
        have hhi : (bufferRegion post gn).1 + (bufferRegion post gn).2 ≤ heapEnd :=
          le_trans hin.2 (le_trans hAp.2.2.1 hhl_he)
        exact ⟨Or.inl ⟨hlo, hin.2⟩, wordsOK_of_inside_heap hAp.1 ha8 hsz8 hlo hhi⟩
    · have hm_s : i ∈ fixedObjects s := by rw [hfix_s]; exact List.mem_append_right _ hmr
      rcases hF.1 _ hm_s with h0 | ⟨hal, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hAs.1 hAp.1 hw⟩
  · have hpair_s := hF.2
    rw [hfix_s] at hpair_s
    obtain ⟨hp_buf_s, hp_rest_s, hp_cross_s⟩ := List.pairwise_append.1 hpair_s
    have hp_names_s : globalBuffers.Pairwise (fun a b => Disj (bufferRegion s a) (bufferRegion s b)) :=
      List.pairwise_map.1 hp_buf_s
    rw [hfix_p, hrest_eq]
    refine List.pairwise_append.2 ⟨List.pairwise_map.2 ?_, hp_rest_s, ?_⟩
    · rw [List.pairwise_iff_getElem] at hp_names_s ⊢
      have hpw_new := List.pairwise_iff_getElem.1 hbuf.2
      intro idx1 idx2 hi1 hi2 hlt
      let a := globalBuffers[idx1]
      let b := globalBuffers[idx2]
      change Disj (bufferRegion post a) (bufferRegion post b)
      have ha_mem : a ∈ globalBuffers := List.getElem_mem hi1
      have hb_mem : b ∈ globalBuffers := List.getElem_mem hi2
      have hold_ab : Disj (bufferRegion s a) (bufferRegion s b) := hp_names_s idx1 idx2 hi1 hi2 hlt
      by_cases ha_same : globN post a.1 = globN s a.1
      · have hra : bufferRegion post a = bufferRegion s a := by simp [bufferRegion, ha_same]
        rw [hra]
        rcases hitem b hb_mem with hrb | hrb0 | ⟨_, _, hin_b⟩
        · rw [hrb]; exact hold_ab
        · rw [hrb0]; exact disj_zero_right _
        · have hm_a : bufferRegion s a ∈ fixedObjects s := by
            rw [hfix_s]; exact List.mem_append_left _ (List.mem_map.2 ⟨a, ha_mem, rfl⟩)
          rcases hF.1 _ hm_a with h0 | ⟨hal_a, _⟩
          · exact Or.inl h0
          · exact Disj.flip (disj_allocated_fresh_heap hAs.2 hAp.2 hal_a hin_b)
      · by_cases ha0 : globN post a.1 = 0
        · exact Or.inl (by simp [bufferRegion, ha0])
        · rcases hbuf.1 a ha_mem with h_eq | h_z | ⟨_, hin_a⟩
          · exact absurd h_eq ha_same
          · exact absurd h_z ha0
          · by_cases hb_same : globN post b.1 = globN s b.1
            · have hrb : bufferRegion post b = bufferRegion s b := by simp [bufferRegion, hb_same]
              rw [hrb]
              have hm_b : bufferRegion s b ∈ fixedObjects s := by
                rw [hfix_s]; exact List.mem_append_left _ (List.mem_map.2 ⟨b, hb_mem, rfl⟩)
              rcases hF.1 _ hm_b with h0 | ⟨hal_b, _⟩
              · exact Or.inr (Or.inl h0)
              · have hin_ra : Inside (bufferRegion post a) (globN s "heap_ptr") (globN post "heap_ptr") := by
                  simpa [bufferRegion, ha0] using hin_a
                exact disj_allocated_fresh_heap hAs.2 hAp.2 hal_b hin_ra
            · by_cases hb0 : globN post b.1 = 0
              · exact Or.inr (Or.inl (by simp [bufferRegion, hb0]))
              · have hd_new : Disj (globN post a.1, a.2) (globN post b.1, b.2) :=
                  hpw_new idx1 idx2 hi1 hi2 hlt ⟨ha_same, ha0⟩ ⟨hb_same, hb0⟩
                simpa [bufferRegion, ha0, hb0] using hd_new
    · intro x hx y hy
      obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hx
      rcases hitem gn hgn with heq | hz | ⟨_, _, hin⟩
      · rw [heq]; exact hp_cross_s _ (List.mem_map.2 ⟨gn, hgn, rfl⟩) y hy
      · rw [hz]; exact disj_zero_left y
      · have hm_y : y ∈ fixedObjects s := by rw [hfix_s]; exact List.mem_append_right _ hy
        rcases hF.1 _ hm_y with h0 | ⟨hal_y, _⟩
        · exact Or.inr (Or.inl h0)
        · exact disj_allocated_fresh_heap hAs.2 hAp.2 hal_y hin

/-! ## 5. Master `WorldStep` theorem for untyped buffer allocators & region writers -/

theorem untypedBuf_disj_worldTypedIvls {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) (gn : String × Nat)
    (hg : gn ∈ globalBuffers) (hu : gn.1 ∉ typedRecords.map Prod.fst) :
    ∀ j ∈ worldTypedIvls s S Nd, Disj (bufferRegion s gn) j :=
  bufferRegion_disj hW gn hg hu

theorem worldTypedIvl_allocated {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) {i : Ivl} (hi : i ∈ worldTypedIvls s S Nd) :
    i.2 = 0 ∨ Allocated s i := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hW
  unfold worldTypedIvls at hi
  rcases List.mem_append.1 hi with h12345 | hnd
  · rcases List.mem_append.1 h12345 with h1234 | hbal
    · rcases List.mem_append.1 h1234 with h123 | hbo
      · rcases List.mem_append.1 h123 with h12 | hjr
        · rcases List.mem_append.1 h12 with htab | hrec
          · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 htab
            exact Or.inr (((hT.2.1 t ht).2 i hfp).1)
          · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hrec
            have hmf := typedRecord_mem_fixedObjects s hr
            rcases hF.1 _ hmf with h0 | ⟨hal, _⟩
            · exact Or.inl h0
            · exact Or.inr hal
        · simp only [List.mem_singleton] at hjr; subst hjr
          by_cases hjc0 : globN s "journal_cap" = 0
          · exact Or.inl (by simp [hjc0])
          · rcases hJ.2.2.1 with h0 | ⟨hal, _⟩
            · exact absurd h0 hjc0
            · simp only [hjc0, ↓reduceIte]; exact Or.inr hal
      · have hmf : i ∈ fixedObjects s := by
          unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hbo)))
        rcases hF.1 i hmf with h0 | ⟨hal, _⟩
        · exact Or.inl h0
        · exact Or.inr hal
    · have hmf : i ∈ fixedObjects s := by
        unfold fixedObjects; exact List.mem_append.2 (Or.inr hbal)
      rcases hF.1 i hmf with h0 | ⟨hal, _⟩
      · exact Or.inl h0
      · exact Or.inr hal
  · unfold nodeExtents at hnd
    obtain ⟨n, hn, hni⟩ := List.mem_flatMap.1 hnd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hni
    rcases hni with rfl | rfl
    · exact Or.inr (hTr.1.1 n hn).2.1
    · unfold nodePath
      split_ifs with hp
      · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hp.1 with h0 | ⟨_, hal, _, _⟩
        · exact absurd h0 hp.2
        · exact Or.inr hal
      · exact Or.inl rfl

/-- Master W1 `WorldStep` theorem covering all P27 + P28 functions:
- `R s` output intervals (which may include `bufferRegion s gn` or caller pointers `(locN s "out", 32)`),
- `B` untyped `globalBuffers` that may ALSO be written (already in `worldOwned s S Nd` via `fixedObjects s`!),
- `gw` modified globals (disjoint from `coreWorldGlobals`, only rebinding `heap_ptr`, `scratch_ptr`, or fresh untyped `globalBuffers` satisfying `FreshBufsOK s post`),
- `Q` extra postcondition! -/
theorem worldStep_master {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (B : List (String × Nat))
    (hB_ok : ∀ gs ∈ B, gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst)
    (hWOK : WorldOK s)
    (hAp : ArenaReady post)
    (hag : AllocatorGrows s post)
    (hgw : GlobalsKept gw s post)
    (hcore_out : ∀ g ∈ coreWorldGlobals, ofString g ∉ gw.map ofString)
    (hbuf : FreshBufsOK s post)
    (hcell : ∀ x : BitVec 64, post.memory x ≠ s.memory x →
      s.memaddrs x ∧
      ((∃ ivl ∈ R s, CellHitsPos x.toNat ivl) ∨
       (∃ gs ∈ B, CellHitsPos x.toNat (bufferRegion s gs)) ∨
       CellHitsPos x.toNat (freeGap s) ∨
       CellHitsPos x.toNat (heapFree s)))
    (hbyte : ∀ a : Nat, a < 2 ^ 64 → memB post a ≠ memB s a →
      (∃ ivl ∈ R s, InIvl a ivl) ∨
      (∃ gs ∈ B, InIvl a (bufferRegion s gs)) ∨
      InIvl a (freeGap s) ∨
      InIvl a (heapFree s))
    (hQ : ∀ S Nd, WorldTypedWith s S Nd → IvlsDisj (R s) (worldTypedIvls s S Nd) →
      WorldTypedWith post S Nd →
      OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd) →
      nodeExtents post Nd = nodeExtents s Nd →
      (∀ t ∈ S, htabFootprint post t = htabFootprint s t) →
      Q s r post S Nd) :
    WorldStep R gw stdKeep Q s r post := by
  have hAs := hWOK.1
  have hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g :=
    fun g hg => globN_eq_of_lookup (hgw (ofString g) (hcore_out g hg))
  have hdom_wr : ∀ a : BitVec 64, post.memory a ≠ s.memory a → s.memaddrs a :=
    fun a hne => (hcell a hne).1
  have hlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 :=
    ⟨mem_low_eq_of_domain_writes hdom_wr hAs.1 (by rw [sourceBase_val]; omega),
     mem_low_eq_of_domain_writes hdom_wr hAs.1 (by rw [sourceBase_val]; omega)⟩
  -- 1. `RecordsKept`:
  have hRecKept : RecordsKept R stdKeep s post := by
    obtain ⟨_, S0, hWT0⟩ := hWOK
    obtain ⟨Nd0, hWTW0⟩ := (worldTyped_iff_with s S0).1 hWT0
    have hF0 := hWTW0.2.2.1
    intro rec hrec hgnz k hk hnoR
    have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by simp [typedRecords], ?_⟩; simp at hk; omega
      · refine ⟨80, by simp [typedRecords], ?_⟩; simp at hk; omega
      · refine ⟨72, by simp [typedRecords], ?_⟩; simp at hk; omega
      · refine ⟨88, by simp [typedRecords], ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hk8, hksz⟩ := hrec_sz
    have hmf := typedRecord_mem_fixedObjects s htr
    simp only [hgnz, ↓reduceIte] at hmf
    have hwti_rec : (globN s rec.1, sz) ∈ worldTypedIvls s S0 Nd0 := by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨(rec.1, sz), htr, by simp [hgnz]⟩
    rcases hF0.1 _ hmf with h0 | ⟨hal, hwords⟩
    · omega
    · have hhi := (ivl_allocated_bound hAs.2 hal).2
      have hg8 : (globN s rec.1) % 8 = 0 := hwords.1
      have ha_lt : globN s rec.1 + k < 2 ^ 64 := by dsimp at hhi; omega
      unfold memW
      have hmem_eq : post.memory (BitVec.ofNat 64 (globN s rec.1 + k)) =
          s.memory (BitVec.ofNat 64 (globN s rec.1 + k)) := by
        by_contra hne
        obtain ⟨_, hcases⟩ := hcell _ hne
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at hcases
        have hin_rec : globN s rec.1 + k ≥ globN s rec.1 ∧ globN s rec.1 + k + 8 ≤ globN s rec.1 + sz :=
          ⟨by omega, by omega⟩
        rcases hcases with ⟨ivl, hivl, _, hhit⟩ | ⟨gs, hgs, hhit⟩ | hfg | hhf
        · exact hnoR ivl hivl hhit
        · obtain ⟨hgs_gb, hgs_nt⟩ := hB_ok gs hgs
          have hdj := Disj.flip (untypedBuf_disj_worldTypedIvls hWTW0 gs hgs_gb hgs_nt _ hwti_rec)
          exact not_cellHitsPos_of_disj hin_rec hdj hhit
        · exact not_cellHitsPos_of_disj hin_rec (disj_allocated_freeGap hAs.2 hal) hfg
        · exact not_cellHitsPos_of_disj hin_rec (disj_allocated_heapFree hAs.2 hal) hhf
      rw [hmem_eq]
  refine ⟨hAp, hag.1, hgw, hRecKept, fun S Nd hWT hDisjR => ?_⟩
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  let keep0 : List Ivl := R s ++ B.map (bufferRegion s) ++ [freeGap s]
  have hfr_pos : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
      (∃ j ∈ keep0, CellHitsPos a.toNat j) ∨ CellHitsPos a.toNat (heapFree s) := by
    intro a hne
    rcases (hcell a hne).2 with ⟨ivl, hivl, hhit⟩ | ⟨gs, hgs, hhit⟩ | hfg | hhf
    · left; refine ⟨ivl, ?_, hhit⟩
      simp only [keep0, List.mem_append]; exact Or.inl (Or.inl hivl)
    · left; refine ⟨bufferRegion s gs, ?_, hhit⟩
      simp only [keep0, List.mem_append]; exact Or.inl (Or.inr (List.mem_map.2 ⟨gs, hgs, rfl⟩))
    · left; refine ⟨freeGap s, ?_, hfg⟩
      simp only [keep0, List.mem_append, List.mem_singleton]; exact Or.inr trivial
    · exact Or.inr hhf
  have hu_wti_aligned : ∀ i ∈ worldTypedIvls s S Nd, Allocated s i → i.1 % 8 = 0 → i.2 % 8 = 0 →
      IvlUnhit s post i := by
    intro i hi hal hi1 hi2
    refine ivlUnhit_of_cellHitsPos hi1 hi2 hfr_pos (fun j hj => ?_) (disj_allocated_heapFree hAs.2 hal)
    simp only [keep0, List.mem_append, List.mem_singleton] at hj
    rcases hj with (hjR | hjB) | rfl
    · exact Disj.flip (hDisjR j hjR i hi)
    · obtain ⟨gs, hgs, rfl⟩ := List.mem_map.1 hjB
      obtain ⟨hgs_gb, hgs_nt⟩ := hB_ok gs hgs
      exact Disj.flip (untypedBuf_disj_worldTypedIvls ⟨hT, hJ, hF, hTr⟩ gs hgs_gb hgs_nt i hi)
    · exact disj_allocated_freeGap hAs.2 hal
  have hu_fix_wti : ∀ i ∈ worldTypedIvls s S Nd, i ∈ fixedObjects s → i.2 ≠ 0 → IvlUnhit s post i := by
    intro i hwti hfi hpos
    rcases hF.1 i hfi with h0 | ⟨hal, hw⟩
    · exact absurd h0 hpos
    · exact hu_wti_aligned i hwti hal hw.1 hw.2.1
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i := by
    intro t ht i hi
    have hal := ((hT.2.1 t ht).2 i hi).1
    have hw := ((hT.2.1 t ht).1.1 i hi).2
    refine hu_wti_aligned i ?_ hal hw.1 hw.2.1
    unfold worldTypedIvls
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; left; apply List.mem_append.2; left
    exact List.mem_flatMap.2 ⟨t, ht, hi⟩
  have hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("ws", 40), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by simp [typedRecords]))
      (by simp)
  have hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("bs", 80), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by simp [typedRecords]))
      (by simp)
  have hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("ts", 72), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by simp [typedRecords]))
      (by simp)
  have hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords]))
      (by simp)
  have hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun hcnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; right; simp [hcnz])
      (by unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; right; simp [hcnz])
      (by dsimp only; omega)
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i := fun i hi h24 =>
    hu_fix_wti i
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by omega)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hpos =>
    hu_fix_wti i
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi))
      hpos
  have hu_nd_rec : ∀ n ∈ Nd, IvlUnhit s post (nodeIvl s n) := fun n hn => by
    have hal := (hTr.1.1 n hn).2.1
    have hw := (hTr.1.1 n hn).2.2.2.1
    refine hu_wti_aligned _ ?_ hal hw.1 hw.2.1
    unfold worldTypedIvls; refine List.mem_append.2 (Or.inr ?_)
    unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
    · exact absurd h0 hlen0
    · have hp_wti : (memW s (n + 32), memW s (n + 40)) ∈ worldTypedIvls s S Nd := by
        unfold worldTypedIvls; refine List.mem_append.2 (Or.inr ?_)
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
      by_contra hne_b
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; dsimp at this; omega
      rcases hbyte _ ha_lt hne_b with ⟨ivl, hivl, hin_ivl⟩ | ⟨gs, hgs, hin_gs⟩ | hfg | hhf
      · have hdj := hDisjR ivl hivl _ hp_wti
        unfold InIvl at hin_ivl; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · obtain ⟨hgs_gb, hgs_nt⟩ := hB_ok gs hgs
        have hdj := untypedBuf_disj_worldTypedIvls ⟨hT, hJ, hF, hTr⟩ gs hgs_gb hgs_nt _ hp_wti
        unfold InIvl at hin_gs; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · have hdj := disj_allocated_freeGap hAs.2 hal_p
        unfold InIvl at hfg; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · have hdj := disj_allocated_heapFree hAs.2 hal_p
        unfold InIvl at hhf; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
  have hbo_eq := (blockOutObjects_eq_of_bo_unhit hAs.2 hF (hcore "bo" (by decide))
    hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst).1
  have hbal_eq := (balObjects_eq_of_unhit hAs.2 hT hF (hcore "bal_accounts" (by decide))
    hu_tab hu_bal hlow).1
  obtain ⟨hF_post, hfix_new⟩ := fixedTyped_of_freshBufsOK hAs hAp hag hF
    (hcore "journal" (by decide)) (hcore "journal_cap" (by decide)) hbo_eq hbal_eq hbuf
  obtain ⟨hWT_post, hOG, hne_eq, hfp_eq⟩ := worldTypedWith_congr_w1 hAs hAp hag hcore
    ⟨hT, hJ, hF, hTr⟩ hu_tab hu_ws hu_bs hu_ts hu_bo hu_jr hu_bo_lst hu_bal hu_nd_rec hu_nd_byte
    hlow hF_post hfix_new
  refine ⟨S, Nd, fun _ ht => ht, hWT_post, hOG, ?_,
    hQ S Nd ⟨hT, hJ, hF, hTr⟩ hDisjR hWT_post hOG hne_eq hfp_eq⟩
  -- `FrameOutside`:
  intro a hkeep hfresh
  by_contra hne
  rcases (hcell a hne).2 with ⟨ivl, hivl, _, hhit⟩ | ⟨gs, hgs, _, hhit⟩ | ⟨_, hfg⟩ | ⟨_, hhf⟩
  · exact hkeep ivl (List.mem_append_left _ (List.mem_append_right _ hivl)) hhit
  · have hfo_gs : bufferRegion s gs ∈ fixedObjects s := by
      unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨gs, (hB_ok gs hgs).1, rfl⟩
    have hwo_gs : bufferRegion s gs ∈ worldOwned s S Nd := by
      unfold worldOwned; exact List.mem_append_left _ (List.mem_append_right _ hfo_gs)
    exact hkeep _ (List.mem_append_left _ (List.mem_append_left _ hwo_gs)) hhit
  · exact hkeep (freeGap s) (List.mem_append_right _ List.mem_cons_self) hfg
  · exact hfresh hhf

end InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
