import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.StoreAllocHelpers
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03

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

/-! ## 1. Byte store & word store primitives -/

def memWordAt (mem : BitVec 64 → HolWordLab 64) (addr : BitVec 64) : BitVec 64 :=
  match mem addr with
  | .word w => w

def memByteAt (mem : BitVec 64 → HolWordLab 64) (be : Bool) (addr : BitVec 64) : UInt8 :=
  panGetByteHOL addr (memWordAt mem (panByteAlignHOL addr)) be

theorem memB_eq_memByteAt {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) :
    memB s a = (memByteAt s.memory s.be (BitVec.ofNat 64 a)).toNat := by
  unfold memB memByteAt memWordAt
  cases s.memory (panByteAlignHOL (BitVec.ofNat 64 a)) with
  | word w => rfl

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
    rw [hdK, hdK8, ← Nat.mul_assoc x, ← Nat.mul_assoc y, ← Nat.add_mul, ← Nat.mul_assoc]; omega
  rw [h1, Nat.add_mul_div_right _ _ hpJ]; omega

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
    conv_lhs => rw [hj_eq]; rw [Nat.pow_add]
  have hpK8 : 0 < 2 ^ (K + 8) := Nat.two_pow_pos _
  have hsum : x * 2 ^ (K + 8) + y * 2 ^ K + z = (y * 2 ^ K + z) + x * 2 ^ (K + 8) := by omega
  rw [hsum, hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_right _ _ hpK8, Nat.div_eq_of_lt hyz, Nat.zero_add,
    Nat.mul_div_cancel _ hpK8]

theorem panMemStoreByte_other_byte {mem : BitVec 64 → HolWordLab 64}
    {dom : BitVec 64 → Prop} [DecidablePred dom] {be : Bool}
    {addr : BitVec 64} {bw : BitVec 8} {mem' : BitVec 64 → HolWordLab 64}
    (hst : panMemStoreByteWord8HOL mem dom be addr bw = some mem')
    {addr' : BitVec 64} (hne : addr' ≠ addr) :
    (match mem' (panByteAlignHOL addr') with | .word v => (panGetByteHOL addr' v be).toNat) =
    (match mem (panByteAlignHOL addr') with | .word v => (panGetByteHOL addr' v be).toNat) := by
  unfold panMemStoreByteWord8HOL at hst
  dsimp only at hst
  cases hcell : mem (panByteAlignHOL addr) with
  | word cell =>
    rw [hcell] at hst
    split at hst
    · injection hst with hmem
      subst hmem
      by_cases hal : panByteAlignHOL addr' = panByteAlignHOL addr
      · simp only [hal, ↓reduceIte, hcell, panGetByteHOL]
        let b : UInt8 := UInt8.ofNat bw.toNat
        have hb8 : b.toNat < 256 := b.toNat_lt_size
        have hbw_eq : bw.toNat = b.toNat := by
          have := bw.isLt
          simp [b, UInt8.toNat_ofNat', Nat.mod_eq_of_lt this]
        rw [hbw_eq]
        have hset_nat := panSetByteHOL_toNat (width := 64) (by decide) addr cell b be
        have hcell_high : ∀ J : Nat, byteBitIndex addr be + 8 ≤ J →
            ((cell.toNat / 2 ^ (byteBitIndex addr be + 8)) * 2 ^ (byteBitIndex addr be + 8)) / 2 ^ J =
              cell.toNat / 2 ^ J := by
          intro J hKJ
          have hdJ : 2 ^ J = 2 ^ (byteBitIndex addr be + 8) * 2 ^ (J - (byteBitIndex addr be + 8)) := by
            have hj_eq : J = (byteBitIndex addr be + 8) + (J - (byteBitIndex addr be + 8)) := by omega
            conv_lhs => rw [hj_eq]; rw [Nat.pow_add]
          have hpK8 : 0 < 2 ^ (byteBitIndex addr be + 8) := Nat.two_pow_pos _
          rw [hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hpK8]
        have h256_pow : ∀ a : BitVec 64,
            (256 : Nat) ^ (if be then 8 - 1 - a.toNat % 8 else a.toNat % 8) = 2 ^ byteBitIndex a be := by
          intro a
          have : ∀ k, (256 : Nat) ^ k = 2 ^ (8 * k) := fun k => by
            rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]
          rw [this]; cases be <;> simp [byteBitIndex, Nat.mul_comm 8]
        have hmod_ne : addr'.toNat % 8 ≠ addr.toNat % 8 := by
          intro hmeq; apply hne; apply BitVec.eq_of_toNat_eq
          have ha1 := panByteAlign_toNat64 addr'
          have ha2 := panByteAlign_toNat64 addr
          rw [hal] at ha1; omega
        have hidx_sep : byteBitIndex addr' be + 8 ≤ byteBitIndex addr be ∨
            byteBitIndex addr be + 8 ≤ byteBitIndex addr' be := by
          have hm1 : addr'.toNat % 8 < 8 := by omega
          have hm2 : addr.toNat % 8 < 8 := by omega
          cases be <;> simp only [byteBitIndex, Bool.false_eq_true, if_true, if_false] <;> omega
        have heq_mod : (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
            256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256 =
          cell.toNat / 256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256 := by
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
              rw [hmul] at hdm; omega
            conv_rhs => rw [hcell_eq]
            rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]; omega
          · rw [pow_div_high _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hhigh,
              hcell_high _ hhigh]
        simpa [UInt8.toNat_ofNat'] using heq_mod
      · simp only [hal, ↓reduceIte]
    · cases hst

/-! ## 2. `ByteEff`: pure memory-region write effect (no global changes) -/

structure ByteEff {F : Type} (s post : PanSemStateFiniteExact 64 F) (Rl : List Ivl) : Prop where
  code       : post.code = s.code
  memaddrs   : post.memaddrs = s.memaddrs
  shMemaddrs : post.shMemaddrs = s.shMemaddrs
  baseAddr   : post.baseAddr = s.baseAddr
  be         : post.be = s.be
  globals    : post.globals = s.globals
  eshapes    : post.eshapes = s.eshapes
  out_dom    : ∀ a : BitVec 64, post.memory a ≠ s.memory a → s.memaddrs a
  cell_frame : ∀ a : BitVec 64, post.memory a ≠ s.memory a → ∃ i ∈ Rl, CellHitsPos a.toNat i
  byte_frame : ∀ b : Nat, b < 2 ^ 64 → memB post b ≠ memB s b → ∃ i ∈ Rl, InIvl b i

theorem ByteEff.refl {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    ByteEff s s Rl :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => absurd rfl h,
   fun _ h => absurd rfl h, fun _ _ h => absurd rfl h⟩

theorem ByteEff.locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : ByteEff s post Rl) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ByteEff s { post with locals := L, clock := k } Rl :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals, h.eshapes,
   h.out_dom, h.cell_frame, h.byte_frame⟩

theorem ByteEff.trans {F : Type} {a b c : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h1 : ByteEff a b Rl) (h2 : ByteEff b c Rl) : ByteEff a c Rl := by
  refine ⟨h2.code.trans h1.code, h2.memaddrs.trans h1.memaddrs,
    h2.shMemaddrs.trans h1.shMemaddrs, h2.baseAddr.trans h1.baseAddr,
    h2.be.trans h1.be, h2.globals.trans h1.globals, h2.eshapes.trans h1.eshapes, ?_, ?_, ?_⟩
  · intro x hne
    by_cases hcb : c.memory x = b.memory x
    · rw [hcb] at hne; exact h1.out_dom x hne
    · rw [← h1.memaddrs]; exact h2.out_dom x hcb
  · intro x hne
    by_cases hcb : c.memory x = b.memory x
    · rw [hcb] at hne; exact h1.cell_frame x hne
    · exact h2.cell_frame x hcb
  · intro x hx hne
    by_cases hcb : memB c x = memB b x
    · rw [hcb] at hne; exact h1.byte_frame x hx hne
    · exact h2.byte_frame x hx hcb

theorem ByteEff.mono {F : Type} {s post : PanSemStateFiniteExact 64 F} {R1 R2 : List Ivl}
    (h : ByteEff s post R1)
    (hsub : ∀ i ∈ R1, 0 < i.2 → ∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) :
    ByteEff s post R2 := by
  refine ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals, h.eshapes, h.out_dom, ?_, ?_⟩
  · intro a hne
    obtain ⟨i, hi, hipos, hc1, hc2⟩ := h.cell_frame a hne
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi hipos
    exact ⟨j, hj, by omega, by omega, by omega⟩
  · intro b hb hne
    obtain ⟨i, hi, hb1, hb2⟩ := h.byte_frame b hb hne
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi (by omega)
    exact ⟨j, hj, by omega, by omega⟩

theorem byteEff_store_one {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64)
    (hval_one : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w))
    (hin : ∀ x : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word x)) →
      s.memaddrs x →
      ∃ i ∈ Rl, i.1 ≤ x.toNat ∧ x.toNat + 8 ≤ i.1 + i.2) :
    ByteEff s (evaluateHOLFiniteState s (.store dstExp valExp)).2 Rl ∧
    ((evaluateHOLFiniteState s (.store dstExp valExp)).1 = none →
      ∃ x : BitVec 64,
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
          some (.val (.word x)) ∧
        sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd ∧ x.toNat % 8 = 0) := by
  rw [evaluateHOLFiniteState_store]
  split
  · rename_i x hx
    split
    · rename_i val hval
      obtain ⟨w, rfl⟩ := hval_one val hval
      split
      · rename_i mem' hmem
        simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
        by_cases hdom : s.memaddrs x
        · simp only [hdom, ↓reduceIte, Option.some.injEq] at hmem
          subst hmem
          have hdom_ord : x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
            rw [hG.memaddrs, ordinaryDomain_iff] at hdom; exact hdom
          have hhe8 : heapEnd % 8 = 0 := by decide
          obtain ⟨ivl, hivl, hi1, hi2⟩ := hin x hx hdom
          refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩,
            fun _ => ⟨x, hx, hdom_ord.2.1, by omega, hdom_ord.1⟩⟩
          · intro a hne; by_cases hax : a = x
            · subst hax; exact hdom
            · simp [hax] at hne
          · intro a hne; by_cases hax : a = x
            · subst hax; exact ⟨ivl, hivl, by omega, by omega, by omega⟩
            · simp [hax] at hne
          · intro b hb hne
            by_cases hal : panByteAlignHOL (BitVec.ofNat 64 b) = x
            · have hc_nat := panByteAlign_toNat64 (BitVec.ofNat 64 b)
              rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at hc_nat
              exact ⟨ivl, hivl, by omega, by omega⟩
            · unfold memB at hne; simp [hal] at hne
        · simp [hdom] at hmem
      · exact ⟨ByteEff.refl s Rl, by simp⟩
    · exact ⟨ByteEff.refl s Rl, by simp⟩
  · exact ⟨ByteEff.refl s Rl, by simp⟩

theorem byteEff_storeByte {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64)
    (hin : ∀ x : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word x)) →
      s.memaddrs (panByteAlignHOL x) →
      ∃ i ∈ Rl, InIvl x.toNat i) :
    ByteEff s (evaluateHOLFiniteState s (.storeByte dstExp valExp)).2 Rl ∧
    ((evaluateHOLFiniteState s (.storeByte dstExp valExp)).1 = none →
      ∃ x : BitVec 64,
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
          some (.val (.word x)) ∧
        sourceBase ≤ x.toNat ∧ x.toNat + 1 ≤ heapEnd) := by
  rw [evaluateHOLFiniteState_storeByte]
  split
  · rename_i x hx
    split
    · rename_i vw hvw
      split
      · rename_i mem' hmem
        have hdom : s.memaddrs (panByteAlignHOL x) := by
          by_contra hc
          unfold panMemStoreByteWord8HOL at hmem
          cases s.memory (panByteAlignHOL x) with
          | word _ => simp [hc] at hmem
        have hdom_ord : (panByteAlignHOL x).toNat % 8 = 0 ∧
            sourceBase ≤ (panByteAlignHOL x).toNat ∧ (panByteAlignHOL x).toNat < heapEnd := by
          rw [hG.memaddrs, ordinaryDomain_iff] at hdom; exact hdom
        have hhe8 : heapEnd % 8 = 0 := by decide
        have hal_nat := panByteAlign_toNat64 x
        obtain ⟨ivl, hivl, hin_x⟩ := hin x hx hdom
        have hmem_cell : ∀ a : BitVec 64, a ≠ panByteAlignHOL x → mem' a = s.memory a := by
          intro a hne
          have hm' := hmem
          unfold panMemStoreByteWord8HOL at hm'
          cases s.memory (panByteAlignHOL x) with
          | word cell =>
            dsimp only at hm'; rw [if_pos hdom] at hm'
            injection hm' with hm_eq; subst hm_eq; simp [hne]
        refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩,
          fun _ => ⟨x, hx, by omega, by omega⟩⟩
        · intro a hne; by_cases hax : a = panByteAlignHOL x
          · subst hax; exact hdom
          · exact False.elim (hne (hmem_cell a hax))
        · intro a hne; by_cases hax : a = panByteAlignHOL x
          · subst hax
            obtain ⟨hx1, hx2⟩ := hin_x
            exact ⟨ivl, hivl, by omega, by rw [hal_nat]; omega, by rw [hal_nat]; omega⟩
          · exact False.elim (hne (hmem_cell a hax))
        · intro b hb hne
          by_cases hbx : BitVec.ofNat 64 b = x
          · have hb_eq : b = x.toNat := by
              have := congrArg BitVec.toNat hbx
              rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at this
            rw [hb_eq]; exact ⟨ivl, hivl, hin_x⟩
          · have hob := @panMemStoreByte_other_byte s.memory s.memaddrs
              (fun addr => Classical.propDecidable (s.memaddrs addr)) s.be x
              (BitVec.ofNat 8 vw.toNat) mem' hmem (BitVec.ofNat 64 b) hbx
            exact False.elim (hne hob)
      · exact ⟨ByteEff.refl s Rl, by simp⟩
    · exact ⟨ByteEff.refl s Rl, by simp⟩
  · exact ⟨ByteEff.refl s Rl, by simp⟩

/-! ## 3. `memzero`, `memcpy`, `st_le32`, `st_le64`, `st_be32`, `st_be64`, `addr_from_words` -/

theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

private def noReturnOrRaise : ProgHOL 64 → Bool
  | .seq a b => noReturnOrRaise a && noReturnOrRaise b
  | .ite _ a b => noReturnOrRaise a && noReturnOrRaise b
  | .while _ a => noReturnOrRaise a
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noReturnOrRaise {F : Type} (p : ProgHOL 64) (hp : noReturnOrRaise p = true)
    (s : PanSemStateFiniteExact 64 F) :
    ¬ Resumes (evaluateHOLFiniteState s p).1 := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noReturnOrRaise] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact not_resumes_error
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
      · exact not_resumes_error
    · exact not_resumes_error
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
      · exact not_resumes_error
    · exact not_resumes_error
  | seq a b =>
    have hab : noReturnOrRaise a = true ∧ noReturnOrRaise b = true := by
      simpa [shape, noReturnOrRaise, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noReturnOrRaise a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    cases r with
    | none =>
      have mclk : m.clock ≤ s.clock := rem
      exact evaluate_noReturnOrRaise b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noReturnOrRaise a = true ∧ noReturnOrRaise b = true := by
      simpa [shape, noReturnOrRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturnOrRaise b hab.2 s
      · exact evaluate_noReturnOrRaise a hab.1 s
    · exact not_resumes_error
  | «while» cond body =>
    have hb : noReturnOrRaise body = true := by simpa [shape, noReturnOrRaise] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noReturnOrRaise body hb (decClockHOLFinite s)
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none =>
            exact evaluate_noReturnOrRaise (.while cond body) (by simpa [noReturnOrRaise] using hb) mid
          | some r1 =>
            cases r1 with
            | «continue» =>
              exact evaluate_noReturnOrRaise (.while cond body) (by simpa [noReturnOrRaise] using hb) mid
            | «break» => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
            | returned _ => exact ih1
            | exception _ _ => exact ih1
            | timeOut => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
            | error => exact not_resumes_error
            | finalFfi _ => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
      · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
    · exact not_resumes_error
  | _ => simp [shape, noReturnOrRaise] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

private def noBreakOrCont : ProgHOL 64 → Bool
  | .seq a b => noBreakOrCont a && noBreakOrCont b
  | .ite _ a b => noBreakOrCont a && noBreakOrCont b
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noBreakOrCont {F : Type} (p : ProgHOL 64) (hp : noBreakOrCont p = true)
    (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ some .break ∧
    (evaluateHOLFiniteState s p).1 ≠ some .continue := by
  cases shape : p with
  | skip => simp [evaluateHOLFiniteState_skip]
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noBreakOrCont] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · simp
      · split <;> simp
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | seq a b =>
    have hab : noBreakOrCont a = true ∧ noBreakOrCont b = true := by
      simpa [shape, noBreakOrCont, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noBreakOrCont a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha
    cases r with
    | none => exact evaluate_noBreakOrCont b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noBreakOrCont a = true ∧ noBreakOrCont b = true := by
      simpa [shape, noBreakOrCont, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noBreakOrCont b hab.2 s
      · exact evaluate_noBreakOrCont a hab.1 s
    · simp
  | _ => simp [shape, noBreakOrCont] at hp

private def CopyInv {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ GuestInv s ∧
  ByteEff s0 s [(dst0.toNat, n0.toNat)] ∧
  s.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  ∃ iw : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
    iw.toNat ≤ n0.toNat ∧
    (0 < iw.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + iw.toNat ≤ heapEnd)

theorem eval_add2_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d i : MlS) (x y : BitVec 64)
    (hx : s.locals.lookup d = some (.val (.word x)))
    (hy : s.locals.lookup i = some (.val (.word y))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local d, .var .local i]) = some (.val (.word (x + y))) := by
  simp [evalHOLExact, evalListHOLExact, hx, hy, valueIsWord, valueWord, wordOpHOL, wordOp]

private theorem eval_add3_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d i : MlS) (x y c : BitVec 64)
    (hx : s.locals.lookup d = some (.val (.word x)))
    (hy : s.locals.lookup i = some (.val (.word y))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local d, .var .local i, .const c]) = some (.val (.word (x + y + c))) := by
  simp [evalHOLExact, evalListHOLExact, hx, hy, valueIsWord, valueWord, wordOpHOL, wordOp,
    BitVec.add_assoc]

theorem eval_load_one_word {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one e) = some v → ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  simp only [evalHOLExact] at hv
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | ev
  · simp [he] at hv
  · rcases ev with ⟨⟨addr⟩⟩ | _ | _
    · simp only [he, memLoadHOLExact] at hv
      split at hv
      · cases hm : s.memory addr with
        | word w =>
          rw [hm] at hv
          split at hv
          · injection hv with h; exact ⟨w, h.symm⟩
          · cases hv
      · cases hv
    · simp [he] at hv
    · simp [he] at hv

private theorem step_domain_nowrap (dst0 iw n0 k : BitVec 64)
    (hle : iw.toNat ≤ n0.toNat)
    (hprev : 0 < iw.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + iw.toNat ≤ heapEnd)
    (hcur : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + k.toNat ≤ heapEnd)
    (hk : 0 < k.toNat) (hk32 : k.toNat ≤ 32)
    (hcond : ¬ (n0 < iw + k)) :
    (dst0 + iw).toNat = dst0.toNat + iw.toNat ∧
    (iw + k).toNat = iw.toNat + k.toNat ∧
      (iw + k).toNat ≤ n0.toNat ∧
      sourceBase ≤ dst0.toNat ∧ dst0.toNat + (iw + k).toNat ≤ heapEnd := by
  rw [sourceBase_val, heapEnd_val] at hprev hcur ⊢
  have hdlt := dst0.isLt; have hilt := iw.isLt; have hnlt := n0.isLt
  rw [BitVec.lt_def] at hcond
  by_cases hiz : iw.toNat = 0
  · have hi0 : iw = 0 := BitVec.eq_of_toNat_eq hiz
    subst hi0
    have hd0 : dst0 + 0 = dst0 := BitVec.add_zero _
    have hk0 : (0 : BitVec 64) + k = k := BitVec.zero_add _
    rw [hd0] at hcur ⊢; rw [hk0] at hcond ⊢
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [hz0]
    exact ⟨by omega, by omega, by omega, hcur.1, hcur.2⟩
  · obtain ⟨hdlo, hdhi⟩ := hprev (by omega)
    have hadd_di : (dst0 + iw).toNat = dst0.toNat + iw.toNat := BitVec.toNat_add_of_lt (by omega)
    rw [hadd_di] at hcur ⊢
    have hik_lt : iw.toNat + k.toNat < 2 ^ 64 := by omega
    have hadd_ik : (iw + k).toNat = iw.toNat + k.toNat := BitVec.toNat_add_of_lt hik_lt
    rw [hadd_ik] at hcond ⊢
    exact ⟨rfl, rfl, by omega, hdlo, by omega⟩

private theorem eval_notLower_true {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n0 iw k w : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const k])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    ¬ (n0 < iw + k) := by
  simp [evalHOLExact, evalListHOLExact, hn, hi, valueIsWord, valueWord, wordOpHOL, wordOp,
    Compiler.Encoders.Asm.wordCmpHOL] at he
  intro hlt
  have hnotle : ¬ (iw + k ≤ n0) := by rw [BitVec.lt_def] at hlt; rw [BitVec.le_def]; omega
  simp [hnotle] at he; exact hw he.symm

private theorem eval_lower_true {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n0 iw w : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)))
    (hw : w ≠ 0) :
    iw < n0 := by
  simp [evalHOLExact, hn, hi, Compiler.Encoders.Asm.wordCmpHOL] at he
  by_contra hge; simp [hge] at he; exact hw he.symm

private theorem while_copyInv {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnbc : noBreakOrCont body = true)
    (hbody : ∀ (s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      CopyInv s0 dst0 n0 s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      CopyInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hinv : CopyInv s0 dst0 n0 s)
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, post)) :
    CopyInv s0 dst0 n0 post ∧
    @evalHOLExact 64 F _ post.toExact (fun a => Classical.propDecidable (post.memaddrs a)) cond =
      some (.val (.word 0)) := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun
        · simp at hrun
        · omega
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0
        simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
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
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have nbc := evaluate_noBreakOrCont body hnbc (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at hrun rem nbc
          cases r1 with
          | none =>
            have hmid : CopyInv s0 dst0 n0 mid := by
              have hb := hbody s cw hinv hcond hnz (by rw [hbr])
              rw [hbr] at hb; exact hb
            exact ih mid (by change mid.clock ≤ s.clock - 1 at rem; omega) hmid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl nbc.2
            | «break» => exact absurd rfl nbc.1
            | _ => simp at hrun
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0
        simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun

private theorem assign_i_copyInv {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 n0 iw k : BitVec 64}
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (heff : ByteEff s0 s [(dst0.toNat, n0.toNat)])
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hle : (iw + k).toNat ≤ n0.toNat)
    (hdlo : sourceBase ≤ dst0.toNat) (hdhi : dst0.toNat + (iw + k).toNat ≤ heapEnd) :
    CopyInv s0 dst0 n0
      (evaluateHOLFiniteState s (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k]))).2 := by
  have hrun : evaluateHOLFiniteState s
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k])) =
      (none, setVarHOLFinite (ofString "i") (.val (.word (iw + k))) s) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi, wordOpHOL, wordOp,
      valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL]
  rw [hrun]; dsimp only
  refine ⟨hc, guestInv_setVar _ _ s hG, heff.locals_clock _ s.clock, ?_, ?_, iw + k, ?_, hle, fun _ => ⟨hdlo, hdhi⟩⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd, show ofString "i" ≠ ofString "dst" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "i" ≠ ofString "n" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem seq_store_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (st b : ProgHOL 64)
    (hloc : (evaluateHOLFiniteState s st).2.locals = s.locals)
    (h : (evaluateHOLFiniteState s (.seq st b)).1 = none) :
    (evaluateHOLFiniteState s st).1 = none ∧
    (evaluateHOLFiniteState (evaluateHOLFiniteState s st).2 b).1 = none ∧
    (evaluateHOLFiniteState s (.seq st b)).2 =
      (evaluateHOLFiniteState (evaluateHOLFiniteState s st).2 b).2 ∧
    (evaluateHOLFiniteState s st).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_seq_line780] at h ⊢
  rcases hr : evaluateHOLFiniteState s st with ⟨r, m⟩
  rw [hr] at h hloc
  cases r with
  | none => exact ⟨rfl, h, rfl, hloc⟩
  | some _ => simp at h

theorem store_one_domain {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64)
    (hval_one : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w))
    (hnone : (evaluateHOLFiniteState s (.store dstExp valExp)).1 = none) :
    ∃ x : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word x)) ∧
      sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd ∧ x.toNat % 8 = 0 := by
  rw [evaluateHOLFiniteState_store] at hnone
  split at hnone
  · rename_i x hx
    split at hnone
    · rename_i val hval
      obtain ⟨w, rfl⟩ := hval_one val hval
      split at hnone
      · rename_i mem' hmem
        simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
        by_cases hdom : s.memaddrs x
        · have hdom_ord : x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
            rw [hG.memaddrs, ordinaryDomain_iff] at hdom; exact hdom
          have hhe8 : heapEnd % 8 = 0 := by decide
          exact ⟨x, hx, hdom_ord.2.1, by omega, hdom_ord.1⟩
        · simp [hdom] at hmem
      · simp at hnone
    · simp at hnone
  · simp at hnone

theorem storeByte_domain {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64)
    (hnone : (evaluateHOLFiniteState s (.storeByte dstExp valExp)).1 = none) :
    ∃ x : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word x)) ∧
      sourceBase ≤ x.toNat ∧ x.toNat + 1 ≤ heapEnd := by
  rw [evaluateHOLFiniteState_storeByte] at hnone
  split at hnone
  · rename_i x hx
    split at hnone
    · split at hnone
      · rename_i mem' hmem
        have hdom : s.memaddrs (panByteAlignHOL x) := by
          by_contra hc
          unfold panMemStoreByteWord8HOL at hmem
          cases s.memory (panByteAlignHOL x) with
          | word _ => simp [hc] at hmem
        have hdom_ord : (panByteAlignHOL x).toNat % 8 = 0 ∧
            sourceBase ≤ (panByteAlignHOL x).toNat ∧ (panByteAlignHOL x).toNat < heapEnd := by
          rw [hG.memaddrs, ordinaryDomain_iff] at hdom; exact hdom
        have hhe8 : heapEnd % 8 = 0 := by decide
        have hal_nat := panByteAlign_toNat64 x
        exact ⟨x, hx, by omega, by omega⟩
      · simp at hnone
    · simp at hnone
  · simp at hnone

theorem byteEff_store_at {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64) (base : BitVec 64) (off len : Nat)
    (hbound : base.toNat + len ≤ heapEnd)
    (hin_Rl : 0 < len → ∃ i ∈ Rl, i.1 ≤ base.toNat ∧ base.toNat + len ≤ i.1 + i.2)
    (hval : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w))
    (hoff : off + 8 ≤ len)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off)))) :
    ByteEff s (evaluateHOLFiniteState s (.store dstExp valExp)).2 Rl := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  refine (byteEff_store_one hG dstExp valExp hval (fun x hx _ => ?_)).1
  rw [hdst] at hx; injection hx with hx'; injection hx' with hx''; injection hx'' with hx'''; subst hx'''
  obtain ⟨ivl, hivl, h1, h2⟩ := hin_Rl (by omega)
  have hadd : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact ⟨ivl, hivl, by omega, by omega⟩

theorem byteEff_storeByte_at {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64) (base : BitVec 64) (off len : Nat)
    (hbound : base.toNat + len ≤ heapEnd)
    (hin_Rl : 0 < len → ∃ i ∈ Rl, i.1 ≤ base.toNat ∧ base.toNat + len ≤ i.1 + i.2)
    (hoff : off < len)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off)))) :
    ByteEff s (evaluateHOLFiniteState s (.storeByte dstExp valExp)).2 Rl := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  refine (byteEff_storeByte hG dstExp valExp (fun x hx _ => ?_)).1
  rw [hdst] at hx; injection hx with hx'; injection hx' with hx''; injection hx'' with hx'''; subst hx'''
  obtain ⟨ivl, hivl, h1, h2⟩ := hin_Rl (by omega)
  have hadd : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact ⟨ivl, hivl, by omega, by omega⟩

private theorem step_copy_loop32 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (v0 v8 v16 v24 : ExpHOL 64)
    (hv0 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v0 = some v → ∃ w, v = .val (.word w))
    (hv8 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v8 = some v → ∃ w, v = .val (.word w))
    (hv16 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v16 = some v → ∃ w, v = .val (.word w))
    (hv24 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v24 = some v → ∃ w, v = .val (.word w))
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : CopyInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 32])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8]) v8)
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16]) v16)
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24]) v24)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32]))))))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      CopyInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  obtain ⟨hc, hG, heff, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have heffd : ByteEff s0 sd [(dst0.toNat, n0.toNat)] := heff.locals_clock s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 32 w hn hi hcond hw
  obtain ⟨hs0, hr1, heq1, hl1⟩ := seq_store_none sd _ _ (evaluate_store_control_frame sd _ _).2.1 hnone
  let s1 := (evaluateHOLFiniteState sd (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)).2
  have hG1 : GuestInv s1 := guestInv_evaluate sd _ hGd
  obtain ⟨hs8, hr2, heq2, hl2⟩ := seq_store_none s1 _ _ (evaluate_store_control_frame s1 _ _).2.1 hr1
  let s2 := (evaluateHOLFiniteState s1 (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8]) v8)).2
  have hG2 : GuestInv s2 := guestInv_evaluate s1 _ hG1
  obtain ⟨hs16, hr3, heq3, hl3⟩ := seq_store_none s2 _ _ (evaluate_store_control_frame s2 _ _).2.1 hr2
  let s3 := (evaluateHOLFiniteState s2 (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16]) v16)).2
  have hG3 : GuestInv s3 := guestInv_evaluate s2 _ hG2
  obtain ⟨hs24, _, heq4, hl4⟩ := seq_store_none s3 _ _ (evaluate_store_control_frame s3 _ _).2.1 hr3
  let s4 := (evaluateHOLFiniteState s3 (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24]) v24)).2
  have hG4 : GuestInv s4 := guestInv_evaluate s3 _ hG3
  have hd_s1 : s1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl1]; exact hdst
  have hi_s1 : s1.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl1]; exact hi
  have hd_s2 : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl2]; exact hd_s1
  have hi_s2 : s2.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl2]; exact hi_s1
  have hd_s3 : s3.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl3]; exact hd_s2
  have hi_s3 : s3.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl3]; exact hi_s2
  have hd_s4 : s4.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl4]; exact hd_s3
  have hi_s4 : s4.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl4]; exact hi_s3
  have hn_s4 : s4.locals.lookup (ofString "n") = some (.val (.word n0)) := by rw [hl4, hl3, hl2, hl1]; exact hn
  obtain ⟨x0, hx0, hd0_lo, hd0_hi, _⟩ := store_one_domain hGd _ v0 (hv0 sd) hs0
  obtain ⟨x8, hx8, _, hd8_hi, _⟩ := store_one_domain hG1 _ v8 (hv8 s1) hs8
  obtain ⟨x16, hx16, _, hd16_hi, _⟩ := store_one_domain hG2 _ v16 (hv16 s2) hs16
  obtain ⟨x24, hx24, _, hd24_hi, _⟩ := store_one_domain hG3 _ v24 (hv24 s3) hs24
  have ex0 := eval_add2_locals sd _ _ dst0 iw hdst hi
  have ex8 := eval_add3_locals s1 _ _ dst0 iw 8 hd_s1 hi_s1
  have ex16 := eval_add3_locals s2 _ _ dst0 iw 16 hd_s2 hi_s2
  have ex24 := eval_add3_locals s3 _ _ dst0 iw 24 hd_s3 hi_s3
  rw [ex0] at hx0; injection hx0 with hx0; injection hx0 with hx0; injection hx0 with hx0; subst hx0
  rw [ex8] at hx8; injection hx8 with hx8; injection hx8 with hx8; injection hx8 with hx8; subst hx8
  rw [ex16] at hx16; injection hx16 with hx16; injection hx16 with hx16; injection hx16 with hx16; subst hx16
  rw [ex24] at hx24; injection hx24 with hx24; injection hx24 with hx24; injection hx24 with hx24; subst hx24
  have a8 : (dst0 + iw + 8).toNat = (dst0 + iw).toNat + 8 :=
    BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 8 < 2 ^ 64; omega)
  have a16 : (dst0 + iw + 16).toNat = (dst0 + iw).toNat + 16 := by
    rw [a8] at hd8_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 16 < 2 ^ 64; omega)
  have a24 : (dst0 + iw + 24).toNat = (dst0 + iw).toNat + 24 := by
    rw [a16] at hd16_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 24 < 2 ^ 64; omega)
  have hcur32 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (32 : BitVec 64).toNat ≤ heapEnd := by
    rw [a24] at hd24_hi; exact ⟨hd0_lo, by change (dst0 + iw).toNat + 32 ≤ heapEnd; omega⟩
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 32 hle hdom hcur32 (by decide) (by decide) hnl
  have hk32_val : (32 : BitVec 64).toNat = 32 := rfl
  have hin32 : 0 < 32 → ∃ i ∈ [(dst0.toNat, n0.toNat)],
      i.1 ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + 32 ≤ i.1 + i.2 :=
    fun _ => ⟨(dst0.toNat, n0.toNat), List.mem_singleton.2 rfl, by omega, by omega⟩
  have eff1 := byteEff_store_at hGd _ v0 (dst0 + iw) 0 32 (by omega) hin32 (hv0 sd) (by omega)
    (by simpa [BitVec.add_zero] using ex0)
  have eff2 := byteEff_store_at hG1 _ v8 (dst0 + iw) 8 32 (by omega) hin32 (hv8 s1) (by omega) ex8
  have eff3 := byteEff_store_at hG2 _ v16 (dst0 + iw) 16 32 (by omega) hin32 (hv16 s2) (by omega) ex16
  have eff4 := byteEff_store_at hG3 _ v24 (dst0 + iw) 24 32 (by omega) hin32 (hv24 s3) (by omega) ex24
  have hmeta4 : s4.code = originalRuntimeCode := hG4.code
  change CopyInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4]
  exact assign_i_copyInv hmeta4 hG4 (heffd.trans (eff1.trans (eff2.trans (eff3.trans eff4))))
    hd_s4 hn_s4 hi_s4 hle_ik hdlo hdhi

private theorem step_copy_loop8w {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (v0 : ExpHOL 64)
    (hv0 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v0 = some v → ∃ w, v = .val (.word w))
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : CopyInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      CopyInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, heff, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have heffd : ByteEff s0 sd [(dst0.toNat, n0.toNat)] := heff.locals_clock s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  obtain ⟨hs0, _, heq1, hl1⟩ := seq_store_none sd _ _ (evaluate_store_control_frame sd _ _).2.1 hnone
  let s1 := (evaluateHOLFiniteState sd (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)).2
  have hG1 : GuestInv s1 := guestInv_evaluate sd _ hGd
  obtain ⟨x0, hx0, hd0_lo, hd0_hi, _⟩ := store_one_domain hGd _ v0 (hv0 sd) hs0
  have ex0 := eval_add2_locals sd _ _ dst0 iw hdst hi
  rw [ex0] at hx0; injection hx0 with hx0; injection hx0 with hx0; injection hx0 with hx0; subst hx0
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom ⟨hd0_lo, hd0_hi⟩ (by decide) (by decide) hnl
  have hk8_val : (8 : BitVec 64).toNat = 8 := rfl
  have eff1 := byteEff_store_at hGd _ v0 (dst0 + iw) 0 8 hd0_hi
    (fun _ => ⟨(dst0.toNat, n0.toNat), List.mem_singleton.2 rfl, by omega, by omega⟩)
    (hv0 sd) (by omega) (by simpa [BitVec.add_zero] using ex0)
  change CopyInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_copyInv hG1.code hG1 (heffd.trans eff1)
    (by rw [hl1]; exact hdst) (by rw [hl1]; exact hn) (by rw [hl1]; exact hi) hle_ik hdlo hdhi

private theorem step_copy_loop8b {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (b0 b1 b2 b3 b4 b5 b6 b7 : ExpHOL 64)
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : CopyInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body :=
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1]) b1)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2]) b2)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3]) b3)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4]) b4)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5]) b5)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6]) b6)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7]) b7)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))))))))))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      CopyInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  obtain ⟨hc, hG, heff, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have heffd : ByteEff s0 sd [(dst0.toNat, n0.toNat)] := heff.locals_clock s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  obtain ⟨hs0, hr1, heq1, hl1⟩ := seq_store_none sd _ _ (evaluate_storeByte_control_frame sd _ _).2.2.1 hnone
  let s1 := (evaluateHOLFiniteState sd (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)).2
  have hG1 : GuestInv s1 := guestInv_evaluate sd _ hGd
  obtain ⟨hs1, hr2, heq2, hl2⟩ := seq_store_none s1 _ _ (evaluate_storeByte_control_frame s1 _ _).2.2.1 hr1
  let s2 := (evaluateHOLFiniteState s1 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1]) b1)).2
  have hG2 : GuestInv s2 := guestInv_evaluate s1 _ hG1
  obtain ⟨hs2, hr3, heq3, hl3⟩ := seq_store_none s2 _ _ (evaluate_storeByte_control_frame s2 _ _).2.2.1 hr2
  let s3 := (evaluateHOLFiniteState s2 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2]) b2)).2
  have hG3 : GuestInv s3 := guestInv_evaluate s2 _ hG2
  obtain ⟨hs3, hr4, heq4, hl4⟩ := seq_store_none s3 _ _ (evaluate_storeByte_control_frame s3 _ _).2.2.1 hr3
  let s4 := (evaluateHOLFiniteState s3 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3]) b3)).2
  have hG4 : GuestInv s4 := guestInv_evaluate s3 _ hG3
  obtain ⟨hs4, hr5, heq5, hl5⟩ := seq_store_none s4 _ _ (evaluate_storeByte_control_frame s4 _ _).2.2.1 hr4
  let s5 := (evaluateHOLFiniteState s4 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4]) b4)).2
  have hG5 : GuestInv s5 := guestInv_evaluate s4 _ hG4
  obtain ⟨hs5, hr6, heq6, hl6⟩ := seq_store_none s5 _ _ (evaluate_storeByte_control_frame s5 _ _).2.2.1 hr5
  let s6 := (evaluateHOLFiniteState s5 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5]) b5)).2
  have hG6 : GuestInv s6 := guestInv_evaluate s5 _ hG5
  obtain ⟨hs6, hr7, heq7, hl7⟩ := seq_store_none s6 _ _ (evaluate_storeByte_control_frame s6 _ _).2.2.1 hr6
  let s7 := (evaluateHOLFiniteState s6 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6]) b6)).2
  have hG7 : GuestInv s7 := guestInv_evaluate s6 _ hG6
  obtain ⟨hs7, _, heq8, hl8⟩ := seq_store_none s7 _ _ (evaluate_storeByte_control_frame s7 _ _).2.2.1 hr7
  let s8 := (evaluateHOLFiniteState s7 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7]) b7)).2
  have hG8 : GuestInv s8 := guestInv_evaluate s7 _ hG7
  have hd1 : s1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl1]; exact hdst
  have hi1 : s1.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl1]; exact hi
  have hd2 : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl2]; exact hd1
  have hi2 : s2.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl2]; exact hi1
  have hd3 : s3.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl3]; exact hd2
  have hi3 : s3.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl3]; exact hi2
  have hd4 : s4.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl4]; exact hd3
  have hi4 : s4.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl4]; exact hi3
  have hd5 : s5.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl5]; exact hd4
  have hi5 : s5.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl5]; exact hi4
  have hd6 : s6.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl6]; exact hd5
  have hi6 : s6.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl6]; exact hi5
  have hd7 : s7.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl7]; exact hd6
  have hi7 : s7.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl7]; exact hi6
  have hd8 : s8.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl8]; exact hd7
  have hi8 : s8.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl8]; exact hi7
  have hn8 : s8.locals.lookup (ofString "n") = some (.val (.word n0)) := by
    rw [hl8, hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hn
  have ex0 := eval_add2_locals sd _ _ dst0 iw hdst hi
  have ex1 := eval_add3_locals s1 _ _ dst0 iw 1 hd1 hi1
  have ex2 := eval_add3_locals s2 _ _ dst0 iw 2 hd2 hi2
  have ex3 := eval_add3_locals s3 _ _ dst0 iw 3 hd3 hi3
  have ex4 := eval_add3_locals s4 _ _ dst0 iw 4 hd4 hi4
  have ex5 := eval_add3_locals s5 _ _ dst0 iw 5 hd5 hi5
  have ex6 := eval_add3_locals s6 _ _ dst0 iw 6 hd6 hi6
  have ex7 := eval_add3_locals s7 _ _ dst0 iw 7 hd7 hi7
  obtain ⟨x0, hx0, hd0_lo, hd0_hi⟩ := storeByte_domain hGd _ b0 hs0
  obtain ⟨x1, hx1, _, hd1_hi⟩ := storeByte_domain hG1 _ b1 hs1
  obtain ⟨x2, hx2, _, hd2_hi⟩ := storeByte_domain hG2 _ b2 hs2
  obtain ⟨x3, hx3, _, hd3_hi⟩ := storeByte_domain hG3 _ b3 hs3
  obtain ⟨x4, hx4, _, hd4_hi⟩ := storeByte_domain hG4 _ b4 hs4
  obtain ⟨x5, hx5, _, hd5_hi⟩ := storeByte_domain hG5 _ b5 hs5
  obtain ⟨x6, hx6, _, hd6_hi⟩ := storeByte_domain hG6 _ b6 hs6
  obtain ⟨x7, hx7, _, hd7_hi⟩ := storeByte_domain hG7 _ b7 hs7
  rw [ex0] at hx0; injection hx0 with hx0; injection hx0 with hx0; injection hx0 with hx0; subst hx0
  rw [ex1] at hx1; injection hx1 with hx1; injection hx1 with hx1; injection hx1 with hx1; subst hx1
  rw [ex2] at hx2; injection hx2 with hx2; injection hx2 with hx2; injection hx2 with hx2; subst hx2
  rw [ex3] at hx3; injection hx3 with hx3; injection hx3 with hx3; injection hx3 with hx3; subst hx3
  rw [ex4] at hx4; injection hx4 with hx4; injection hx4 with hx4; injection hx4 with hx4; subst hx4
  rw [ex5] at hx5; injection hx5 with hx5; injection hx5 with hx5; injection hx5 with hx5; subst hx5
  rw [ex6] at hx6; injection hx6 with hx6; injection hx6 with hx6; injection hx6 with hx6; subst hx6
  rw [ex7] at hx7; injection hx7 with hx7; injection hx7 with hx7; injection hx7 with hx7; subst hx7
  have a1 : (dst0 + iw + 1).toNat = (dst0 + iw).toNat + 1 :=
    BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 1 < 2 ^ 64; omega)
  have a2 : (dst0 + iw + 2).toNat = (dst0 + iw).toNat + 2 := by
    rw [a1] at hd1_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 2 < 2 ^ 64; omega)
  have a3 : (dst0 + iw + 3).toNat = (dst0 + iw).toNat + 3 := by
    rw [a2] at hd2_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 3 < 2 ^ 64; omega)
  have a4 : (dst0 + iw + 4).toNat = (dst0 + iw).toNat + 4 := by
    rw [a3] at hd3_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 4 < 2 ^ 64; omega)
  have a5 : (dst0 + iw + 5).toNat = (dst0 + iw).toNat + 5 := by
    rw [a4] at hd4_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 5 < 2 ^ 64; omega)
  have a6 : (dst0 + iw + 6).toNat = (dst0 + iw).toNat + 6 := by
    rw [a5] at hd5_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 6 < 2 ^ 64; omega)
  have a7 : (dst0 + iw + 7).toNat = (dst0 + iw).toNat + 7 := by
    rw [a6] at hd6_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 7 < 2 ^ 64; omega)
  have hcur8 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (8 : BitVec 64).toNat ≤ heapEnd := by
    rw [a7] at hd7_hi; exact ⟨hd0_lo, by change (dst0 + iw).toNat + 8 ≤ heapEnd; omega⟩
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom hcur8 (by decide) (by decide) hnl
  have hk8_val : (8 : BitVec 64).toNat = 8 := rfl
  have hin8 : 0 < 8 → ∃ i ∈ [(dst0.toNat, n0.toNat)],
      i.1 ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + 8 ≤ i.1 + i.2 :=
    fun _ => ⟨(dst0.toNat, n0.toNat), List.mem_singleton.2 rfl, by omega, by omega⟩
  have eff0 := byteEff_storeByte_at hGd _ b0 (dst0 + iw) 0 8 (by omega) hin8 (by omega)
    (by simpa [BitVec.add_zero] using ex0)
  have eff1 := byteEff_storeByte_at hG1 _ b1 (dst0 + iw) 1 8 (by omega) hin8 (by omega) ex1
  have eff2 := byteEff_storeByte_at hG2 _ b2 (dst0 + iw) 2 8 (by omega) hin8 (by omega) ex2
  have eff3 := byteEff_storeByte_at hG3 _ b3 (dst0 + iw) 3 8 (by omega) hin8 (by omega) ex3
  have eff4 := byteEff_storeByte_at hG4 _ b4 (dst0 + iw) 4 8 (by omega) hin8 (by omega) ex4
  have eff5 := byteEff_storeByte_at hG5 _ b5 (dst0 + iw) 5 8 (by omega) hin8 (by omega) ex5
  have eff6 := byteEff_storeByte_at hG6 _ b6 (dst0 + iw) 6 8 (by omega) hin8 (by omega) ex6
  have eff7 := byteEff_storeByte_at hG7 _ b7 (dst0 + iw) 7 8 (by omega) hin8 (by omega) ex7
  change CopyInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8]
  exact assign_i_copyInv hG8.code hG8
    (heffd.trans (eff0.trans (eff1.trans (eff2.trans (eff3.trans (eff4.trans (eff5.trans (eff6.trans eff7))))))))
    hd8 hn8 hi8 hle_ik hdlo hdhi

private theorem step_copy_loop1b {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (b0 : ExpHOL 64)
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : CopyInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body :=
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      CopyInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, heff, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have heffd : ByteEff s0 sd [(dst0.toNat, n0.toNat)] := heff.locals_clock s.locals (s.clock - 1)
  have hlt := eval_lower_true s n0 iw w hn hi hcond hw
  rw [BitVec.lt_def] at hlt
  have hnl : ¬ (n0 < iw + 1) := by
    rw [BitVec.lt_def]
    have := n0.isLt
    have : (iw + 1).toNat = iw.toNat + 1 := BitVec.toNat_add_of_lt (by change iw.toNat + 1 < 2 ^ 64; omega)
    omega
  obtain ⟨hs0, _, heq1, hl1⟩ := seq_store_none sd _ _ (evaluate_storeByte_control_frame sd _ _).2.2.1 hnone
  let s1 := (evaluateHOLFiniteState sd (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)).2
  have hG1 : GuestInv s1 := guestInv_evaluate sd _ hGd
  have ex0 := eval_add2_locals sd _ _ dst0 iw hdst hi
  obtain ⟨x0, hx0, hd0_lo, hd0_hi⟩ := storeByte_domain hGd _ b0 hs0
  rw [ex0] at hx0; injection hx0 with hx0; injection hx0 with hx0; injection hx0 with hx0; subst hx0
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 1 hle hdom ⟨hd0_lo, hd0_hi⟩ (by decide) (by decide) hnl
  have hk1_val : (1 : BitVec 64).toNat = 1 := rfl
  have eff0 := byteEff_storeByte_at hGd _ b0 (dst0 + iw) 0 1 hd0_hi
    (fun _ => ⟨(dst0.toNat, n0.toNat), List.mem_singleton.2 rfl, by omega, by omega⟩)
    (by omega) (by simpa [BitVec.add_zero] using ex0)
  change CopyInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_copyInv hG1.code hG1 (heffd.trans eff0)
    (by rw [hl1]; exact hdst) (by rw [hl1]; exact hn) (by rw [hl1]; exact hi) hle_ik hdlo hdhi

private theorem copy_body_eff {F : Type}
    (alignCond v0 v8 v16 v24 b0 b1 b2 b3 b4 b5 b6 b7 : ExpHOL 64)
    (hv0 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v0 = some v → ∃ w, v = .val (.word w))
    (hv8 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v8 = some v → ∃ w, v = .val (.word w))
    (hv16 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v16 = some v → ∃ w, v = .val (.word w))
    (hv24 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v24 = some v → ∃ w, v = .val (.word w))
    (s0 : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64)
    (hc : s0.code = originalRuntimeCode) (hG : GuestInv s0)
    (hdst : s0.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s0.locals.lookup (ofString "n") = some (.val (.word n0))) :
    let w32 := ProgHOL.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32]))
      (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8]) v8)
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16]) v16)
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24]) v24)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32]))))))
    let w8w := ProgHOL.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8]))
      (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
    let w8b := ProgHOL.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8]))
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1]) b1)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2]) b2)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3]) b3)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4]) b4)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5]) b5)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6]) b6)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7]) b7)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))))))))))
    let w1b := ProgHOL.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
    let fullBody := ProgHOL.dec (ofString "i") .one (.const 0)
      (.seq (.ite alignCond (.seq w32 w8w) .skip) (.seq w8b (.seq w1b (.return (.const 0)))))
    Resumes (evaluateHOLFiniteState s0 fullBody).1 →
      ByteEff s0 (evaluateHOLFiniteState s0 fullBody).2 [(dst0.toNat, n0.toNat)] ∧
      (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) := by
  intro w32 w8w w8b w1b fullBody hres
  have hdec : evaluateHOLFiniteState s0 fullBody =
      let si := setVarHOLFinite (ofString "i") (.val (.word 0)) s0
      let r := evaluateHOLFiniteState si (.seq (.ite alignCond (.seq w32 w8w) .skip) (.seq w8b (.seq w1b (.return (.const 0)))))
      (r.1, { r.2 with locals := HolFiniteMapExact.resVarEq r.2.locals (ofString "i", s0.locals.lookup (ofString "i")) }) := by
    rw [evaluateHOLFiniteState_dec_total]
    simp [evalHOLExact, shapeEqHOL, shapeOfHOLExact]
  rw [hdec] at hres ⊢
  dsimp only at hres ⊢
  let si := setVarHOLFinite (ofString "i") (.val (.word 0)) s0
  have hinv_si : CopyInv s0 dst0 n0 si := by
    refine ⟨hc, guestInv_setVar _ _ s0 hG, (ByteEff.refl s0 _).locals_clock _ s0.clock, ?_, ?_, 0, ?_, by simp, fun h => by simp at h⟩
    · simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hdst, show ofString "i" ≠ ofString "dst" by decide]
    · simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "i" ≠ ofString "n" by decide]
    · simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
  rcases h1 : evaluateHOLFiniteState si (.ite alignCond (.seq w32 w8w) .skip) with ⟨r1, m1⟩
  rw [h1] at hres
  cases r1 with
  | some _ =>
    exfalso; exact evaluate_noReturnOrRaise (.ite alignCond (.seq w32 w8w) .skip) rfl si (by rw [h1]; exact hres)
  | none =>
    have hinv_m1 : CopyInv s0 dst0 n0 m1 := by
      rw [evaluateHOLFiniteState_ite] at h1
      split at h1
      · split at h1
        · rw [evaluateHOLFiniteState_skip] at h1; injection h1 with _ hm1; subst hm1; exact hinv_si
        · rw [evaluateHOLFiniteState_seq_line780] at h1
          rcases hw32 : evaluateHOLFiniteState si w32 with ⟨rw32, mw32⟩
          rw [hw32] at h1
          cases rw32 with
          | some _ => simp at h1
          | none =>
            have hinv_32 := (while_copyInv _ _ rfl (step_copy_loop32 v0 v8 v16 v24 hv0 hv8 hv16 hv24)
              si.clock si mw32 le_rfl hinv_si hw32).1
            exact (while_copyInv _ _ rfl (step_copy_loop8w v0 hv0)
              mw32.clock mw32 m1 le_rfl hinv_32 h1).1
      · simp at h1
    dsimp only at hres ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
    rcases h2 : evaluateHOLFiniteState m1 w8b with ⟨r2, m2⟩
    rw [h2] at hres
    cases r2 with
    | some _ =>
      exfalso; exact evaluate_noReturnOrRaise w8b rfl m1 (by rw [h2]; exact hres)
    | none =>
      have hinv_m2 := (while_copyInv _ _ rfl (step_copy_loop8b b0 b1 b2 b3 b4 b5 b6 b7)
        m1.clock m1 m2 le_rfl hinv_m1 h2).1
      dsimp only at hres ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
      rcases h3 : evaluateHOLFiniteState m2 w1b with ⟨r3, m3⟩
      rw [h3] at hres
      cases r3 with
      | some _ =>
        exfalso; exact evaluate_noReturnOrRaise w1b rfl m2 (by rw [h3]; exact hres)
      | none =>
        obtain ⟨hinv_m3, hfalse3⟩ := while_copyInv _ _ rfl (step_copy_loop1b b0)
          m2.clock m2 m3 le_rfl hinv_m2 h3
        dsimp only at hres ⊢
        obtain ⟨_, _, heff3, _, hn3, iw3, hi3, hle3, hdom3⟩ := hinv_m3
        have heq_in : iw3.toNat = n0.toNat := by
          simp only [evalHOLExact, hi3, hn3, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def] at hfalse3
          by_cases hlt3 : iw3.toNat < n0.toNat
          · simp [hlt3] at hfalse3
          · omega
        have hret_eff : ByteEff s0 (evaluateHOLFiniteState m3 (.return (.const 0))).2 [(dst0.toNat, n0.toNat)] := by
          rw [evaluateHOLFiniteState_return]
          dsimp only [evalHOLExact, shapeOfHOLExact]
          split
          · exact heff3.locals_clock _ m3.clock
          · exact heff3
        exact ⟨hret_eff.locals_clock _ _, fun hpos => by rw [← heq_in] at hpos ⊢; exact hdom3 hpos⟩

theorem memzero_body_eff {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64)
    (hc : s0.code = originalRuntimeCode) (hG : GuestInv s0)
    (hdst : s0.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s0.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hres : Resumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memzero)).1) :
    ByteEff s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memzero)).2
      [(dst0.toNat, n0.toNat)] ∧
    (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) := by
  have hc0 : ∀ (t : PanSemStateFiniteExact 64 F) v,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (.const 0) = some v →
      ∃ w : BitVec 64, v = .val (.word w) := fun _ _ h => by injection h with h'; exact ⟨0, h'.symm⟩
  exact copy_body_eff _ _ _ _ _ _ _ _ _ _ _ _ _ hc0 hc0 hc0 hc0 s0 dst0 n0 hc hG hdst hn hres

theorem memcpy_body_eff {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64)
    (hc : s0.code = originalRuntimeCode) (hG : GuestInv s0)
    (hdst : s0.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s0.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hres : Resumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memcpy)).1) :
    ByteEff s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memcpy)).2
      [(dst0.toNat, n0.toNat)] ∧
    (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) := by
  exact copy_body_eff _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun t => eval_load_one_word t _) (fun t => eval_load_one_word t _)
    (fun t => eval_load_one_word t _) (fun t => eval_load_one_word t _)
    s0 dst0 n0 hc hG hdst hn hres

/-! ## 4. Composable `ByteEff` statement combinators & helper callees -/

theorem byteEff_seq {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {Rl : List Ivl}
    (ha : ByteEff s (evaluateHOLFiniteState s a).2 Rl)
    (hb : ∀ m, evaluateHOLFiniteState s a = (none, m) → ByteEff m (evaluateHOLFiniteState m b).2 Rl) :
    ByteEff s (evaluateHOLFiniteState s (.seq a b)).2 Rl := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s a with ⟨r1, m⟩
  rw [hr] at ha
  cases r1 with
  | none => exact ha.trans (hb m hr)
  | some _ => exact ha

theorem byteEff_ite {F : Type} {s : PanSemStateFiniteExact 64 F} (cond : ExpHOL 64)
    {yes no : ProgHOL 64} {Rl : List Ivl}
    (hy : ByteEff s (evaluateHOLFiniteState s yes).2 Rl)
    (hn : ByteEff s (evaluateHOLFiniteState s no).2 Rl) :
    ByteEff s (evaluateHOLFiniteState s (.ite cond yes no)).2 Rl := by
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn
    · exact hy
  · exact ByteEff.refl s Rl

theorem byteEff_dec {F : Type} {s : PanSemStateFiniteExact 64 F}
    (name : MlS) (sh : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {Rl : List Ivl}
    (hb : ∀ val,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init = some val →
      ByteEff (setVarHOLFinite name val s) (evaluateHOLFiniteState (setVarHOLFinite name val s) body).2 Rl) :
    ByteEff s (evaluateHOLFiniteState s (.dec name sh init body)).2 Rl := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact ByteEff.refl s Rl
  · rename_i val hval
    split
    · exact ((ByteEff.refl s Rl).locals_clock _ s.clock).trans (hb val hval) |>.locals_clock _ _
    · exact ByteEff.refl s Rl

theorem byteEff_assign_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (e : ExpHOL 64) (Rl : List Ivl) :
    ByteEff s (evaluateHOLFiniteState s (.assign .local name e)).2 Rl := by
  rw [evaluateHOLFiniteState_assign]
  split
  · exact ByteEff.refl s Rl
  · split
    · exact (ByteEff.refl s Rl).locals_clock _ s.clock
    · exact ByteEff.refl s Rl

theorem byteEff_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (Rl : List Ivl) :
    ByteEff s (evaluateHOLFiniteState s (.return e)).2 Rl := by
  rw [evaluateHOLFiniteState_return]
  split
  · exact ByteEff.refl s Rl
  · split
    · exact (ByteEff.refl s Rl).locals_clock _ s.clock
    · exact ByteEff.refl s Rl

theorem byteEff_skip {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    ByteEff s (evaluateHOLFiniteState s .skip).2 Rl := by
  rw [evaluateHOLFiniteState_skip]; exact ByteEff.refl s Rl

theorem byteEff_while {F : Type} (cond : ExpHOL 64) {body : ProgHOL 64} {Rl : List Ivl}
    (hb : ∀ (t : PanSemStateFiniteExact 64 F), t.code = originalRuntimeCode → GuestInv t →
      ByteEff t (evaluateHOLFiniteState t body).2 Rl)
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (hG : GuestInv s) :
    ByteEff s (evaluateHOLFiniteState s (.while cond body)).2 Rl := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · split
    · split
      · exact (ByteEff.refl s Rl).locals_clock _ s.clock
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have hGd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hG
        have ih1 := hb (decClockHOLFinite s) hc hGd
        have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
        rw [hbr] at ih1 rem
        have hlt : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
        have heff1 : ByteEff s mid Rl := ((ByteEff.refl s Rl).locals_clock _ _).trans ih1
        have hGm : GuestInv mid := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hG
        cases r1 with
        | none => exact heff1.trans (byteEff_while cond hb mid (heff1.code.trans hc) hGm)
        | some res =>
          cases res with
          | «continue» => exact heff1.trans (byteEff_while cond hb mid (heff1.code.trans hc) hGm)
          | _ => exact heff1
    · exact ByteEff.refl s Rl
  · exact ByteEff.refl s Rl
termination_by s.clock

/-- Call wrapper for a `ByteEff` callee that only takes effect when `Resumes` holds
(or unconditionally on any non-timeout outcome). -/
def FunByteEff (fname : MlS)
    (argR : List (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → List Ivl) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (entry : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64)),
      entry.code = originalRuntimeCode → GuestInv entry →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, entry.locals, retShape) →
      (evaluateHOLFiniteState entry body).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState entry body).1 →
      ByteEff entry (evaluateHOLFiniteState entry body).2 (argR vals entry.globals)

theorem call0_byteEff {F : Type} {fname : MlS}
    {argR : List (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → List Ivl}
    (hf : FunByteEff fname argR)
    (s : PanSemStateFiniteExact 64 F) (args : List (ExpHOL 64)) (Rl : List Ivl)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hsub : ∀ vals,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals →
      ∀ i ∈ argR vals s.globals, 0 < i.2 → ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1) :
    ByteEff s (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2 Rl := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_call] at hnt hor ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact ByteEff.refl s Rl
  · simp only [hargs] at hnt hor ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact ByteEff.refl s Rl
    · simp only [hl] at hnt hor ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hsame
      have hret := lookupCodeHOLFinite_installed_return s fname params body' body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hret
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hor ⊢
        let entry := callEntryStateHOLFinite s callee
        have hGe : GuestInv entry := guestInv_callEntry s callee hG
        have hl_e : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body', entry.locals, ret') := by
          simpa [hc, entry, callEntryStateHOLFinite] using hl
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hor ⊢
        have hntb : res ≠ some .timeOut := by intro h; subst h; simp at hnt
        have runSpec (hr : Resumes res) : ByteEff s post Rl := by
          have hb := hspec entry vals hc hGe hl_e (by dsimp only [entry]; rw [hrun]; exact hntb)
            (by dsimp only [entry]; rw [hrun]; exact hr)
          dsimp only [entry] at hb; rw [hrun] at hb
          exact (((ByteEff.refl s _).locals_clock _ _).trans hb).mono (hsub vals hargs)
        cases res with
        | none =>
          exfalso; rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hor ⊢
            split
            · exact (runSpec (Or.inl ⟨v, rfl⟩)).locals_clock _ _
            · rename_i hbad
              rw [if_neg hbad] at hor
              exfalso; rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          | exception eid ev =>
            have hnot_trap : eid ≠ ofString "TrapErr" := by
              rcases hor with h | ⟨_, h⟩ | ⟨e', v', h, hne⟩
              · simp at h
              · simp at h
              · simp at h; obtain ⟨rfl, _⟩ := h; exact hne
            exact (runSpec (Or.inr ⟨eid, ev, rfl, hnot_trap⟩)).locals_clock _ _
          | _ =>
            exfalso; rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

/-! ## 1. Lookup helpers & `FunByteEff` instances -/

def valWordNat : ValueHOL 64 → Nat
  | .val (.word w) => w.toNat
  | _ => 0

def globMapN (G : HolFiniteMapExact MlS (ValueHOL 64)) (name : String) : Nat :=
  match G.lookup (ofString name) with
  | some (.val (.word w)) => w.toNat
  | _ => 0

def globBufIvl (G : HolFiniteMapExact MlS (ValueHOL 64)) (name : String) (sz : Nat) : Ivl :=
  (globMapN G name, if globMapN G name = 0 then 0 else sz)

theorem globBufIvl_eq_bufferRegion {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) (sz : Nat) :
    globBufIvl s.globals name sz = bufferRegion s (name, sz) := rfl

theorem lookupCode_one_word {fname p1 : MlS} {body : ProgHOL 64} {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one)], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, .one)) :
    ∃ w1 : BitVec 64,
      vals = [.val (.word w1)] ∧
      L.lookup p1 = some (.val (.word w1)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L .one hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | _⟩
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    exact ⟨w1, rfl, by rw [← hx]; simp⟩
  · simp at hx

theorem lookupCode_two_words {fname p1 p2 : MlS} {body : ProgHOL 64} {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, .one)) :
    ∃ w1 w2 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L .one hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, rfl, ?_, ?_⟩ <;> (rw [← hL]; simp [hne, Ne.symm hne])
  · simp at hx

theorem lookupCode_three_words {fname p1 p2 p3 : MlS} {body : ProgHOL 64} {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one), (p3, .one)], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, .one)) :
    ∃ w1 w2 w3 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2), .val (.word w3)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) ∧
      L.lookup p3 = some (.val (.word w3)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L .one hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      rcases v3 with ⟨⟨w3⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, w3, rfl, ?_, ?_, ?_⟩ <;>
      (rw [← hL]; simp [h12, h13, h23, Ne.symm h12, Ne.symm h13, Ne.symm h23])
  · simp at hx

theorem lookupCode_four_words {fname p1 p2 p3 p4 : MlS} {body : ProgHOL 64} {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hlook : originalRuntimeCode.lookup fname =
      some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one)], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, .one)) :
    ∃ w1 w2 w3 w4 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) ∧
      L.lookup p3 = some (.val (.word w3)) ∧
      L.lookup p4 = some (.val (.word w4)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L .one hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | _⟩⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      rcases v3 with ⟨⟨w3⟩⟩ | _ | _ <;> rcases v4 with ⟨⟨w4⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, w3, w4, rfl, ?_, ?_, ?_, ?_⟩ <;>
      (rw [← hL]; simp [h12, h13, h14, h23, h24, h34,
        Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h23, Ne.symm h24, Ne.symm h24, Ne.symm h34])
  · simp at hx

theorem funByteEff_memzero :
    FunByteEff (ofString "memzero")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), valWordNat (vals[1]?.getD (.rStruct [])))]) := by
  refine ⟨_, _, _, lookup_memzero, fun entry vals hc hG hl _ hres => ?_⟩
  obtain ⟨dst0, n0, rfl, hdst, hn⟩ := lookupCode_two_words (by decide) lookup_memzero hl
  exact (memzero_body_eff entry dst0 n0 hc hG hdst hn hres).1

theorem funByteEff_memcpy :
    FunByteEff (ofString "memcpy")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), valWordNat (vals[2]?.getD (.rStruct [])))]) := by
  have hlook : originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
    lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_memcpy) rfl
  refine ⟨_, _, _, hlook, fun entry vals hc hG hl _ hres => ?_⟩
  obtain ⟨dst0, _, n0, rfl, hdst, _, hn⟩ := lookupCode_three_words (by decide) (by decide) (by decide) hlook hl
  exact (memcpy_body_eff entry dst0 n0 hc hG hdst hn hres).1

theorem four_byte_stores_eff {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (v0 v1 v2 v3 : ExpHOL 64)
    (hG : GuestInv s0)
    (hp : s0.locals.lookup (ofString "p") = some (.val (.word p)))
    (hres : Resumes (evaluateHOLFiniteState s0
      (.seq (.storeByte (.var .local (ofString "p")) v0)
        (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 1]) v1)
          (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 2]) v2)
            (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 3]) v3)
              (.return (.const 0))))))).1) :
    ByteEff s0 (evaluateHOLFiniteState s0
      (.seq (.storeByte (.var .local (ofString "p")) v0)
        (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 1]) v1)
          (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 2]) v2)
            (.seq (.storeByte (.op .add [.var .local (ofString "p"), .const 3]) v3)
              (.return (.const 0))))))).2 [(p.toNat, 4)] ∧
    sourceBase ≤ p.toNat ∧ p.toNat + 4 ≤ heapEnd := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have seq_res : ∀ (t : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64),
      (∀ x : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState x a).1 = none ∨ (evaluateHOLFiniteState x a).1 = some .error) →
      (evaluateHOLFiniteState t a).2.locals = t.locals →
      Resumes (evaluateHOLFiniteState t (.seq a b)).1 →
      (evaluateHOLFiniteState t a).1 = none ∧
      Resumes (evaluateHOLFiniteState (evaluateHOLFiniteState t a).2 b).1 ∧
      (evaluateHOLFiniteState t (.seq a b)).2 =
        (evaluateHOLFiniteState (evaluateHOLFiniteState t a).2 b).2 ∧
      (evaluateHOLFiniteState t a).2.locals = t.locals := by
    intro t a b ha hloc hr
    rw [evaluateHOLFiniteState_seq_line780] at hr ⊢
    rcases he : evaluateHOLFiniteState t a with ⟨r1, m⟩
    have ha_t := ha t
    rw [he] at hr hloc ha_t
    rcases ha_t with rfl | rfl
    · exact ⟨rfl, hr, rfl, hloc⟩
    · exact False.elim (not_resumes_error hr)
  obtain ⟨hs0, hr1, heq1, hl1⟩ := seq_res s0 _ _
    (fun x => (evaluate_storeByte_control_frame x _ _).1)
    (evaluate_storeByte_control_frame s0 _ _).2.2.1 hres
  let s1 := (evaluateHOLFiniteState s0 (.storeByte (.var .local (ofString "p")) v0)).2
  have hG1 : GuestInv s1 := guestInv_evaluate s0 _ hG
  obtain ⟨hs1, hr2, heq2, hl2⟩ := seq_res s1 _ _
    (fun x => (evaluate_storeByte_control_frame x _ _).1)
    (evaluate_storeByte_control_frame s1 _ _).2.2.1 hr1
  let s2 := (evaluateHOLFiniteState s1 (.storeByte (.op .add [.var .local (ofString "p"), .const 1]) v1)).2
  have hG2 : GuestInv s2 := guestInv_evaluate s1 _ hG1
  obtain ⟨hs2, hr3, heq3, hl3⟩ := seq_res s2 _ _
    (fun x => (evaluate_storeByte_control_frame x _ _).1)
    (evaluate_storeByte_control_frame s2 _ _).2.2.1 hr2
  let s3 := (evaluateHOLFiniteState s2 (.storeByte (.op .add [.var .local (ofString "p"), .const 2]) v2)).2
  have hG3 : GuestInv s3 := guestInv_evaluate s2 _ hG2
  obtain ⟨hs3, _, heq4, _⟩ := seq_res s3 _ _
    (fun x => (evaluate_storeByte_control_frame x _ _).1)
    (evaluate_storeByte_control_frame s3 _ _).2.2.1 hr3
  let s4 := (evaluateHOLFiniteState s3 (.storeByte (.op .add [.var .local (ofString "p"), .const 3]) v3)).2
  have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl1]; exact hp
  have hp2 : s2.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl2]; exact hp1
  have hp3 : s3.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl3]; exact hp2
  have ex0 : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
      (.var .local (ofString "p")) = some (.val (.word p)) := hp
  have ex1 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.op .add [.var .local (ofString "p"), .const 1]) = some (.val (.word (p + 1))) := by
    simp [evalHOLExact, evalListHOLExact, hp1, valueIsWord, valueWord, wordOpHOL, wordOp]
  have ex2 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
      (.op .add [.var .local (ofString "p"), .const 2]) = some (.val (.word (p + 2))) := by
    simp [evalHOLExact, evalListHOLExact, hp2, valueIsWord, valueWord, wordOpHOL, wordOp]
  have ex3 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
      (.op .add [.var .local (ofString "p"), .const 3]) = some (.val (.word (p + 3))) := by
    simp [evalHOLExact, evalListHOLExact, hp3, valueIsWord, valueWord, wordOpHOL, wordOp]
  obtain ⟨x0, hx0, hd0_lo, _⟩ := storeByte_domain hG _ v0 hs0
  obtain ⟨x1, hx1, _, hd1_hi⟩ := storeByte_domain hG1 _ v1 hs1
  obtain ⟨x2, hx2, _, hd2_hi⟩ := storeByte_domain hG2 _ v2 hs2
  obtain ⟨x3, hx3, _, hd3_hi⟩ := storeByte_domain hG3 _ v3 hs3
  rw [ex0] at hx0; injection hx0 with hx0; injection hx0 with hx0; injection hx0 with hx0; subst hx0
  rw [ex1] at hx1; injection hx1 with hx1; injection hx1 with hx1; injection hx1 with hx1; subst hx1
  rw [ex2] at hx2; injection hx2 with hx2; injection hx2 with hx2; injection hx2 with hx2; subst hx2
  rw [ex3] at hx3; injection hx3 with hx3; injection hx3 with hx3; injection hx3 with hx3; subst hx3
  have a1 : (p + 1).toNat = p.toNat + 1 := BitVec.toNat_add_of_lt (by change p.toNat + 1 < 2 ^ 64; omega)
  have a2 : (p + 2).toNat = p.toNat + 2 := by rw [a1] at hd1_hi; exact BitVec.toNat_add_of_lt (by change p.toNat + 2 < 2 ^ 64; omega)
  have a3 : (p + 3).toNat = p.toNat + 3 := by rw [a2] at hd2_hi; exact BitVec.toNat_add_of_lt (by change p.toNat + 3 < 2 ^ 64; omega)
  have hp4_hi : p.toNat + 4 ≤ heapEnd := by rw [a3] at hd3_hi; omega
  have hin4 : 0 < 4 → ∃ i ∈ [(p.toNat, 4)], i.1 ≤ p.toNat ∧ p.toNat + 4 ≤ i.1 + i.2 :=
    fun _ => ⟨(p.toNat, 4), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩
  have eff0 := byteEff_storeByte_at hG _ v0 p 0 4 hp4_hi hin4 (by omega) (by simpa [BitVec.add_zero] using ex0)
  have eff1 := byteEff_storeByte_at hG1 _ v1 p 1 4 hp4_hi hin4 (by omega) ex1
  have eff2 := byteEff_storeByte_at hG2 _ v2 p 2 4 hp4_hi hin4 (by omega) ex2
  have eff3 := byteEff_storeByte_at hG3 _ v3 p 3 4 hp4_hi hin4 (by omega) ex3
  have eff4 : ByteEff s4 (evaluateHOLFiniteState s4 (.return (.const 0))).2 [(p.toNat, 4)] :=
    byteEff_return s4 _ _
  refine ⟨?_, hd0_lo, hp4_hi⟩
  rw [heq1, heq2, heq3, heq4]
  exact eff0.trans (eff1.trans (eff2.trans (eff3.trans eff4)))

theorem st_le32_body_eff {F : Type} (s0 : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hG : GuestInv s0) (hp : s0.locals.lookup (ofString "p") = some (.val (.word p)))
    (hres : Resumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_st_le32)).1) :
    ByteEff s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_st_le32)).2 [(p.toNat, 4)] ∧
    sourceBase ≤ p.toNat ∧ p.toNat + 4 ≤ heapEnd :=
  four_byte_stores_eff s0 p _ _ _ _ hG hp hres

theorem st_be32_body_eff {F : Type} (s0 : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hG : GuestInv s0) (hp : s0.locals.lookup (ofString "p") = some (.val (.word p)))
    (hres : Resumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_st_be32)).1) :
    ByteEff s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_st_be32)).2 [(p.toNat, 4)] ∧
    sourceBase ≤ p.toNat ∧ p.toNat + 4 ≤ heapEnd :=
  four_byte_stores_eff s0 p _ _ _ _ hG hp hres

theorem funByteEff_st_be32 :
    FunByteEff (ofString "st_be32")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), 4)]) := by
  have hlook : originalRuntimeCode.lookup (ofString "st_be32") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_be32, .one) :=
    lookup_of_guestAst_getElem 27 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_st_be32) rfl
  refine ⟨_, _, _, hlook, fun entry vals _ hG hl _ hres => ?_⟩
  obtain ⟨p, _, rfl, hp, _⟩ := lookupCode_two_words (by decide) hlook hl
  exact (st_be32_body_eff entry p hG hp hres).1

/-- Extract return postcondition + caller locals preservation for a successful `call (some (none, none))`! -/
theorem call0_two_word_success {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname p1 p2 : MlS) (body : ProgHOL 64) (a1 a2 : ExpHOL 64) (w1 w2 : BitVec 64)
    (hne : p1 ≠ p2)
    (hc : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, .one))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [a1, a2] =
      some [.val (.word w1), .val (.word w2)])
    (hnone : (evaluateHOLFiniteState s (.call (some (none, none)) fname [a1, a2])).1 = none) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname [a1, a2])).2.locals = s.locals ∧
    ∃ rv, (evaluateHOLFiniteState
      (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))))
      body).1 = some (.returned rv) := by
  rw [evaluateHOLFiniteState_call, ha] at hnone ⊢
  dsimp only at hnone ⊢
  have hl := pan_two_word_lookup s.code.lookup fname p1 p2 body w1 w2 hne (by rw [hc]; exact hlook)
  rw [hl] at hnone ⊢; dsimp only at hnone ⊢
  split at hnone
  · simp at hnone
  · rename_i hclk
    rw [if_neg hclk]
    rcases hb : evaluateHOLFiniteState
      (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))))
      body with ⟨rb, pb⟩
    rw [hb] at hnone ⊢
    cases rb with
    | none => simp at hnone
    | some rb' =>
      cases rb' with
      | returned rv =>
        dsimp only at hnone ⊢
        split at hnone
        · rename_i hsh; rw [if_pos hsh]; exact ⟨rfl, rv, rfl⟩
        · simp at hnone
      | _ => simp at hnone

theorem funByteEff_st_le64 :
    FunByteEff (ofString "st_le64")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), 8)]) := by
  have hlook32 : originalRuntimeCode.lookup (ofString "st_le32") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_le32, .one) :=
    lookup_of_guestAst_getElem 25 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_st_le32) rfl
  have hlook64 : originalRuntimeCode.lookup (ofString "st_le64") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_le64, .one) :=
    lookup_of_guestAst_getElem 26 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_st_le64) rfl
  have hf32 : FunByteEff (ofString "st_le32")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), 4)]) := by
    refine ⟨_, _, _, hlook32, fun entry vals _ hG hl _ hres => ?_⟩
    obtain ⟨p, _, rfl, hp, _⟩ := lookupCode_two_words (by decide) hlook32 hl
    exact (st_le32_body_eff entry p hG hp hres).1
  refine ⟨_, _, _, hlook64, fun entry vals hc hG hl hnt hres => ?_⟩
  obtain ⟨p, v, rfl, hp, hv⟩ := lookupCode_two_words (by decide) hlook64 hl
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hbody : sourceFnBody Guest.Software.guestFn_st_le64 =
      .seq (.call (some (none, none)) (ofString "st_le32") [.var .local (ofString "p"), .var .local (ofString "v")])
        (.seq (.call (some (none, none)) (ofString "st_le32")
            [.op .add [.var .local (ofString "p"), .const 4], .shift .lsr (.var .local (ofString "v")) (.const 32)])
          (.return (.const 0))) := rfl
  rw [hbody] at hnt hres ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hc1 : evaluateHOLFiniteState entry
      (.call (some (none, none)) (ofString "st_le32") [.var .local (ofString "p"), .var .local (ofString "v")]) with ⟨r1, s1⟩
  rw [hc1] at hnt hres
  have hnt1 : r1 ≠ some .timeOut := by intro h; subst h; simp at hnt
  have hargs1 : evalListHOLFinite entry (h := fun a => Classical.propDecidable (entry.memaddrs a))
      [.var .local (ofString "p"), .var .local (ofString "v")] = some [.val (.word p), .val (.word v)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hv]
  have heff1 : ByteEff entry s1 [(p.toNat, 8)] := by
    have := call0_byteEff hf32 entry _ [(p.toNat, 8)] hc hG
      (fun vs hvs i hi _ => by
        rw [hargs1] at hvs; injection hvs with hvs; subst hvs
        simp [valWordNat] at hi; subst hi; exact ⟨(p.toNat, 8), List.mem_singleton.2 rfl, le_rfl, by omega⟩)
      (by rw [hc1]; exact hnt1)
      (by rw [hc1]; cases r1 with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
    rwa [hc1] at this
  cases r1 with
  | some _ => exact heff1
  | none =>
    obtain ⟨hs1_loc, rv1, hrv1⟩ := call0_two_word_success entry _ _ _ _ _ _ p v (by decide) hc hlook32 hargs1 (by rw [hc1])
    rw [hc1] at hs1_loc
    have hp_hi4 : p.toNat + 4 ≤ heapEnd :=
      (st_le32_body_eff _ p (guestInv_callEntry entry _ hG)
        (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "v" ≠ ofString "p" by decide])
        (Or.inl ⟨rv1, hrv1⟩)).2.2
    dsimp only at hnt hres ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hc2 : evaluateHOLFiniteState s1
        (.call (some (none, none)) (ofString "st_le32")
          [.op .add [.var .local (ofString "p"), .const 4], .shift .lsr (.var .local (ofString "v")) (.const 32)]) with ⟨r2, s2⟩
    rw [hc2] at hnt hres
    have hnt2 : r2 ≠ some .timeOut := by intro h; subst h; simp at hnt
    have hGs1 : GuestInv s1 := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hG
    have hc_s1 : s1.code = originalRuntimeCode := heff1.code.trans hc
    have hp_s1 : s1.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hs1_loc]; exact hp
    have hv_s1 : s1.locals.lookup (ofString "v") = some (.val (.word v)) := by rw [hs1_loc]; exact hv
    have hp4_add : (p + 4).toNat = p.toNat + 4 := BitVec.toNat_add_of_lt (by change p.toNat + 4 < 2 ^ 64; omega)
    have hargs2 : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.op .add [.var .local (ofString "p"), .const 4], .shift .lsr (.var .local (ofString "v")) (.const 32)] =
        some [.val (.word (p + 4)), .val (.word (v >>> 32))] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp_s1, hv_s1,
        valueIsWord, valueWord, wordOpHOL, wordOp, wordShiftHOL]
    have heff2 : ByteEff s1 s2 [(p.toNat, 8)] := by
      have := call0_byteEff hf32 s1 _ [(p.toNat, 8)] hc_s1 hGs1
        (fun vs hvs i hi _ => by
          rw [hargs2] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat, hp4_add] at hi; subst hi
          exact ⟨(p.toNat, 8), List.mem_singleton.2 rfl, by omega, by omega⟩)
        (by rw [hc2]; exact hnt2)
        (by rw [hc2]; cases r2 with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
      rwa [hc2] at this
    cases r2 with
    | some _ => exact heff1.trans heff2
    | none => exact (heff1.trans heff2).trans (byteEff_return s2 _ _)

theorem bswap64_locFrame {F : Type} (s : PanSemStateFiniteExact 64 F) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bswap64)
    out.2 = { s with locals := out.2.locals, clock := out.2.clock } := by
  dsimp only
  have hbody : sourceFnBody Guest.Software.guestFn_bswap64 =
      .seq (.assign .local (ofString "x")
          (.op .or [.shift .lsl (.op .and [.var .local (ofString "x"), .const 71777214294589695]) (.const 8),
            .op .and [.shift .lsr (.var .local (ofString "x")) (.const 8), .const 71777214294589695]]))
        (.seq (.assign .local (ofString "x")
            (.op .or [.shift .lsl (.op .and [.var .local (ofString "x"), .const 281470681808895]) (.const 16),
              .op .and [.shift .lsr (.var .local (ofString "x")) (.const 16), .const 281470681808895]]))
          (.return (.op .or [.shift .lsl (.var .local (ofString "x")) (.const 32),
            .shift .lsr (.var .local (ofString "x")) (.const 32)]))) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
  split
  · cases s; rfl
  · split
    · dsimp only [setKvarHOLFinite, setVarHOLFinite]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
      split
      · rfl
      · split
        · dsimp only [setKvarHOLFinite, setVarHOLFinite]
          rw [evaluateHOLFiniteState_return]
          split
          · rfl
          · split <;> rfl
        · rfl
    · cases s; rfl

theorem funByteEff_st_be64 :
    FunByteEff (ofString "st_be64")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), 8)]) := by
  have hlook_bs : originalRuntimeCode.lookup (ofString "bswap64") =
      some ([(ofString "x", .one)], sourceFnBody Guest.Software.guestFn_bswap64, .one) :=
    lookup_of_guestAst_getElem 23 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_bswap64) rfl
  have hlook32 : originalRuntimeCode.lookup (ofString "st_be32") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_be32, .one) :=
    lookup_of_guestAst_getElem 27 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_st_be32) rfl
  have hlook64 : originalRuntimeCode.lookup (ofString "st_be64") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_be64, .one) :=
    lookup_of_guestAst_getElem 28 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_st_be64) rfl
  refine ⟨_, _, _, hlook64, fun entry vals hc hG hl hnt hres => ?_⟩
  obtain ⟨p, v, rfl, hp, hv⟩ := lookupCode_two_words (by decide) hlook64 hl
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hbody : sourceFnBody Guest.Software.guestFn_st_be64 =
      .seq (.ite (.cmp .equal (.op .and [.var .local (ofString "p"), .const 7]) (.const 0))
          (.decCall (ofString "w") .one (ofString "bswap64") [.var .local (ofString "v")]
            (.seq (.store (.var .local (ofString "p")) (.var .local (ofString "w")))
              (.return (.const 0))))
          .skip)
        (.seq (.call (some (none, none)) (ofString "st_be32")
            [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32)])
          (.seq (.call (some (none, none)) (ofString "st_be32")
              [.op .add [.var .local (ofString "p"), .const 4], .var .local (ofString "v")])
            (.return (.const 0)))) := rfl
  rw [hbody] at hnt hres ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  dsimp only [valWordNat]
  rcases h1 : evaluateHOLFiniteState entry
      (.ite (.cmp .equal (.op .and [.var .local (ofString "p"), .const 7]) (.const 0))
        (.decCall (ofString "w") .one (ofString "bswap64") [.var .local (ofString "v")]
          (.seq (.store (.var .local (ofString "p")) (.var .local (ofString "w")))
            (.return (.const 0))))
        .skip) with ⟨r1, s1⟩
  rw [h1] at hnt hres
  -- Analyze `ite`: if true branch taken, `decCall` either returns `(0)` or errors/times out (never `none`!).
  -- If false branch taken, `.skip` returns `(none, entry)`!
  have hite_branch : (r1 = none ∧ s1 = entry) ∨ (r1 ≠ none ∧ ByteEff entry s1 [(p.toNat, 8)]) := by
    rw [evaluateHOLFiniteState_ite] at h1
    split at h1
    · split at h1
      · rw [evaluateHOLFiniteState_skip] at h1; injection h1 with hr1 hs1; exact Or.inl ⟨hr1.symm, hs1.symm⟩
      · right
        rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at h1
        have hargs_bs : evalListHOLFinite entry (h := fun a => Classical.propDecidable (entry.memaddrs a))
            [.var .local (ofString "v")] = some [.val (.word v)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hv]
        rw [hargs_bs] at h1; dsimp only at h1
        have hl_bs := pan_one_word_lookup entry.code.lookup (ofString "bswap64") (ofString "x")
          (sourceFnBody Guest.Software.guestFn_bswap64) v (by rw [hc]; exact hlook_bs)
        rw [hl_bs] at h1; dsimp only at h1
        split at h1
        · injection h1 with hr1 hs1; subst hr1 hs1; exact ⟨by simp, (ByteEff.refl entry _).locals_clock _ _⟩
        · have hbs := bswap64_locFrame (callEntryStateHOLFinite entry (HolFiniteMapExact.empty.update (ofString "x", .val (.word v))))
          rcases hrun_bs : evaluateHOLFiniteState (callEntryStateHOLFinite entry (HolFiniteMapExact.empty.update (ofString "x", .val (.word v))))
            (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rbs, pbs⟩
          rw [hrun_bs] at h1 hbs; dsimp only at hbs
          have heff_pbs : ByteEff entry pbs [(p.toNat, 8)] := by
            rw [hbs]; exact (ByteEff.refl entry _).locals_clock _ _
          cases rbs with
          | none => injection h1 with hr1 hs1; subst hr1 hs1; exact ⟨by simp, heff_pbs.locals_clock _ _⟩
          | some rbs' =>
            cases rbs' with
            | returned rv =>
              dsimp only at h1; split at h1
              · rename_i hsh_rv
                rcases rv with ⟨⟨wv⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hsh_rv)
                let st_w := setVarHOLFinite (ofString "w") (.val (.word wv)) { pbs with locals := entry.locals }
                have hGw : GuestInv st_w := guestInv_setVar _ _ _
                  (guestInv_congr heff_pbs.code heff_pbs.memaddrs heff_pbs.shMemaddrs heff_pbs.baseAddr hG)
                have hp_w : st_w.locals.lookup (ofString "p") = some (.val (.word p)) := by
                  simp [st_w, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp, show ofString "w" ≠ ofString "p" by decide]
                have hw_w : st_w.locals.lookup (ofString "w") = some (.val (.word wv)) := by
                  simp [st_w, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                rw [evaluateHOLFiniteState_seq_line780] at h1
                have heff_st := (byteEff_store_one (Rl := [(p.toNat, 8)]) hGw
                  (.var .local (ofString "p")) (.var .local (ofString "w"))
                  (fun val hval => by simp [evalHOLExact, hw_w] at hval; exact ⟨wv, hval.symm⟩)
                  (fun x hx _ => by
                    simp [evalHOLExact, hp_w] at hx; subst hx
                    exact ⟨(p.toNat, 8), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)).1
                rcases hst_ev : evaluateHOLFiniteState st_w (.store (.var .local (ofString "p")) (.var .local (ofString "w"))) with ⟨rst, mst⟩
                rw [hst_ev] at h1 heff_st
                cases rst with
                | some rst' =>
                  injection h1 with hr1 hs1; subst hr1 hs1
                  exact ⟨by simp, ((heff_pbs.locals_clock _ _).trans heff_st).locals_clock _ _⟩
                | none =>
                  dsimp only at h1
                  have heff_ret := byteEff_return mst (.const 0) [(p.toNat, 8)]
                  have hret_nz : (evaluateHOLFiniteState mst (.return (.const 0))).1 ≠ none := by
                    rw [evaluateHOLFiniteState_return]; dsimp only [evalHOLExact, shapeOfHOLExact]; split <;> simp
                  rcases hret_ev : evaluateHOLFiniteState mst (.return (.const 0)) with ⟨rret, mret⟩
                  rw [hret_ev] at h1 heff_ret hret_nz
                  injection h1 with hr1 hs1; subst hr1 hs1
                  exact ⟨hret_nz, (((heff_pbs.locals_clock _ _).trans heff_st).trans heff_ret).locals_clock _ _⟩
              · injection h1 with hr1 hs1; subst hr1 hs1; exact ⟨by simp, heff_pbs.locals_clock _ _⟩
            | timeOut | error | «break» | «continue» | exception _ _ | finalFfi _ =>
              dsimp only at h1
              injection h1 with hr1 hs1; subst hr1 hs1; exact ⟨by simp, heff_pbs.locals_clock _ _⟩
    · injection h1 with hr1 hs1; subst hr1 hs1; exact Or.inr ⟨by simp, ByteEff.refl entry _⟩
  rcases hite_branch with ⟨rfl, hs1_eq⟩ | ⟨hr1_ne, heff1⟩
  · subst hs1_eq
    -- False branch: two `st_be32` calls!
    dsimp only at hnt hres ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hc1 : evaluateHOLFiniteState s1
        (.call (some (none, none)) (ofString "st_be32")
          [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32)]) with ⟨rc1_r, m1⟩
    rw [hc1] at hnt hres
    have hnt1 : rc1_r ≠ some .timeOut := by intro h; subst h; simp at hnt
    have hargs1 : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32)] =
        some [.val (.word p), .val (.word (v >>> 32))] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hv, valueIsWord, valueWord, wordShiftHOL]
    have heff_c1 : ByteEff s1 m1 [(p.toNat, 8)] := by
      have := call0_byteEff funByteEff_st_be32 s1 _ [(p.toNat, 8)] hc hG
        (fun vs hvs i hi _ => by
          rw [hargs1] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat] at hi; subst hi; exact ⟨(p.toNat, 8), List.mem_singleton.2 rfl, le_rfl, by omega⟩)
        (by rw [hc1]; exact hnt1)
        (by rw [hc1]; cases rc1_r with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
      rwa [hc1] at this
    cases rc1_r with
    | some _ => exact heff_c1
    | none =>
      obtain ⟨hm1_loc, rv1, hrv1⟩ := call0_two_word_success s1 _ _ _ _ _ _ p (v >>> 32) (by decide) hc hlook32 hargs1 (by rw [hc1])
      rw [hc1] at hm1_loc
      have hp_hi4 : p.toNat + 4 ≤ heapEnd :=
        (st_be32_body_eff _ p (guestInv_callEntry s1 _ hG)
          (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "v" ≠ ofString "p" by decide])
          (Or.inl ⟨rv1, hrv1⟩)).2.2
      dsimp only at hnt hres ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
      rcases hc2 : evaluateHOLFiniteState m1
          (.call (some (none, none)) (ofString "st_be32")
            [.op .add [.var .local (ofString "p"), .const 4], .var .local (ofString "v")]) with ⟨rc2_r, m2⟩
      rw [hc2] at hnt hres
      have hnt2 : rc2_r ≠ some .timeOut := by intro h; subst h; simp at hnt
      have hGm1 : GuestInv m1 := guestInv_congr heff_c1.code heff_c1.memaddrs heff_c1.shMemaddrs heff_c1.baseAddr hG
      have hc_m1 : m1.code = originalRuntimeCode := heff_c1.code.trans hc
      have hp_m1 : m1.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hm1_loc]; exact hp
      have hv_m1 : m1.locals.lookup (ofString "v") = some (.val (.word v)) := by rw [hm1_loc]; exact hv
      have hp4_add : (p + 4).toNat = p.toNat + 4 := BitVec.toNat_add_of_lt (by change p.toNat + 4 < 2 ^ 64; omega)
      have hargs2 : evalListHOLFinite m1 (h := fun a => Classical.propDecidable (m1.memaddrs a))
          [.op .add [.var .local (ofString "p"), .const 4], .var .local (ofString "v")] =
          some [.val (.word (p + 4)), .val (.word v)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp_m1, hv_m1, valueIsWord, valueWord, wordOpHOL, wordOp]
      have heff_c2 : ByteEff m1 m2 [(p.toNat, 8)] := by
        have := call0_byteEff funByteEff_st_be32 m1 _ [(p.toNat, 8)] hc_m1 hGm1
          (fun vs hvs i hi _ => by
            rw [hargs2] at hvs; injection hvs with hvs; subst hvs
            simp [valWordNat, hp4_add] at hi; subst hi
            exact ⟨(p.toNat, 8), List.mem_singleton.2 rfl, by omega, by omega⟩)
          (by rw [hc2]; exact hnt2)
          (by rw [hc2]; cases rc2_r with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
        rwa [hc2] at this
      cases rc2_r with
      | some _ => exact heff_c1.trans heff_c2
      | none => exact (heff_c1.trans heff_c2).trans (byteEff_return m2 _ _)
  · cases r1 with
    | none => exact absurd rfl hr1_ne
    | some _ => exact heff1

/-! ## 2. Declarative checker `checkConstStores` & `checkByteStoresAt` -/

/-- Check that `prog` writes only to `[base, base + sz)` via `.storeByte` at `ptrVar + off`
(`off < sz` and `sz ≤ sourceBase`, so `base + off` cannot wrap when in `ordinaryDomain`!)
and never assigns/declares `ptrVar` or modifies globals. Covers `sha256_pair` (512 steps) in 1 `rfl`! -/
def checkByteStoresLocal (ptrVar : MlS) (sz : Nat) : ProgHOL 64 → Bool
  | .dec nm _ _ b => !(nm == ptrVar) && checkByteStoresLocal ptrVar sz b
  | .seq a b => checkByteStoresLocal ptrVar sz a && checkByteStoresLocal ptrVar sz b
  | .ite _ a b => checkByteStoresLocal ptrVar sz a && checkByteStoresLocal ptrVar sz b
  | .while _ b => checkByteStoresLocal ptrVar sz b
  | .assign .local nm _ => !(nm == ptrVar)
  | .storeByte (.var .local nm) _ => (nm == ptrVar) && decide (1 ≤ sz)
  | .storeByte (.op .add [.var .local nm, .const off]) _ =>
      (nm == ptrVar) && decide (off.toNat < sz)
  | .skip | .break | .continue | .return _ | .raise _ _ | .annot _ _ => true
  | _ => false

theorem checkByteStoresLocal_sound {F : Type} (ptrVar : MlS) (sz : Nat) (hsz : sz ≤ 2048)
    (prog : ProgHOL 64) (hok : checkByteStoresLocal ptrVar sz prog = true)
    (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hp : s.locals.lookup ptrVar = some (.val (.word p))) :
    ByteEff s (evaluateHOLFiniteState s prog).2 [(p.toNat, sz)] ∧
    ((evaluateHOLFiniteState s prog).1 = none ∨
     (evaluateHOLFiniteState s prog).1 = some .break ∨
     (evaluateHOLFiniteState s prog).1 = some .continue →
      (evaluateHOLFiniteState s prog).2.locals.lookup ptrVar = some (.val (.word p))) := by
  have hsb : 2048 < sourceBase := by rw [sourceBase_val]; decide
  cases shape : prog with
  | skip => rw [evaluateHOLFiniteState_skip]; exact ⟨ByteEff.refl s _, fun _ => hp⟩
  | «break» => rw [evaluateHOLFiniteState_break]; exact ⟨ByteEff.refl s _, fun _ => hp⟩
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact ⟨ByteEff.refl s _, fun _ => hp⟩
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; exact ⟨ByteEff.refl s _, fun _ => hp⟩
  | «return» e =>
    refine ⟨byteEff_return s e _, fun h => ?_⟩
    rw [evaluateHOLFiniteState_return] at h
    split at h
    · simp at h
    · split at h <;> simp at h
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split
      · exact ⟨(ByteEff.refl s _).locals_clock _ _, by simp⟩
      · exact ⟨ByteEff.refl s _, by simp⟩
    · exact ⟨ByteEff.refl s _, by simp⟩
  | assign k nm e =>
    cases k with
    | global => simp [shape, checkByteStoresLocal] at hok
    | «local» =>
      have hne : nm ≠ ptrVar := by simpa [shape, checkByteStoresLocal] using hok
      refine ⟨byteEff_assign_local s nm e _, fun h => ?_⟩
      rw [evaluateHOLFiniteState_assign] at h ⊢
      rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | val
      · simp [hev] at h
      · simp only [hev] at h ⊢
        split at h
        · rename_i hv; rw [if_pos hv]
          simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hp]
        · simp at h
  | dec nm sh init b =>
    have h12 : nm ≠ ptrVar ∧ checkByteStoresLocal ptrVar sz b = true := by
      simpa [shape, checkByteStoresLocal, Bool.and_eq_true] using hok
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · exact ⟨ByteEff.refl s _, by simp⟩
    · rename_i val hval
      split
      · have hp' : (setVarHOLFinite nm val s).locals.lookup ptrVar = some (.val (.word p)) := by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h12.1, hp]
        have ih := checkByteStoresLocal_sound ptrVar sz hsz b h12.2 (setVarHOLFinite nm val s) p
          hc (guestInv_setVar nm val s hG) hp'
        refine ⟨(((ByteEff.refl s _).locals_clock _ _).trans ih.1).locals_clock _ _, fun h => ?_⟩
        dsimp only at h ⊢
        rw [resVarEq_lookup_ne _ nm ptrVar _ (Ne.symm h12.1), ih.2 h]
      · exact ⟨ByteEff.refl s _, by simp⟩
  | seq a b =>
    have h12 : checkByteStoresLocal ptrVar sz a = true ∧ checkByteStoresLocal ptrVar sz b = true := by
      simpa [shape, checkByteStoresLocal, Bool.and_eq_true] using hok
    have rem := evaluateHOLFiniteState_clock_le s a
    have iha := checkByteStoresLocal_sound ptrVar sz hsz a h12.1 s p hc hG hp
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hra : evaluateHOLFiniteState s a with ⟨r1, m⟩
    rw [hra] at iha rem
    cases r1 with
    | none =>
      have mclk : m.clock ≤ s.clock := rem
      have hpm := iha.2 (Or.inl rfl)
      have hGm := guestInv_congr iha.1.code iha.1.memaddrs iha.1.shMemaddrs iha.1.baseAddr hG
      have ihb := checkByteStoresLocal_sound ptrVar sz hsz b h12.2 m p (iha.1.code.trans hc) hGm hpm
      exact ⟨iha.1.trans ihb.1, ihb.2⟩
    | some _ => exact iha
  | ite c a b =>
    have h12 : checkByteStoresLocal ptrVar sz a = true ∧ checkByteStoresLocal ptrVar sz b = true := by
      simpa [shape, checkByteStoresLocal, Bool.and_eq_true] using hok
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact checkByteStoresLocal_sound ptrVar sz hsz b h12.2 s p hc hG hp
      · exact checkByteStoresLocal_sound ptrVar sz hsz a h12.1 s p hc hG hp
    · exact ⟨ByteEff.refl s _, by simp⟩
  | «while» c b =>
    have hb : checkByteStoresLocal ptrVar sz b = true := by simpa [shape, checkByteStoresLocal] using hok
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact ⟨(ByteEff.refl s _).locals_clock _ _, by simp⟩
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by simp only [decClockHOLFinite]; omega
          dsimp only; rw [fixClockHOLFinite_evaluateState]
          have hGd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hG
          have ih1 := checkByteStoresLocal_sound ptrVar sz hsz b hb (decClockHOLFinite s) p hc hGd hp
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) b
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) b with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
          have heff1 : ByteEff s mid [(p.toNat, sz)] := ((ByteEff.refl s _).locals_clock _ _).trans ih1.1
          have hGm : GuestInv mid := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hG
          cases r1 with
          | none =>
            have ihw := checkByteStoresLocal_sound ptrVar sz hsz (.while c b) (by simpa [checkByteStoresLocal] using hb)
              mid p (heff1.code.trans hc) hGm (ih1.2 (Or.inl rfl))
            exact ⟨heff1.trans ihw.1, ihw.2⟩
          | some res =>
            cases res with
            | «continue» =>
              have ihw := checkByteStoresLocal_sound ptrVar sz hsz (.while c b) (by simpa [checkByteStoresLocal] using hb)
                mid p (heff1.code.trans hc) hGm (ih1.2 (Or.inr (Or.inr rfl)))
              exact ⟨heff1.trans ihw.1, ihw.2⟩
            | «break» => exact ⟨heff1, fun _ => ih1.2 (Or.inr (Or.inl rfl))⟩
            | _ => exact ⟨heff1, by simp⟩
      · exact ⟨ByteEff.refl s _, fun _ => hp⟩
    · exact ⟨ByteEff.refl s _, by simp⟩
  | storeByte dst vexp =>
    have hloc_sb := (evaluate_storeByte_control_frame s dst vexp).2.2.1
    refine ⟨?_, fun _ => by rw [hloc_sb]; exact hp⟩
    cases dst with
    | var vk nm =>
      cases vk with
      | global => simp [shape, checkByteStoresLocal] at hok
      | «local» =>
        simp only [shape, checkByteStoresLocal, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
        rcases hok with ⟨rfl, hsz1⟩
        exact (byteEff_storeByte hG (.var .local nm) vexp (fun x hx _ => by
          simp [evalHOLExact, hp] at hx; subst hx
          exact ⟨(p.toNat, sz), List.mem_singleton.2 rfl, le_rfl, by omega⟩)).1
    | op bop args =>
      cases bop <;> try (simp [shape, checkByteStoresLocal] at hok)
      rcases args with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> try (simp [shape, checkByteStoresLocal] at hok)
      cases e1 with
      | var vk1 nm1 =>
        cases vk1 <;> try (simp [shape, checkByteStoresLocal] at hok)
        cases e2 with
        | const off =>
          simp only [shape, checkByteStoresLocal, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
          rcases hok with ⟨rfl, hoff⟩
          refine (byteEff_storeByte hG (.op .add [.var .local nm1, .const off]) vexp (fun x hx hdom => ?_)).1
          simp [evalHOLExact, evalListHOLExact, hp, valueIsWord, valueWord, wordOpHOL, wordOp] at hx
          subst hx
          rw [hG.memaddrs, ordinaryDomain_iff] at hdom
          have hal := panByteAlign_toNat64 (p + off)
          have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
          have hp_lt := p.isLt; have hoff_lt := off.isLt
          have hnw : p.toNat + off.toNat < 2 ^ 64 := by
            by_contra hge
            have : (p + off).toNat = p.toNat + off.toNat - 2 ^ 64 := by rw [BitVec.toNat_add]; omega
            omega
          have hadd : (p + off).toNat = p.toNat + off.toNat := BitVec.toNat_add_of_lt hnw
          exact ⟨(p.toNat, sz), List.mem_singleton.2 rfl, by omega, by omega⟩
        | _ => simp [shape, checkByteStoresLocal] at hok
      | _ => simp [shape, checkByteStoresLocal] at hok
    | _ => simp [shape, checkByteStoresLocal] at hok
  | _ => simp [shape, checkByteStoresLocal] at hok
termination_by (s.clock, sizeOf prog)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

theorem funByteEff_sha256_pair :
    FunByteEff (ofString "sha256_pair")
      (fun vals _ => [(valWordNat (vals[2]?.getD (.rStruct [])), 32)]) := by
  have hlook : originalRuntimeCode.lookup (ofString "sha256_pair") =
      some ([(ofString "input_a", .one), (ofString "input_b", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_sha256_pair, .one) :=
    lookup_of_guestAst_getElem 96 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sha256_pair) rfl
  refine ⟨_, _, _, hlook, fun entry vals hc hG hl _ _ => ?_⟩
  obtain ⟨_, _, out, rfl, _, _, hout⟩ := lookupCode_three_words (by decide) (by decide) (by decide) hlook hl
  exact (checkByteStoresLocal_sound (ofString "out") 32 (by omega)
    (sourceFnBody Guest.Software.guestFn_sha256_pair) rfl entry out hc hG hout).1

theorem funByteEff_addr_from_words :
    FunByteEff (ofString "addr_from_words")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), 20)]) := by
  have hlook32 : originalRuntimeCode.lookup (ofString "st_be32") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_be32, .one) :=
    lookup_of_guestAst_getElem 27 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_st_be32) rfl
  have hlook64 : originalRuntimeCode.lookup (ofString "st_be64") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_be64, .one) :=
    lookup_of_guestAst_getElem 28 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_st_be64) rfl
  have hlook : originalRuntimeCode.lookup (ofString "addr_from_words") =
      some ([(ofString "out", .one), (ofString "hi4", .one), (ofString "mid8", .one), (ofString "lo8", .one)],
        sourceFnBody Guest.Software.guestFn_addr_from_words, .one) :=
    lookup_of_guestAst_getElem 860 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_addr_from_words) rfl
  refine ⟨_, _, _, hlook, fun entry vals hc hG hl hnt hres => ?_⟩
  obtain ⟨out, hi4, mid8, lo8, rfl, hout, hhi, hmid, hlo⟩ :=
    lookupCode_four_words (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hlook hl
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hsb : 20 < sourceBase := by rw [sourceBase_val]; decide
  have hbody : sourceFnBody Guest.Software.guestFn_addr_from_words =
      .seq (.call (some (none, none)) (ofString "st_be32") [.var .local (ofString "out"), .var .local (ofString "hi4")])
        (.seq (.call (some (none, none)) (ofString "st_be64")
            [.op .add [.var .local (ofString "out"), .const 4], .var .local (ofString "mid8")])
          (.seq (.call (some (none, none)) (ofString "st_be64")
              [.op .add [.var .local (ofString "out"), .const 12], .var .local (ofString "lo8")])
            (.return (.const 0)))) := rfl
  rw [hbody] at hnt hres ⊢
  dsimp only [valWordNat]
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hc1 : evaluateHOLFiniteState entry
      (.call (some (none, none)) (ofString "st_be32") [.var .local (ofString "out"), .var .local (ofString "hi4")]) with ⟨r1, s1⟩
  rw [hc1] at hnt hres
  have hnt1 : r1 ≠ some .timeOut := by intro h; subst h; simp at hnt
  have hargs1 : evalListHOLFinite entry (h := fun a => Classical.propDecidable (entry.memaddrs a))
      [.var .local (ofString "out"), .var .local (ofString "hi4")] = some [.val (.word out), .val (.word hi4)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hout, hhi]
  have heff1 : ByteEff entry s1 [(out.toNat, 20)] := by
    have := call0_byteEff funByteEff_st_be32 entry _ [(out.toNat, 20)] hc hG
      (fun vs hvs i hi _ => by
        rw [hargs1] at hvs; injection hvs with hvs; subst hvs
        simp [valWordNat] at hi; subst hi; exact ⟨(out.toNat, 20), List.mem_singleton.2 rfl, le_rfl, by omega⟩)
      (by rw [hc1]; exact hnt1)
      (by rw [hc1]; cases r1 with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
    rwa [hc1] at this
  cases r1 with
  | some _ => exact heff1
  | none =>
    obtain ⟨hs1_loc, rv1, hrv1⟩ := call0_two_word_success entry _ _ _ _ _ _ out hi4 (by decide) hc hlook32 hargs1 (by rw [hc1])
    rw [hc1] at hs1_loc
    have hout_hi : out.toNat + 4 ≤ heapEnd :=
      (st_be32_body_eff _ out (guestInv_callEntry entry _ hG)
        (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "v" ≠ ofString "p" by decide])
        (Or.inl ⟨rv1, hrv1⟩)).2.2
    have h264_plus : heapEnd + 16 < 2 ^ 64 := by rw [heapEnd_val]; decide
    have ha4 : (out + 4).toNat = out.toNat + 4 := BitVec.toNat_add_of_lt (by change out.toNat + 4 < 2 ^ 64; omega)
    have ha12 : (out + 12).toNat = out.toNat + 12 := BitVec.toNat_add_of_lt (by change out.toNat + 12 < 2 ^ 64; omega)
    dsimp only at hnt hres ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hc2 : evaluateHOLFiniteState s1
        (.call (some (none, none)) (ofString "st_be64")
          [.op .add [.var .local (ofString "out"), .const 4], .var .local (ofString "mid8")]) with ⟨r2, s2⟩
    rw [hc2] at hnt hres
    have hnt2 : r2 ≠ some .timeOut := by intro h; subst h; simp at hnt
    have hGs1 : GuestInv s1 := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hG
    have hc_s1 : s1.code = originalRuntimeCode := heff1.code.trans hc
    have hout_s1 : s1.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hs1_loc]; exact hout
    have hmid_s1 : s1.locals.lookup (ofString "mid8") = some (.val (.word mid8)) := by rw [hs1_loc]; exact hmid
    have hargs2 : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.op .add [.var .local (ofString "out"), .const 4], .var .local (ofString "mid8")] =
        some [.val (.word (out + 4)), .val (.word mid8)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hout_s1, hmid_s1, valueIsWord, valueWord, wordOpHOL, wordOp]
    have heff2 : ByteEff s1 s2 [(out.toNat, 20)] := by
      have := call0_byteEff funByteEff_st_be64 s1 _ [(out.toNat, 20)] hc_s1 hGs1
        (fun vs hvs i hi _ => by
          rw [hargs2] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat, ha4] at hi; subst hi
          exact ⟨(out.toNat, 20), List.mem_singleton.2 rfl, by omega, by omega⟩)
        (by rw [hc2]; exact hnt2)
        (by rw [hc2]; cases r2 with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
      rwa [hc2] at this
    cases r2 with
    | some _ => exact heff1.trans heff2
    | none =>
      obtain ⟨hs2_loc, _, _⟩ := call0_two_word_success s1 _ _ _ _ _ _ (out + 4) mid8 (by decide) hc_s1 hlook64 hargs2 (by rw [hc2])
      rw [hc2] at hs2_loc
      dsimp only at hnt hres ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
      rcases hc3 : evaluateHOLFiniteState s2
          (.call (some (none, none)) (ofString "st_be64")
            [.op .add [.var .local (ofString "out"), .const 12], .var .local (ofString "lo8")]) with ⟨r3, s3⟩
      rw [hc3] at hnt hres
      have hnt3 : r3 ≠ some .timeOut := by intro h; subst h; simp at hnt
      have hGs2 : GuestInv s2 := guestInv_congr heff2.code heff2.memaddrs heff2.shMemaddrs heff2.baseAddr hGs1
      have hc_s2 : s2.code = originalRuntimeCode := heff2.code.trans hc_s1
      have hout_s2 : s2.locals.lookup (ofString "out") = some (.val (.word out)) := by rw [hs2_loc]; exact hout_s1
      have hlo_s2 : s2.locals.lookup (ofString "lo8") = some (.val (.word lo8)) := by rw [hs2_loc]; exact (hs1_loc ▸ hlo)
      have hargs3 : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
          [.op .add [.var .local (ofString "out"), .const 12], .var .local (ofString "lo8")] =
          some [.val (.word (out + 12)), .val (.word lo8)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hout_s2, hlo_s2, valueIsWord, valueWord, wordOpHOL, wordOp]
      have heff3 : ByteEff s2 s3 [(out.toNat, 20)] := by
        have := call0_byteEff funByteEff_st_be64 s2 _ [(out.toNat, 20)] hc_s2 hGs2
          (fun vs hvs i hi _ => by
            rw [hargs3] at hvs; injection hvs with hvs; subst hvs
            simp [valWordNat, ha12] at hi; subst hi
            exact ⟨(out.toNat, 20), List.mem_singleton.2 rfl, by omega, by omega⟩)
          (by rw [hc3]; exact hnt3)
          (by rw [hc3]; cases r3 with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
        rwa [hc3] at this
      cases r3 with
      | some _ => exact (heff1.trans heff2).trans heff3
      | none => exact ((heff1.trans heff2).trans heff3).trans (byteEff_return s3 _ _)

/-! ## 3. `keccak_f1600`, `keccak_absorb_block`, `keccak256` -/

/-- Check that `prog` writes only to `[base, base + sz)` via single-word `.store` at `ptrVar + off`
(`off + 8 ≤ sz ≤ 2048`), with single-word value expressions (`const`, `op`, `shift`, `load .one`,
or local variable in `wordVars` whose wordness is preserved!), and never modifies `ptrVar` or globals. -/
def isGuaranteedWordExp (wordVars : List MlS) : ExpHOL 64 → Bool
  | .const _ | .load .one _ | .loadByte _ | .load32 _
  | .op _ _ | .panop _ _ | .cmp _ _ _ | .shift _ _ _ | .baseAddr | .topAddr => true
  | .var .local nm => wordVars.contains nm
  | _ => false

theorem eval_isGuaranteedWordExp {F : Type} (s : PanSemStateFiniteExact 64 F)
    (wordVars : List MlS)
    (hwv : ∀ nm ∈ wordVars, ∃ w : BitVec 64, s.locals.lookup nm = some (.val (.word w)))
    (e : ExpHOL 64) (he : isGuaranteedWordExp wordVars e = true) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v →
      ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  cases e with
  | const c => simp [evalHOLExact] at hv; exact ⟨c, hv.symm⟩
  | baseAddr => simp [evalHOLExact] at hv; exact ⟨s.baseAddr, hv.symm⟩
  | topAddr => simp [evalHOLExact] at hv; exact ⟨s.topAddr, hv.symm⟩
  | var vk nm =>
    cases vk with
    | global => simp [isGuaranteedWordExp] at he
    | «local» =>
      have hmem : nm ∈ wordVars := List.contains_iff_mem.1 (by simpa [isGuaranteedWordExp] using he)
      obtain ⟨w, hw⟩ := hwv nm hmem
      simp [evalHOLExact, hw] at hv; exact ⟨w, hv.symm⟩
  | load sh addrExp =>
    cases sh with
    | one => exact eval_load_one_word s addrExp v hv
    | comb _ | named _ => simp [isGuaranteedWordExp] at he
  | loadByte _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · simp only [Option.map_eq_some_iff] at hv
      obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
    · cases hv
  | load32 _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · simp only [Option.map_eq_some_iff] at hv
      obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
    · cases hv
  | op _ _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · split at hv
      · simp only [Option.map_eq_some_iff] at hv
        obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
      · cases hv
    · cases hv
  | panop _ _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · split at hv
      · simp only [Option.map_eq_some_iff] at hv
        obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
      · cases hv
    · cases hv
  | cmp _ _ _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · injection hv with h; exact ⟨_, h.symm⟩
    · cases hv
  | shift _ _ _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · simp only [Option.map_eq_some_iff] at hv
      obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
    · cases hv
  | _ => simp [isGuaranteedWordExp] at he

def checkWordStoresLocal (ptrVar : MlS) (sz : Nat) (wordVars : List MlS) : ProgHOL 64 → Bool
  | .dec nm .one init b =>
      !(nm == ptrVar) && isGuaranteedWordExp wordVars init &&
      checkWordStoresLocal ptrVar sz (nm :: wordVars) b
  | .seq a b => checkWordStoresLocal ptrVar sz wordVars a && checkWordStoresLocal ptrVar sz wordVars b
  | .ite _ a b => checkWordStoresLocal ptrVar sz wordVars a && checkWordStoresLocal ptrVar sz wordVars b
  | .while _ b => checkWordStoresLocal ptrVar sz wordVars b
  | .assign .local nm e => !(nm == ptrVar) &&
      (!(wordVars.contains nm) || isGuaranteedWordExp wordVars e)
  | .store (.var .local nm) vexp =>
      (nm == ptrVar) && decide (8 ≤ sz) && isGuaranteedWordExp wordVars vexp
  | .store (.op .add [.var .local nm, .const off]) vexp =>
      (nm == ptrVar) && decide (off.toNat + 8 ≤ sz) && isGuaranteedWordExp wordVars vexp
  | .skip | .break | .continue | .return _ | .raise _ _ | .annot _ _ => true
  | _ => false

theorem checkWordStoresLocal_sound {F : Type} (ptrVar : MlS) (sz : Nat) (hsz : sz ≤ 2048)
    (wordVars : List MlS) (prog : ProgHOL 64)
    (hok : checkWordStoresLocal ptrVar sz wordVars prog = true)
    (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hp : s.locals.lookup ptrVar = some (.val (.word p)))
    (hwv : ∀ nm ∈ wordVars, ∃ w : BitVec 64, s.locals.lookup nm = some (.val (.word w))) :
    ByteEff s (evaluateHOLFiniteState s prog).2 [(p.toNat, sz)] ∧
    ((evaluateHOLFiniteState s prog).1 = none ∨
     (evaluateHOLFiniteState s prog).1 = some .break ∨
     (evaluateHOLFiniteState s prog).1 = some .continue →
      (evaluateHOLFiniteState s prog).2.locals.lookup ptrVar = some (.val (.word p)) ∧
      ∀ nm ∈ wordVars, ∃ w : BitVec 64,
        (evaluateHOLFiniteState s prog).2.locals.lookup nm = some (.val (.word w))) := by
  have hsb : 2048 < sourceBase := by rw [sourceBase_val]; decide
  cases shape : prog with
  | skip => rw [evaluateHOLFiniteState_skip]; exact ⟨ByteEff.refl s _, fun _ => ⟨hp, hwv⟩⟩
  | «break» => rw [evaluateHOLFiniteState_break]; exact ⟨ByteEff.refl s _, fun _ => ⟨hp, hwv⟩⟩
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact ⟨ByteEff.refl s _, fun _ => ⟨hp, hwv⟩⟩
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; exact ⟨ByteEff.refl s _, fun _ => ⟨hp, hwv⟩⟩
  | «return» e =>
    refine ⟨byteEff_return s e _, fun h => ?_⟩
    rw [evaluateHOLFiniteState_return] at h
    split at h
    · simp at h
    · split at h <;> simp at h
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split
      · exact ⟨(ByteEff.refl s _).locals_clock _ _, by simp⟩
      · exact ⟨ByteEff.refl s _, by simp⟩
    · exact ⟨ByteEff.refl s _, by simp⟩
  | assign k nm e =>
    cases k with
    | global => simp [shape, checkWordStoresLocal] at hok
    | «local» =>
      have h12 : nm ≠ ptrVar ∧ (!(wordVars.contains nm) || isGuaranteedWordExp wordVars e) = true := by
        simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
      refine ⟨byteEff_assign_local s nm e _, fun h => ?_⟩
      rw [evaluateHOLFiniteState_assign] at h ⊢
      rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | val
      · simp [hev] at h
      · simp only [hev] at h ⊢
        split at h
        · rename_i hv; rw [if_pos hv]
          refine ⟨by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h12.1, hp],
            fun m hm => ?_⟩
          by_cases hmn : m = nm
          · subst hmn
            have hge : isGuaranteedWordExp wordVars e = true := by
              have hmem : wordVars.contains m = true := List.contains_iff_mem.2 hm
              have h2 := h12.2
              rw [hmem] at h2; simpa using h2
            obtain ⟨w, rfl⟩ := eval_isGuaranteedWordExp s wordVars hwv e hge val hev
            exact ⟨w, by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
          · obtain ⟨w, hw⟩ := hwv m hm
            exact ⟨w, by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hmn, hw]⟩
        · simp at h
  | dec nm sh init b =>
    cases sh with
    | comb _ | named _ => simp [shape, checkWordStoresLocal] at hok
    | one =>
      have h123 : (nm ≠ ptrVar ∧ isGuaranteedWordExp wordVars init = true) ∧
          checkWordStoresLocal ptrVar sz (nm :: wordVars) b = true := by
        simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      rcases hinit : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init with _ | val
      · exact ⟨ByteEff.refl s _, by simp⟩
      · dsimp only
        split
        · obtain ⟨wi, rfl⟩ := eval_isGuaranteedWordExp s wordVars hwv init h123.1.2 val hinit
          have hp' : (setVarHOLFinite nm (.val (.word wi)) s).locals.lookup ptrVar = some (.val (.word p)) := by
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h123.1.1, hp]
          have hwv' : ∀ m ∈ nm :: wordVars, ∃ w : BitVec 64,
              (setVarHOLFinite nm (.val (.word wi)) s).locals.lookup m = some (.val (.word w)) := by
            intro m hm
            by_cases hmn : m = nm
            · subst hmn; exact ⟨wi, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
            · have hm_old : m ∈ wordVars := by simp [hmn] at hm; exact hm
              obtain ⟨w, hw⟩ := hwv m hm_old
              exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hmn, hw]⟩
          have ih := checkWordStoresLocal_sound ptrVar sz hsz (nm :: wordVars) b h123.2
            (setVarHOLFinite nm (.val (.word wi)) s) p hc (guestInv_setVar nm _ s hG) hp' hwv'
          refine ⟨(((ByteEff.refl s _).locals_clock _ _).trans ih.1).locals_clock _ _, fun h => ?_⟩
          dsimp only at h ⊢
          obtain ⟨hp_post, hwv_post⟩ := ih.2 h
          refine ⟨by rw [resVarEq_lookup_ne _ nm ptrVar _ (Ne.symm h123.1.1), hp_post], fun m hm => ?_⟩
          by_cases hmn : m = nm
          · subst hmn
            obtain ⟨w0, hw0⟩ := hwv m hm
            exact ⟨w0, by simp [HolFiniteMapExact.resVarEq, hw0, HolFiniteMapExact.updateEq, FUPDATE_HOL]⟩
          · obtain ⟨w', hw'⟩ := hwv_post m (List.mem_cons_of_mem _ hm)
            exact ⟨w', by rw [resVarEq_lookup_ne _ nm m _ hmn, hw']⟩
        · exact ⟨ByteEff.refl s _, by simp⟩
  | seq a b =>
    have h12 : checkWordStoresLocal ptrVar sz wordVars a = true ∧
        checkWordStoresLocal ptrVar sz wordVars b = true := by
      simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
    have rem := evaluateHOLFiniteState_clock_le s a
    have iha := checkWordStoresLocal_sound ptrVar sz hsz wordVars a h12.1 s p hc hG hp hwv
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hra : evaluateHOLFiniteState s a with ⟨r1, m⟩
    rw [hra] at iha rem
    cases r1 with
    | none =>
      have mclk : m.clock ≤ s.clock := rem
      obtain ⟨hpm, hwvm⟩ := iha.2 (Or.inl rfl)
      have hGm := guestInv_congr iha.1.code iha.1.memaddrs iha.1.shMemaddrs iha.1.baseAddr hG
      have ihb := checkWordStoresLocal_sound ptrVar sz hsz wordVars b h12.2 m p (iha.1.code.trans hc) hGm hpm hwvm
      exact ⟨iha.1.trans ihb.1, ihb.2⟩
    | some _ => exact iha
  | ite c a b =>
    have h12 : checkWordStoresLocal ptrVar sz wordVars a = true ∧
        checkWordStoresLocal ptrVar sz wordVars b = true := by
      simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact checkWordStoresLocal_sound ptrVar sz hsz wordVars b h12.2 s p hc hG hp hwv
      · exact checkWordStoresLocal_sound ptrVar sz hsz wordVars a h12.1 s p hc hG hp hwv
    · exact ⟨ByteEff.refl s _, by simp⟩
  | «while» c b =>
    have hb : checkWordStoresLocal ptrVar sz wordVars b = true := by
      simpa [shape, checkWordStoresLocal] using hok
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact ⟨(ByteEff.refl s _).locals_clock _ _, by simp⟩
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by simp only [decClockHOLFinite]; omega
          dsimp only; rw [fixClockHOLFinite_evaluateState]
          have hGd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hG
          have ih1 := checkWordStoresLocal_sound ptrVar sz hsz wordVars b hb (decClockHOLFinite s) p hc hGd hp hwv
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) b
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) b with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
          have heff1 : ByteEff s mid [(p.toNat, sz)] := ((ByteEff.refl s _).locals_clock _ _).trans ih1.1
          have hGm : GuestInv mid := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hG
          cases r1 with
          | none =>
            obtain ⟨hpm, hwvm⟩ := ih1.2 (Or.inl rfl)
            have ihw := checkWordStoresLocal_sound ptrVar sz hsz wordVars (.while c b)
              (by simpa [checkWordStoresLocal] using hb) mid p (heff1.code.trans hc) hGm hpm hwvm
            exact ⟨heff1.trans ihw.1, ihw.2⟩
          | some res =>
            cases res with
            | «continue» =>
              obtain ⟨hpm, hwvm⟩ := ih1.2 (Or.inr (Or.inr rfl))
              have ihw := checkWordStoresLocal_sound ptrVar sz hsz wordVars (.while c b)
                (by simpa [checkWordStoresLocal] using hb) mid p (heff1.code.trans hc) hGm hpm hwvm
              exact ⟨heff1.trans ihw.1, ihw.2⟩
            | «break» => exact ⟨heff1, fun _ => ih1.2 (Or.inr (Or.inl rfl))⟩
            | _ => exact ⟨heff1, by simp⟩
      · exact ⟨ByteEff.refl s _, fun _ => ⟨hp, hwv⟩⟩
    · exact ⟨ByteEff.refl s _, by simp⟩
  | store dst vexp =>
    have hloc_st := (evaluate_store_control_frame s dst vexp).2.1
    refine ⟨?_, fun _ => by rw [hloc_st]; exact ⟨hp, hwv⟩⟩
    cases dst with
    | var vk nm =>
      cases vk with
      | global => simp [shape, checkWordStoresLocal] at hok
      | «local» =>
        have h123 : (nm = ptrVar ∧ 8 ≤ sz) ∧ isGuaranteedWordExp wordVars vexp = true := by
          simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
        rcases h123 with ⟨⟨rfl, hsz8⟩, hv_ok⟩
        exact (byteEff_store_one hG (.var .local nm) vexp
          (eval_isGuaranteedWordExp s wordVars hwv vexp hv_ok)
          (fun x hx _ => by
            simp [evalHOLExact, hp] at hx; subst hx
            exact ⟨(p.toNat, sz), List.mem_singleton.2 rfl, le_rfl, by omega⟩)).1
    | op bop args =>
      cases bop <;> try (simp [shape, checkWordStoresLocal] at hok)
      rcases args with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> try (simp [shape, checkWordStoresLocal] at hok)
      cases e1 with
      | var vk1 nm1 =>
        cases vk1 <;> try (simp [shape, checkWordStoresLocal] at hok)
        cases e2 with
        | const off =>
          have h123 : (nm1 = ptrVar ∧ off.toNat + 8 ≤ sz) ∧ isGuaranteedWordExp wordVars vexp = true := by
            simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
          rcases h123 with ⟨⟨rfl, hoff⟩, hv_ok⟩
          refine (byteEff_store_one hG (.op .add [.var .local nm1, .const off]) vexp
            (eval_isGuaranteedWordExp s wordVars hwv vexp hv_ok) (fun x hx hdom => ?_)).1
          simp [evalHOLExact, evalListHOLExact, hp, valueIsWord, valueWord, wordOpHOL, wordOp] at hx
          subst hx
          rw [hG.memaddrs, ordinaryDomain_iff] at hdom
          have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
          have hp_lt := p.isLt; have hoff_lt := off.isLt
          have hnw : p.toNat + off.toNat < 2 ^ 64 := by
            by_contra hge
            have : (p + off).toNat = p.toNat + off.toNat - 2 ^ 64 := by rw [BitVec.toNat_add]; omega
            omega
          have hadd : (p + off).toNat = p.toNat + off.toNat := BitVec.toNat_add_of_lt hnw
          exact ⟨(p.toNat, sz), List.mem_singleton.2 rfl, by omega, by omega⟩
        | _ => simp [shape, checkWordStoresLocal] at hok
      | _ => simp [shape, checkWordStoresLocal] at hok
    | _ => simp [shape, checkWordStoresLocal] at hok
  | _ => simp [shape, checkWordStoresLocal] at hok
termination_by (s.clock, sizeOf prog)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

theorem funByteEff_keccak_f1600 :
    FunByteEff (ofString "keccak_f1600")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), 200)]) := by
  have hlook : originalRuntimeCode.lookup (ofString "keccak_f1600") =
      some ([(ofString "stp", .one)], sourceFnBody Guest.Software.guestFn_keccak_f1600, .one) :=
    lookup_of_guestAst_getElem 101 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_keccak_f1600) rfl
  refine ⟨_, _, _, hlook, fun entry vals hc hG hl _ _ => ?_⟩
  obtain ⟨stp, rfl, hstp⟩ := lookupCode_one_word hlook hl
  exact (checkWordStoresLocal_sound (ofString "stp") 200 (by omega) []
    (sourceFnBody Guest.Software.guestFn_keccak_f1600) rfl entry stp hc hG hstp
    (fun _ h => by simp at h)).1

/-- `keccak_absorb_block(stp, blk)`: loop updates `stp + i` for `i <s 136`, then calls `keccak_f1600(stp)`. -/
private theorem absorb_loop_eff {F : Type}
    (valExp : ExpHOL 64)
    (hval : ∀ (t : PanSemStateFiniteExact 64 F) v,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (k : Nat) (s : PanSemStateFiniteExact 64 F) (stp iw : BitVec 64)
    (hk : s.clock ≤ k) (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hstp : s.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hi_bound : iw.toNat ≤ 136 ∧ iw.toNat % 8 = 0) :
    let body := ProgHOL.seq
      (.store (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))
    let lp := ProgHOL.while (.cmp .less (.var .local (ofString "i")) (.const 136)) body
    ByteEff s (evaluateHOLFiniteState s lp).2 [(stp.toNat, 200)] ∧
    ((evaluateHOLFiniteState s lp).1 = none →
      (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "stp") = some (.val (.word stp))) := by
  have hsb : 200 < sourceBase := by rw [sourceBase_val]; decide
  induction k generalizing s iw with
  | zero =>
    dsimp only; rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact ⟨(ByteEff.refl s _).locals_clock _ _, by simp⟩
        · omega
      · exact ⟨ByteEff.refl s _, fun _ => hstp⟩
    · exact ⟨ByteEff.refl s _, by simp⟩
  | succ k ih =>
    dsimp only; rw [evaluateHOLFiniteState_while_total]
    split
    · rename_i cw hcond
      split
      · rename_i hnz
        split
        · exact ⟨(ByteEff.refl s _).locals_clock _ _, by simp⟩
        · dsimp only; rw [fixClockHOLFinite_evaluateState]
          have hlt136 : iw.toNat < 136 := by
            rw [evalHOLFinite_eq_toExact] at hcond
            simp only [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL,
              holAsmSignedLess_small iw 136 (by omega) (by decide)] at hcond
            by_cases hlt : iw.toNat < (136 : BitVec 64).toNat
            · exact hlt
            · have h136_val : (136 : BitVec 64).toNat = 136 := rfl
              rw [h136_val] at hlt
              simp [hlt] at hcond; exact absurd hcond.symm hnz
          let sd := decClockHOLFinite s
          have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
          have heff_st : ByteEff sd
              (evaluateHOLFiniteState sd (.store (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp)).2
              [(stp.toNat, 200)] := by
            refine (byteEff_store_one hGd _ valExp (hval sd) (fun x hx hdom => ?_)).1
            have ex := eval_add2_locals sd _ _ stp iw hstp hi
            rw [ex] at hx; injection hx with hx; injection hx with hx; injection hx with hx; subst hx
            rw [hGd.memaddrs, ordinaryDomain_iff] at hdom
            have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
            have hs_lt := stp.isLt
            have hnw : stp.toNat + iw.toNat < 2 ^ 64 := by
              by_contra hge
              have : (stp + iw).toNat = stp.toNat + iw.toNat - 2 ^ 64 := by rw [BitVec.toNat_add]; omega
              omega
            have hadd : (stp + iw).toNat = stp.toNat + iw.toNat := BitVec.toNat_add_of_lt hnw
            exact ⟨(stp.toNat, 200), List.mem_singleton.2 rfl, by omega, by omega⟩
          have hloc_st := (evaluate_store_control_frame sd (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp).2.1
          have hclk_st := (evaluate_store_control_frame sd (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp).2.2
          rw [evaluateHOLFiniteState_seq_line780]
          rcases hst_r : evaluateHOLFiniteState sd (.store (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp) with ⟨r1, m1⟩
          rw [hst_r] at heff_st hloc_st hclk_st
          cases r1 with
          | some r1' =>
            have hcf := (evaluate_store_control_frame sd (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp).1
            rw [hst_r] at hcf
            rcases hcf with h | h <;> simp at h; subst h
            exact ⟨((ByteEff.refl s _).locals_clock _ _).trans heff_st, by simp⟩
          | none =>
            dsimp only
            have hi_m1 : m1.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hloc_st]; exact hi
            have hstp_m1 : m1.locals.lookup (ofString "stp") = some (.val (.word stp)) := by rw [hloc_st]; exact hstp
            have hasgn : evaluateHOLFiniteState m1
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])) =
                (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 8))) m1) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi_m1, wordOpHOL, wordOp,
                valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
                shapeOfHOLExact, shapeEqHOL]
            rw [hasgn]; dsimp only
            let m2 := setVarHOLFinite (ofString "i") (.val (.word (iw + 8))) m1
            have heff_m2 : ByteEff s m2 [(stp.toNat, 200)] :=
              (((ByteEff.refl s _).locals_clock _ _).trans heff_st).locals_clock _ _
            have hGm2 : GuestInv m2 := guestInv_congr heff_m2.code heff_m2.memaddrs heff_m2.shMemaddrs heff_m2.baseAddr hG
            have hstp_m2 : m2.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
              simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hstp_m1, show ofString "i" ≠ ofString "stp" by decide]
            have hi_m2 : m2.locals.lookup (ofString "i") = some (.val (.word (iw + 8))) := by
              simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hi8_le : (iw + 8).toNat ≤ 136 ∧ (iw + 8).toNat % 8 = 0 := by
              have : (iw + 8).toNat = iw.toNat + 8 := BitVec.toNat_add_of_lt (by change iw.toNat + 8 < 2 ^ 64; omega)
              omega
            have hm2_clk : m2.clock ≤ k := by
              change m1.clock ≤ k; rw [hclk_st]; change s.clock - 1 ≤ k; omega
            have ih_res := ih m2 (iw + 8) hm2_clk (heff_m2.code.trans hc) hGm2 hstp_m2 hi_m2 hi8_le
            exact ⟨heff_m2.trans ih_res.1, ih_res.2⟩
      · exact ⟨ByteEff.refl s _, fun _ => hstp⟩
    · exact ⟨ByteEff.refl s _, by simp⟩

theorem funByteEff_keccak_absorb_block :
    FunByteEff (ofString "keccak_absorb_block")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), 200)]) := by
  have hlook : originalRuntimeCode.lookup (ofString "keccak_absorb_block") =
      some ([(ofString "stp", .one), (ofString "blk", .one)],
        sourceFnBody Guest.Software.guestFn_keccak_absorb_block, .one) :=
    lookup_of_guestAst_getElem 102 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_keccak_absorb_block) rfl
  refine ⟨_, _, _, hlook, fun {F} entry vals hc hG hl hnt hres => ?_⟩
  obtain ⟨stp, blk, rfl, hstp, _⟩ := lookupCode_two_words (by decide) hlook hl
  change ByteEff entry _ [(stp.toNat, 200)]
  have hop_word : ∀ (t : PanSemStateFiniteExact 64 F) bop eL v,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (.op bop eL) = some v →
      ∃ w : BitVec 64, v = .val (.word w) :=
    fun t bop eL => eval_isGuaranteedWordExp t [] (fun _ h => by simp at h) (.op bop eL) rfl
  let vAligned : ExpHOL 64 := InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
    (Exp.op BinOp.xor
      [Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.local "stp", Exp.var VarKind.local "i"]),
       Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i"])])
  let vUnaligned : ExpHOL 64 := InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
    (Exp.op BinOp.xor
      [Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.local "stp", Exp.var VarKind.local "i"]),
       Exp.op BinOp.or
        [(Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i"]).loadByte,
         Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 1#64]).loadByte (Exp.const 8#64),
         Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 2#64]).loadByte (Exp.const 16#64),
         Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 3#64]).loadByte (Exp.const 24#64),
         Exp.shift Shift.lsl
          (Exp.op BinOp.or
            [(Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 4#64]).loadByte,
             Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 4#64, Exp.const 1#64]).loadByte (Exp.const 8#64),
             Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 4#64, Exp.const 2#64]).loadByte (Exp.const 16#64),
             Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 4#64, Exp.const 3#64]).loadByte (Exp.const 24#64)])
          (Exp.const 32#64)]])
  let lpA := ProgHOL.while (.cmp .less (.var .local (ofString "i")) (.const 136))
    (.seq (.store (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) vAligned)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
  let lpU := ProgHOL.while (.cmp .less (.var .local (ofString "i")) (.const 136))
    (.seq (.store (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) vUnaligned)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
  have hbody : sourceFnBody Guest.Software.guestFn_keccak_absorb_block =
      .dec (ofString "i") .one (.const 0)
        (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "blk"), .const 7]) (.const 0)) lpA lpU)
          (.seq (.call (some (none, none)) (ofString "keccak_f1600") [.var .local (ofString "stp")])
            (.return (.const 0)))) := rfl
  rw [hbody] at hnt hres ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
  have hev0 : @evalHOLExact 64 F _ entry.toExact (fun a => Classical.propDecidable (entry.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only at hnt hres ⊢
  rw [hev0] at hnt hres ⊢; dsimp only at hnt hres ⊢
  rw [if_pos hsh0] at hnt hres ⊢; dsimp only at hnt hres ⊢
  let si := setVarHOLFinite (ofString "i") (.val (.word 0)) entry
  have hGi : GuestInv si := guestInv_setVar _ _ entry hG
  have hstp_i : si.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hstp, show ofString "i" ≠ ofString "stp" by decide]
  have hi_i : si.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  have hite_eff : ByteEff si (evaluateHOLFiniteState si
      (.ite (.cmp .equal (.op .and [.var .local (ofString "blk"), .const 7]) (.const 0)) lpA lpU)).2 [(stp.toNat, 200)] ∧
      ((evaluateHOLFiniteState si
        (.ite (.cmp .equal (.op .and [.var .local (ofString "blk"), .const 7]) (.const 0)) lpA lpU)).1 = none →
        (evaluateHOLFiniteState si
          (.ite (.cmp .equal (.op .and [.var .local (ofString "blk"), .const 7]) (.const 0)) lpA lpU)).2.locals.lookup
          (ofString "stp") = some (.val (.word stp))) := by
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact absorb_loop_eff vUnaligned (fun t => hop_word t _ _) si.clock si stp 0 le_rfl hc hGi hstp_i hi_i ⟨by simp, by simp⟩
      · exact absorb_loop_eff vAligned (fun t => hop_word t _ _) si.clock si stp 0 le_rfl hc hGi hstp_i hi_i ⟨by simp, by simp⟩
    · exact ⟨ByteEff.refl si _, by simp⟩
  rcases h1 : evaluateHOLFiniteState si
      (.ite (.cmp .equal (.op .and [.var .local (ofString "blk"), .const 7]) (.const 0)) lpA lpU) with ⟨r1, s1⟩
  rw [h1] at hnt hres hite_eff
  have heff_e1 : ByteEff entry s1 [(stp.toNat, 200)] := ((ByteEff.refl entry _).locals_clock _ _).trans hite_eff.1
  cases r1 with
  | some _ => exact heff_e1.locals_clock _ _
  | none =>
    dsimp only at hnt hres ⊢
    have hstp_1 : s1.locals.lookup (ofString "stp") = some (.val (.word stp)) := hite_eff.2 rfl
    have hGs1 : GuestInv s1 := guestInv_congr heff_e1.code heff_e1.memaddrs heff_e1.shMemaddrs heff_e1.baseAddr hG
    have hc_s1 : s1.code = originalRuntimeCode := heff_e1.code.trans hc
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hc_f : evaluateHOLFiniteState s1
        (.call (some (none, none)) (ofString "keccak_f1600") [.var .local (ofString "stp")]) with ⟨rf, sf⟩
    rw [hc_f] at hnt hres
    have hnt_f : rf ≠ some .timeOut := by intro h; subst h; simp at hnt
    have hargs_f : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.var .local (ofString "stp")] = some [.val (.word stp)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hstp_1]
    have heff_f : ByteEff s1 sf [(stp.toNat, 200)] := by
      have := call0_byteEff funByteEff_keccak_f1600 s1 _ [(stp.toNat, 200)] hc_s1 hGs1
        (fun vs hvs i hi _ => by
          rw [hargs_f] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat] at hi; subst hi
          exact ⟨(stp.toNat, 200), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
        (by rw [hc_f]; exact hnt_f)
        (by rw [hc_f]; cases rf with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
      rwa [hc_f] at this
    cases rf with
    | some _ => exact (heff_e1.trans heff_f).locals_clock _ _
    | none => exact ((heff_e1.trans heff_f).trans (byteEff_return sf _ _)).locals_clock _ _

private theorem call0_any_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname : MlS) (args : List (ExpHOL 64))
    (hnone : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_call]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · rfl
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨b, c, r⟩
    · rfl
    · dsimp only
      by_cases hclk : s.clock = 0
      · exfalso
        rw [evaluateHOLFiniteState_call, hargs] at hnone
        simp [hl, hclk] at hnone
      · rw [if_neg hclk]
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s c) b with ⟨rb, pb⟩
        cases rb with
        | none =>
          exfalso; rw [evaluateHOLFiniteState_call, hargs] at hnone
          simp [hl, hclk, hb] at hnone
        | some rb' =>
          cases rb' with
          | returned rv =>
            dsimp only
            split
            · rfl
            · rename_i hbad
              exfalso; rw [evaluateHOLFiniteState_call, hargs] at hnone
              simp [hl, hclk, hb, hbad] at hnone
          | _ =>
            exfalso; rw [evaluateHOLFiniteState_call, hargs] at hnone
            simp [hl, hclk, hb] at hnone

private theorem eval_cmp_notLower_i136 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n iw cw : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hev : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 136])) =
      some (.val (.word cw))) :
    cw = if (iw + 136).toNat ≤ n.toNat then 1 else 0 := by
  rw [evalHOLFinite_eq_toExact] at hev
  simp [evalHOLExact, evalListHOLExact, hn, hi, valueIsWord, valueWord, wordOpHOL, wordOp,
    Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, BitVec.le_def] at hev
  by_cases hle : (iw + 136).toNat ≤ n.toNat
  · have hnl : ¬ (n.toNat < (iw + 136).toNat) := by omega
    simp [hle, hnl] at hev ⊢; exact hev.symm
  · have hl : n.toNat < (iw + 136).toNat := by omega
    simp [hle, hl] at hev ⊢; exact hev.symm

private theorem call0_ne_break_continue {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some .break ∧
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some .continue := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨b, c, r⟩
    · simp
    · dsimp only
      by_cases hclk : s.clock = 0
      · simp [hclk]
      · rw [if_neg hclk]
        rcases evaluateHOLFiniteState (callEntryStateHOLFinite s c) b with ⟨rb, pb⟩
        cases rb with
        | none => simp
        | some rb' =>
          cases rb' <;> dsimp only
          all_goals try (split <;> simp)
          all_goals simp

private theorem keccak_main_loop_eff {F : Type}
    (k : Nat) (s : PanSemStateFiniteExact 64 F) (stp p n iw : BitVec 64)
    (hk : s.clock ≤ k) (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hstp : s.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hle : iw.toNat ≤ n.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.while (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 136]))
        (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
            [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136]))))).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s
      (.while (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 136]))
        (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
            [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136]))))).1 = none ∨
      Resumes (evaluateHOLFiniteState s
        (.while (.cmp .notLower (.var .local (ofString "n"))
            (.op .add [.var .local (ofString "i"), .const 136]))
          (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
              [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136]))))).1) :
    let out := evaluateHOLFiniteState s
      (.while (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 136]))
        (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
            [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136]))))
    ByteEff s out.2 [(stp.toNat, 200)] ∧
    (out.1 = none →
      (∀ v, v ≠ ofString "i" → out.2.locals.lookup v = s.locals.lookup v) ∧
      ∃ iw' : BitVec 64,
        out.2.locals.lookup (ofString "i") = some (.val (.word iw')) ∧
        (n - iw').toNat < 136) := by
  induction k generalizing s iw with
  | zero =>
    dsimp only at hnt hor ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt hor ⊢
    rcases hc_ev : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 136])) with _ | cv
    · simp only [hc_ev] at hor ⊢; exact ⟨ByteEff.refl s _, by simp⟩
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try (simp only [hc_ev] at hor ⊢; exact ⟨ByteEff.refl s _, by simp⟩)
      simp only [hc_ev] at hnt hor ⊢
      by_cases hnz : cw ≠ 0
      · have hz : s.clock = 0 := by omega
        rw [if_pos hnz, if_pos hz] at hnt
        exact absurd rfl hnt
      · have hcw0 : cw = 0 := Classical.not_not.1 hnz
        subst hcw0
        rw [if_neg (by simp)]
        refine ⟨ByteEff.refl s _, fun _ => ⟨fun _ _ => rfl, iw, hi, ?_⟩⟩
        have hcw_eq := eval_cmp_notLower_i136 s n iw 0 hn hi hc_ev
        have hnlt := n.isLt; have hilt := iw.isLt
        have hsub : (n - iw).toNat = n.toNat - iw.toNat := by rw [BitVec.toNat_sub]; omega
        by_cases hlt136 : (iw + 136).toNat ≤ n.toNat
        · rw [if_pos hlt136] at hcw_eq; cases hcw_eq
        · by_cases hwrap : iw.toNat + 136 < 2 ^ 64
          · have : (iw + 136).toNat = iw.toNat + 136 := BitVec.toNat_add_of_lt hwrap
            omega
          · omega
  | succ k ih =>
    dsimp only at hnt hor ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt hor ⊢
    rcases hc_ev : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 136])) with _ | cv
    · simp only [hc_ev] at hor ⊢; exact ⟨ByteEff.refl s _, by simp⟩
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try (simp only [hc_ev] at hor ⊢; exact ⟨ByteEff.refl s _, by simp⟩)
      simp only [hc_ev] at hnt hor ⊢
      by_cases hnz : cw ≠ 0
      · rw [if_pos hnz] at hnt hor ⊢
        by_cases hz : s.clock = 0
        · rw [if_pos hz] at hnt; exact absurd rfl hnt
        · rw [if_neg hz] at hnt hor ⊢
          rw [fixClockHOLFinite_evaluateState] at hnt hor ⊢
          have hik_le : (iw + 136).toNat ≤ n.toNat := by
            have hcw_eq := eval_cmp_notLower_i136 s n iw cw hn hi hc_ev
            by_cases hle' : (iw + 136).toNat ≤ n.toNat
            · exact hle'
            · rw [if_neg hle'] at hcw_eq; exact absurd hcw_eq hnz
          let sd := decClockHOLFinite s
          have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
          rw [evaluateHOLFiniteState_seq_line780] at hnt hor ⊢
          rcases hcall : evaluateHOLFiniteState (decClockHOLFinite s)
              (.call (some (none, none)) (ofString "keccak_absorb_block")
                [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]]) with ⟨rc, m1⟩
          have hnt' := hnt; have hor' := hor
          rw [hcall] at hnt' hor'
          have hnt_c : rc ≠ some .timeOut := by
            intro h; subst h; simp at hnt'
          have hnbc := call0_ne_break_continue (decClockHOLFinite s) (ofString "keccak_absorb_block")
            [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]]
          rw [hcall] at hnbc
          have hor_c : rc = none ∨ Resumes rc := by
            cases rc with
            | none => exact Or.inl rfl
            | some rc' =>
              cases rc' with
              | returned v => exact Or.inr (Or.inl ⟨v, rfl⟩)
              | exception e v =>
                rcases hor' with h | ⟨_, h⟩ | ⟨e', v', h, hne⟩
                · simp at h
                · simp at h
                · simp at h; obtain ⟨rfl, _⟩ := h; exact Or.inr (Or.inr ⟨e, v, rfl, hne⟩)
              | «break» => exact absurd rfl hnbc.1
              | «continue» => exact absurd rfl hnbc.2
              | error | timeOut | finalFfi _ =>
                exfalso; rcases hor' with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          have hargs_c : evalListHOLFinite sd (h := fun a => Classical.propDecidable (sd.memaddrs a))
              [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]] =
              some [.val (.word stp), .val (.word (p + iw))] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, sd, decClockHOLFinite, hstp, hp, hi,
              valueIsWord, valueWord, wordOpHOL, wordOp]
          have heff_c : ByteEff sd m1 [(stp.toNat, 200)] := by
            have := call0_byteEff funByteEff_keccak_absorb_block sd _ [(stp.toNat, 200)] hc hGd
              (fun vs hvs i hi_in _ => by
                rw [hargs_c] at hvs; injection hvs with hvs; subst hvs
                simp [valWordNat] at hi_in; subst hi_in
                exact ⟨(stp.toNat, 200), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
              (by dsimp only [sd]; rw [hcall]; exact hnt_c)
              (by dsimp only [sd]; rw [hcall]; exact hor_c)
            dsimp only [sd] at this; rwa [hcall] at this
          have hclk_c := evaluateHOLFiniteState_clock_le (decClockHOLFinite s)
            (.call (some (none, none)) (ofString "keccak_absorb_block")
              [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
          rw [hcall] at hclk_c
          cases rc with
          | some rc' =>
            cases rc' with
            | «break» => exact absurd rfl hnbc.1
            | «continue» => exact absurd rfl hnbc.2
            | _ => exact ⟨((ByteEff.refl s _).locals_clock _ _).trans heff_c, by simp⟩
          | none =>
            have hloc_m1 : m1.locals = sd.locals := by
              have := call0_any_locals (decClockHOLFinite s) (ofString "keccak_absorb_block")
                [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]]
                (by rw [hcall])
              rwa [hcall] at this
            dsimp only at hnt' hor' ⊢
            have hi_m1 : m1.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hloc_m1]; exact hi
            have hasgn : evaluateHOLFiniteState m1
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136])) =
                (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 136))) m1) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi_m1, wordOpHOL, wordOp,
                valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
                shapeOfHOLExact, shapeEqHOL]
            rw [hasgn] at hnt' hor' ⊢
            dsimp only at hnt' hor' ⊢
            let m2 := setVarHOLFinite (ofString "i") (.val (.word (iw + 136))) m1
            have heff_m2 : ByteEff s m2 [(stp.toNat, 200)] :=
              (((ByteEff.refl s _).locals_clock _ _).trans heff_c).locals_clock _ _
            have hGm2 : GuestInv m2 := guestInv_congr heff_m2.code heff_m2.memaddrs heff_m2.shMemaddrs heff_m2.baseAddr hG
            have hm2_other : ∀ v, v ≠ ofString "i" → m2.locals.lookup v = s.locals.lookup v := by
              intro v hv
              have hv' : (ofString "i" == v) = false := beq_eq_false_iff_ne.2 (Ne.symm hv)
              simp only [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv',
                Bool.false_eq_true, ↓reduceIte, hloc_m1]
              rfl
            have hi_m2 : m2.locals.lookup (ofString "i") = some (.val (.word (iw + 136))) := by
              simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hm2_clk : m2.clock ≤ k := by change m1.clock ≤ k; change m1.clock ≤ s.clock - 1 at hclk_c; omega
            have ih_res := ih m2 (iw + 136) hm2_clk (heff_m2.code.trans hc) hGm2
              (by rw [hm2_other _ (by decide)]; exact hstp)
              (by rw [hm2_other _ (by decide)]; exact hp)
              (by rw [hm2_other _ (by decide)]; exact hn)
              hi_m2 hik_le hnt' hor'
            refine ⟨heff_m2.trans ih_res.1, fun hnone => ?_⟩
            obtain ⟨ho, hr⟩ := ih_res.2 hnone
            exact ⟨fun v hv => (ho v hv).trans (hm2_other v hv), hr⟩
      · have hcw0 : cw = 0 := Classical.not_not.1 hnz
        subst hcw0
        rw [if_neg (by simp)]
        refine ⟨ByteEff.refl s _, fun _ => ⟨fun _ _ => rfl, iw, hi, ?_⟩⟩
        have hcw_eq := eval_cmp_notLower_i136 s n iw 0 hn hi hc_ev
        have hnlt := n.isLt; have hilt := iw.isLt
        have hsub : (n - iw).toNat = n.toNat - iw.toNat := by rw [BitVec.toNat_sub]; omega
        by_cases hlt136 : (iw + 136).toNat ≤ n.toNat
        · rw [if_pos hlt136] at hcw_eq; cases hcw_eq
        · by_cases hwrap : iw.toNat + 136 < 2 ^ 64
          · have : (iw + 136).toNat = iw.toNat + 136 := BitVec.toNat_add_of_lt hwrap
            omega
          · omega

theorem call0_two_word_resumes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname p1 p2 : MlS) (body : ProgHOL 64) (a1 a2 : ExpHOL 64) (w1 w2 : BitVec 64)
    (hne : p1 ≠ p2)
    (hc : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, .one))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [a1, a2] =
      some [.val (.word w1), .val (.word w2)])
    (hor : (evaluateHOLFiniteState s (.call (some (none, none)) fname [a1, a2])).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname [a1, a2])).1) :
    Resumes (evaluateHOLFiniteState
      (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))))
      body).1 := by
  rw [evaluateHOLFiniteState_call, ha] at hor
  dsimp only at hor
  have hl := pan_two_word_lookup s.code.lookup fname p1 p2 body w1 w2 hne (by rw [hc]; exact hlook)
  rw [hl] at hor; dsimp only at hor
  split at hor
  · rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
  · rcases hb : evaluateHOLFiniteState
        (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))))
        body with ⟨rb, pb⟩
    rw [hb] at hor ⊢
    cases rb with
    | none => rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    | some rb' =>
      cases rb' with
      | returned rv => exact Or.inl ⟨rv, rfl⟩
      | exception eid ev =>
        rcases hor with h | ⟨_, h⟩ | ⟨e', v', h, hne_t⟩
        · simp at h
        · simp at h
        · simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨eid, ev, rfl, hne_t⟩
      | _ => rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

private theorem keccak_out_ite_eff {F : Type}
    (s : PanSemStateFiniteExact 64 F) (out stp : BitVec 64) (Rl : List Ivl)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hstp : s.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (hout_in : ∀ i ∈ [(out.toNat, 32)], 0 < i.2 → ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hnt : (evaluateHOLFiniteState s
      (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0))
        (.seq (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp"))))
          (.seq (.store (.op .add [.var .local (ofString "out"), .const 8])
              (.load .one (.op .add [.var .local (ofString "stp"), .const 8])))
            (.seq (.store (.op .add [.var .local (ofString "out"), .const 16])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 16])))
              (.store (.op .add [.var .local (ofString "out"), .const 24])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 24]))))))
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32]))).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s
      (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0))
        (.seq (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp"))))
          (.seq (.store (.op .add [.var .local (ofString "out"), .const 8])
              (.load .one (.op .add [.var .local (ofString "stp"), .const 8])))
            (.seq (.store (.op .add [.var .local (ofString "out"), .const 16])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 16])))
              (.store (.op .add [.var .local (ofString "out"), .const 24])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 24]))))))
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32]))).1 = none ∨
      Resumes (evaluateHOLFiniteState s
        (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0))
          (.seq (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp"))))
            (.seq (.store (.op .add [.var .local (ofString "out"), .const 8])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 8])))
              (.seq (.store (.op .add [.var .local (ofString "out"), .const 16])
                  (.load .one (.op .add [.var .local (ofString "stp"), .const 16])))
                (.store (.op .add [.var .local (ofString "out"), .const 24])
                  (.load .one (.op .add [.var .local (ofString "stp"), .const 24]))))))
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32]))).1) :
    ByteEff s (evaluateHOLFiniteState s
      (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0))
        (.seq (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp"))))
          (.seq (.store (.op .add [.var .local (ofString "out"), .const 8])
              (.load .one (.op .add [.var .local (ofString "stp"), .const 8])))
            (.seq (.store (.op .add [.var .local (ofString "out"), .const 16])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 16])))
              (.store (.op .add [.var .local (ofString "out"), .const 24])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 24]))))))
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32]))).2 Rl := by
  rw [evaluateHOLFiniteState_ite] at hnt hor ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0)) with _ | cv
  · exact ByteEff.refl s Rl
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try exact ByteEff.refl s Rl
    have hnt' := hnt; have hor' := hor
    rw [hev] at hnt' hor'
    dsimp only at hnt' hor' ⊢
    by_cases h0 : cw = 0
    · rw [if_pos h0] at hnt' hor' ⊢
      have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
          [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32] =
          some [.val (.word out), .val (.word stp), .val (.word 32)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hout, hstp]
      exact call0_byteEff funByteEff_memcpy s _ Rl hc hG
        (fun vs hvs i hi hp => by
          rw [hargs] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat] at hi; subst hi
          exact hout_in (out.toNat, 32) (List.mem_singleton.2 rfl) hp)
        hnt' hor'
    · rw [if_neg h0]
      exact (checkWordStoresLocal_sound (ofString "out") 32 (by omega) [] _ rfl s out hc hG hout
        (fun _ h => by simp at h)).1.mono hout_in

theorem funByteEff_keccak256 :
    FunByteEff (ofString "keccak256")
      (fun vals G =>
        [globBufIvl G "keccak_st" 200, globBufIvl G "keccak_pad" 136,
         (valWordNat (vals[2]?.getD (.rStruct [])), 32)]) := by
  have hlook : originalRuntimeCode.lookup (ofString "keccak256") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_keccak256, .one) :=
    lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_keccak256) rfl
  have hlook_mz : originalRuntimeCode.lookup (ofString "memzero") =
      some ([(ofString "dst", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memzero, .one) := lookup_memzero
  refine ⟨_, _, _, hlook, fun {F} entry vals hc hG hl hnt hres => ?_⟩
  obtain ⟨p, n, out, rfl, hp0, hn0, hout0⟩ :=
    lookupCode_three_words (by decide) (by decide) (by decide) hlook hl
  let Rl := [globBufIvl entry.globals "keccak_st" 200,
    globBufIvl entry.globals "keccak_pad" 136, (out.toNat, 32)]
  change ByteEff entry (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_keccak256)).2 Rl
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have seq_step : ∀ (t : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64),
      (evaluateHOLFiniteState t (.seq a b)).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t (.seq a b)).1 = none ∨ Resumes (evaluateHOLFiniteState t (.seq a b)).1) →
      (evaluateHOLFiniteState t a).1 ≠ some .timeOut ∧
      ((evaluateHOLFiniteState t a).1 = none ∨ Resumes (evaluateHOLFiniteState t a).1) := by
    intro t a b h1 h2
    rw [evaluateHOLFiniteState_seq_line780] at h1 h2
    rcases ha : evaluateHOLFiniteState t a with ⟨ra, ma⟩
    rw [ha] at h1 h2
    refine ⟨fun h => by subst h; simp at h1, ?_⟩
    cases ra with
    | none => exact Or.inl rfl
    | some _ =>
      right
      rcases h2 with h | h
      · simp at h
      · exact h
  -- Unfold outer `dec "stp"`
  have hbody : sourceFnBody Guest.Software.guestFn_keccak256 =
      .dec (ofString "stp") .one (.var .global (ofString "keccak_st"))
        (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const 200])
          (.dec (ofString "i") .one (.const 0)
            (.seq (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 136]))
                (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
                    [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
                  (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136]))))
              (.dec (ofString "rem") .one (.op .sub [.var .local (ofString "n"), .var .local (ofString "i")])
                (.seq (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "keccak_pad"), .const 136])
                  (.seq (.call (some (none, none)) (ofString "memcpy")
                      [.var .global (ofString "keccak_pad"),
                       .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
                       .var .local (ofString "rem")])
                    (.seq (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")]) (.const 1))
                      (.seq (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .const 135])
                          (.op .or [.loadByte (.op .add [.var .global (ofString "keccak_pad"), .const 135]), .const 128]))
                        (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
                            [.var .local (ofString "stp"), .var .global (ofString "keccak_pad")])
                          (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0))
                              (.seq (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp"))))
                                (.seq (.store (.op .add [.var .local (ofString "out"), .const 8])
                                    (.load .one (.op .add [.var .local (ofString "stp"), .const 8])))
                                  (.seq (.store (.op .add [.var .local (ofString "out"), .const 16])
                                      (.load .one (.op .add [.var .local (ofString "stp"), .const 16])))
                                    (.store (.op .add [.var .local (ofString "out"), .const 24])
                                      (.load .one (.op .add [.var .local (ofString "stp"), .const 24]))))))
                              (.call (some (none, none)) (ofString "memcpy")
                                [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32]))
                            (.return (.const 0)))))))))))) := rfl
  rw [hbody] at hnt hres ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
  dsimp only at hnt hres ⊢
  rcases hgst : entry.globals.lookup (ofString "keccak_st") with _ | vst
  · simp only [evalHOLExact, hgst]; exact ByteEff.refl entry Rl
  · rcases vst with ⟨⟨stp⟩⟩ | _ | _ <;>
      try (simp only [evalHOLExact, hgst, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hres ⊢
           exact ByteEff.refl entry Rl)
    simp only [evalHOLExact, hgst, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt hres ⊢
    have hsb_pos : 0 < sourceBase := by rw [sourceBase_val]; decide
    let s0 := setVarHOLFinite (ofString "stp") (.val (.word stp)) entry
    have hGs0 : GuestInv s0 := guestInv_setVar _ _ entry hG
    have hstp_0 : s0.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_0 : s0.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp0, show ofString "stp" ≠ ofString "p" by decide]
    have hn_0 : s0.locals.lookup (ofString "n") = some (.val (.word n)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn0, show ofString "stp" ≠ ofString "n" by decide]
    have hout_0 : s0.locals.lookup (ofString "out") = some (.val (.word out)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hout0, show ofString "stp" ≠ ofString "out" by decide]
    -- Step 1: `memzero(stp, 200)`
    obtain ⟨hnt1, hor1⟩ := seq_step s0 _ _ hnt (Or.inr hres)
    have hargs1 : evalListHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
        [.var .local (ofString "stp"), .const 200] = some [.val (.word stp), .val (.word 200)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hstp_0]
    have hres_mz1 := call0_two_word_resumes s0 _ _ _ _ _ _ stp 200 (by decide) hc hlook_mz hargs1 hor1
    let c0 := callEntryStateHOLFinite s0
      ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word stp))).update (ofString "n", .val (.word 200)))
    have hstp_dom := (memzero_body_eff c0 stp 200 hc (guestInv_callEntry s0 _ hGs0)
      (by simp [c0, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "n" ≠ ofString "dst" by decide])
      (by simp [c0, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      hres_mz1).2 (by decide)
    have hstp_nz : stp.toNat ≠ 0 := by omega
    have hstp_sub : ∀ i ∈ [(stp.toNat, 200)], 0 < i.2 → ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2 := by
      intro i hi _
      simp at hi; subst hi
      refine ⟨globBufIvl entry.globals "keccak_st" 200, List.mem_cons_self, ?_, ?_⟩ <;>
        simp [globBufIvl, globMapN, hgst, hstp_nz]
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hm1 : evaluateHOLFiniteState s0
        (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const 200]) with ⟨r1, s1⟩
    rw [hm1] at hnt hres
    have heff1 : ByteEff s0 s1 Rl := by
      have := call0_byteEff funByteEff_memzero s0 _ Rl hc hGs0
        (fun vs hvs i hi hp => by
          rw [hargs1] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat] at hi; subst hi
          exact hstp_sub (stp.toNat, 200) (List.mem_singleton.2 rfl) hp)
        hnt1 hor1
      rwa [hm1] at this
    have heff_e1 : ByteEff entry s1 Rl := ((ByteEff.refl entry Rl).locals_clock _ _).trans heff1
    cases r1 with
    | some _ => exact heff_e1.locals_clock _ _
    | none =>
      have hs1_loc : s1.locals = s0.locals := by
        have := call0_any_locals s0 _ _ (by rw [hm1])
        rwa [hm1] at this
      have hGs1 : GuestInv s1 := guestInv_congr heff_e1.code heff_e1.memaddrs heff_e1.shMemaddrs heff_e1.baseAddr hG
      have hc_s1 : s1.code = originalRuntimeCode := heff_e1.code.trans hc
      -- Step 2: `dec "i" 0`
      dsimp only at hnt hres ⊢
      rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
      simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt hres ⊢
      let s2 := setVarHOLFinite (ofString "i") (.val (.word 0)) s1
      have hGs2 : GuestInv s2 := guestInv_setVar _ _ s1 hGs1
      have hstp_2 : s2.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
        simp only [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "stp" by decide, ↓reduceIte, hs1_loc]; exact hstp_0
      have hp_2 : s2.locals.lookup (ofString "p") = some (.val (.word p)) := by
        simp only [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "p" by decide, ↓reduceIte, hs1_loc]; exact hp_0
      have hn_2 : s2.locals.lookup (ofString "n") = some (.val (.word n)) := by
        simp only [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "n" by decide, ↓reduceIte, hs1_loc]; exact hn_0
      have hout_2 : s2.locals.lookup (ofString "out") = some (.val (.word out)) := by
        simp only [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "out" by decide, ↓reduceIte, hs1_loc]; exact hout_0
      have hi_2 : s2.locals.lookup (ofString "i") = some (.val (.word 0)) := by
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      -- Step 3: `while (n >=u i + 136)`
      obtain ⟨hnt_w, hor_w⟩ := seq_step s2 _ _ hnt (Or.inr hres)
      have hw_eff := keccak_main_loop_eff s2.clock s2 stp p n 0 le_rfl hc_s1 hGs2
        hstp_2 hp_2 hn_2 hi_2 (Nat.zero_le _) hnt_w hor_w
      rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
      rcases hw : evaluateHOLFiniteState s2 _ with ⟨rw_res, s3⟩
      rw [hw] at hnt hres hw_eff
      have heff_e3 : ByteEff entry s3 Rl :=
        (heff_e1.locals_clock _ _).trans (hw_eff.1.mono hstp_sub)
      cases rw_res with
      | some _ => exact (heff_e3.locals_clock _ _).locals_clock _ _
      | none =>
        obtain ⟨hs3_other, iw, hi_3, hrem_lt⟩ := hw_eff.2 rfl
        have hGs3 : GuestInv s3 := guestInv_congr heff_e3.code heff_e3.memaddrs heff_e3.shMemaddrs heff_e3.baseAddr hG
        have hc_s3 : s3.code = originalRuntimeCode := heff_e3.code.trans hc
        have hglob_s3 : s3.globals = entry.globals := heff_e3.globals
        have hstp_3 : s3.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
          rw [hs3_other _ (by decide)]; exact hstp_2
        have hp_3 : s3.locals.lookup (ofString "p") = some (.val (.word p)) := by
          rw [hs3_other _ (by decide)]; exact hp_2
        have hn_3 : s3.locals.lookup (ofString "n") = some (.val (.word n)) := by
          rw [hs3_other _ (by decide)]; exact hn_2
        have hout_3 : s3.locals.lookup (ofString "out") = some (.val (.word out)) := by
          rw [hs3_other _ (by decide)]; exact hout_2
        -- Step 4: `dec "rem" (n - i)`
        dsimp only at hnt hres ⊢
        rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
        have hi_3' : s3.locals.lookup (ofString "i") = some (.val (.word iw)) := hi_3
        have hev_rem : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
            (.op .sub [.var .local (ofString "n"), .var .local (ofString "i")]) = some (.val (.word (n - iw))) := by
          simp [evalHOLExact, evalListHOLExact, hn_3, hi_3', valueIsWord, valueWord, wordOpHOL, wordOp]
        simp only [hev_rem, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt hres ⊢
        let remw := n - iw
        let s4 := setVarHOLFinite (ofString "rem") (.val (.word remw)) s3
        have hGs4 : GuestInv s4 := guestInv_setVar _ _ s3 hGs3
        have hstp_4 : s4.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
          simp only [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rem" ≠ ofString "stp" by decide, ↓reduceIte]; exact hstp_3
        have hp_4 : s4.locals.lookup (ofString "p") = some (.val (.word p)) := by
          simp only [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rem" ≠ ofString "p" by decide, ↓reduceIte]; exact hp_3
        have hi_4 : s4.locals.lookup (ofString "i") = some (.val (.word iw)) := by
          simp only [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rem" ≠ ofString "i" by decide, ↓reduceIte]; exact hi_3'
        have hout_4 : s4.locals.lookup (ofString "out") = some (.val (.word out)) := by
          simp only [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rem" ≠ ofString "out" by decide, ↓reduceIte]; exact hout_3
        have hrem_4 : s4.locals.lookup (ofString "rem") = some (.val (.word remw)) := by
          simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        -- Step 5: `memzero(keccak_pad, 136)`
        obtain ⟨hnt_p1, hor_p1⟩ := seq_step s4 _ _ hnt (Or.inr hres)
        have hnot_err : ∀ r, r = some .error → ¬ (r = none ∨ Resumes r) := by
          rintro _ rfl (h | ⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
        rcases hgpad : entry.globals.lookup (ofString "keccak_pad") with _ | vpad
        · exfalso
          apply hnot_err _ _ hor_p1
          rw [evaluateHOLFiniteState_call]
          have hgpad4 : s4.globals.lookup (ofString "keccak_pad") = none := by
            change s3.globals.lookup _ = none; rw [hglob_s3]; exact hgpad
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hgpad4]
        · have hpad_w : ∃ pad : BitVec 64, vpad = .val (.word pad) := by
            by_cases hsh1 : shapeEqHOL .one (shapeOfHOLExact vpad) = true
            · cases vpad with
              | val wlab =>
                cases wlab with
                | word pad => exact ⟨pad, rfl⟩
              | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at hsh1
              | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at hsh1
            · exfalso
              apply hnot_err _ _ hor_p1
              rw [evaluateHOLFiniteState_call]
              have hgpad4 : s4.globals.lookup (ofString "keccak_pad") = some vpad := by
                change s3.globals.lookup _ = _; rw [hglob_s3]; exact hgpad
              have hargs_bad : evalListHOLFinite s4 (h := fun a => Classical.propDecidable (s4.memaddrs a))
                  [.var .global (ofString "keccak_pad"), .const 136] =
                  some [vpad, .val (.word 136)] := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hgpad4]
              rw [hargs_bad]; dsimp only
              have hl_bad : lookupCodeHOLFinite s4.code.lookup (ofString "memzero") [vpad, .val (.word 136)] = none := by
                apply Option.eq_none_iff_forall_not_mem.2
                intro ⟨b, c, r⟩ hmem
                have hx := lookupCodeHOLFinite_eq_some s4.code.lookup _ _ b c r hmem
                have hc4 : s4.code = originalRuntimeCode := hc_s3
                rw [hc4] at hx
                simp [lookupCodeHOLExact, hlook_mz] at hx
                exact hsh1 hx.1.2.1
              rw [hl_bad]
          obtain ⟨pad, rfl⟩ := hpad_w
          have hgpad4 : s4.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
            change s3.globals.lookup _ = _; rw [hglob_s3]; exact hgpad
          have hargs_p1 : evalListHOLFinite s4 (h := fun a => Classical.propDecidable (s4.memaddrs a))
              [.var .global (ofString "keccak_pad"), .const 136] = some [.val (.word pad), .val (.word 136)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hgpad4]
          have hres_p1 := call0_two_word_resumes s4 _ _ _ _ _ _ pad 136 (by decide) hc_s3 hlook_mz hargs_p1 hor_p1
          let cp1 := callEntryStateHOLFinite s4
            ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word pad))).update (ofString "n", .val (.word 136)))
          have hpad_dom := (memzero_body_eff cp1 pad 136 hc_s3 (guestInv_callEntry s4 _ hGs4)
            (by simp [cp1, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "n" ≠ ofString "dst" by decide])
            (by simp [cp1, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
            hres_p1).2 (by decide)
          have hpad_nz : pad.toNat ≠ 0 := by omega
          have hpad_sub : ∀ i ∈ [(pad.toNat, 136)], 0 < i.2 → ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2 := by
            intro i hi _
            simp at hi; subst hi
            refine ⟨globBufIvl entry.globals "keccak_pad" 136, List.mem_cons_of_mem _ List.mem_cons_self, ?_, ?_⟩ <;>
              simp [globBufIvl, globMapN, hgpad, hpad_nz]
          have hpad_in : 0 < 136 → ∃ i ∈ Rl, i.1 ≤ pad.toNat ∧ pad.toNat + 136 ≤ i.1 + i.2 :=
            fun hp => hpad_sub (pad.toNat, 136) (List.mem_singleton.2 rfl) hp
          rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
          rcases hmp1 : evaluateHOLFiniteState s4
              (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "keccak_pad"), .const 136]) with ⟨rp1, s5⟩
          rw [hmp1] at hnt hres
          have heff_p1 : ByteEff s4 s5 Rl := by
            have := call0_byteEff funByteEff_memzero s4 _ Rl hc_s3 hGs4
              (fun vs hvs i hi hp => by
                rw [hargs_p1] at hvs; injection hvs with hvs; subst hvs
                simp [valWordNat] at hi; subst hi
                exact hpad_sub (pad.toNat, 136) (List.mem_singleton.2 rfl) hp)
              hnt_p1 hor_p1
            rwa [hmp1] at this
          have heff_e5 : ByteEff entry s5 Rl := (heff_e3.locals_clock _ _).trans heff_p1
          cases rp1 with
          | some _ => exact ((heff_e5.locals_clock _ _).locals_clock _ _).locals_clock _ _
          | none =>
            have hs5_loc : s5.locals = s4.locals := by
              have := call0_any_locals s4 _ _ (by rw [hmp1]); rwa [hmp1] at this
            have hGs5 : GuestInv s5 := guestInv_congr heff_e5.code heff_e5.memaddrs heff_e5.shMemaddrs heff_e5.baseAddr hG
            have hc_s5 : s5.code = originalRuntimeCode := heff_e5.code.trans hc
            have hgpad5 : s5.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
              rw [heff_e5.globals]; exact hgpad
            -- Step 6: `memcpy(keccak_pad, p + i, rem)`
            dsimp only at hnt hres ⊢
            obtain ⟨hnt_mc, hor_mc⟩ := seq_step s5 _ _ hnt (Or.inr hres)
            have hargs_mc : evalListHOLFinite s5 (h := fun a => Classical.propDecidable (s5.memaddrs a))
                [.var .global (ofString "keccak_pad"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
                 .var .local (ofString "rem")] =
                some [.val (.word pad), .val (.word (p + iw)), .val (.word remw)] := by
              simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hgpad5, hs5_loc, hp_4, hi_4, hrem_4,
                valueIsWord, valueWord, wordOpHOL, wordOp]
            rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
            rcases hmc : evaluateHOLFiniteState s5
                (.call (some (none, none)) (ofString "memcpy")
                  [.var .global (ofString "keccak_pad"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
                   .var .local (ofString "rem")]) with ⟨rmc, s6⟩
            rw [hmc] at hnt hres
            have heff_mc : ByteEff s5 s6 Rl := by
              have := call0_byteEff funByteEff_memcpy s5 _ Rl hc_s5 hGs5
                (fun vs hvs i hi hp => by
                  rw [hargs_mc] at hvs; injection hvs with hvs; subst hvs
                  simp [valWordNat] at hi; subst hi
                  refine ⟨globBufIvl entry.globals "keccak_pad" 136, List.mem_cons_of_mem _ List.mem_cons_self, ?_, ?_⟩
                  · simp [globBufIvl, globMapN, hgpad, hpad_nz]
                  · simp only [globBufIvl, globMapN, hgpad, hpad_nz, ↓reduceIte]
                    change pad.toNat + (n - iw).toNat ≤ pad.toNat + 136; omega)
                hnt_mc hor_mc
              rwa [hmc] at this
            have heff_e6 : ByteEff entry s6 Rl := heff_e5.trans heff_mc
            cases rmc with
            | some _ => exact ((heff_e6.locals_clock _ _).locals_clock _ _).locals_clock _ _
            | none =>
              have hs6_loc : s6.locals = s4.locals := by
                have := call0_any_locals s5 _ _ (by rw [hmc]); rw [hmc] at this; exact this.trans hs5_loc
              have hGs6 : GuestInv s6 := guestInv_congr heff_e6.code heff_e6.memaddrs heff_e6.shMemaddrs heff_e6.baseAddr hG
              have hgpad6 : s6.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
                rw [heff_e6.globals]; exact hgpad
              -- Step 7: `storeByte(keccak_pad + rem, 1)`
              dsimp only at hnt hres ⊢
              rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
              have hev_sb1 : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a))
                  (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")]) =
                  some (.val (.word (pad + BitVec.ofNat 64 remw.toNat))) := by
                simp [evalHOLExact, evalListHOLExact, hgpad6, hs6_loc, hrem_4, valueIsWord, valueWord, wordOpHOL, wordOp]
              have heff_sb1 : ByteEff s6 (evaluateHOLFiniteState s6
                  (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")]) (.const 1))).2 Rl :=
                byteEff_storeByte_at hGs6 _ _ pad remw.toNat 136 hpad_dom.2 hpad_in hrem_lt hev_sb1
              rcases hsb1 : evaluateHOLFiniteState s6
                  (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")]) (.const 1)) with ⟨rsb1, s7⟩
              rw [hsb1] at hnt hres heff_sb1
              have heff_e7 : ByteEff entry s7 Rl := heff_e6.trans heff_sb1
              cases rsb1 with
              | some _ => exact ((heff_e7.locals_clock _ _).locals_clock _ _).locals_clock _ _
              | none =>
                have hs7_loc : s7.locals = s4.locals := by
                  have := (evaluate_storeByte_control_frame s6
                    (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")]) (.const 1)).2.2.1
                  rw [hsb1] at this; exact this.trans hs6_loc
                have hGs7 : GuestInv s7 := guestInv_congr heff_e7.code heff_e7.memaddrs heff_e7.shMemaddrs heff_e7.baseAddr hG
                have hgpad7 : s7.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
                  rw [heff_e7.globals]; exact hgpad
                -- Step 8: `storeByte(keccak_pad + 135, ...)`
                dsimp only at hnt hres ⊢
                rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
                have hev_sb2 : @evalHOLExact 64 F _ s7.toExact (fun a => Classical.propDecidable (s7.memaddrs a))
                    (.op .add [.var .global (ofString "keccak_pad"), .const 135]) =
                    some (.val (.word (pad + 135))) := by
                  simp [evalHOLExact, evalListHOLExact, hgpad7, valueIsWord, valueWord, wordOpHOL, wordOp]
                have heff_sb2 : ByteEff s7 (evaluateHOLFiniteState s7
                    (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .const 135])
                      (.op .or [.loadByte (.op .add [.var .global (ofString "keccak_pad"), .const 135]), .const 128]))).2 Rl :=
                  byteEff_storeByte_at hGs7 _ _ pad 135 136 hpad_dom.2 hpad_in (by decide) hev_sb2
                rcases hsb2 : evaluateHOLFiniteState s7
                    (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .const 135])
                      (.op .or [.loadByte (.op .add [.var .global (ofString "keccak_pad"), .const 135]), .const 128])) with ⟨rsb2, s8⟩
                rw [hsb2] at hnt hres heff_sb2
                have heff_e8 : ByteEff entry s8 Rl := heff_e7.trans heff_sb2
                cases rsb2 with
                | some _ => exact ((heff_e8.locals_clock _ _).locals_clock _ _).locals_clock _ _
                | none =>
                  have hs8_loc : s8.locals = s4.locals := by
                    have := (evaluate_storeByte_control_frame s7
                      (.op .add [.var .global (ofString "keccak_pad"), .const 135])
                      (.op .or [.loadByte (.op .add [.var .global (ofString "keccak_pad"), .const 135]), .const 128])).2.2.1
                    rw [hsb2] at this; exact this.trans hs7_loc
                  have hGs8 : GuestInv s8 := guestInv_congr heff_e8.code heff_e8.memaddrs heff_e8.shMemaddrs heff_e8.baseAddr hG
                  have hc_s8 : s8.code = originalRuntimeCode := heff_e8.code.trans hc
                  have hgpad8 : s8.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
                    rw [heff_e8.globals]; exact hgpad
                  -- Step 9: `keccak_absorb_block(stp, keccak_pad)`
                  dsimp only at hnt hres ⊢
                  obtain ⟨hnt_ab, hor_ab⟩ := seq_step s8 _ _ hnt (Or.inr hres)
                  have hargs_ab : evalListHOLFinite s8 (h := fun a => Classical.propDecidable (s8.memaddrs a))
                      [.var .local (ofString "stp"), .var .global (ofString "keccak_pad")] =
                      some [.val (.word stp), .val (.word pad)] := by
                    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs8_loc, hstp_4, hgpad8]
                  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
                  rcases hab : evaluateHOLFiniteState s8
                      (.call (some (none, none)) (ofString "keccak_absorb_block")
                        [.var .local (ofString "stp"), .var .global (ofString "keccak_pad")]) with ⟨rab, s9⟩
                  rw [hab] at hnt hres
                  have heff_ab : ByteEff s8 s9 Rl := by
                    have := call0_byteEff funByteEff_keccak_absorb_block s8 _ Rl hc_s8 hGs8
                      (fun vs hvs i hi hp => by
                        rw [hargs_ab] at hvs; injection hvs with hvs; subst hvs
                        simp [valWordNat] at hi; subst hi
                        exact hstp_sub (stp.toNat, 200) (List.mem_singleton.2 rfl) hp)
                      hnt_ab hor_ab
                    rwa [hab] at this
                  have heff_e9 : ByteEff entry s9 Rl := heff_e8.trans heff_ab
                  cases rab with
                  | some _ => exact ((heff_e9.locals_clock _ _).locals_clock _ _).locals_clock _ _
                  | none =>
                    have hs9_loc : s9.locals = s4.locals := by
                      have := call0_any_locals s8 _ _ (by rw [hab]); rw [hab] at this; exact this.trans hs8_loc
                    have hGs9 : GuestInv s9 := guestInv_congr heff_e9.code heff_e9.memaddrs heff_e9.shMemaddrs heff_e9.baseAddr hG
                    have hc_s9 : s9.code = originalRuntimeCode := heff_e9.code.trans hc
                    -- Step 10: `ite` output 32 bytes to `out`, then `return 0`!
                    dsimp only at hnt hres ⊢
                    obtain ⟨hnt_oi, hor_oi⟩ := seq_step s9 _ _ hnt (Or.inr hres)
                    have hout_sub : ∀ i ∈ [(out.toNat, 32)], 0 < i.2 → ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2 := by
                      intro i hi _
                      simp at hi; subst hi
                      exact ⟨(out.toNat, 32), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), le_rfl, le_rfl⟩
                    have heff_oi := keccak_out_ite_eff s9 out stp Rl hc_s9 hGs9
                      (by rw [hs9_loc]; exact hout_4) (by rw [hs9_loc]; exact hstp_4)
                      hout_sub hnt_oi hor_oi
                    rw [evaluateHOLFiniteState_seq_line780] at ⊢
                    rcases hoi : evaluateHOLFiniteState s9 _ with ⟨roi, s10⟩
                    rw [hoi] at heff_oi
                    have heff_e10 : ByteEff entry s10 Rl := heff_e9.trans heff_oi
                    cases roi with
                    | some _ => exact ((heff_e10.locals_clock _ _).locals_clock _ _).locals_clock _ _
                    | none =>
                      exact (((heff_e10.trans (byteEff_return s10 _ Rl)).locals_clock _ _).locals_clock _ _).locals_clock _ _


structure InitEff {F : Type} (s cur : PanSemStateFiniteExact 64 F)
    (Rl : List Ivl) (B : List (String × Nat)) (gw : List String) : Prop where
  arena      : ArenaReady cur
  code       : cur.code = originalRuntimeCode
  memaddrs   : cur.memaddrs = s.memaddrs
  be         : cur.be = s.be
  eshapes    : cur.eshapes = s.eshapes
  hp_word    : ∃ pw : BitVec 64, cur.globals.lookup (ofString "heap_ptr") = some (.val (.word pw))
  hp_lo      : globN s "heap_ptr" ≤ globN cur "heap_ptr"
  fmp_eq     : globN cur "frame_mem_ptr" = globN s "frame_mem_ptr"
  sp_eq      : globN cur "scratch_ptr" = globN s "scratch_ptr"
  gw_kept    : GlobalsKept gw s cur
  fresh_bufs : FreshBufsOK s cur
  out_dom    : ∀ a : BitVec 64, cur.memory a ≠ s.memory a → s.memaddrs a
  cell_frame : ∀ a : BitVec 64, cur.memory a ≠ s.memory a →
                 (∃ ivl ∈ Rl, CellHitsPos a.toNat ivl) ∨
                 (∃ gs ∈ B, CellHitsPos a.toNat (bufferRegion s gs)) ∨
                 CellHitsPos a.toNat (heapFree s)
  byte_frame : ∀ b : Nat, b < 2 ^ 64 → memB cur b ≠ memB s b →
                 (∃ ivl ∈ Rl, InIvl b ivl) ∨
                 (∃ gs ∈ B, InIvl b (bufferRegion s gs)) ∨
                 InIvl b (heapFree s)

theorem InitEff.refl {F : Type} (s : PanSemStateFiniteExact 64 F)
    (Rl : List Ivl) (B : List (String × Nat)) (gw : List String)
    (hA : ArenaReady s) (hc : s.code = originalRuntimeCode) :
    InitEff s s Rl B gw := by
  have hhp : ∃ pw : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) := by
    have hlo := hA.2.1
    have hsb : 0 < sourceBase := by rw [sourceBase_val]; decide
    unfold globN at hlo
    rcases hg : s.globals.lookup (ofString "heap_ptr") with _ | v
    · simp [hg] at hlo; omega
    · rcases v with ⟨⟨pw⟩⟩ | _ | _ <;> simp [hg] at hlo
      · exact ⟨pw, rfl⟩
      · omega
      · omega
  refine ⟨hA, hc, rfl, rfl, rfl, hhp, le_rfl, rfl, rfl, fun _ _ => rfl, ?_,
    fun _ h => absurd rfl h, fun _ h => absurd rfl h, fun _ _ h => absurd rfl h⟩
  refine ⟨fun _ _ => Or.inl rfl, ?_⟩
  rw [List.pairwise_iff_getElem]
  intro i j _ _ _ h1 _; exact absurd rfl h1.1

theorem InitEff.locals_clock {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : InitEff s cur Rl B gw) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    InitEff s { cur with locals := L, clock := k } Rl B gw :=
  ⟨⟨guestInv_with_locals_clock cur L k h.arena.1, h.arena.2⟩,
   h.code, h.memaddrs, h.be, h.eshapes, h.hp_word, h.hp_lo, h.fmp_eq, h.sp_eq,
   h.gw_kept, h.fresh_bufs, h.out_dom, h.cell_frame, h.byte_frame⟩

theorem InitEff.of_byteEff {F : Type} {s cur next : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String} {Sub : List Ivl}
    (h : InitEff s cur Rl B gw) (hb : ByteEff cur next Sub)
    (hsub : ∀ iv ∈ Sub, 0 < iv.2 →
      (∃ j ∈ Rl, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
      (∃ gs ∈ B, (bufferRegion s gs).1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
      (globN s "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit)) :
    InitEff s next Rl B gw := by
  have hGn : GuestInv next :=
    guestInv_congr hb.code hb.memaddrs hb.shMemaddrs hb.baseAddr h.arena.1
  have hAn : ArenaReady next := ⟨hGn, arenaOK_congr hb.globals h.arena.2⟩
  refine ⟨hAn, hb.code.trans h.code, hb.memaddrs.trans h.memaddrs, hb.be.trans h.be, hb.eshapes.trans h.eshapes,
    by rw [hb.globals]; exact h.hp_word,
    by simpa [globN, hb.globals] using h.hp_lo,
    by simpa [globN, hb.globals] using h.fmp_eq,
    by simpa [globN, hb.globals] using h.sp_eq,
    fun k hk => (h.gw_kept k hk).trans (by rw [hb.globals]),
    by simpa [FreshBufsOK, globN, hb.globals] using h.fresh_bufs, ?_, ?_, ?_⟩
  · intro a hne
    by_cases hnc : next.memory a = cur.memory a
    · rw [hnc] at hne; exact h.out_dom a hne
    · rw [← h.memaddrs]; exact hb.out_dom a hnc
  · intro a hne
    by_cases hnc : next.memory a = cur.memory a
    · rw [hnc] at hne; exact h.cell_frame a hne
    · obtain ⟨iv, hiv, hpos, hc1, hc2⟩ := hb.cell_frame a hnc
      rcases hsub iv hiv hpos with ⟨j, hj, h1, h2⟩ | ⟨gs, hgs, h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨j, hj, by omega, by omega, by omega⟩
      · exact Or.inr (Or.inl ⟨gs, hgs, by omega, by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨by dsimp [heapFree]; omega, by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩)
  · intro b hb64 hne
    by_cases hnc : memB next b = memB cur b
    · rw [hnc] at hne; exact h.byte_frame b hb64 hne
    · obtain ⟨iv, hiv, hb1, hb2⟩ := hb.byte_frame b hb64 hnc
      rcases hsub iv hiv (by omega) with ⟨j, hj, h1, h2⟩ | ⟨gs, hgs, h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨j, hj, by omega, by omega⟩
      · exact Or.inr (Or.inl ⟨gs, hgs, by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩)

theorem InitEff.to_worldStep {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {B : List (String × Nat)} {gw : List String}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hWOK : WorldOK s)
    (hB_ok : ∀ gs ∈ B, gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst)
    (hcore_out : ∀ g ∈ coreWorldGlobals, ofString g ∉ gw.map ofString)
    (heff : InitEff s post (R s) B gw) :
    WorldStep R gw stdKeep NoExtra s r post := by
  refine worldStep_master B hB_ok hWOK heff.arena ⟨heff.hp_lo, by rw [heff.sp_eq]⟩
    heff.gw_kept hcore_out heff.fresh_bufs
    (fun a hne => ⟨heff.out_dom a hne, ?_⟩)
    (fun b hb64 hne => ?_)
    (fun _ _ _ _ _ _ _ _ => trivial)
  · rcases heff.cell_frame a hne with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inr h3))
  · rcases heff.byte_frame b hb64 hne with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inr h3))

/-! ## 2. Exact `alloc`, `heap_mark`, `heap_release` behavior -/

theorem lookup_heap_mark :
    originalRuntimeCode.lookup (ofString "heap_mark") =
      some ([], sourceFnBody Guest.Software.guestFn_heap_mark, .one) :=
  lookup_of_guestAst_getElem 8 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_heap_mark) rfl

theorem lookup_heap_release :
    originalRuntimeCode.lookup (ofString "heap_release") =
      some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_heap_release, .one) :=
  lookup_of_guestAst_getElem 9 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_heap_release) rfl

theorem evaluate_call_trap_with_no_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (codeVal : BitVec 64)
    (hcode : state.code = originalRuntimeCode) :
    ¬ Resumes (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal])).1 := by
  rw [evaluateHOLFiniteState_call]
  have hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const codeVal] =
      some [.val (.word codeVal)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlookup := pan_one_word_lookup state.code.lookup (ofString "trap_with") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_trap_with) codeVal (by rw [hcode]; exact lookup_trap_with)
  rw [hargs]; dsimp only; rw [hlookup]; dsimp only
  split
  · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
  · have hout := evaluate_trap_with_body_outcomes
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
    rcases hbody : evaluateHOLFiniteState
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
      (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
    rw [hbody] at hout
    cases res with
    | none => exact absurd rfl hout.1
    | some r =>
      cases r with
      | returned v => exact absurd rfl (hout.2.1 v)
      | exception eid ev =>
        rintro (⟨_, h⟩ | ⟨e', v', h, hne⟩)
        · simp at h
        · simp at h; obtain ⟨rfl, rfl⟩ := h; exact hout.2.2 eid ev hne rfl
      | «break» | «continue» | error | timeOut | finalFfi _ =>
        rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

theorem evaluate_alloc_body_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hres : Resumes (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)).1) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    out.1 = some (.returned (.val (.word p))) ∧
    out.2 =
      { state with
        locals := out.2.locals
        globals := state.globals.update (ofString "heap_ptr", .val (.word q))
        clock := out.2.clock } ∧
    ¬ (cMax.toNat < q.toNat) := by
  dsimp only
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
  rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hres ⊢
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only at hres ⊢
  rw [hp_eval] at hres ⊢
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only at hres ⊢
  rw [if_pos hsh_p] at hres ⊢
  dsimp only at hres ⊢
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "p" ≠ ofString "n" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (cMax - p).toNat < n.toNat then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    rfl
  by_cases hcmp1 : (cMax - p).toNat < n.toNat
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1] at hres
    have hno_none := evaluate_call_trap_with_no_none pState 1 hcode
    have hno_res := evaluate_call_trap_with_no_resumes pState 1 hcode
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_res hres
    cases r1 with
    | none => exact absurd rfl hno_none
    | some _ => exact False.elim (hno_res hres)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1] at hres ⊢
    dsimp only at hres ⊢
    rw [evaluateHOLFiniteState_dec_total] at hres ⊢
    let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (alloc_q_word_eq p n)
    dsimp only at hres ⊢
    rw [hq_eval] at hres ⊢
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only at hres ⊢
    rw [if_pos hsh_q] at hres ⊢
    dsimp only at hres ⊢
    let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
        show ofString "q" ≠ ofString "p" by decide]
    rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.const cMax) (.var .local (ofString "q"))) =
        some (.val (.word (if cMax.toNat < q.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    by_cases hcmp2 : cMax.toNat < q.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2] at hres
      have hno_none := evaluate_call_trap_with_no_none qState 1 hcode
      have hno_res := evaluate_call_trap_with_no_resumes qState 1 hcode
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_res hres
      cases r2 with
      | none => exact absurd rfl hno_none
      | some _ => exact False.elim (hno_res hres)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2]
      dsimp only
      have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := hp_lookup
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "p")))) =
          (some (.returned (.val (.word p))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [heval_end]
      exact ⟨rfl, rfl, hcmp2⟩

theorem alloc_bounds_general (p n : BitVec 64)
    (hp_lt : p.toNat ≤ heapLimit) (hp8 : p.toNat % 8 = 0)
    (hn_hi : n.toNat ≤ 8192)
    (hcmp2 : ¬ (cMax.toNat < ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)).toNat)) :
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    p.toNat + n.toNat ≤ q.toNat ∧ q.toNat ≤ heapLimit ∧ q.toNat % 8 = 0 ∧ p.toNat % 8 = 0 := by
  intro q
  have hhl : heapLimit = 2952790016 := by decide
  have hcMax : cMax.toNat = 2952790016 := rfl
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hq_eq : q.toNat = (p + (n + 7)).toNat / 8 * 8 := and_neg8_toNat (p + (n + 7))
  have h7 : (7 : BitVec 64).toNat = 7 := rfl
  have hp_isLt := p.isLt; have hn_isLt := n.isLt
  have hn7 : (n + 7).toNat = n.toNat + 7 := BitVec.toNat_add_of_lt (by omega)
  have hsum : (p + (n + 7)).toNat = p.toNat + n.toNat + 7 :=
    by rw [BitVec.toNat_add_of_lt (by rw [hn7]; omega), hn7, Nat.add_assoc]
  have hdiv8 : q.toNat ≥ p.toNat + n.toNat := by
    have hp_div : p.toNat = p.toNat / 8 * 8 := by omega
    rw [hq_eq, hsum, hp_div]
    omega
  have hq_le : q.toNat ≤ heapLimit := by
    have hnot : q.toNat ≤ cMax.toNat := Nat.le_of_not_lt hcmp2
    rwa [hcMax, ← hhl] at hnot
  exact ⟨hdiv8, hq_le, by rw [hq_eq]; omega, hp8⟩

theorem FreshBufsOK.update_fresh {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    (gname : String) (sz : Nat) (pw q : BitVec 64)
    (hfb : FreshBufsOK s cur)
    (hhp_cur : cur.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)))
    (hhp_lo : globN s "heap_ptr" ≤ pw.toNat)
    (hpw8 : pw.toNat % 8 = 0)
    (hq_lo : pw.toNat + sz ≤ q.toNat)
    (hgb_mem : (gname, sz) ∈ globalBuffers)
    (hgn_ne_hp : ofString gname ≠ ofString "heap_ptr") :
    let nextG := HolFiniteMapExact.update
      (HolFiniteMapExact.update cur.globals (ofString "heap_ptr", .val (.word q)))
      (ofString gname, .val (.word pw))
    let next : PanSemStateFiniteExact 64 F := { cur with globals := nextG }
    FreshBufsOK s next := by
  intro nextG next
  have hpw_glob : globN cur "heap_ptr" = pw.toNat := by simp [globN, hhp_cur]
  have hq_glob : globN next "heap_ptr" = q.toNat := by
    have h1 : (ofString gname == ofString "heap_ptr") = false := beq_eq_false_iff_ne.2 hgn_ne_hp
    simp [next, nextG, globN, HolFiniteMapExact.lookup_update, FUPDATE, h1]
  have hg_next : globN next gname = pw.toNat := by
    simp [next, nextG, globN, HolFiniteMapExact.lookup_update, FUPDATE]
  have hother_next : ∀ k : String, ofString k ≠ ofString gname → ofString k ≠ ofString "heap_ptr" →
      globN next k = globN cur k := by
    intro k hk1 hk2
    have h1 : (ofString gname == ofString k) = false := beq_eq_false_iff_ne.2 (Ne.symm hk1)
    have h2 : (ofString "heap_ptr" == ofString k) = false := beq_eq_false_iff_ne.2 (Ne.symm hk2)
    simp [next, nextG, globN, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2]
  have hgb_nd : (globalBuffers.map (fun p => ofString p.1)).Nodup := by decide
  have hgb_uniq : ∀ k n, (k, n) ∈ globalBuffers → ofString k = ofString gname → k = gname ∧ n = sz := by
    intro k n hkn heq
    have : ∀ l : List (String × Nat), (l.map (fun p => ofString p.1)).Nodup →
        ∀ a1 b1 a2 b2, (a1, b1) ∈ l → (a2, b2) ∈ l → ofString a1 = ofString a2 → a1 = a2 ∧ b1 = b2 := by
      intro l hl a1 b1 a2 b2 h1 h2 heqm
      induction l with
      | nil => cases h1
      | cons hd tl ih =>
        simp only [List.map_cons, List.nodup_cons] at hl
        rcases List.mem_cons.1 h1 with rfl | h1' <;> rcases List.mem_cons.1 h2 with h2eq | h2'
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2eq; exact ⟨rfl, rfl⟩
        · exfalso; apply hl.1; rw [heqm]; exact List.mem_map.2 ⟨_, h2', rfl⟩
        · subst h2eq; exfalso; apply hl.1; rw [← heqm]; exact List.mem_map.2 ⟨_, h1', rfl⟩
        · exact ih hl.2 h1' h2'
    exact this globalBuffers hgb_nd k n gname sz hkn hgb_mem heq
  have hgb_not_hp : ∀ k n, (k, n) ∈ globalBuffers → ofString k ≠ ofString "heap_ptr" := by
    have hall : ∀ p ∈ globalBuffers, ofString p.1 ≠ ofString "heap_ptr" := by decide
    exact fun k n hkn => hall (k, n) hkn
  refine ⟨?_, ?_⟩
  · intro ⟨k, n⟩ hkn
    by_cases hkg : ofString k = ofString gname
    · obtain ⟨rfl, rfl⟩ := hgb_uniq k n hkn hkg
      right; right
      rw [hg_next, hq_glob]
      exact ⟨hpw8, hhp_lo, hq_lo⟩
    · rw [hother_next k hkg (hgb_not_hp k n hkn), hq_glob]
      rcases hfb.1 (k, n) hkn with h1 | h2 | ⟨h8, hin1, hin2⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · rw [hpw_glob] at hin2
        exact Or.inr (Or.inr ⟨h8, hin1, by dsimp at hin2 ⊢; omega⟩)
  · rw [List.pairwise_iff_getElem]
    have hpw_old := List.pairwise_iff_getElem.1 hfb.2
    intro i j hi hj hlt ha hb
    let a := globalBuffers[i]
    let b := globalBuffers[j]
    have ha_mem : a ∈ globalBuffers := List.getElem_mem hi
    have hb_mem : b ∈ globalBuffers := List.getElem_mem hj
    have hab_ne : ofString a.1 ≠ ofString b.1 := by
      have hpw_fst := List.pairwise_iff_getElem.1 hgb_nd
      have := hpw_fst i j (by simpa using hi) (by simpa using hj) hlt
      simpa [a, b] using this
    by_cases hag : ofString a.1 = ofString gname
    · obtain ⟨hag_eq, _⟩ := hgb_uniq a.1 a.2 ha_mem hag
      have hbg : ofString b.1 ≠ ofString gname := fun h => hab_ne (hag.trans h.symm)
      have hb_eq := hother_next b.1 hbg (hgb_not_hp b.1 b.2 hb_mem)
      rcases hfb.1 b hb_mem with h1 | h2 | ⟨_, _, hin_b2⟩
      · rw [hb_eq] at hb; exact absurd h1 hb.1
      · rw [hb_eq] at hb; exact absurd h2 hb.2
      · rw [hpw_glob] at hin_b2
        right; right; right
        dsimp at hin_b2 ⊢
        rw [hb_eq, hag_eq, hg_next]
        exact hin_b2
    · by_cases hbg : ofString b.1 = ofString gname
      · obtain ⟨hbg_eq, _⟩ := hgb_uniq b.1 b.2 hb_mem hbg
        have ha_eq := hother_next a.1 hag (hgb_not_hp a.1 a.2 ha_mem)
        rcases hfb.1 a ha_mem with h1 | h2 | ⟨_, _, hin_a2⟩
        · rw [ha_eq] at ha; exact absurd h1 ha.1
        · rw [ha_eq] at ha; exact absurd h2 ha.2
        · rw [hpw_glob] at hin_a2
          right; right; left
          dsimp at hin_a2 ⊢
          rw [ha_eq, hbg_eq, hg_next]
          exact hin_a2
      · have ha_eq := hother_next a.1 hag (hgb_not_hp a.1 a.2 ha_mem)
        have hb_eq := hother_next b.1 hbg (hgb_not_hp b.1 b.2 hb_mem)
        rw [ha_eq] at ha ⊢
        rw [hb_eq] at hb ⊢
        exact hpw_old i j hi hj hlt ha hb

theorem step_call_alloc_global {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (gname : String) (sz : Nat) (szExp : ExpHOL 64)
    (heff : InitEff s cur Rl B gw)
    (hsz_bound : 0 < sz ∧ sz ≤ 8192)
    (hsz_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) szExp =
      some (.val (.word (BitVec.ofNat 64 sz))))
    (hgb_mem : (gname, sz) ∈ globalBuffers)
    (hgw_hp : ofString "heap_ptr" ∈ gw.map ofString)
    (hgw_mem : ofString gname ∈ gw.map ofString)
    (hnt : (evaluateHOLFiniteState cur
      (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp])).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur
      (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp])).1 = none ∨
      Resumes (evaluateHOLFiniteState cur
        (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp])).1) :
    let out := evaluateHOLFiniteState cur
      (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp])
    out.1 = none ∧
    out.2.locals = cur.locals ∧
    InitEff s out.2 Rl B gw ∧
    (∀ k : MlS, k ≠ ofString gname → k ≠ ofString "heap_ptr" →
      out.2.globals.lookup k = cur.globals.lookup k) ∧
    ∃ pw : BitVec 64,
      out.2.globals.lookup (ofString gname) = some (.val (.word pw)) ∧
      pw.toNat % 8 = 0 ∧
      globN s "heap_ptr" ≤ pw.toNat ∧
      pw.toNat + sz ≤ globN out.2 "heap_ptr" := by
  dsimp only
  obtain ⟨pw, hpw⟩ := heff.hp_word
  have hgn_ne_hp : ofString gname ≠ ofString "heap_ptr" :=
    (by decide : ∀ p ∈ globalBuffers, ofString p.1 ≠ ofString "heap_ptr") (gname, sz) hgb_mem
  have hgn_ne_fmp : ofString gname ≠ ofString "frame_mem_ptr" :=
    (by decide : ∀ p ∈ globalBuffers, ofString p.1 ≠ ofString "frame_mem_ptr") (gname, sz) hgb_mem
  have hgn_ne_sp : ofString gname ≠ ofString "scratch_ptr" :=
    (by decide : ∀ p ∈ globalBuffers, ofString p.1 ≠ ofString "scratch_ptr") (gname, sz) hgb_mem
  have hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [szExp] =
      some [.val (.word (BitVec.ofNat 64 sz))] := by
    simp [evalListHOLFinite, evalListHOLExact, hsz_ev]
  have hl_al := pan_one_word_lookup cur.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) (BitVec.ofNat 64 sz)
    (by rw [heff.code]; exact lookup_alloc)
  rw [evaluateHOLFiniteState_call, hargs] at hnt hor ⊢
  dsimp only at hnt hor ⊢
  rw [hl_al] at hnt hor ⊢
  dsimp only at hnt hor ⊢
  by_cases hclk : cur.clock = 0
  · rw [if_pos hclk] at hnt; exact absurd rfl hnt
  · rw [if_neg hclk] at hnt hor ⊢
    let entry := callEntryStateHOLFinite cur
      (HolFiniteMapExact.empty.update (ofString "n", .val (.word (BitVec.ofNat 64 sz))))
    have hres_entry : Resumes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc)).1 := by
      rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc) with ⟨rb, pb⟩
      dsimp only [entry] at hb
      rw [hb] at hor
      cases rb with
      | none => rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | some rb' =>
        cases rb' with
        | returned rv => exact Or.inl ⟨rv, rfl⟩
        | exception eid ev =>
          rcases hor with h | ⟨_, h⟩ | ⟨e', v', h, hne_t⟩
          · simp at h
          · simp at h
          · simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨eid, ev, rfl, hne_t⟩
        | _ => rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    have hal := evaluate_alloc_body_resumes entry pw (BitVec.ofNat 64 sz) heff.code hpw
      (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      hres_entry
    dsimp only at hal
    rcases hb : evaluateHOLFiniteState
        (callEntryStateHOLFinite cur (HolFiniteMapExact.empty.update (ofString "n", .val (.word (BitVec.ofNat 64 sz)))))
        (sourceFnBody Guest.Software.guestFn_alloc) with ⟨rb, pb⟩
    dsimp only [entry] at hal
    have hor' := hor
    rw [hb] at hal hor'
    obtain ⟨rfl, hpb_eq, hcmp2⟩ := hal
    dsimp only at hpb_eq hor' ⊢
    have hsh_ok : shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh_ok] at hor' ⊢
    by_cases hvalid : isValidValueHOLExact cur.toExact .global (ofString gname) (.val (.word pw)) = true
    · rw [if_pos hvalid]
      let q := (pw + (BitVec.ofNat 64 sz + 7)) &&& ((0 : BitVec 64) - 8)
      have hpw_glob : globN cur "heap_ptr" = pw.toNat := by simp [globN, hpw]
      have hsz_toNat : (BitVec.ofNat 64 sz).toNat = sz := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hbnds := alloc_bounds_general pw (BitVec.ofNat 64 sz)
        (by rw [← hpw_glob]; exact heff.arena.2.2.1)
        (by rw [← hpw_glob]; exact heff.arena.2.2.2.2.2.2.1)
        (by rw [hsz_toNat]; exact hsz_bound.2) hcmp2
      dsimp only at hbnds
      rw [hsz_toNat] at hbnds
      let post0 : PanSemStateFiniteExact 64 F :=
        { locals := cur.locals, globals := pb.globals, structs := pb.structs, code := pb.code,
          eshapes := pb.eshapes, memory := pb.memory, memaddrs := pb.memaddrs, shMemaddrs := pb.shMemaddrs,
          clock := pb.clock, be := pb.be, ffi := pb.ffi, baseAddr := pb.baseAddr, topAddr := pb.topAddr }
      let outSt := setKvarHOLFinite .global (ofString gname) (.val (.word pw)) post0
      let newGlobals := HolFiniteMapExact.update
        (HolFiniteMapExact.update cur.globals (ofString "heap_ptr", .val (.word q)))
        (ofString gname, .val (.word pw))
      have hout_eq : outSt = { cur with globals := newGlobals, clock := pb.clock } := by
        dsimp only [outSt, post0, setKvarHOLFinite, setGlobalHOLFinite, newGlobals]
        rw [hpb_eq]
        rfl
      change (none, outSt).1 = none ∧ outSt.locals = cur.locals ∧ InitEff s outSt Rl B gw ∧
        (∀ k : MlS, k ≠ ofString gname → k ≠ ofString "heap_ptr" →
          outSt.globals.lookup k = cur.globals.lookup k) ∧
        ∃ pw' : BitVec 64,
          outSt.globals.lookup (ofString gname) = some (.val (.word pw')) ∧
          pw'.toNat % 8 = 0 ∧
          globN s "heap_ptr" ≤ pw'.toNat ∧
          pw'.toNat + sz ≤ globN outSt "heap_ptr"
      rw [hout_eq]
      have hfmp_out : globN { cur with globals := newGlobals, clock := pb.clock } "frame_mem_ptr" =
          globN cur "frame_mem_ptr" := by
        have h1 : (ofString gname == ofString "frame_mem_ptr") = false := beq_eq_false_iff_ne.2 hgn_ne_fmp
        have h2 : (ofString "heap_ptr" == ofString "frame_mem_ptr") = false := by decide
        simp [newGlobals, globN, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2]
      have hsp_out : globN { cur with globals := newGlobals, clock := pb.clock } "scratch_ptr" =
          globN cur "scratch_ptr" := by
        have h1 : (ofString gname == ofString "scratch_ptr") = false := beq_eq_false_iff_ne.2 hgn_ne_sp
        have h2 : (ofString "heap_ptr" == ofString "scratch_ptr") = false := by decide
        simp [newGlobals, globN, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2]
      have hhp_out_lookup : newGlobals.lookup (ofString "heap_ptr") = some (.val (.word q)) := by
        have h1 : (ofString gname == ofString "heap_ptr") = false := beq_eq_false_iff_ne.2 hgn_ne_hp
        simp [newGlobals, HolFiniteMapExact.lookup_update, FUPDATE, h1]
      have hhp_out : globN { cur with globals := newGlobals, clock := pb.clock } "heap_ptr" = q.toNat := by
        simp [globN, hhp_out_lookup]
      have hq_ge_pw : pw.toNat ≤ q.toNat := le_trans (Nat.le_add_right _ _) hbnds.1
      refine ⟨rfl, rfl, ?_, ?_, pw, ?_, hbnds.2.2.2, by rw [← hpw_glob]; exact heff.hp_lo,
        by rw [hhp_out]; exact hbnds.1⟩
      · refine ⟨⟨guestInv_congr (s := cur) rfl rfl rfl rfl heff.arena.1, ?_⟩,
          heff.code, heff.memaddrs, heff.be, heff.eshapes,
          ⟨q, hhp_out_lookup⟩, ?_, hfmp_out.trans heff.fmp_eq, hsp_out.trans heff.sp_eq,
          ?_, ?_, heff.out_dom, heff.cell_frame, heff.byte_frame⟩
        · obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9⟩ := heff.arena.2
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hhp_out]; rw [hpw_glob] at ha1; exact le_trans ha1 hq_ge_pw
          · rw [hhp_out]; exact hbnds.2.1
          · rw [hfmp_out]; exact ha3
          · rw [hfmp_out, hsp_out]; exact ha4
          · rw [hsp_out]; exact ha5
          · rw [hhp_out]; exact hbnds.2.2.1
          · rw [hfmp_out]; exact ha7
          · rw [hsp_out]; exact ha8
          · exact globalsWord_update (t := { cur with globals := newGlobals, clock := pb.clock }) (ofString gname) pw rfl
              (globalsWord_update (s := cur) (t := { cur with globals := cur.globals.update (ofString "heap_ptr", .val (.word q)) })
                (ofString "heap_ptr") q rfl ha9)
        · rw [hhp_out]; have := heff.hp_lo; rw [hpw_glob] at this; exact le_trans this hq_ge_pw
        · intro k hk
          have hk_ne_gn : (ofString gname == k) = false :=
            beq_eq_false_iff_ne.2 (fun h => hk (by subst h; exact hgw_mem))
          have hk_ne_hp : (ofString "heap_ptr" == k) = false :=
            beq_eq_false_iff_ne.2 (fun h => hk (by subst h; exact hgw_hp))
          simp only [newGlobals, HolFiniteMapExact.lookup_update, FUPDATE, hk_ne_gn, hk_ne_hp,
            Bool.false_eq_true, ↓reduceIte]
          exact heff.gw_kept k hk
        · have hfb' := FreshBufsOK.update_fresh gname sz pw q heff.fresh_bufs hpw
            (by rw [← hpw_glob]; exact heff.hp_lo) hbnds.2.2.2 hbnds.1 hgb_mem hgn_ne_hp
          simpa [FreshBufsOK, globN, newGlobals] using hfb'
      · intro k hk1 hk2
        have h1 : (ofString gname == k) = false := beq_eq_false_iff_ne.2 (Ne.symm hk1)
        have h2 : (ofString "heap_ptr" == k) = false := beq_eq_false_iff_ne.2 (Ne.symm hk2)
        simp [newGlobals, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2]
      · simp [newGlobals, HolFiniteMapExact.lookup_update, FUPDATE]
    · exfalso
      rw [if_neg hvalid] at hor'
      rcases hor' with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

/-! ## 3. Declarative Global-Buffer Constant-Store Checker & Combinators -/

/-- Check that `prog` is a tree of `.seq`, `.skip`, `.return`, `.store`, `.storeByte` writing only
to `G:gname + off` within `[0, sz)` (`sz ≤ 8192`) using constant words or 4-word `rStruct`s of
constants. Covers `bls_consts_init` (892 stores), `bls_precompiles_init` (256 stores),
`ssz_init` (256 stores), `bn254_init` (`rStruct` + word stores), `keccak_init`, `ripemd160_init`,
`blake2_init`, etc. in O(1) kernel reduction! -/
def isConstWordList : List (ExpHOL 64) → Bool
  | [] => true
  | .const _ :: rest => isConstWordList rest
  | _ => false

def checkGlobalConstStores (gname : MlS) (sz : Nat) : ProgHOL 64 → Bool
  | .seq a b => checkGlobalConstStores gname sz a && checkGlobalConstStores gname sz b
  | .skip | .return _ => true
  | .store (.var .global nm) (.const _) => (nm == gname) && decide (8 ≤ sz)
  | .store (.op .add [.var .global nm, .const off]) (.const _) =>
      (nm == gname) && decide (off.toNat + 8 ≤ sz)
  | .store (.var .global nm) (.rstruct es) =>
      (nm == gname) && isConstWordList es && decide (8 * es.length ≤ sz)
  | .store (.op .add [.var .global nm, .const off]) (.rstruct es) =>
      (nm == gname) && isConstWordList es && decide (off.toNat + 8 * es.length ≤ sz)
  | .storeByte (.var .global nm) (.const _) => (nm == gname) && decide (1 ≤ sz)
  | .storeByte (.op .add [.var .global nm, .const off]) (.const _) =>
      (nm == gname) && decide (off.toNat < sz)
  | _ => false

private theorem evalList_constWordList {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ∀ (es : List (ExpHOL 64)), isConstWordList es = true →
      ∃ ws : List (HolWordLab 64),
        @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) es =
          some (ws.map ValueHOL.val) ∧
        ws.length = es.length
  | [], _ => ⟨[], rfl, rfl⟩
  | e :: rest, h => by
    cases e with
    | const c =>
      have hr : isConstWordList rest = true := by simpa [isConstWordList] using h
      obtain ⟨ws, hws, hlen⟩ := evalList_constWordList s rest hr
      refine ⟨.word c :: ws, ?_, by simp [hlen]⟩
      simp [evalListHOLExact, evalHOLExact, hws]
    | _ => simp [isConstWordList] at h

private theorem flattenHOL_vals :
    ∀ (ws : List (HolWordLab 64)), flattenHOL (.rStruct (ws.map ValueHOL.val)) = ws
  | [] => by simp [flattenHOL]
  | w :: rest => by
    have ih := flattenHOL_vals rest
    simp only [flattenHOL, List.map_cons, List.flatten_cons] at ih ⊢
    rw [ih]; simp [flattenHOL]

private theorem panMemStores_eff
    (dom : BitVec 64 → Prop) [DecidablePred dom] (be : Bool)
    (hdom_ord : dom = ordinaryDomain) :
    ∀ (ws : List (HolWordLab 64)) (addr : BitVec 64)
      (mem mem' : BitVec 64 → HolWordLab 64),
      addr.toNat + 8 * ws.length < 2 ^ 64 →
      panMemStoresHOL addr ws dom mem = some mem' →
      (∀ x : BitVec 64, mem' x ≠ mem x →
        dom x ∧ addr.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ addr.toNat + 8 * ws.length) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        (memByteAt mem' be (BitVec.ofNat 64 b)).toNat ≠ (memByteAt mem be (BitVec.ofNat 64 b)).toNat →
        addr.toNat ≤ b ∧ b < addr.toNat + 8 * ws.length)
  | [], _, mem, mem', _, hst => by
    simp [panMemStoresHOL] at hst; subst hst
    exact ⟨fun _ h => absurd rfl h, fun _ _ h => absurd rfl h⟩
  | w :: rest, addr, mem, mem', hlt, hst => by
    simp only [panMemStoresHOL, panMemStoreHOL] at hst
    by_cases hd : dom addr
    · simp only [hd, ↓reduceIte] at hst
      have hbw : (panBytesInWord 64 : BitVec 64).toNat = 8 := rfl
      have hnext_add : (addr + panBytesInWord 64).toNat = addr.toNat + 8 := by
        apply BitVec.toNat_add_of_lt
        rw [hbw]; simp [List.length_cons] at hlt; omega
      have hlt_rest : (addr + panBytesInWord 64).toNat + 8 * rest.length < 2 ^ 64 := by
        rw [hnext_add]; simp [List.length_cons] at hlt; omega
      let mid := fun current => if current = addr then w else mem current
      obtain ⟨ih_c, ih_b⟩ := panMemStores_eff dom be hdom_ord rest (addr + panBytesInWord 64) mid mem' hlt_rest hst
      have hd_ord : addr.toNat % 8 = 0 := by
        rw [hdom_ord, ordinaryDomain_iff] at hd; exact hd.1
      refine ⟨?_, ?_⟩
      · intro x hne
        by_cases hxm : mem' x = mid x
        · rw [hxm] at hne
          by_cases hxa : x = addr
          · subst hxa; simp only [List.length_cons]; exact ⟨hd, le_rfl, by omega⟩
          · simp [mid, hxa] at hne
        · obtain ⟨hdx, hx1, hx2⟩ := ih_c x hxm
          rw [hnext_add] at hx1 hx2
          simp only [List.length_cons]; exact ⟨hdx, by omega, by omega⟩
      · intro b hb64 hne
        by_cases hbm : (memByteAt mem' be (BitVec.ofNat 64 b)).toNat =
            (memByteAt mid be (BitVec.ofNat 64 b)).toNat
        · rw [hbm] at hne
          by_cases hal : panByteAlignHOL (BitVec.ofNat 64 b) = addr
          · have hc_nat := panByteAlign_toNat64 (BitVec.ofNat 64 b)
            rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64] at hc_nat
            simp only [List.length_cons]; omega
          · unfold memByteAt memWordAt at hne; simp [mid, hal] at hne
        · obtain ⟨hb1, hb2⟩ := ih_b b hb64 hbm
          rw [hnext_add] at hb1 hb2
          simp only [List.length_cons]; omega
    · simp [hd] at hst

private theorem byteEff_store_rstruct_at {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hG : GuestInv s) (dstExp : ExpHOL 64) (es : List (ExpHOL 64))
    (base : BitVec 64) (off sz : Nat)
    (hcw : isConstWordList es = true)
    (hbase_hi : base.toNat + sz ≤ heapEnd)
    (hoff : off + 8 * es.length ≤ sz)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off)))) :
    ByteEff s (evaluateHOLFiniteState s (.store dstExp (.rstruct es))).2 [(base.toNat, sz)] := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  rw [evaluateHOLFiniteState_store]
  rw [hdst]
  dsimp only
  obtain ⟨ws, hws, hlen⟩ := evalList_constWordList s es hcw
  have hrst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.rstruct es) =
      some (.rStruct (ws.map ValueHOL.val)) := by
    simp [evalHOLExact, hws]
  rw [hrst]; dsimp only
  rw [flattenHOL_vals ws]
  split
  · rename_i mem' hmem
    have hadd : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hlt : (base + BitVec.ofNat 64 off).toNat + 8 * ws.length < 2 ^ 64 := by omega
    obtain ⟨hc, hb⟩ := @panMemStores_eff s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a))
      s.be hG.memaddrs ws (base + BitVec.ofNat 64 off) s.memory mem' hlt hmem
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun a hne => (hc a hne).1,
      fun a hne => ?_,
      fun b hb64 hne => ?_⟩
    · obtain ⟨_, h1, h2⟩ := hc a hne
      exact ⟨(base.toNat, sz), List.mem_singleton.2 rfl, by omega, by omega, by omega⟩
    · rw [memB_eq_memByteAt, memB_eq_memByteAt] at hne
      obtain ⟨h1, h2⟩ := hb b hb64 hne
      exact ⟨(base.toNat, sz), List.mem_singleton.2 rfl, by omega, by omega⟩
  · exact ByteEff.refl s _

theorem checkGlobalConstStores_sound {F : Type} (gname : MlS) (sz : Nat) (hsz : sz ≤ 8192)
    (prog : ProgHOL 64) (hok : checkGlobalConstStores gname sz prog = true)
    (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hG : GuestInv s) (hp_hi : p.toNat + sz ≤ heapEnd)
    (hp : s.globals.lookup gname = some (.val (.word p))) :
    ByteEff s (evaluateHOLFiniteState s prog).2 [(p.toNat, sz)] := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  cases shape : prog with
  | seq a b =>
    have h12 : checkGlobalConstStores gname sz a = true ∧ checkGlobalConstStores gname sz b = true := by
      simpa [shape, checkGlobalConstStores, Bool.and_eq_true] using hok
    have effa := checkGlobalConstStores_sound gname sz hsz a h12.1 s p hG hp_hi hp
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hra : evaluateHOLFiniteState s a with ⟨r1, m⟩
    rw [hra] at effa
    cases r1 with
    | some _ => exact effa
    | none =>
      have hGm := guestInv_congr effa.code effa.memaddrs effa.shMemaddrs effa.baseAddr hG
      have hpm : m.globals.lookup gname = some (.val (.word p)) := by rw [effa.globals]; exact hp
      exact effa.trans (checkGlobalConstStores_sound gname sz hsz b h12.2 m p hGm hp_hi hpm)
  | skip => exact byteEff_skip s _
  | «return» e => exact byteEff_return s e _
  | store dst vexp =>
    have hin_sz : 0 < sz → ∃ i ∈ [(p.toNat, sz)], i.1 ≤ p.toNat ∧ p.toNat + sz ≤ i.1 + i.2 :=
      fun _ => ⟨(p.toNat, sz), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩
    cases dst with
    | var vk nm =>
      cases vk with
      | «local» => simp [shape, checkGlobalConstStores] at hok
      | global =>
        cases vexp with
        | const c =>
          have h12 : nm = gname ∧ 8 ≤ sz := by
            simpa [shape, checkGlobalConstStores, Bool.and_eq_true] using hok
          rcases h12 with ⟨rfl, h8⟩
          exact byteEff_store_at hG _ _ p 0 sz hp_hi hin_sz
            (fun _ hv => by simp [evalHOLExact] at hv; exact ⟨c, hv.symm⟩) h8
            (by simpa [BitVec.add_zero, evalHOLExact] using hp)
        | rstruct es =>
          have h123 : (nm = gname ∧ isConstWordList es = true) ∧ 8 * es.length ≤ sz := by
            simpa [shape, checkGlobalConstStores, Bool.and_eq_true] using hok
          rcases h123 with ⟨⟨rfl, hcw⟩, hlen⟩
          exact byteEff_store_rstruct_at hG _ es p 0 sz hcw hp_hi (by omega)
            (by simpa [BitVec.add_zero, evalHOLExact] using hp)
        | _ => simp [shape, checkGlobalConstStores] at hok
    | op bop args =>
      cases bop <;> try (simp [shape, checkGlobalConstStores] at hok)
      rcases args with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> try (simp [shape, checkGlobalConstStores] at hok)
      cases e1 with
      | var vk1 nm1 =>
        cases vk1 <;> try (simp [shape, checkGlobalConstStores] at hok)
        cases e2 with
        | const off =>
          have hoff_eq : BitVec.ofNat 64 off.toNat = off := BitVec.eq_of_toNat_eq (by simp)
          cases vexp with
          | const c =>
            have h12 : nm1 = gname ∧ off.toNat + 8 ≤ sz := by
              simpa [shape, checkGlobalConstStores, Bool.and_eq_true] using hok
            rcases h12 with ⟨rfl, hoff⟩
            refine byteEff_store_at hG _ _ p off.toNat sz hp_hi hin_sz
              (fun _ hv => by simp [evalHOLExact] at hv; exact ⟨c, hv.symm⟩) hoff ?_
            simp [evalHOLExact, evalListHOLExact, hp, valueIsWord, valueWord, wordOpHOL, wordOp, hoff_eq]
          | rstruct es =>
            have h123 : (nm1 = gname ∧ isConstWordList es = true) ∧ off.toNat + 8 * es.length ≤ sz := by
              simpa [shape, checkGlobalConstStores, Bool.and_eq_true] using hok
            rcases h123 with ⟨⟨rfl, hcw⟩, hoff⟩
            refine byteEff_store_rstruct_at hG _ es p off.toNat sz hcw hp_hi hoff ?_
            simp [evalHOLExact, evalListHOLExact, hp, valueIsWord, valueWord, wordOpHOL, wordOp, hoff_eq]
          | _ => simp [shape, checkGlobalConstStores] at hok
        | _ => simp [shape, checkGlobalConstStores] at hok
      | _ => simp [shape, checkGlobalConstStores] at hok
    | _ => simp [shape, checkGlobalConstStores] at hok
  | storeByte dst vexp =>
    have hin_sz : 0 < sz → ∃ i ∈ [(p.toNat, sz)], i.1 ≤ p.toNat ∧ p.toNat + sz ≤ i.1 + i.2 :=
      fun _ => ⟨(p.toNat, sz), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩
    cases dst with
    | var vk nm =>
      cases vk with
      | «local» => simp [shape, checkGlobalConstStores] at hok
      | global =>
        cases vexp with
        | const c =>
          have h12 : nm = gname ∧ 1 ≤ sz := by
            simpa [shape, checkGlobalConstStores, Bool.and_eq_true] using hok
          rcases h12 with ⟨rfl, h1⟩
          exact byteEff_storeByte_at hG _ _ p 0 sz hp_hi hin_sz h1
            (by simpa [BitVec.add_zero, evalHOLExact] using hp)
        | _ => simp [shape, checkGlobalConstStores] at hok
    | op bop args =>
      cases bop <;> try (simp [shape, checkGlobalConstStores] at hok)
      rcases args with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> try (simp [shape, checkGlobalConstStores] at hok)
      cases e1 with
      | var vk1 nm1 =>
        cases vk1 <;> try (simp [shape, checkGlobalConstStores] at hok)
        cases e2 with
        | const off =>
          have hoff_eq : BitVec.ofNat 64 off.toNat = off := BitVec.eq_of_toNat_eq (by simp)
          cases vexp with
          | const c =>
            have h12 : nm1 = gname ∧ off.toNat < sz := by
              simpa [shape, checkGlobalConstStores, Bool.and_eq_true] using hok
            rcases h12 with ⟨rfl, hoff⟩
            refine byteEff_storeByte_at hG _ _ p off.toNat sz hp_hi hin_sz hoff ?_
            simp [evalHOLExact, evalListHOLExact, hp, valueIsWord, valueWord, wordOpHOL, wordOp, hoff_eq]
          | _ => simp [shape, checkGlobalConstStores] at hok
        | _ => simp [shape, checkGlobalConstStores] at hok
      | _ => simp [shape, checkGlobalConstStores] at hok
    | _ => simp [shape, checkGlobalConstStores] at hok
  | _ => simp [shape, checkGlobalConstStores] at hok
termination_by sizeOf prog
decreasing_by
  all_goals
    subst shape
    simp_wf
    try omega

/-! ## 4. `InitEff` Statement Combinators & First 10 Init `wk_*` Proofs -/

theorem seq_nt_or {F : Type} (cur : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64)
    (hnt : (evaluateHOLFiniteState cur (.seq a b)).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur (.seq a b)).1 = none ∨
      Resumes (evaluateHOLFiniteState cur (.seq a b)).1) :
    (evaluateHOLFiniteState cur a).1 ≠ some .timeOut ∧
    ((evaluateHOLFiniteState cur a).1 = none ∨ Resumes (evaluateHOLFiniteState cur a).1) := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt hor
  rcases ha : evaluateHOLFiniteState cur a with ⟨ra, ma⟩
  rw [ha] at hnt hor
  refine ⟨fun h => by subst h; simp at hnt, ?_⟩
  cases ra with
  | none => exact Or.inl rfl
  | some _ =>
    right
    rcases hor with h | h
    · simp at h
    · exact h

theorem initEff_seq {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    {a b : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.seq a b)).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur (.seq a b)).1 = none ∨
      Resumes (evaluateHOLFiniteState cur (.seq a b)).1)
    (ha : (evaluateHOLFiniteState cur a).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState cur a).1 = none ∨ Resumes (evaluateHOLFiniteState cur a).1) →
      InitEff s (evaluateHOLFiniteState cur a).2 Rl B gw)
    (hb : ∀ mid, evaluateHOLFiniteState cur a = (none, mid) →
      InitEff s mid Rl B gw →
      (evaluateHOLFiniteState mid b).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState mid b).1 = none ∨ Resumes (evaluateHOLFiniteState mid b).1) →
      InitEff s (evaluateHOLFiniteState mid b).2 Rl B gw) :
    InitEff s (evaluateHOLFiniteState cur (.seq a b)).2 Rl B gw := by
  obtain ⟨hnt_a, hor_a⟩ := seq_nt_or cur a b hnt hor
  have effa := ha hnt_a hor_a
  rw [evaluateHOLFiniteState_seq_line780] at hnt hor ⊢
  rcases hra : evaluateHOLFiniteState cur a with ⟨ra, mid⟩
  rw [hra] at hnt hor effa
  cases ra with
  | some _ => exact effa
  | none => exact hb mid hra effa hnt hor

theorem initEff_ite {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (cond : ExpHOL 64) {yes no : ProgHOL 64}
    (heff : InitEff s cur Rl B gw)
    (hnt : (evaluateHOLFiniteState cur (.ite cond yes no)).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur (.ite cond yes no)).1 = none ∨
      Resumes (evaluateHOLFiniteState cur (.ite cond yes no)).1)
    (hy : (evaluateHOLFiniteState cur yes).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState cur yes).1 = none ∨ Resumes (evaluateHOLFiniteState cur yes).1) →
      InitEff s (evaluateHOLFiniteState cur yes).2 Rl B gw)
    (hn : (evaluateHOLFiniteState cur no).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState cur no).1 = none ∨ Resumes (evaluateHOLFiniteState cur no).1) →
      InitEff s (evaluateHOLFiniteState cur no).2 Rl B gw) :
    InitEff s (evaluateHOLFiniteState cur (.ite cond yes no)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_ite] at hnt hor ⊢
  rcases hc : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
  · exact heff
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try exact heff
    rw [hc] at hnt hor
    dsimp only at hnt hor ⊢
    by_cases h0 : cw = 0
    · rw [if_pos h0] at hnt hor ⊢; exact hn hnt hor
    · rw [if_neg h0] at hnt hor ⊢; exact hy hnt hor

theorem initEff_return {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (e : ExpHOL 64) (heff : InitEff s cur Rl B gw) :
    InitEff s (evaluateHOLFiniteState cur (.return e)).2 Rl B gw := by
  rw [evaluateHOLFiniteState_return]
  split
  · exact heff
  · split
    · exact heff.locals_clock _ cur.clock
    · exact heff

theorem initEff_skip {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (heff : InitEff s cur Rl B gw) :
    InitEff s (evaluateHOLFiniteState cur .skip).2 Rl B gw := by
  rw [evaluateHOLFiniteState_skip]; exact heff

theorem initEff_seq_alloc_global {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (gname : String) (sz : Nat) (szExp : ExpHOL 64) {rest : ProgHOL 64}
    (heff : InitEff s cur Rl B gw)
    (hsz_bound : 0 < sz ∧ sz ≤ 8192)
    (hsz_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) szExp =
      some (.val (.word (BitVec.ofNat 64 sz))))
    (hgb_mem : (gname, sz) ∈ globalBuffers)
    (hgw_hp : ofString "heap_ptr" ∈ gw.map ofString)
    (hgw_mem : ofString gname ∈ gw.map ofString)
    (hnt : (evaluateHOLFiniteState cur
      (.seq (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp]) rest)).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur
      (.seq (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp]) rest)).1 = none ∨
      Resumes (evaluateHOLFiniteState cur
        (.seq (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp]) rest)).1)
    (hrest : ∀ (mid : PanSemStateFiniteExact 64 F) (pw : BitVec 64),
      mid.locals = cur.locals →
      (∀ k : MlS, k ≠ ofString gname → k ≠ ofString "heap_ptr" →
        mid.globals.lookup k = cur.globals.lookup k) →
      InitEff s mid Rl B gw →
      mid.globals.lookup (ofString gname) = some (.val (.word pw)) →
      pw.toNat % 8 = 0 →
      globN s "heap_ptr" ≤ pw.toNat →
      pw.toNat + sz ≤ globN mid "heap_ptr" →
      (evaluateHOLFiniteState mid rest).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState mid rest).1 = none ∨ Resumes (evaluateHOLFiniteState mid rest).1) →
      InitEff s (evaluateHOLFiniteState mid rest).2 Rl B gw) :
    InitEff s (evaluateHOLFiniteState cur
      (.seq (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp]) rest)).2 Rl B gw := by
  obtain ⟨hnt1, hor1⟩ := seq_nt_or cur _ rest hnt hor
  obtain ⟨hnone, hloc, heff1, hg_keep, pw, hpw_g, hpw8, hpw_lo, hpw_hi⟩ :=
    step_call_alloc_global gname sz szExp heff hsz_bound hsz_ev hgb_mem hgw_hp hgw_mem hnt1 hor1
  rw [evaluateHOLFiniteState_seq_line780] at hnt hor ⊢
  rcases hc : evaluateHOLFiniteState cur
      (.call (some (some (.global, ofString gname), none)) (ofString "alloc") [szExp]) with ⟨r1, mid⟩
  rw [hc] at hnone hloc heff1 hg_keep hpw_g hpw_hi hnt hor
  subst hnone
  exact hrest mid pw hloc hg_keep heff1 hpw_g hpw8 hpw_lo hpw_hi hnt hor

theorem initEff_fresh_constStores {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (gname : String) (sz : Nat) (pw : BitVec 64) (prog : ProgHOL 64)
    (heff : InitEff s cur Rl B gw)
    (hsz : sz ≤ 8192)
    (hok : checkGlobalConstStores (ofString gname) sz prog = true)
    (hpw_g : cur.globals.lookup (ofString gname) = some (.val (.word pw)))
    (hpw_lo : globN s "heap_ptr" ≤ pw.toNat)
    (hpw_hi : pw.toNat + sz ≤ heapLimit) :
    InitEff s (evaluateHOLFiniteState cur prog).2 Rl B gw ∧
    (evaluateHOLFiniteState cur prog).2.globals = cur.globals := by
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hb := checkGlobalConstStores_sound (ofString gname) sz hsz prog hok cur pw
    heff.arena.1 (le_trans hpw_hi hhl_he) hpw_g
  refine ⟨heff.of_byteEff hb (fun iv hiv _ => ?_), hb.globals⟩
  simp at hiv; subst hiv
  exact Or.inr (Or.inr ⟨hpw_lo, hpw_hi⟩)

theorem wk_header_init :
    WorldKeeps WorldOK (fun s => [(globN s "hdr_zero8", if globN s "hdr_zero8" = 0 then 0 else 8)])
      ["hdr_zero8", "heap_ptr"] stdKeep NoExtra (ofString "header_init") := by
  have hlook : originalRuntimeCode.lookup (ofString "header_init") =
      some ([], sourceFnBody Guest.Software.guestFn_header_init, .one) :=
    lookup_of_guestAst_getElem 238 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_header_init) rfl
  refine ⟨_, _, _, hlook, fun s hc hWOK _ hnt hres => ?_⟩
  refine InitEff.to_worldStep (B := []) hWOK (by simp) (by decide) ?_
  have hbody : sourceFnBody Guest.Software.guestFn_header_init =
      .seq (.ite (.cmp .notEqual (.var .global (ofString "hdr_zero8")) (.const 0))
          (.return (.const 0)) .skip)
        (.seq (.call (some (some (.global, ofString "hdr_zero8"), none)) (ofString "alloc") [.const 8])
          (.seq (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "hdr_zero8"), .const 8])
            (.return (.const 0)))) := rfl
  rw [hbody] at hnt hres ⊢
  have heff0 := InitEff.refl s [(globN s "hdr_zero8", if globN s "hdr_zero8" = 0 then 0 else 8)]
    [] ["hdr_zero8", "heap_ptr"] hWOK.1 hc
  refine initEff_seq hnt (Or.inr hres)
    (fun hnt_i hor_i => initEff_ite _ heff0 hnt_i hor_i
      (fun _ _ => initEff_return _ heff0)
      (fun _ _ => initEff_skip heff0))
    (fun s1 _ heff1 hnt1 hor1 => ?_)
  refine initEff_seq_alloc_global "hdr_zero8" 8 (.const 8) heff1
    ⟨by omega, by omega⟩ rfl (by decide) (by decide) (by decide) hnt1 hor1
    (fun s2 pw _ _ heff2 hpw_g _ hpw_lo hpw_hi hnt2 hor2 => ?_)
  refine initEff_seq hnt2 hor2 (fun hnt_m hor_m => ?_) (fun s3 _ heff3 _ _ => initEff_return _ heff3)
  have hargs : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
      [.var .global (ofString "hdr_zero8"), .const 8] = some [.val (.word pw), .val (.word 8)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hpw_g]
  have hb := call0_byteEff funByteEff_memzero s2 _ [(pw.toNat, 8)] heff2.code heff2.arena.1
    (fun vs hvs i hi _ => by
      rw [hargs] at hvs; injection hvs with hvs; subst hvs
      simp [valWordNat] at hi; subst hi
      exact ⟨(pw.toNat, 8), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
    hnt_m hor_m
  exact heff2.of_byteEff hb (fun iv hiv _ => by
    simp at hiv; subst hiv
    exact Or.inr (Or.inr ⟨hpw_lo, le_trans hpw_hi heff2.arena.2.2.1⟩))


theorem wk_keccak256 :
    WorldKeeps WorldOK
      (fun s =>
        [(locN s "out", 32),
         (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      []
      [("ws", [0, 8, 16, 24, 32]),
       ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "keccak256") := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := funByteEff_keccak256
  refine ⟨params, body, ret, hlook, fun {F} s hc hWOK ⟨vals, hl⟩ hnt hres => ?_⟩
  have hlook_k : originalRuntimeCode.lookup (ofString "keccak256") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_keccak256, .one) :=
    lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_keccak256) rfl
  have heq_pbr : (params, body, ret) =
      ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)],
       sourceFnBody Guest.Software.guestFn_keccak256, .one) :=
    Option.some.inj (hlook.symm.trans hlook_k)
  rcases Prod.mk.inj heq_pbr with ⟨rfl, hbr⟩
  rcases Prod.mk.inj hbr with ⟨rfl, rfl⟩
  obtain ⟨p, n, out, rfl, _, _, hout⟩ :=
    lookupCode_three_words (by decide) (by decide) (by decide) hlook_k hl
  have hb := hspec s [.val (.word p), .val (.word n), .val (.word out)] hc hWOK.1.1 hl hnt hres
  have hout_eq : locN s "out" = out.toNat := by simp [locN, hout]
  refine InitEff.to_worldStep (B := []) hWOK (by simp) (by decide) ?_
  have heff0 := InitEff.refl s
    [(locN s "out", 32),
     (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
     (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
    [] [] hWOK.1 hc
  refine heff0.of_byteEff hb (fun iv hiv _ => ?_)
  left
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
  rcases hiv with rfl | rfl | rfl
  · exact ⟨(globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
      by simp, le_rfl, le_rfl⟩
  · exact ⟨(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
      by simp, le_rfl, le_rfl⟩
  · refine ⟨(locN s "out", 32), by simp, ?_, ?_⟩ <;> simp [hout_eq, valWordNat]

end InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03
