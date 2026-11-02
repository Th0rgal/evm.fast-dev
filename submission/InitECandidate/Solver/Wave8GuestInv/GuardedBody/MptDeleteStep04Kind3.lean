import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptCuts
import InitECandidate.Solver.GuestTrapOutcomes
import InitECandidate.Solver.HeapPotential

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

/-! ### From Memory.lean -/


namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.Memory
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Backend
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv


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

theorem disj_symm {i j : Ivl} (h : Disj i j) : Disj j i :=
  Disj.flip h

theorem disj_allocated_fresh_heap {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaOK s) (hp : ArenaOK post) {i f : Ivl}
    (hi : Allocated s i) (hf : Inside f (globN s "heap_ptr") (globN post "heap_ptr")) :
    Disj f i := by
  apply Or.inr ∘ Or.inr
  rcases hi with hi | hi
  · exact Or.inr (Nat.le_trans hi.2 hf.1)
  · have hsep : heapLimit ≤ scratchStart := by decide
    exact Or.inl (Nat.le_trans hf.2 (Nat.le_trans hp.2.1
      (Nat.le_trans hsep (Nat.le_trans hs.2.2.1 (Nat.le_trans hs.2.2.2.1 hi.1)))))

theorem disj_allocated_heapFree {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : ArenaOK s) {i : Ivl} (hi : Allocated s i) :
    Disj i (heapFree s) := by
  unfold heapFree
  apply Or.inr ∘ Or.inr
  rcases hi with hi | hi
  · exact Or.inl hi.2
  · have hsep : heapLimit ≤ scratchStart := by decide
    have := hs.1; have := hs.2.1; have := hs.2.2.1; have := hs.2.2.2.1; have := hi.1
    exact Or.inr (by dsimp only; omega)

theorem disj_allocated_freeGap {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : ArenaOK s) {i : Ivl} (hi : Allocated s i) :
    Disj i (freeGap s) := by
  unfold freeGap
  apply Or.inr ∘ Or.inr
  rcases hi with hi | hi
  · have hsep : heapLimit ≤ scratchStart := by decide
    have := hs.2.1; have := hs.2.2.1; have := hi.2
    exact Or.inl (by dsimp only; omega)
  · have := hs.2.2.2.1; have := hi.1
    exact Or.inr (by dsimp only; omega)

def IvlUnhit {F : Type} (s post : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  ∀ a : BitVec 64, a.toNat % 8 = 0 → CellHits a.toNat i → post.memory a = s.memory a

/-- Byte-interval unhit from `FrameOutside` when every kept/fresh region is 8-byte aligned:
critical for MPT nibble paths `(p, len)` where `p` or `len` need not be 8-byte aligned. -/
theorem ivlUnhit_of_frameOutside_aligned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hfr : FrameOutside s post keep fresh)
    (hk_al : ∀ j ∈ keep, j.1 % 8 = 0 ∧ j.2 % 8 = 0)
    (hf_al : fresh.1 % 8 = 0 ∧ fresh.2 % 8 = 0)
    (hk : ∀ j ∈ keep, Disj i j) (hf : Disj i fresh) (hi : i.2 ≠ 0) :
    IvlUnhit s post i := by
  intro a ha8 hhit
  obtain ⟨hi1, hi2⟩ := hhit
  apply hfr a
  · intro j hj hcj
    obtain ⟨hj1, hj2⟩ := hk_al j hj
    obtain ⟨hc1, hc2⟩ := hcj
    have hin : j.1 ≤ a.toNat ∧ a.toNat + 8 ≤ j.1 + j.2 := by omega
    rcases hk j hj with hd | hd | hd | hd <;> omega
  · intro hcf
    obtain ⟨hf1, hf2⟩ := hf_al
    obtain ⟨hc1, hc2⟩ := hcf
    have hin : fresh.1 ≤ a.toNat ∧ a.toNat + 8 ≤ fresh.1 + fresh.2 := by omega
    rcases hf with hd | hd | hd | hd <;> omega

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
    obtain ⟨hk3, hal_n, hin_n, hw_n, _, _, hkey_n, _⟩ := hN.1 n hn
    have hhi_n : n + nodeSize (memW s n) ≤ 2 ^ 64 := by
      have := hin_n.2; dsimp [nodeIvl] at this; omega
    have hn8 : n % 8 = 0 := hw_n.1
    have hu_n : IvlUnhit s post (n, nodeSize (memW s n)) := hu_rec n hn
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
          refine ⟨fun k hk => ?_, hag.allocated hal_p, hin_p, ?_⟩
          · rw [hu_byte n hn h12 hlen0 k hk]
            exact hnib k hk
          · intro m hm
            have hm_ivl : nodeIvl post m = nodeIvl s m := by
              have hhm_hi : m + nodeSize (memW s m) ≤ 2 ^ 64 := by
                have := (hN.1 m hm).2.2.1.2; dsimp [nodeIvl] at this; omega
              have hm8 : m % 8 = 0 := (hN.1 m hm).2.2.2.1.1
              have hu_m : IvlUnhit s post (m, nodeSize (memW s m)) := hu_rec m hm
              have hsz_m : 32 ≤ nodeSize (memW s m) := by unfold nodeSize; split_ifs <;> omega
              have hwm : memW post m = memW s m :=
                memW_eq_of_ivlUnhit hu_m hm8 hhm_hi ⟨by omega, by omega⟩
              simp [nodeIvl, hwm]
            rw [hm_ivl]
            exact hdisj_p m hm⟩
  constructor
  · refine ⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩
    · obtain ⟨hk3, hal_n, hin_n, hw_n, hext, hbr, _, hcache, hleaf, hbranch⟩ := hN.1 n hn
      obtain ⟨hw0, hivl_eq, hw_k, _, hkey_post⟩ := hn_props n hn
      rw [hw0, hivl_eq]
      refine ⟨hk3, hag.allocated hal_n, hin_n, wordsOK_transfer hgS hgP hw_n, ?_, ?_, hkey_post, ?_, ?_, ?_⟩
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
      · have hsz : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
        have he := hw_k 2 (by omega)
        simpa only [Nat.reduceMul, he] using hcache
      · intro h1
        have hsz : nodeSize (memW s n) = 64 := by simp [nodeSize, h1]
        have he := hw_k 7 (by omega)
        simpa only [Nat.reduceMul, he] using hleaf h1
      · intro h3
        have hsz : nodeSize (memW s n) = 176 := by simp [nodeSize, h3]
        have he := hw_k 21 (by omega)
        simpa only [Nat.reduceMul, he] using hbranch h3
    · rw [(hn_props n hn).2.1, (hn_props m hm).2.1]
      exact hN.2 n hn m hm hne
  · unfold nodeExtents
    apply List.flatMap_congr
    intro n hn
    rw [(hn_props n hn).2.1, (hn_props n hn).2.2.2.1]

theorem nodeHeap_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) (hbe : post.be = s.be)
    (hag : AllocatorGrows s post)
    {Nd : List Nat} (hN : NodeHeap s Nd)
    (hu : ∀ o ∈ nodeExtents s Nd, IvlUnhit s post o) :
    NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  refine nodeHeap_congr_bytes hgS hgP hag hN
    (fun n hn => hu _ (by unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩))
    (fun n hn h12 hlen0 k hk => ?_)
  rcases (hN.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, _, hin_p, _⟩
  · exact absurd h0 hlen0
  · have hu_p : IvlUnhit s post (memW s (n + 32), memW s (n + 40)) := by
      apply hu
      unfold nodeExtents
      exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
    exact memB_eq_of_ivlUnhit hu_p hbe (by have := hin_p.2; omega) ⟨by omega, by omega⟩


end InitECandidate.Solver.Wave8GuestInv.GuardedBody.Memory

/-! ### From MptDeleteKind3Bound.lean -/


namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
/-- The clock bound is independent of the node kind. Each call is charged once,
and each conditional uses the larger of its two branch charges. -/
theorem mptDelete_body_bound (h : MptDeleteCallees) :
    TerminatingProgBoundedOn GuestInv mptDeleteBody mptDeleteCost := by
  apply TerminatingProgBoundedOn.mono_bound
  · repeat' first
    | exact TerminatingProgBoundedOn.call_guestInv h.fb_mpt_fail _ _
    | exact TerminatingProgBoundedOn.call_guestInv h.fb_node_invalidate _ _
    | exact TerminatingProgBoundedOn.call_guestInv h.fb_memeq _ _
    | exact TerminatingProgBoundedOn.call_guestInv h.fb_common_prefix_length _ _
    | exact TerminatingProgBoundedOn.call_guestInv h.fb_scratch_alloc _ _
    | exact TerminatingProgBoundedOn.call_guestInv h.fb__collapse_branch _ _
    | apply TerminatingProgBoundedOn.decCall_guestInv h.fb_memeq
    | apply TerminatingProgBoundedOn.decCall_guestInv h.fb_common_prefix_length
    | apply TerminatingProgBoundedOn.decCall_guestInv h.fb_scratch_alloc
    | apply TerminatingProgBoundedOn.seq_guestInv
    | apply TerminatingProgBoundedOn.ite_on
    | apply TerminatingProgBoundedOn.dec_on localsFree_guestInv
    | exact fun s hc _ => TerminatingProgBounded.straight _ (by rfl) s hc
  · simp only [mptDeleteCost, Nat.zero_add, Nat.add_zero, Nat.max_zero,
      Nat.zero_max, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, le_refl]

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

/-! ### From MptDeleteKind3Support.lean -/


namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv.GuardedBody.Memory (IvlUnhit wordsOK_transfer
  ivl_allocated_bound memW_eq_of_ivlUnhit memB_eq_of_ivlUnhit
  ivlUnhit_of_frameOutside_aligned disj_allocated_freeGap disj_allocated_heapFree
  disj_allocated_fresh_heap disj_symm)

/-- Changing only locals and clock preserves a key array and a typed heap. -/
theorem mptKeyIn_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (Nd : List Nat) (p len : Nat) :
    KeyIn { s with locals := ls, clock := clock } Nd p len ↔ KeyIn s Nd p len := Iff.rfl

theorem mptNodeHeap_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat) (Nd : List Nat) :
    NodeHeap { s with locals := ls, clock := clock } Nd ↔ NodeHeap s Nd := Iff.rfl

theorem mptStack_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat) (Nd : List Nat) :
    ∀ fs p, MptStack { s with locals := ls, clock := clock } Nd p fs ↔ MptStack s Nd p fs := by
  intro fs
  induction fs with
  | nil => exact fun _ => Iff.rfl
  | cons q qs ih =>
    intro p
    simp only [MptStack, MptFrameOK, mptKeyIn_locals, ih]
    exact Iff.rfl

theorem mptLocN_locals {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ls : HolFiniteMapExact MlS (ValueHOL 64)} {clock : Nat} {n : String}
    (h : ls.lookup (ofString n) = s.locals.lookup (ofString n)) :
    locN { s with locals := ls, clock := clock } n = locN s n := by
  simp only [locN, h]

theorem mptSetVar_locN_ne {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (v : ValueHOL 64) (n : String) (hn : ofString n ≠ name) :
    locN (setVarHOLFinite name v s) n = locN s n := by
  simp only [setVarHOLFinite, locN, HolFiniteMapExact.lookup_update_pointwise, hn, if_false]

theorem mptSetVar_locN_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n : String) (w : BitVec 64) :
    locN (setVarHOLFinite (ofString n) (.val (.word w)) s) n = w.toNat := by
  simp only [setVarHOLFinite, locN, HolFiniteMapExact.lookup_update_pointwise, if_true]

theorem mptDeleteHead_locals {F : Type} {s : PanSemStateFiniteExact 64 F}
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ n ∈ ["top", "res", "go", "level", "klen", "node", "key"],
      ls.lookup (ofString n) = s.locals.lookup (ofString n))
    (hs : MptDeleteHead s) : MptDeleteHead { s with locals := ls, clock := clock } := by
  obtain ⟨ha, Nd, fs, hn, hstack, hres, hactive⟩ := hs
  have heq : ∀ n ∈ ["top", "res", "go", "level", "klen", "node", "key"],
      locN { s with locals := ls, clock := clock } n = locN s n :=
    fun n hn => mptLocN_locals (hl n hn)
  refine ⟨(arenaReady_with_locals s ls clock).2 ha, Nd, fs,
    (mptNodeHeap_locals s ls clock Nd).2 hn, ?_, ?_, ?_⟩
  · rw [heq "top" (by simp)]
    exact (mptStack_locals s ls clock Nd fs _).2 hstack
  · rw [heq "res" (by simp)]
    exact hres
  · intro hgo
    rw [heq "go" (by simp)] at hgo
    obtain ⟨hle, hnode, hkey⟩ := hactive hgo
    simp only [heq "level" (by simp), heq "klen" (by simp), heq "node" (by simp),
      heq "key" (by simp), mptKeyIn_locals]
    exact ⟨hle, hnode, hkey⟩

/-- Saved frames survive a transition that retains their words, node tags and
key arrays. The node heap may grow and the scratch pointer may decrease. -/
theorem mptStack_transfer {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat} (hs : GuestInv s) (ht : GuestInv t)
    (hg : AllocatorGrows s t) (hsub : ∀ n ∈ Nd, n ∈ Nd')
    (hkind : ∀ n ∈ Nd, memW t n = memW s n)
    (hkey : ∀ p len, KeyIn s Nd p len → KeyIn t Nd' p len)
    (hmem : ∀ a, globN s "scratch_ptr" ≤ a → a + 8 ≤ scratchEnd → a % 8 = 0 →
      memW t a = memW s a) :
    ∀ fs p, MptStack s Nd p fs → MptStack t Nd' p fs := by
  intro fs
  induction fs with
  | nil => exact fun _ h => h
  | cons q qs ih =>
    intro p hp
    obtain ⟨hpq, hp0, hf, hrest, htail⟩ := hp
    obtain ⟨hi, hw, hn, hk⟩ := hf
    have hp8 : p % 8 = 0 := hw.1
    have heq (off : Nat) (hoff : off ≤ 32) (hal : off % 8 = 0) :
        memW t (p + off) = memW s (p + off) :=
      hmem _ (by have := hi.1; omega) (by have := hi.2; omega) (by omega)
    have heq0 : memW t p = memW s p := by simpa using heq 0 (by omega) (by decide)
    have heq8 := heq 8 (by omega) (by decide)
    have heq16 := heq 16 (by omega) (by decide)
    have heq24 := heq 24 (by omega) (by decide)
    have heq32 := heq 32 (by omega) (by decide)
    refine ⟨hpq, hp0, ?_, hrest, ?_⟩
    · refine ⟨⟨Nat.le_trans hg.2 hi.1, hi.2⟩, wordsOK_transfer hs ht hw, ?_⟩
      dsimp only
      rw [heq8, heq16, heq24, heq32, hkind _ hn]
      refine ⟨hsub _ hn, ?_⟩
      rcases hk with ⟨h2, hn2, hpath⟩ | ⟨h3, hn3, hidx⟩
      · exact Or.inl ⟨h2, hn2, hkey _ _ hpath⟩
      · exact Or.inr ⟨h3, hn3, hidx⟩
    · rw [heq0]
      exact ih _ htail

/-- A key array survives a node function's frame, including growth of the node
set into fresh heap. -/
theorem mptKeyIn_nodeFrame {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat} (hs : ArenaReady s) (ht : ArenaReady t)
    (hbe : t.be = s.be) (hg : AllocatorGrows s t)
    (hN : NodeHeap s Nd)
    (hkind : ∀ n ∈ Nd, memW t n = memW s n)
    (hfresh : ∀ n ∈ Nd', n ∈ Nd ∨
      Inside (nodeIvl t n) (globN s "heap_ptr") (globN t "heap_ptr"))
    (hfr : FrameOutside s t
      ((Nd.map fun n => nodeIvl s n) ++
        [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr"))
    {p len : Nat} (hk : KeyIn s Nd p len) : KeyIn t Nd' p len := by
  by_cases hlen : len = 0
  · exact Or.inl hlen
  have ⟨hhlo, hhhi, hflo, hgap, hshi, hh8, hf8, hs8⟩ := hs.2
  rcases hk with hz | ⟨hnib, hal, hi, hd⟩
  · exact Or.inl hz
  · right
    have hunhit : IvlUnhit s t (p, len) := by
      apply ivlUnhit_of_frameOutside_aligned hfr
      · intro j hj
        rcases List.mem_append.1 hj with hj | hj
        · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hj
          exact ⟨(hN.1 n hn).2.2.2.1.1, (hN.1 n hn).2.2.2.1.2.1⟩
        · have hj' := List.mem_singleton.1 hj
          subst j
          exact ⟨hf8, by omega⟩
      · exact ⟨hh8, by
          have h8 : heapLimit % 8 = 0 := by decide
          omega⟩
      · intro j hj
        rcases List.mem_append.1 hj with hj | hj
        · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hj
          exact hd n hn
        · have hj' := List.mem_singleton.1 hj
          subst j
          exact disj_allocated_freeGap hs.2 hal
      · exact disj_allocated_heapFree hs.2 hal
      · exact hlen
    refine ⟨?_, hg.allocated hal, hi, ?_⟩
    · intro k hk
      rw [memB_eq_of_ivlUnhit hunhit hbe (by
        have := hi.2
        have hlim : heapLimit ≤ 2 ^ 64 := by decide
        omega) ⟨by omega, by omega⟩]
      exact hnib k hk
    · intro n hn
      rcases hfresh n hn with hold | hnew
      · have hivl : nodeIvl t n = nodeIvl s n := by
          simp only [nodeIvl, hkind n hold]
        rw [hivl]
        exact hd n hold
      · exact disj_symm (disj_allocated_fresh_heap hs.2 ht.2 hal hnew)

/-- A node function cannot overwrite a word in the caller's allocated scratch
stack: nodes lie in the heap, and the scratch write region ends at the old
scratch pointer. -/
theorem mptScratch_nodeFrame {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hs : ArenaReady s) (hN : NodeHeap s Nd)
    (hfr : FrameOutside s t
      ((Nd.map fun n => nodeIvl s n) ++
        [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr"))
    {a : Nat} (hlo : globN s "scratch_ptr" ≤ a) (hhi : a + 8 ≤ scratchEnd) :
    memW t a = memW s a := by
  have ⟨hhlo, hhhi, hflo, hgap, hshi, hh8, hf8, hs8⟩ := hs.2
  have hsep : heapLimit ≤ scratchStart := by decide
  have ha : a < 2 ^ 64 := by
    have hlim : scratchEnd < 2 ^ 64 := by decide
    omega
  have hnat : (BitVec.ofNat 64 a).toNat = a := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  unfold memW
  rw [hfr _ ?_ ?_]
  · intro j hj hhit
    rw [hnat] at hhit
    rcases List.mem_append.1 hj with hj | hj
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hj
      have hin := (hN.1 n hn).2.2.1.2
      change n + nodeSize (memW s n) ≤ heapLimit at hin
      change n < a + 8 ∧ a < n + nodeSize (memW s n) at hhit
      omega
    · obtain rfl := List.mem_singleton.1 hj
      change globN s "frame_mem_ptr" < a + 8 ∧
        a < globN s "frame_mem_ptr" +
          (globN s "scratch_ptr" - globN s "frame_mem_ptr") at hhit
      omega
  · rw [hnat]
    change ¬ (globN s "heap_ptr" < a + 8 ∧
      a < globN s "heap_ptr" + (heapLimit - globN s "heap_ptr"))
    omega

theorem mptFreeFrame_unhit {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hs : ArenaReady s)
    (hfr : FrameOutside s t
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr"))
    {i : Ivl} (hi : Allocated s i) : IvlUnhit s t i := by
  obtain ⟨hhlo, hhhi, hflo, hgap, hshi, hh8, hf8, hs8⟩ := hs.2
  have hsep : heapLimit ≤ scratchStart := by decide
  intro a ha8 hhit
  apply hfr a
  · intro j hj hjhit
    obtain rfl := List.mem_singleton.1 hj
    dsimp [CellHits] at hhit hjhit
    rcases hi with hi | hi <;> dsimp [Inside] at hi <;> omega
  · intro hhit'
    dsimp [CellHits] at hhit hhit'
    rcases hi with hi | hi <;> dsimp [Inside] at hi <;> omega

theorem mptNodeExtents_allocated {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hN : NodeHeap s Nd) {i : Ivl} (hi : i ∈ nodeExtents s Nd) :
    i = (0, 0) ∨ Allocated s i := by
  obtain ⟨n, hn, hi⟩ := List.mem_flatMap.1 hi
  rcases List.mem_cons.1 hi with rfl | hi
  · exact Or.inr (hN.1 n hn).2.1
  · obtain rfl := List.mem_singleton.1 hi
    unfold nodePath
    split
    · rename_i hc
      rcases (hN.1 n hn).2.2.2.2.2.2.1 hc.1 with hz | hk
      · exact (hc.2 hz).elim
      · exact Or.inr hk.2.1
    · exact Or.inl rfl

theorem mptFreeFrame_heap {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hs : ArenaReady s) (ht : ArenaReady t) (hbe : t.be = s.be)
    (hg : AllocatorGrows s t) (hN : NodeHeap s Nd)
    (hfr : FrameOutside s t
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr")) :
    NodeHeap t Nd ∧ (∀ p len, KeyIn s Nd p len → KeyIn t Nd p len) ∧
      (∀ n ∈ Nd, memW t n = memW s n) := by
  have hu : ∀ i ∈ nodeExtents s Nd, IvlUnhit s t i := by
    intro i hi
    rcases mptNodeExtents_allocated hN hi with rfl | hal
    · intro a _ hhit
      exact (Nat.not_lt_zero _ hhit.2).elim
    · exact mptFreeFrame_unhit hs hfr hal
  have hNt := (InitECandidate.Solver.Wave8GuestInv.GuardedBody.Memory.nodeHeap_congr_unhit
    hs.1 ht.1 hbe hg hN hu).1
  have hkind : ∀ n ∈ Nd, memW t n = memW s n := by
    intro n hn
    have hp := hN.1 n hn
    have hmin : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
    exact memW_eq_of_ivlUnhit (mptFreeFrame_unhit hs hfr hp.2.1) hp.2.2.2.1.1
      (ivl_allocated_bound hs.2 hp.2.1).2 ⟨Nat.le_refl _, by dsimp [nodeIvl]; omega⟩
  have hfr' : FrameOutside s t
      ((Nd.map fun n => nodeIvl s n) ++
        [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") := by
    intro a hk hf
    exact hfr a (fun i hi => hk i (List.mem_append_right _ hi)) hf
  exact ⟨hNt, fun _ _ hk => mptKeyIn_nodeFrame hs ht hbe hg hN hkind
    (fun _ hn => Or.inl hn) hfr' hk, hkind⟩

/-- Restore caller locals and optionally bind a local call destination. -/
def mptCallPost {F : Type} (dst : Option MlS)
    (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    PanSemStateFiniteExact 64 F :=
  match dst with
  | none => { post with locals := s.locals }
  | some n => setVarHOLFinite n v { post with locals := s.locals }

theorem mptOneParam_lookup
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fname param : MlS) (shape ret : ShapeHOL) (body : ProgHOL 64) (v : ValueHOL 64)
    {body' : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hi : code.lookup fname = some ([(param, shape)], body, ret))
    (hl : lookupCodeHOLFinite code.lookup fname [v] = some (body', callee, ret')) :
    callee.lookup param = some v := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
  split at hl
  · cases hl
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hl
    obtain ⟨rfl, hrest⟩ := Prod.mk.inj heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrest
    unfold lookupCodeHOLExact at raw
    rw [hi] at raw
    dsimp only at raw
    split at raw
    · have heq := Option.some.inj raw
      obtain ⟨_, hrest⟩ := Prod.mk.inj heq
      obtain ⟨hloc, _⟩ := Prod.mk.inj hrest
      subst hloc
      simp [List.zip, List.foldl]
    · cases raw

theorem mptOneArg_eval {F : Type} {s : PanSemStateFiniteExact 64 F}
    {arg : ExpHOL 64} {values : List (ValueHOL 64)}
    (h : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] = some values) :
    ∃ v, values = [v] ∧ evalAt s arg = some v := by
  rw [evalListHOLFinite_eq_toExact] at h
  simp only [evalListHOLExact] at h
  rcases hv : evalAt s arg with _ | v
  · change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) arg = none at hv
    rw [hv] at h
    cases h
  · change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) arg = some v at hv
    rw [hv] at h
    cases h
    exact ⟨v, rfl, rfl⟩

theorem mptOneLocal_param {F : Type} {s : PanSemStateFiniteExact 64 F}
    {fname : MlS} {param arg : String} {shape ret : ShapeHOL} {body body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    {values : List (ValueHOL 64)}
    (hi : s.code.lookup fname = some ([(ofString param, shape)], body, ret))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString arg)] = some values)
    (hl : lookupCodeHOLFinite s.code.lookup fname values = some (body', callee, ret')) :
    callee.lookup (ofString param) = s.locals.lookup (ofString arg) := by
  obtain ⟨v, rfl, hv⟩ := mptOneArg_eval ha
  have hp := mptOneParam_lookup s.code fname (ofString param) shape ret body v hi hl
  change s.locals.lookup (ofString arg) = some v at hv
  exact hp.trans hv.symm

/-- Normal calls expose their successful argument/lookup/body evaluations to
the postcondition proof. Other outcomes cannot continue the descent. -/
theorem mptCall_hoare
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    (dst : Option MlS) (fname : MlS) (args : List (ExpHOL 64))
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values body callee ret v post,
      s.code = originalRuntimeCode → P s →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      Q none (mptCallPost dst s post v))
    (hother : ∀ {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F),
      r ≠ none → r ≠ some .continue → Q r t) :
    Hoare P (.call (some (dst.map (fun n => (.local, n)), none)) fname args) Q := by
  refine ⟨fun {F} s hc hp _ => ?_⟩
  rw [evaluateHOLFiniteState_call]
  rcases hargs : evalListHOLFinite s
    (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · exact hother _ _ (by simp) (by simp)
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
    · exact hother _ _ (by simp) (by simp)
    · dsimp only
      split
      · exact hother _ _ (by simp) (by simp)
      · rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        cases r with
        | none => exact hother _ _ (by simp) (by simp)
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · cases dst with
              | none => exact hret s values body callee ret v post hc hp hargs hl hr
              | some n =>
                dsimp only [Option.map]
                split
                · exact hret s values body callee ret v post hc hp hargs hl hr
                · exact hother _ _ (by simp) (by simp)
            · exact hother _ _ (by simp) (by simp)
          | «continue» => exact hother _ _ (by simp) (by simp)
          | «break» => exact hother _ _ (by simp) (by simp)
          | timeOut => exact hother _ _ (by simp) (by simp)
          | error => exact hother _ _ (by simp) (by simp)
          | exception _ _ => exact hother _ _ (by simp) (by simp)
          | _ => exact hother _ _ (by simp) (by simp)

theorem mptHoare_seq
    {P R S : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p q : ProgHOL 64}
    (hp : Hoare P p (fun r t => r = none → R t))
    (hq : Hoare R q (fun r t => r = none → S t)) :
    Hoare P (.seq p q) (fun r t => r = none → S t) := by
  apply Hoare.seq (R := R)
  · exact ⟨fun s hc hP hnt => ⟨hp.run s hc hP hnt, fun hn hz => (hn hz).elim⟩⟩
  · exact hq

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

/-! ### From MptDeleteKind3Calls.lean -/


namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
/-- The branch path after reading tag 3 and resetting the descent flag. -/
def MptDeleteBranchReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "go" = 0 ∧ locN s "k" = 3 ∧
    ∃ Nd fs, NodeHeap s Nd ∧ MptStack s Nd (locN s "top") fs ∧
      RootIn Nd (locN s "res") ∧ locN s "level" ≤ locN s "klen" ∧
      NodeKind s Nd "node" 3 ∧
      KeyIn s Nd (locN s "key" + locN s "level") (locN s "klen" - locN s "level")

theorem mptDeleteBranch_head {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : MptDeleteBranchReady s) : MptDeleteHead s := by
  obtain ⟨ha, hgo, _, Nd, fs, hn, hstack, hres, _⟩ := h
  exact ⟨ha, Nd, fs, hn, hstack, hres, fun h => (h hgo).elim⟩

theorem mptInvalidate_lookup : originalRuntimeCode.lookup (ofString "node_invalidate") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_invalidate).2) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 259 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_invalidate) rfl

/-- Invalidation preserves the caller's branch invariant and cannot raise the
scratch pointer. This uses the supplied node contract. -/
theorem mptDeleteBranch_invalidate (h : MptDeleteCallees) (sp : Nat) :
    Hoare (fun s => MptDeleteBranchReady s ∧ globN s "scratch_ptr" ≤ sp)
      (.call (some (none, none)) (ofString "node_invalidate") [.var .local (ofString "node")])
      (fun r t => r = none → MptDeleteBranchReady t ∧ globN t "scratch_ptr" ≤ sp) := by
  apply mptCall_hoare none (ofString "node_invalidate") [.var .local (ofString "node")]
  · intro F s values body callee ret v post hc hp hargs hl hr _
    obtain ⟨⟨ha, hgo, htag, Nd, fs, hn, hstack, hres, hlevel, hnode, hkey⟩, hsp⟩ := hp
    have hparam := mptOneLocal_param (param := "nd") (arg := "node")
      (by rw [hc]; exact mptInvalidate_lookup) hargs hl
    have hloc : locN (callEntryStateHOLFinite s callee) "nd" = locN s "node" := by
      simp only [locN, callEntryStateHOLFinite, hparam]
    have hae : ArenaReady (callEntryStateHOLFinite s callee) :=
      (arenaReady_with_locals s callee (s.clock - 1)).2 ha
    have hne : NodeHeap (callEntryStateHOLFinite s callee) Nd := hn
    have hroots : ∀ n ∈ ["nd"], RootIn Nd (locN (callEntryStateHOLFinite s callee) n) := by
      intro n hmem
      obtain rfl := List.mem_singleton.1 hmem
      rw [hloc]
      exact Or.inr hnode.1
    have hentry : NodeArgs ["nd"] (fun _ _ => True) (callEntryStateHOLFinite s callee) :=
      ⟨hae, Nd, hne, hroots, trivial⟩
    have he := FunSpec.at_lookup h.nf_node_invalidate s hc values body callee ret hl
      hentry (by rw [hr]; simp)
    rw [hr] at he
    obtain ⟨hat, hheap, hscratch, he⟩ := he (Or.inl ⟨v, rfl⟩)
    obtain ⟨Nd', hnt, hsub, hkind, hfresh, hfr, _, _⟩ := he Nd hne hroots trivial
    have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
    rw [hr] at hmeta
    have hbe : post.be = (callEntryStateHOLFinite s callee).be := hmeta.2.2.1
    have hg : AllocatorGrows (callEntryStateHOLFinite s callee) post := ⟨hheap, hscratch⟩
    have hkeys : ∀ p len, KeyIn (callEntryStateHOLFinite s callee) Nd p len → KeyIn post Nd' p len :=
      fun _ _ hk => mptKeyIn_nodeFrame hae hat hbe hg hne hkind hfresh hfr hk
    have hst : MptStack post Nd' (locN s "top") fs :=
      mptStack_transfer hae.1 hat.1 hg hsub hkind hkeys
        (fun _ hlo hhi _ => mptScratch_nodeFrame hae hne hfr hlo hhi) fs _ ((mptStack_locals s callee (s.clock - 1) Nd fs _).2 hstack)
    change MptDeleteBranchReady { post with locals := s.locals } ∧ globN post "scratch_ptr" ≤ sp
    refine ⟨⟨(arenaReady_with_locals post s.locals post.clock).2 hat,
      hgo, htag, Nd', fs, (mptNodeHeap_locals post s.locals post.clock Nd').2 hnt,
      (mptStack_locals post s.locals post.clock Nd' fs _).2 hst, ?_, hlevel, ?_, ?_⟩, ?_⟩
    · rcases hres with hz | hm
      · exact Or.inl hz
      · exact Or.inr (hsub _ hm)
    · exact ⟨hsub _ hnode.1, (hkind _ hnode.1).trans hnode.2⟩
    · exact (mptKeyIn_locals post s.locals post.clock Nd' _ _).2 (hkeys _ _ hkey)
    · change globN post "scratch_ptr" ≤ globN s "scratch_ptr" at hscratch
      omega
  · intro F r t hn _ hr
    exact (hn hr).elim

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

/-! ### From MptDeleteKind3Stores.lean -/


namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
/-- Structural words, separate from the length fields bounded by R10 node typing. -/
def MptStructuralOffset (kind off : Nat) : Prop :=
  off = 0 ∨ ((kind = 1 ∨ kind = 2) ∧ (off = 32 ∨ off = 40)) ∨
    (kind = 2 ∧ off = 48) ∨ (kind = 3 ∧ ∃ i, i < 16 ∧ off = 32 + 8 * i)

theorem mptStructuralOffset_bounds {kind off : Nat} (h : MptStructuralOffset kind off) :
    off + 8 ≤ nodeSize kind ∧ off % 8 = 0 := by
  rcases h with rfl | ⟨hk, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, i, hi, rfl⟩
  all_goals simp only [nodeSize]
  all_goals split_ifs <;> simp_all <;> omega

/-- Preserve structural words, nibble arrays, and the R10 length bounds. -/
theorem mptNodeHeap_fields {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hs : GuestInv s) (ht : GuestInv t) (hg : AllocatorGrows s t)
    (hn : NodeHeap s Nd)
    (hr : ∀ n ∈ Nd, ∀ off, MptStructuralOffset (memW s n) off →
      memW t (n + off) = memW s (n + off))
    (hkey : ∀ p len, KeyIn s Nd p len → KeyIn t Nd p len)
    (hlength : ∀ n ∈ Nd, memW t (n + 16) < 2 ^ 40 ∧
      (memW s n = 1 → memW t (n + 56) < 2 ^ 40) ∧
      (memW s n = 3 → memW t (n + 168) < 2 ^ 40)) : NodeHeap t Nd := by
  have htag : ∀ n ∈ Nd, memW t n = memW s n := fun n hn => by
    simpa only [Nat.add_zero] using hr n hn 0 (Or.inl rfl)
  have hivl : ∀ n ∈ Nd, nodeIvl t n = nodeIvl s n := fun n hn => by
    simp only [nodeIvl, htag n hn]
  refine ⟨fun n hm => ?_, fun n hnm m hm hne => ?_⟩
  · obtain ⟨hk, hal, hi, hw, hext, hbr, hpath, _⟩ := hn.1 n hm
    rw [htag n hm, hivl n hm]
    refine ⟨hk, hg.allocated hal, hi,
      InitECandidate.Solver.Wave8GuestInv.GuardedBody.Memory.wordsOK_transfer hs ht hw, ?_, ?_, ?_, hlength n hm⟩
    · intro h2
      rw [hr n hm 48 (Or.inr (Or.inr (Or.inl ⟨h2, rfl⟩)))]
      exact hext h2
    · intro h3 i hi
      have heq := hr n hm (32 + 8 * i) (Or.inr (Or.inr (Or.inr ⟨h3, i, hi, rfl⟩)))
      rw [← Nat.add_assoc] at heq
      rw [heq]
      exact hbr h3 i hi
    · intro h12
      rw [hr n hm 32 (Or.inr (Or.inl ⟨h12, Or.inl rfl⟩)),
        hr n hm 40 (Or.inr (Or.inl ⟨h12, Or.inr rfl⟩))]
      exact hkey _ _ (hpath h12)
  · rw [hivl n hnm, hivl m hm]
    exact hn.2 n hnm m hm hne

/-- The exact state update made by a successful one-word store. -/
def mptWordWrite {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) (w : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  { s with memory := fun b => if b = BitVec.ofNat 64 a then .word w else s.memory b }

theorem mptWordWrite_memW_ne {F : Type} (s : PanSemStateFiniteExact 64 F)
    {a b : Nat} (w : BitVec 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : b ≠ a) :
    memW (mptWordWrite s a w) b = memW s b := by
  have hbit : BitVec.ofNat 64 b ≠ BitVec.ofNat 64 a := by
    intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact hne this
  simp only [mptWordWrite, memW, hbit, if_false]

theorem mptBranchWrite_reads {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hN : NodeHeap s Nd) {n off : Nat} (hn : n ∈ Nd)
    (hk : memW s n = 3) (hoff : off = 160 ∨ off = 168) (w : BitVec 64) :
    ∀ m ∈ Nd, ∀ k, MptStructuralOffset (memW s m) k →
      memW (mptWordWrite s (n + off) w) (m + k) = memW s (m + k) := by
  have hsize : nodeSize (memW s n) = 176 := by simp [nodeSize, hk]
  have hnhi := (hN.1 n hn).2.2.1.2
  change n + nodeSize (memW s n) ≤ heapLimit at hnhi
  rw [hsize] at hnhi
  have hlim : heapLimit < 2 ^ 64 := by decide
  have ha : n + off < 2 ^ 64 := by rcases hoff with rfl | rfl <;> omega
  intro m hm k hstruct
  obtain ⟨hkb, _⟩ := mptStructuralOffset_bounds hstruct
  have hmhi := (hN.1 m hm).2.2.1.2
  change m + nodeSize (memW s m) ≤ heapLimit at hmhi
  apply mptWordWrite_memW_ne s w ha (by omega)
  by_cases heq : m = n
  · subst m
    rw [hk] at hstruct
    rcases hstruct with hz | ⟨hz, _⟩ | ⟨hz, _⟩ | ⟨_, i, hi, heq⟩
    all_goals rcases hoff with rfl | rfl <;> omega
  · have hd := hN.2 m hm n hn heq
    simp only [Disj, nodeIvl] at hd
    have hmin : 32 ≤ nodeSize (memW s m) := by unfold nodeSize; split_ifs <;> omega
    rw [hsize] at hd
    rcases hoff with rfl | rfl <;> rcases hd with hd | hd <;> omega

/-- A word write contained in a node record leaves every disjoint key byte
unchanged. The byte interval need not be word aligned. -/
theorem mptWordWrite_key {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {n a : Nat} (hn : n ∈ Nd)
    (ha : n ≤ a ∧ a + 8 ≤ n + nodeSize (memW s n)) (ha64 : a < 2 ^ 64)
    (w : BitVec 64)
    (htag : ∀ m ∈ Nd, memW (mptWordWrite s a w) m = memW s m)
    {p len : Nat} (hk : KeyIn s Nd p len) : KeyIn (mptWordWrite s a w) Nd p len := by
  rcases hk with hz | ⟨hnib, hal, hi, hd⟩
  · exact Or.inl hz
  · right
    refine ⟨?_, hal, hi, ?_⟩
    · intro k hk
      have hu : InitECandidate.Solver.Wave8GuestInv.GuardedBody.Memory.IvlUnhit s
          (mptWordWrite s a w) (p, len) := by
        intro b _ hb
        have hne : b ≠ BitVec.ofNat 64 a := by
          intro heq
          subst b
          have hnat : (BitVec.ofNat 64 a).toNat = a := by
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64]
          rw [hnat] at hb
          have hdisj := hd n hn
          simp only [Disj, nodeIvl] at hdisj
          change p < a + 8 ∧ a < p + len at hb
          rcases hdisj with hdisj | hdisj <;> omega
        simp only [mptWordWrite, hne, if_false]
      rw [InitECandidate.Solver.Wave8GuestInv.GuardedBody.Memory.memB_eq_of_ivlUnhit hu rfl (by
        have := hi.2
        have hlim : heapLimit ≤ 2 ^ 64 := by decide
        omega) ⟨by omega, by omega⟩]
      exact hnib k hk
    · intro m hm
      simpa only [nodeIvl, htag m hm] using hd m hm

theorem mptWordWrite_lt {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b : Nat) (w : BitVec 64) {bound : Nat}
    (hw : w.toNat < bound) (hb : memW s b < bound) :
    memW (mptWordWrite s a w) b < bound := by
  simp only [mptWordWrite, memW]
  split
  · exact hw
  · exact hb

theorem mptBranchWrite_heap {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hs : GuestInv s) (hN : NodeHeap s Nd) {n off : Nat} (hn : n ∈ Nd)
    (hk : memW s n = 3) (hoff : off = 160 ∨ off = 168) (w : BitVec 64) (hw : w.toNat < 2 ^ 40) :
    NodeHeap (mptWordWrite s (n + off) w) Nd ∧
      (∀ p len, KeyIn s Nd p len → KeyIn (mptWordWrite s (n + off) w) Nd p len) := by
  have hr := mptBranchWrite_reads hN hn hk hoff w
  have htag : ∀ m ∈ Nd, memW (mptWordWrite s (n + off) w) m = memW s m := by
    intro m hm
    simpa only [Nat.add_zero] using hr m hm 0 (Or.inl rfl)
  have hbound : n + nodeSize (memW s n) ≤ heapLimit := (hN.1 n hn).2.2.1.2
  have hsize : nodeSize (memW s n) = 176 := by simp [nodeSize, hk]
  have ha : n ≤ n + off ∧ n + off + 8 ≤ n + nodeSize (memW s n) := by
    rcases hoff with rfl | rfl <;> rw [hsize] <;> constructor <;> omega
  have ha64 : n + off < 2 ^ 64 := by
    have hlim : heapLimit < 2 ^ 64 := by decide
    omega
  have hkey : ∀ p len, KeyIn s Nd p len → KeyIn (mptWordWrite s (n + off) w) Nd p len :=
    fun _ _ hk => mptWordWrite_key hn ha ha64 w htag hk
  refine ⟨mptNodeHeap_fields hs ?_ ⟨Nat.le_refl _, Nat.le_refl _⟩ hN hr hkey ?_, hkey⟩
  · exact guestInv_congr (s := s) rfl rfl rfl rfl hs
  intro m hm
  obtain ⟨_, _, _, _, _, _, _, hcache, hleaf, hbranch⟩ := hN.1 m hm
  exact ⟨mptWordWrite_lt s _ _ w hw hcache,
    fun h1 => mptWordWrite_lt s _ _ w hw (hleaf h1),
    fun h3 => mptWordWrite_lt s _ _ w hw (hbranch h3)⟩

theorem mptBranchWrite_stack {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hs : ArenaReady s) (hN : NodeHeap s Nd) {n off : Nat} (hn : n ∈ Nd)
    (hk : memW s n = 3) (hoff : off = 160 ∨ off = 168) (w : BitVec 64) (hw : w.toNat < 2 ^ 40)
    {fs : List Nat} {p : Nat} (hst : MptStack s Nd p fs) :
    MptStack (mptWordWrite s (n + off) w) Nd p fs := by
  have ht : GuestInv (mptWordWrite s (n + off) w) :=
    guestInv_congr (s := s) rfl rfl rfl rfl hs.1
  obtain ⟨_, hkey⟩ := mptBranchWrite_heap hs.1 hN hn hk hoff w hw
  have hr := mptBranchWrite_reads hN hn hk hoff w
  have hkind : ∀ m ∈ Nd, memW (mptWordWrite s (n + off) w) m = memW s m := by
    intro m hm
    simpa only [Nat.add_zero] using hr m hm 0 (Or.inl rfl)
  apply mptStack_transfer hs.1 ht ⟨Nat.le_refl _, Nat.le_refl _⟩
    (fun _ hm => hm) hkind hkey ?_ fs p hst
  intro a hlo hhi _
  have hbound := (hN.1 n hn).2.2.1.2
  change n + nodeSize (memW s n) ≤ heapLimit at hbound
  have hsize : nodeSize (memW s n) = 176 := by simp [nodeSize, hk]
  have ⟨_, _, hflo, hgap, _, _, _, _⟩ := hs.2
  have hsep : heapLimit ≤ scratchStart := by decide
  have hlim : scratchEnd < 2 ^ 64 := by decide
  apply mptWordWrite_memW_ne s w
  · rcases hoff with rfl | rfl <;> rw [hsize] at hbound <;> omega
  · omega
  · rcases hoff with rfl | rfl <;> rw [hsize] at hbound <;> omega

theorem mptDeleteBranch_write {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : MptDeleteBranchReady s) {off : Nat} (hoff : off = 160 ∨ off = 168) (w : BitVec 64) (hw : w.toNat < 2 ^ 40) :
    MptDeleteBranchReady (mptWordWrite s (locN s "node" + off) w) := by
  obtain ⟨ha, hgo, htag, Nd, fs, hn, hstack, hres, hlevel, hnode, hkey⟩ := hs
  obtain ⟨hnt, hkeys⟩ := mptBranchWrite_heap ha.1 hn hnode.1 hnode.2 hoff w hw
  refine ⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl ha.1, ha.2⟩,
    hgo, htag, Nd, fs, hnt, ?_, hres, hlevel, ?_, hkeys _ _ hkey⟩
  · exact mptBranchWrite_stack ha hn hnode.1 hnode.2 hoff w hw hstack
  · refine ⟨hnode.1, ?_⟩
    have heq := mptBranchWrite_reads hn hnode.1 hnode.2 hoff w _ hnode.1 0 (Or.inl rfl)
    change memW (mptWordWrite s (locN s "node" + off) w) (locN s "node") = 3
    simpa only [Nat.add_zero, hnode.2] using heq

theorem mptLocN_nonzero {F : Type} {s : PanSemStateFiniteExact 64 F} {n : String}
    (hn : locN s n ≠ 0) :
    ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w)) ∧ w.toNat = locN s n := by
  unfold locN at hn ⊢
  split at hn
  · rename_i w hw
    exact ⟨w, hw, rfl⟩
  · contradiction

theorem mptStore_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dst src : ExpHOL 64) (a w : BitVec 64)
    (hd : evalAt s dst = some (.val (.word a)))
    (hv : evalAt s src = some (.val (.word w))) (ha : s.memaddrs a) :
    evaluateHOLFiniteState s (.store dst src) =
      (none, { s with memory := fun b => if b = a then .word w else s.memory b }) := by
  rw [evaluateHOLFiniteState_store]
  change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst = _ at hd
  change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) src = _ at hv
  rw [hd, hv]
  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, ha, if_true]

theorem mptDeleteBranch_store_eval {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : MptDeleteBranchReady s) {off : Nat} (hoff : off = 160 ∨ off = 168) :
    evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 off)]) (.const 0)) =
      (none, mptWordWrite s (locN s "node" + off) 0) := by
  obtain ⟨ha, _, _, Nd, fs, hN, _, _, _, hnode, _⟩ := hs
  obtain ⟨_, _, hinside, hw, _⟩ := hN.1 _ hnode.1
  have hsize : nodeSize (memW s (locN s "node")) = 176 := by simp [nodeSize, hnode.2]
  change sourceBase ≤ locN s "node" ∧
    locN s "node" + nodeSize (memW s (locN s "node")) ≤ heapLimit at hinside
  change locN s "node" % 8 = 0 ∧ _ at hw
  rw [hsize] at hinside
  have hnonnull : locN s "node" ≠ 0 := by
    have hbase : 0 < sourceBase := by decide
    omega
  obtain ⟨nw, hnw, hnat⟩ := mptLocN_nonzero hnonnull
  have hoff64 : off < 2 ^ 64 := by rcases hoff with rfl | rfl <;> decide
  have hadd : nw + BitVec.ofNat 64 off = BitVec.ofNat 64 (locN s "node" + off) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64, hnat]
  apply mptStore_eval s _ _ (BitVec.ofNat 64 (locN s "node" + off)) 0
  · change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) _ = _
    simp [evalHOLExact, evalListHOLExact, hnw, valueIsWord, valueWord, wordOpHOL, wordOp, hadd]
  · rfl
  · obtain ⟨_, hdom, _⟩ := InitECandidate.Solver.Wave8GuestInv.GuardedBody.Memory.wordAt_of_ordinary ha.1
      (a := locN s "node" + off)
      (by rcases hoff with rfl | rfl <;> omega)
      (by omega)
      (by have hlim : heapLimit ≤ heapEnd := by decide
          rcases hoff with rfl | rfl <;> omega)
    exact hdom

theorem mptDeleteBranch_store (off : Nat) (hoff : off = 160 ∨ off = 168) :
    Hoare MptDeleteBranchReady
      (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 off)]) (.const 0))
      (fun r t => r = none → MptDeleteBranchReady t) := by
  refine ⟨fun s _ hs _ _ => ?_⟩
  rw [mptDeleteBranch_store_eval hs hoff]
  exact mptDeleteBranch_write hs hoff 0 (by decide)

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

/-! ### From MptDeleteKind3Value.lean -/


namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
theorem mptCollapse_lookup : originalRuntimeCode.lookup (ofString "_collapse_branch") =
    some ((sourceFunctionEntry Guest.Software.guestFn__collapse_branch).2) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 276 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__collapse_branch) rfl

/-- A branch collapse returns a typed result while preserving the saved stack. -/
theorem mptDeleteBranch_collapse (h : MptDeleteCallees) :
    Hoare MptDeleteBranchReady
      (.call (some (some (.local, ofString "res"), none)) (ofString "_collapse_branch")
        [.var .local (ofString "node")])
      (fun r t => r = none → MptDeleteHead t ∧ locN t "go" = 0) := by
  apply mptCall_hoare (some (ofString "res")) (ofString "_collapse_branch")
    [.var .local (ofString "node")]
  · intro F s values body callee ret v post hc hp hargs hl hr _
    obtain ⟨ha, hgo, _, Nd, fs, hn, hstack, _, _, hnode, _⟩ := hp
    have hparam := mptOneLocal_param (param := "node") (arg := "node")
      (by rw [hc]; exact mptCollapse_lookup) hargs hl
    have hloc : locN (callEntryStateHOLFinite s callee) "node" = locN s "node" := by
      simp only [locN, callEntryStateHOLFinite, hparam]
    have hae : ArenaReady (callEntryStateHOLFinite s callee) :=
      (arenaReady_with_locals s callee (s.clock - 1)).2 ha
    have hne : NodeHeap (callEntryStateHOLFinite s callee) Nd := hn
    have hroots : ∀ n ∈ ["node"], RootIn Nd (locN (callEntryStateHOLFinite s callee) n) := by
      intro n hmem
      obtain rfl := List.mem_singleton.1 hmem
      rw [hloc]
      exact Or.inr hnode.1
    have hreq : NodeKind (callEntryStateHOLFinite s callee) Nd "node" 3 := by
      change locN (callEntryStateHOLFinite s callee) "node" ∈ Nd ∧
        memW s (locN (callEntryStateHOLFinite s callee) "node") = 3
      rw [hloc]
      exact hnode
    have hentry : NodeArgs ["node"] (fun s Nd => NodeKind s Nd "node" 3)
        (callEntryStateHOLFinite s callee) := ⟨hae, Nd, hne, hroots, hreq⟩
    have he := FunSpec.at_lookup h.nf__collapse_branch s hc values body callee ret hl
      hentry (by rw [hr]; simp)
    rw [hr] at he
    obtain ⟨hat, hheap, hscratch, he⟩ := he (Or.inl ⟨v, rfl⟩)
    obtain ⟨Nd', hnt, hsub, hkind, hfresh, hfr, _, hret⟩ := he Nd hne hroots hreq
    obtain ⟨w, rfl, hroot⟩ := hret v rfl
    have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
    rw [hr] at hmeta
    have hbe : post.be = (callEntryStateHOLFinite s callee).be := hmeta.2.2.1
    have hg : AllocatorGrows (callEntryStateHOLFinite s callee) post := ⟨hheap, hscratch⟩
    have hkeys : ∀ p len, KeyIn (callEntryStateHOLFinite s callee) Nd p len → KeyIn post Nd' p len :=
      fun _ _ hk => mptKeyIn_nodeFrame hae hat hbe hg hne hkind hfresh hfr hk
    have hst : MptStack post Nd' (locN s "top") fs :=
      mptStack_transfer hae.1 hat.1 hg hsub hkind hkeys
        (fun _ hlo hhi _ => mptScratch_nodeFrame hae hne hfr hlo hhi) fs _
        ((mptStack_locals s callee (s.clock - 1) Nd fs _).2 hstack)
    let t := setVarHOLFinite (ofString "res") (.val (.word w)) { post with locals := s.locals }
    change MptDeleteHead t ∧ locN t "go" = 0
    have htgo : locN t "go" = 0 := by
      rw [mptSetVar_locN_ne _ _ _ "go" (by decide)]
      exact hgo
    have httop : locN t "top" = locN s "top" :=
      mptSetVar_locN_ne _ _ _ "top" (by decide)
    have htres : locN t "res" = w.toNat := mptSetVar_locN_word _ _ _
    refine ⟨⟨?_, Nd', fs, ?_, ?_, ?_, fun hg => (hg htgo).elim⟩, htgo⟩
    · exact (arenaReady_with_locals post t.locals post.clock).2 hat
    · exact (mptNodeHeap_locals post t.locals post.clock Nd').2 hnt
    · rw [httop]
      exact (mptStack_locals post t.locals post.clock Nd' fs _).2 hst
    · rw [htres]
      exact hroot
  · intro F r t hn _ hr
    exact (hn hr).elim

theorem mptDeleteBranch_keep_node :
    Hoare MptDeleteBranchReady (.assign .local (ofString "res") (.var .local (ofString "node")))
      (fun r t => r = none → MptDeleteHead t ∧ locN t "go" = 0) := by
  apply Hoare.assign
  · intro F s v hs hv _
    obtain ⟨ha, hgo, _, Nd, fs, hn, hstack, _, _, hnode, _⟩ := hs
    have hnonnull : locN s "node" ≠ 0 := by
      have := (hn.1 _ hnode.1).2.2.1.1
      have hbase : 0 < sourceBase := by decide
      change sourceBase ≤ locN s "node" at this
      omega
    obtain ⟨w, hw, hnat⟩ := mptLocN_nonzero hnonnull
    change s.locals.lookup (ofString "node") = some v at hv
    rw [hw] at hv
    cases hv
    change MptDeleteHead (setVarHOLFinite (ofString "res") (.val (.word w)) s) ∧
      locN (setVarHOLFinite (ofString "res") (.val (.word w)) s) "go" = 0
    let t := setVarHOLFinite (ofString "res") (.val (.word w)) s
    have htgo : locN t "go" = 0 := by
      rw [mptSetVar_locN_ne _ _ _ "go" (by decide)]
      exact hgo
    have httop : locN t "top" = locN s "top" := mptSetVar_locN_ne _ _ _ _ (by decide)
    have htres : locN t "res" = w.toNat := mptSetVar_locN_word _ _ _
    refine ⟨⟨(arenaReady_with_locals s t.locals s.clock).2 ha,
      Nd, fs, (mptNodeHeap_locals s t.locals s.clock Nd).2 hn, ?_, ?_,
      fun hg => (hg htgo).elim⟩, htgo⟩
    · rw [httop]
      exact (mptStack_locals s t.locals s.clock Nd fs _).2 hstack
    · rw [htres, hnat]
      exact Or.inr hnode.1
  · intro F s hs hz
    cases hz

def mptDeleteValueCode : ProgHOL 64 :=
  .ite (.cmp .equal
      (.load .one (.op .add [.var .local (ofString "node"), .const 168])) (.const 0))
    (.assign .local (ofString "res") (.var .local (ofString "node")))
    (.seq (.store (.op .add [.var .local (ofString "node"), .const 160]) (.const 0))
      (.seq (.store (.op .add [.var .local (ofString "node"), .const 168]) (.const 0))
        (.call (some (some (.local, ofString "res"), none)) (ofString "_collapse_branch")
          [.var .local (ofString "node")])))

/-- The complete terminal branch, including the two value-clearing stores. -/
theorem mptDeleteBranch_value (h : MptDeleteCallees) :
    Hoare MptDeleteBranchReady mptDeleteValueCode
      (fun r t => r = none → MptDeleteHead t ∧ locN t "go" = 0) := by
  apply Hoare.ite
  · exact Hoare.mono mptDeleteBranch_keep_node (fun _ h => h.1)
  · exact Hoare.mono
      (mptHoare_seq (mptDeleteBranch_store 160 (Or.inl rfl))
        (mptHoare_seq (mptDeleteBranch_store 168 (Or.inr rfl)) (mptDeleteBranch_collapse h)))
      (fun _ h => h.1)
  · intro F s hs hr
    cases hr

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

/-! ### From MptDeleteKind3Flow.lean -/


namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
theorem mptSeq_none {F : Type} {s t : PanSemStateFiniteExact 64 F} {p q : ProgHOL 64}
    (hr : evaluateHOLFiniteState s (.seq p q) = (none, t)) :
    ∃ mid, evaluateHOLFiniteState s p = (none, mid) ∧ evaluateHOLFiniteState mid q = (none, t) := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases hp : evaluateHOLFiniteState s p with ⟨r, mid⟩
  rw [hp] at hr
  cases r with
  | none => exact ⟨mid, rfl, hr⟩
  | some r => cases hr

theorem mptDec_none {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hr : evaluateHOLFiniteState s (.dec name shape init body) = (none, t)) :
    ∃ v inner, evalAt s init = some v ∧
      evaluateHOLFiniteState (setVarHOLFinite name v s) body = (none, inner) ∧
      t = { inner with locals := HolFiniteMapExact.resVarEq inner.locals (name, s.locals.lookup name) } := by
  rw [evaluateHOLFiniteState_dec_total] at hr
  dsimp only at hr
  split at hr
  · cases hr
  · rename_i v hv
    split at hr
    · rcases hb : evaluateHOLFiniteState (setVarHOLFinite name v s) body with ⟨r, inner⟩
      simp only [hb] at hr
      obtain ⟨rfl, heq⟩ := Prod.mk.inj hr
      exact ⟨v, inner, hv, hb, heq.symm⟩
    · cases hr

theorem mptDecCall_none {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {name fname : MlS} {shape : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hr : evaluateHOLFiniteState s (.decCall name shape fname args cont) = (none, t)) :
    ∃ values body callee ret v post inner,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) ∧
      evaluateHOLFiniteState (setVarHOLFinite name v { post with locals := s.locals }) cont = (none, inner) ∧
      t = { inner with locals := HolFiniteMapExact.resVarEq inner.locals (name, s.locals.lookup name) } := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · simp only [ha] at hr
    cases hr
  · simp only [ha] at hr
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
    · simp only [hl] at hr
      cases hr
    · simp only [hl] at hr
      split at hr
      · cases hr
      · rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        simp only [hb] at hr
        cases r with
        | none => cases hr
        | some r =>
          cases r with
          | returned v =>
            simp only at hr
            split at hr
            · rcases hcont : evaluateHOLFiniteState
                (setVarHOLFinite name v { post with locals := s.locals }) cont with ⟨r, inner⟩
              simp only [hcont] at hr
              obtain ⟨rfl, heq⟩ := Prod.mk.inj hr
              exact ⟨values, body, callee, ret, v, post, inner, rfl, hl, hb, hcont, heq.symm⟩
            · cases hr
          | _ => cases hr

theorem mptValid_word_local {F : Type} {s : PanSemStateFiniteExact 64 F}
    {name : MlS} {w : BitVec 64}
    (h : isValidValueHOLExact s.toExact .local name (.val (.word w)) = true) :
    ∃ old : BitVec 64, s.locals.lookup name = some (.val (.word old)) := by
  simp only [isValidValueHOLExact, lookupKvarHOLExact] at h
  rcases hl : s.locals.lookup name with _ | v
  · rw [hl] at h
    cases h
  · rw [hl] at h
    cases v with
    | val v => cases v with | word old => exact ⟨old, rfl⟩
    | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at h
    | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at h

theorem mptAssign_none {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {name : MlS} {source : ExpHOL 64}
    (hr : evaluateHOLFiniteState s (.assign .local name source) = (none, t)) :
    ∃ v, evalAt s source = some v ∧
      isValidValueHOLExact s.toExact .local name v = true ∧
      t = setVarHOLFinite name v s := by
  rw [evaluateHOLFiniteState_assign] at hr
  split at hr
  · cases hr
  · rename_i v hv
    split at hr
    · rename_i hvalid
      exact ⟨v, hv, hvalid, (Prod.mk.inj hr).2.symm⟩
    · cases hr

 theorem mptStore_locals {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {dst src : ExpHOL 64}
    (hr : evaluateHOLFiniteState s (.store dst src) = (none, t)) : t.locals = s.locals := by
  have h := (evaluate_store_control_frame s dst src).2.1
  simpa only [hr] using h

theorem mptIte_none {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hr : evaluateHOLFiniteState s (.ite cond yes no) = (none, t)) :
    (CondTrue cond s ∧ evaluateHOLFiniteState s yes = (none, t)) ∨
      (CondFalse cond s ∧ evaluateHOLFiniteState s no = (none, t)) := by
  rw [evaluateHOLFiniteState_ite] at hr
  split at hr
  · rename_i w hw
    split at hr
    · rename_i hz
      subst w
      exact Or.inr ⟨hw, hr⟩
    · rename_i hz
      exact Or.inl ⟨⟨w, hw, hz⟩, hr⟩
  · cases hr

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

/-! ### From MptDeleteKind3Fresh.lean -/


namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
theorem mptKeyIn_sub {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {p len q size : Nat} (hk : KeyIn s Nd p len)
    (hpq : p ≤ q) (hhi : q + size ≤ p + len) : KeyIn s Nd q size := by
  by_cases hz : size = 0
  · exact Or.inl hz
  · rcases hk with hl | ⟨hnib, hal, hi, hd⟩
    · omega
    · right
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro k hk
        have heq : q + k = p + (q - p + k) := by omega
        rw [heq]
        exact hnib _ (by omega)
      · rcases hal with hal | hal <;> [left; right] <;> constructor <;> dsimp [Inside] at * <;> omega
      · constructor <;> dsimp [Inside] at * <;> omega
      · intro n hn
        have hh := hd n hn
        unfold Disj at hh ⊢
        dsimp only at hh ⊢
        rcases hh with hh | hh
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)

theorem mptStack_addresses {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} : ∀ fs p, MptStack s Nd p fs →
      ∀ q ∈ fs, globN s "scratch_ptr" ≤ q := by
  intro fs
  induction fs with
  | nil => simp
  | cons f fs ih =>
    intro p hs q hq
    obtain ⟨rfl, _, hf, _, ht⟩ := hs
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hf.1.1
    · exact ih _ ht q hq

theorem mptFreeFrame_stack {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hs : ArenaReady s) (ht : ArenaReady t) (hbe : t.be = s.be)
    (hg : AllocatorGrows s t) (hN : NodeHeap s Nd)
    (hfr : FrameOutside s t
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr")) :
    ∀ fs p, MptStack s Nd p fs → MptStack t Nd p fs := by
  obtain ⟨_, hkeys, hkind⟩ := mptFreeFrame_heap hs ht hbe hg hN hfr
  apply mptStack_transfer hs.1 ht.1 hg (fun _ hn => hn) hkind hkeys
  intro a hlo hhi _
  apply mptScratch_nodeFrame hs hN (a := a) ?_ hlo hhi
  intro a hk hf
  exact hfr a (fun i hi => hk i (List.mem_append_right _ hi)) hf

theorem mptFreeFrame_write {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {a : Nat} (w : BitVec 64)
    (ha : globN s "frame_mem_ptr" ≤ a ∧ a + 8 ≤ globN s "scratch_ptr")
    (ha64 : a < 2 ^ 64)
    (hf : FrameOutside s t
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr")) :
    FrameOutside s (mptWordWrite t a w)
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") := by
  intro b hk hheap
  have hne : b ≠ BitVec.ofNat 64 a := by
    intro heq
    subst b
    have hn : (BitVec.ofNat 64 a).toNat = a := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64]
    have hh := hk _ (List.mem_singleton_self _)
    rw [hn] at hh
    apply hh
    change globN s "frame_mem_ptr" < a + 8 ∧
      a < globN s "frame_mem_ptr" + (globN s "scratch_ptr" - globN s "frame_mem_ptr")
    constructor <;> omega
  simpa only [mptWordWrite, hne, if_false] using hf b hk hheap

theorem mptWordWrite_same {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a : Nat) (w : BitVec 64) : memW (mptWordWrite s a w) a = w.toNat := by
  simp [mptWordWrite, memW]

theorem mptLocal_word {F : Type} {s : PanSemStateFiniteExact 64 F} {n : String}
    {v : BitVec 64} (h : s.locals.lookup (ofString n) = some (.val (.word v))) :
    locN s n = v.toNat := by simp only [locN, h]

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

/-! ### From MptDeleteKind3Eval.lean -/


namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
theorem mptAddLocals_eval {F : Type} {s : PanSemStateFiniteExact 64 F}
    {n m : String} {a b : BitVec 64}
    (ha : s.locals.lookup (ofString n) = some (.val (.word a)))
    (hb : s.locals.lookup (ofString m) = some (.val (.word b))) :
    evalAt s (.op .add [.var .local (ofString n), .var .local (ofString m)]) =
      some (.val (.word (a + b))) := by
  simp [evalAt, evalHOLExact, evalListHOLExact, ha, hb, valueIsWord, valueWord, wordOpHOL, wordOp]

theorem mptAddConst_eval {F : Type} {s : PanSemStateFiniteExact 64 F}
    {n : String} {a : BitVec 64} (off : Nat)
    (ha : s.locals.lookup (ofString n) = some (.val (.word a))) :
    evalAt s (.op .add [.var .local (ofString n), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (BitVec.ofNat 64 (a.toNat + off)))) := by
  have heq : a + BitVec.ofNat 64 off = BitVec.ofNat 64 (a.toNat + off) := by
    simp [BitVec.ofNat_add]
  simp [evalAt, evalHOLExact, evalListHOLExact, ha, valueIsWord, valueWord, wordOpHOL, wordOp, heq]

theorem mptAddLocals_inv {F : Type} {s : PanSemStateFiniteExact 64 F}
    {n m : String} {v : ValueHOL 64}
    (h : evalAt s (.op .add [.var .local (ofString n), .var .local (ofString m)]) = some v) :
    ∃ a b : BitVec 64,
      s.locals.lookup (ofString n) = some (.val (.word a)) ∧
      s.locals.lookup (ofString m) = some (.val (.word b)) ∧ v = .val (.word (a + b)) := by
  cases ha : s.locals.lookup (ofString n) with
  | none => simp [evalAt, evalHOLExact, evalListHOLExact, ha] at h
  | some a =>
    cases hb : s.locals.lookup (ofString m) with
    | none => simp [evalAt, evalHOLExact, evalListHOLExact, ha, hb] at h
    | some b =>
      cases a <;> cases b
      all_goals simp only [evalAt, evalHOLExact, evalListHOLExact, ha, hb] at h
      all_goals try { simp [valueIsWord] at h }
      rename_i a b
      cases a with | word a =>
        cases b with | word b =>
          simp only [List.all_cons, List.all_nil, valueIsWord, Bool.and_self, if_true, List.map_cons, List.map_nil, valueWord, wordOpHOL, wordOp, Option.map_some, List.foldr, BitVec.add_zero] at h
          refine ⟨a, b, rfl, rfl, ?_⟩
          simpa using (Option.some.inj h).symm

theorem mptLoad_inv {F : Type} {s : PanSemStateFiniteExact 64 F}
    {addr : ExpHOL 64} {a : Nat} {v : ValueHOL 64}
    (ha : evalAt s addr = some (.val (.word (BitVec.ofNat 64 a))))
    (hv : evalAt s (.load .one addr) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat = memW s a := by
  change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addr = _ at ha
  simp only [evalAt, evalHOLExact, isWfShapeExactHOL, ha, memLoadHOLExact] at hv
  cases hm : s.memory (BitVec.ofNat 64 a) with
  | word w =>
    simp only [hm] at hv
    simp only [if_true] at hv
    split at hv
    · exact ⟨w, (Option.some.inj hv).symm, by simp only [memW, hm]⟩
    · cases hv

theorem mptByte_inv {F : Type} {s : PanSemStateFiniteExact 64 F}
    {addr : ExpHOL 64} {a : Nat} {v : ValueHOL 64}
    (ha : evalAt s addr = some (.val (.word (BitVec.ofNat 64 a))))
    (hv : evalAt s (.loadByte addr) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat = memB s a := by
  change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addr = _ at ha
  simp only [evalAt, evalHOLExact, ha, panMemLoadByteHOL] at hv
  cases hm : s.memory (panByteAlignHOL (BitVec.ofNat 64 a)) with
  | word w =>
    simp only [hm] at hv
    split at hv
    · simp only [Option.map_some] at hv
      refine ⟨_, (Option.some.inj hv).symm, ?_⟩
      simp only [BitVec.toNat_ofNat, memB, hm]
      apply Nat.mod_eq_of_lt
      have hh := (panGetByteHOL (BitVec.ofNat 64 a) w s.be).toNat_lt
      omega
    · cases hv

theorem mptStore_word_none {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {dst src : ExpHOL 64} {a : Nat} {w : BitVec 64}
    (hd : evalAt s dst = some (.val (.word (BitVec.ofNat 64 a))))
    (hv : evalAt s src = some (.val (.word w)))
    (hr : evaluateHOLFiniteState s (.store dst src) = (none, t)) :
    t = mptWordWrite s a w := by
  rw [evaluateHOLFiniteState_store] at hr
  change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst = _ at hd
  change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) src = _ at hv
  rw [hd, hv] at hr
  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hr
  by_cases hdom : s.memaddrs (BitVec.ofNat 64 a)
  · simp only [hdom, if_true] at hr
    exact (Prod.mk.inj hr).2.symm
  · simp only [hdom, if_false] at hr
    cases hr

theorem mptByte_addr {F : Type} {s : PanSemStateFiniteExact 64 F}
    {addr : ExpHOL 64} {v : ValueHOL 64}
    (hv : evalAt s (.loadByte addr) = some v) :
    ∃ a : BitVec 64, evalAt s addr = some (.val (.word a)) := by
  unfold evalAt at hv
  rw [evalHOLExact] at hv
  split at hv
  · rename_i a ha
    exact ⟨a, ha⟩
  · cases hv

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

/-! ### From MptDeleteKind3Alloc.lean -/


namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
theorem mptScratch_lookup : originalRuntimeCode.lookup (ofString "scratch_alloc") =
    some ((sourceFunctionEntry Guest.Software.guestFn_scratch_alloc).2) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 13 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_scratch_alloc) rfl

theorem mptScratch_return (h : MptDeleteCallees)
    {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret : ShapeHOL} {v : ValueHOL 64}
    (hc : s.code = originalRuntimeCode) (hs : ArenaReady s)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 40] = some values)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "scratch_alloc") values = some (body, callee, ret))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ ArenaReady post ∧ AllocatorGrows s post ∧
      FreshScratch s post w.toNat 40 ∧ globN post "scratch_ptr" = w.toNat ∧
      post.be = s.be ∧
      FrameOutside s post
        [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
        (globN s "heap_ptr", heapLimit - globN s "heap_ptr") := by
  obtain ⟨arg, rfl, harg⟩ := mptOneArg_eval ha
  have heq := evalAt_const s 40 arg harg
  subst arg
  have hn := mptOneParam_lookup s.code (ofString "scratch_alloc") (ofString "n") .one .one
    (sourceFunctionEntry Guest.Software.guestFn_scratch_alloc).2.2.1 (.val (.word 40))
    (by rw [hc]; exact mptScratch_lookup) hl
  have hae : ArenaReady (callEntryStateHOLFinite s callee) :=
    (arenaReady_with_locals s callee (s.clock - 1)).2 hs
  have hn40 : locN (callEntryStateHOLFinite s callee) "n" = 40 := by
    simp only [locN, callEntryStateHOLFinite, hn]
    rfl
  have hrn := FunSpec.at_lookup h.rt_scratch_alloc s hc _ _ _ _ hl hae (by rw [hr]; simp)
  rw [hr] at hrn
  obtain ⟨w, rfl, hat, hg, hfresh, hsp⟩ := hrn _ rfl
  rw [hn40] at hfresh
  have hw := FunSpec.at_lookup h.ww_scratch_alloc s hc _ _ _ _ hl hae (by rw [hr]; simp)
  rw [hr] at hw
  obtain ⟨_, _, _, hframe, _⟩ := hw (Or.inl ⟨.val (.word w), rfl⟩)
  have hm := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
  rw [hr] at hm
  exact ⟨w, rfl, hat, hg, hfresh, hsp, hm.2.2.1, hframe⟩

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

/-! ### From MptDeleteKind3Push.lean -/


namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
def mptBranchFrame {F : Type} (s : PanSemStateFiniteExact 64 F) (p : Nat)
    (top node idx : BitVec 64) : PanSemStateFiniteExact 64 F :=
  mptWordWrite (mptWordWrite (mptWordWrite (mptWordWrite s p top) (p + 8) node)
    (p + 16) 3) (p + 32) idx

theorem mptBranchFrame_reads {F : Type} (s : PanSemStateFiniteExact 64 F) (p : Nat)
    (top node idx : BitVec 64) (hp : p + 40 < 2 ^ 64) :
    memW (mptBranchFrame s p top node idx) p = top.toNat ∧
    memW (mptBranchFrame s p top node idx) (p + 8) = node.toNat ∧
    memW (mptBranchFrame s p top node idx) (p + 16) = 3 ∧
    memW (mptBranchFrame s p top node idx) (p + 32) = idx.toNat := by
  unfold mptBranchFrame
  constructor
  · rw [mptWordWrite_memW_ne _ idx (by omega) (by omega) (by omega),
      mptWordWrite_memW_ne _ 3 (by omega) (by omega) (by omega),
      mptWordWrite_memW_ne _ node (by omega) (by omega) (by omega), mptWordWrite_same]
  constructor
  · rw [mptWordWrite_memW_ne _ idx (by omega) (by omega) (by omega),
      mptWordWrite_memW_ne _ 3 (by omega) (by omega) (by omega), mptWordWrite_same]
  constructor
  · rw [mptWordWrite_memW_ne _ idx (by omega) (by omega) (by omega), mptWordWrite_same]
    rfl
  · exact mptWordWrite_same _ _ _

theorem mptBranchFrame_push {F : Type} {s u : PanSemStateFiniteExact 64 F}
    {Nd fs : List Nat} {oldtop p : Nat} {top node idx : BitVec 64}
    (hs : ArenaReady s) (hu : ArenaReady u) (hbe : u.be = s.be)
    (hg : AllocatorGrows s u) (hfresh : FreshScratch s u p 40)
    (hn : NodeHeap s Nd) (hst : MptStack s Nd oldtop fs)
    (htop : top.toNat = oldtop) (hnode : node.toNat ∈ Nd) (hkind : memW s node.toNat = 3)
    (hi : idx.toNat < 16)
    (hfr : FrameOutside s u
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr")) :
    let d := mptBranchFrame u p top node idx
    ArenaReady d ∧ NodeHeap d Nd ∧ MptStack d Nd p (p :: fs) ∧
      (∀ q len, KeyIn s Nd q len → KeyIn d Nd q len) ∧
      (∀ n ∈ Nd, memW d n = memW s n) := by
  dsimp only
  let d := mptBranchFrame u p top node idx
  obtain ⟨hp8, hpframe, hpinside, hpwords⟩ := hfresh
  change globN u "scratch_ptr" ≤ p ∧ p + 40 ≤ globN s "scratch_ptr" at hpinside
  change WordsOK u (p, 40) at hpwords
  have hlim : scratchEnd < 2 ^ 64 := by decide
  have hp64 : p + 40 < 2 ^ 64 := by have := hs.2.2.2.2.2.1; omega
  have hfd : FrameOutside s d
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") := by
    apply mptFreeFrame_write idx ⟨by omega, by omega⟩ (by omega)
    apply mptFreeFrame_write 3 ⟨by omega, by omega⟩ (by omega)
    apply mptFreeFrame_write node ⟨by omega, by omega⟩ (by omega)
    exact mptFreeFrame_write top ⟨hpframe, by omega⟩ (by omega) hfr
  have hd : ArenaReady d := ⟨guestInv_congr (s := u) rfl rfl rfl rfl hu.1, hu.2⟩
  obtain ⟨hnd, hkeys, htags⟩ := mptFreeFrame_heap hs hd hbe hg hn hfd
  have hold := mptFreeFrame_stack hs hd hbe hg hn hfd fs oldtop hst
  have hreads := mptBranchFrame_reads u p top node idx hp64
  have hstack : MptStack d Nd p (p :: fs) := by
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · have hb : 0 < scratchStart := by decide
      have hf := hs.2.2.2.1
      omega
    · refine ⟨⟨hpinside.1, ?_⟩,
        InitECandidate.Solver.Wave8GuestInv.GuardedBody.Memory.wordsOK_transfer hu.1 hd.1 hpwords, ?_⟩
      · exact Nat.le_trans hpinside.2 hs.2.2.2.2.2.1
      · dsimp only
        rw [hreads.2.1, hreads.2.2.1, hreads.2.2.2, htags _ hnode]
        exact ⟨hnode, Or.inr ⟨rfl, hkind, hi⟩⟩
    · intro r hr
      exact Nat.le_trans hpinside.2 (mptStack_addresses fs oldtop hst r hr)
    · rw [hreads.1, htop]
      exact hold
  exact ⟨hd, hnd, hstack, hkeys, htags⟩

def mptBranchCont : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "fr2"), .const 0]) (.var .local (ofString "top")))
    (.seq (.store (.op .add [.var .local (ofString "fr2"), .const 8]) (.var .local (ofString "node")))
    (.seq (.store (.op .add [.var .local (ofString "fr2"), .const 16]) (.const 3))
    (.seq (.store (.op .add [.var .local (ofString "fr2"), .const 32]) (.var .local (ofString "idx")))
    (.seq (.assign .local (ofString "top") (.var .local (ofString "fr2")))
    (.seq (.assign .local (ofString "node") (.load .one (.op .add
      [.var .local (ofString "node"), .const 32, .panop .mul [.var .local (ofString "idx"), .const 8]])))
    (.seq (.assign .local (ofString "level") (.op .add [.var .local (ofString "level"), .const 1]))
      (.assign .local (ofString "go") (.const 1))))))))

theorem mptChildAddr_eval {F : Type} {s : PanSemStateFiniteExact 64 F}
    {n i : BitVec 64}
    (hn : s.locals.lookup (ofString "node") = some (.val (.word n)))
    (hi : s.locals.lookup (ofString "idx") = some (.val (.word i))) :
    evalAt s (.op .add [.var .local (ofString "node"), .const 32,
      .panop .mul [.var .local (ofString "idx"), .const 8]]) =
      some (.val (.word (BitVec.ofNat 64 (n.toNat + 32 + 8 * i.toNat)))) := by
  have heq : n + (32 + i * 8) = BitVec.ofNat 64 (n.toNat + 32 + 8 * i.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_mul, Nat.add_mod, Nat.mul_mod, Nat.mul_comm,
      Nat.add_assoc]
  simp [evalAt, evalHOLExact, evalListHOLExact, hn, hi, valueIsWord, valueWord,
    wordOpHOL, wordOp, panOpHOL]
  exact heq

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

/-! ### From MptDeleteKind3Cont.lean -/


namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
theorem mptBranchCont_run {F : Type} {s u t : PanSemStateFiniteExact 64 F}
    (hs : MptDeleteBranchReady s) (hu : ArenaReady u) (hbe : u.be = s.be)
    (hg : AllocatorGrows s u) {pw iw lw : BitVec 64}
    (hfresh : FreshScratch s u pw.toNat 40)
    (hfr2 : u.locals.lookup (ofString "fr2") = some (.val (.word pw)))
    (hloc : ∀ n : String, ofString n ≠ ofString "fr2" → u.locals.lookup (ofString n) = s.locals.lookup (ofString n))
    (hidx : s.locals.lookup (ofString "idx") = some (.val (.word iw)))
    (hi : iw.toNat < 16)
    (hlev : s.locals.lookup (ofString "level") = some (.val (.word lw)))
    (hlt : locN s "level" < locN s "klen")
    (hfr : FrameOutside s u
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr"))
    (hr : evaluateHOLFiniteState u mptBranchCont = (none, t)) :
    MptDeleteHead t ∧ globN t "scratch_ptr" + 40 ≤ globN s "scratch_ptr" := by
  obtain ⟨ha, _, _, Nd, fs, hn, hst, hres, hlevel, hnode, hkey⟩ := hs
  have hnonzero : locN s "node" ≠ 0 := by
    have hb : 0 < sourceBase := by decide
    have hh := (hn.1 _ hnode.1).2.2.1.1
    change sourceBase ≤ locN s "node" at hh
    omega
  obtain ⟨nw, hnw, hnn⟩ := mptLocN_nonzero hnonzero
  have hnwu : u.locals.lookup (ofString "node") = some (.val (.word nw)) :=
    (hloc "node" (by decide)).trans hnw
  have hiwu : u.locals.lookup (ofString "idx") = some (.val (.word iw)) :=
    (hloc "idx" (by decide)).trans hidx
  have hlwu : u.locals.lookup (ofString "level") = some (.val (.word lw)) :=
    (hloc "level" (by decide)).trans hlev
  obtain ⟨a, h0, hr⟩ := mptSeq_none hr
  obtain ⟨b, h8, hr⟩ := mptSeq_none hr
  obtain ⟨c, h16, hr⟩ := mptSeq_none hr
  obtain ⟨d, h32, hr⟩ := mptSeq_none hr
  obtain ⟨e, htop, hr⟩ := mptSeq_none hr
  have hld : d.locals = u.locals :=
    (mptStore_locals h32).trans ((mptStore_locals h16).trans
      ((mptStore_locals h8).trans (mptStore_locals h0)))
  obtain ⟨topval, htv, hvalid, he⟩ := mptAssign_none htop
  change d.locals.lookup (ofString "fr2") = some topval at htv
  rw [hld, hfr2] at htv
  cases htv
  obtain ⟨tw, htw⟩ := mptValid_word_local hvalid
  rw [hld] at htw
  have htopnat : tw.toNat = locN s "top" := by
    have hh := (hloc "top" (by decide)).symm.trans htw
    exact (mptLocal_word hh).symm
  have heqa := mptStore_word_none (src := .var .local (ofString "top")) (mptAddConst_eval 0 hfr2) htw h0
  simp only [Nat.add_zero] at heqa
  subst a
  have heqb := mptStore_word_none (src := .var .local (ofString "node")) (mptAddConst_eval (s := mptWordWrite u pw.toNat tw) 8 hfr2) hnwu h8
  subst b
  have heqc := mptStore_word_none (mptAddConst_eval (s := mptWordWrite (mptWordWrite u pw.toNat tw) (pw.toNat + 8) nw) 16 hfr2) (show evalAt _ (.const 3) = _ from rfl) h16
  subst c
  have heqd := mptStore_word_none (src := .var .local (ofString "idx")) (mptAddConst_eval (s := mptWordWrite (mptWordWrite (mptWordWrite u pw.toNat tw) (pw.toNat + 8) nw) (pw.toNat + 16) 3) 32 hfr2) hiwu h32
  change d = mptBranchFrame u pw.toNat tw nw iw at heqd
  subst d
  subst e
  obtain ⟨f, hchild, hr⟩ := mptSeq_none hr
  obtain ⟨cv, hcv, _, hf⟩ := mptAssign_none hchild
  have hne : (setVarHOLFinite (ofString "top") (.val (.word pw))
      (mptBranchFrame u pw.toNat tw nw iw)).locals.lookup (ofString "node") = some (.val (.word nw)) := by
    simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise]
    simpa +decide [mptBranchFrame, mptWordWrite] using hnwu
  have hie : (setVarHOLFinite (ofString "top") (.val (.word pw))
      (mptBranchFrame u pw.toNat tw nw iw)).locals.lookup (ofString "idx") = some (.val (.word iw)) := by
    simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise]
    simpa +decide [mptBranchFrame, mptWordWrite] using hiwu
  obtain ⟨cw, rfl, hcwn⟩ := mptLoad_inv (mptChildAddr_eval hne hie) hcv
  subst f
  obtain ⟨g, hinc, hr⟩ := mptSeq_none hr
  obtain ⟨lv, hlv, _, hgstate⟩ := mptAssign_none hinc
  have hlg : (setVarHOLFinite (ofString "node") (.val (.word cw))
      (setVarHOLFinite (ofString "top") (.val (.word pw))
      (mptBranchFrame u pw.toNat tw nw iw))).locals.lookup (ofString "level") = some (.val (.word lw)) := by
    simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise]
    simpa +decide [mptBranchFrame, mptWordWrite] using hlwu
  have hleval := mptAddConst_eval 1 hlg
  have heqlv := Option.some.inj (hlv.symm.trans hleval)
  subst lv
  subst g
  obtain ⟨gv, hgv, _, ht⟩ := mptAssign_none hr
  have hgone := evalAt_const _ 1 gv hgv
  subst gv
  subst t
  let d := mptBranchFrame u pw.toNat tw nw iw
  obtain ⟨had, hnd, hstack, hkeys, htags⟩ := mptBranchFrame_push ha hu hbe hg hfresh hn hst
    htopnat (by rw [hnn]; exact hnode.1) (by rw [hnn]; exact hnode.2) hi hfr
  let t := setVarHOLFinite (ofString "go") (.val (.word 1))
    (setVarHOLFinite (ofString "level") (.val (.word (BitVec.ofNat 64 (lw.toNat + 1))))
    (setVarHOLFinite (ofString "node") (.val (.word cw))
    (setVarHOLFinite (ofString "top") (.val (.word pw)) d)))
  change MptDeleteHead t ∧ globN t "scratch_ptr" + 40 ≤ globN s "scratch_ptr"
  have hlwn := mptLocal_word hlev
  have hlwlt : lw.toNat + 1 < 2 ^ 64 := by
    have hkn : locN s "klen" < 2 ^ 64 := by
      obtain ⟨kw, _, hkw⟩ := mptLocN_nonzero (s := s) (n := "klen") (by omega)
      rw [← hkw]
      exact kw.isLt
    omega
  have htopn : locN t "top" = pw.toNat := by
    simp +decide only [t, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, if_true, if_false]
  have hnoden : locN t "node" = cw.toNat := by
    simp +decide only [t, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, if_true, if_false]
  have hleveln : locN t "level" = locN s "level" + 1 := by
    simp +decide only [t, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise,
      if_true, if_false, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlwlt, hlev]
  have hsame (n : String) (hne : n ∈ ["key", "klen", "res"]) : locN t n = locN s n := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hne
    rcases hne with rfl | rfl | rfl
    all_goals simp +decide only [t, d, mptBranchFrame, mptWordWrite, locN, setVarHOLFinite,
      HolFiniteMapExact.lookup_update_pointwise, if_true, if_false, hloc "key" (by decide), hloc "klen" (by decide), hloc "res" (by decide)]
  have hchildroot : RootIn Nd cw.toNat := by
    rw [hcwn]
    exact (hnd.1 _ (by rw [hnn]; exact hnode.1)).2.2.2.2.2.1
      (by change memW d nw.toNat = 3
          rw [htags _ (by rw [hnn]; exact hnode.1), hnn]
          exact hnode.2) iw.toNat hi
  refine ⟨⟨(arenaReady_with_locals d t.locals d.clock).2 had, Nd, pw.toNat :: fs,
    (mptNodeHeap_locals d t.locals d.clock Nd).2 hnd, ?_, ?_, ?_⟩, ?_⟩
  · rw [htopn]
    exact (mptStack_locals d t.locals d.clock Nd _ _).2 hstack
  · rw [hsame "res" (by simp)]
    exact hres
  · intro _
    rw [hleveln, hsame "klen" (by simp), hnoden, hsame "key" (by simp)]
    refine ⟨by omega, hchildroot, ?_⟩
    exact (mptKeyIn_locals d t.locals d.clock Nd _ _).2
      (hkeys _ _ (mptKeyIn_sub hkey (by omega) (by omega)))
  · change globN u "scratch_ptr" + 40 ≤ globN s "scratch_ptr"
    have hp := hfresh.2.2.1
    change globN u "scratch_ptr" ≤ pw.toNat ∧ pw.toNat + 40 ≤ globN s "scratch_ptr" at hp
    omega

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

/-! ### From MptDeleteKind3Post.lean -/


namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
theorem mptBranchReady_locals {F : Type} {s : PanSemStateFiniteExact 64 F}
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ n ∈ ["top", "res", "go", "level", "klen", "node", "key", "k"],
      ls.lookup (ofString n) = s.locals.lookup (ofString n))
    (hs : MptDeleteBranchReady s) : MptDeleteBranchReady { s with locals := ls, clock := clock } := by
  obtain ⟨ha, hgo, hk, Nd, fs, hn, hst, hres, hle, hnode, hkey⟩ := hs
  have heq : ∀ n ∈ ["top", "res", "go", "level", "klen", "node", "key", "k"],
      locN { s with locals := ls, clock := clock } n = locN s n :=
    fun n hn => mptLocN_locals (hl n hn)
  refine ⟨(arenaReady_with_locals s ls clock).2 ha, ?_, ?_, Nd, fs,
    (mptNodeHeap_locals s ls clock Nd).2 hn, ?_, ?_, ?_, ?_, ?_⟩
  · rw [heq "go" (by simp)]; exact hgo
  · rw [heq "k" (by simp)]; exact hk
  · rw [heq "top" (by simp)]; exact (mptStack_locals s ls clock Nd fs _).2 hst
  · rw [heq "res" (by simp)]; exact hres
  · rw [heq "level" (by simp), heq "klen" (by simp)]; exact hle
  · change locN { s with locals := ls, clock := clock } "node" ∈ Nd ∧
      memW s (locN { s with locals := ls, clock := clock } "node") = 3
    rw [heq "node" (by simp)]; exact hnode
  · rw [heq "key" (by simp), heq "level" (by simp), heq "klen" (by simp)]
    exact (mptKeyIn_locals s ls clock Nd _ _).2 hkey

theorem mptBranchReady_idx {F : Type} {s : PanSemStateFiniteExact 64 F}
    (w : BitVec 64) (hs : MptDeleteBranchReady s) :
    MptDeleteBranchReady (setVarHOLFinite (ofString "idx") (.val (.word w)) s) := by
  apply mptBranchReady_locals _ _ _ hs
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp +decide only [setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, if_true, if_false]

theorem mptHead_restore {F : Type} {s : PanSemStateFiniteExact 64 F}
    (name : MlS) (old : Option (ValueHOL 64))
    (hname : ∀ n ∈ ["top", "res", "go", "level", "klen", "node", "key"], ofString n ≠ name)
    (hs : MptDeleteHead s) :
    MptDeleteHead { s with locals := HolFiniteMapExact.resVarEq s.locals (name, old) } := by
  exact mptDeleteHead_locals _ _ (fun n hn => resVarEq_lookup_ne _ _ _ _ (hname n hn)) hs

theorem mptCondTrue_eq {F : Type} {s : PanSemStateFiniteExact 64 F}
    {n : String} {c : BitVec 64}
    (h : CondTrue (.cmp .equal (.var .local (ofString n)) (.const c)) s) : locN s n = c.toNat := by
  obtain ⟨w, hw, hne⟩ := h
  obtain ⟨a, b, han, hb, hw⟩ := cond_local s .equal n (.const c) w hw
  have heq := evalAt_const s c (.val (.word b)) hb
  cases heq
  simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw
  by_cases hac : a = c
  · subst a; exact han.symm
  · simp [hac] at hw
    exact (hne hw).elim

theorem mptCondFalse_eqLoc {F : Type} {s : PanSemStateFiniteExact 64 F}
    {n m : String}
    (h : CondFalse (.cmp .equal (.var .local (ofString n)) (.var .local (ofString m))) s) :
    locN s n ≠ locN s m := by
  obtain ⟨a, b, ha, hb, heq⟩ := evalAt_cmp s .equal _ _ 0 h
  have han := evalAt_local s n a ha
  have hbn := evalAt_local s m b hb
  intro hh
  have hab : a = b := BitVec.eq_of_toNat_eq (han.trans (hh.trans hbn.symm))
  subst b
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at heq

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

/-! ### From MptDeleteKind3Descend.lean -/


namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
def mptBranchDescend : ProgHOL 64 :=
  .dec (ofString "idx") .one (.loadByte (.op .add
    [.var .local (ofString "key"), .var .local (ofString "level")]))
    (.decCall (ofString "fr2") .one (ofString "scratch_alloc") [.const 40] mptBranchCont)

theorem mptBranchDescend_run (h : MptDeleteCallees)
    {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hs : MptDeleteBranchReady s)
    (hlt : locN s "level" < locN s "klen")
    (hr : evaluateHOLFiniteState s mptBranchDescend = (none, t)) :
    MptDeleteHead t ∧ globN t "scratch_ptr" + 40 ≤ globN s "scratch_ptr" := by
  obtain ⟨v, inner, hv, hcall, ht⟩ := mptDec_none hr
  obtain ⟨aw, haw⟩ := mptByte_addr hv
  obtain ⟨kw, lw, hkw, hlw, _⟩ := mptAddLocals_inv haw
  have hadd : kw + lw = BitVec.ofNat 64 (locN s "key" + locN s "level") := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, mptLocal_word hkw, mptLocal_word hlw]
  have haddr := mptAddLocals_eval hkw hlw
  rw [hadd] at haddr
  obtain ⟨iw, rfl, hiw⟩ := mptByte_inv haddr hv
  have hi : iw.toNat < 16 := by
    rw [hiw]
    obtain ⟨_, _, _, Nd, fs, _, _, _, _, _, hk⟩ := hs
    rcases hk with hz | hk
    · omega
    · simpa only [Nat.add_zero] using hk.1 0 (by omega)
  let si := setVarHOLFinite (ofString "idx") (.val (.word iw)) s
  have hsi : MptDeleteBranchReady si := mptBranchReady_idx iw hs
  obtain ⟨values, body, callee, ret, v, post, mid, hargs, hl, hbody, hcont, hinner⟩ :=
    mptDecCall_none hcall
  obtain ⟨pw, rfl, hpost, hg, hfresh, _, hbe, hframe⟩ :=
    mptScratch_return h (s := si) hc hsi.1 hargs hl hbody
  let u := setVarHOLFinite (ofString "fr2") (.val (.word pw)) { post with locals := si.locals }
  have hufr : u.locals.lookup (ofString "fr2") = some (.val (.word pw)) := by
    simp only [u, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, if_true]
  have huloc : ∀ n : String, ofString n ≠ ofString "fr2" →
      u.locals.lookup (ofString n) = si.locals.lookup (ofString n) := by
    intro n hn
    simp only [u, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, hn, if_false]
  have hilev : si.locals.lookup (ofString "level") = some (.val (.word lw)) := by
    simp +decide only [si, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, if_false]
    exact hlw
  have hiidx : si.locals.lookup (ofString "idx") = some (.val (.word iw)) := by
    simp only [si, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, if_true]
  have hilt : locN si "level" < locN si "klen" := by
    simpa +decide only [si, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, if_false] using hlt
  have hdone := mptBranchCont_run (s := si) (u := u) hsi
    ((arenaReady_with_locals post u.locals post.clock).2 hpost) hbe hg hfresh hufr huloc hiidx hi hilev hilt
    hframe hcont
  subst inner
  subst t
  refine ⟨mptHead_restore (ofString "idx") _ ?_
    (mptHead_restore (ofString "fr2") _ ?_ hdone.1), hdone.2⟩
  all_goals simp +decide only [List.forall_mem_cons, List.forall_mem_nil, and_true]

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

/-! ### From MptDeleteKind3Assemble.lean -/


namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
def mptElse : ProgHOL 64 → ProgHOL 64
  | .ite _ _ no => no
  | _ => .skip

def mptDeleteAfterKind : ProgHOL 64 :=
  mptDecBody (mptElse (mptRight mptDeleteBody))

def mptBranchCode : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "level")) (.var .local (ofString "klen")))
    mptDeleteValueCode mptBranchDescend

def MptDeleteDone (sp : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => MptDeleteHead t ∧ (locN t "go" = 0 ∨ globN t "scratch_ptr" + 40 ≤ sp)

theorem mptBranch_hoare (h : MptDeleteCallees) (sp : Nat) :
    Hoare (fun s => MptDeleteBranchReady s ∧ globN s "scratch_ptr" ≤ sp)
      mptBranchCode (fun r t => r = none → MptDeleteDone sp t) := by
  apply Hoare.ite
  · refine ⟨fun s hc hp _ hr => ?_⟩
    have hv := (mptDeleteBranch_value h).run s hc hp.1.1 (by rw [hr]; simp)
    rw [hr] at hv
    exact ⟨(hv rfl).1, Or.inl (hv rfl).2⟩
  · refine ⟨fun s hc hp _ hr => ?_⟩
    have hne := mptCondFalse_eqLoc hp.2
    have hle : locN s "level" ≤ locN s "klen" := by
      obtain ⟨_, _, _, Nd, fs, _, _, _, hle, _⟩ := hp.1.1
      exact hle
    have hd := mptBranchDescend_run h hc hp.1.1 (by omega) (by
      exact (Prod.ext hr rfl : evaluateHOLFiniteState s mptBranchDescend =
        (none, (evaluateHOLFiniteState s mptBranchDescend).2)))
    exact ⟨hd.1, Or.inr (Nat.le_trans hd.2 hp.1.2)⟩
  · intro F s _ hr
    cases hr

theorem mptDeleteAfterKind_hoare (h : MptDeleteCallees) (sp : Nat) :
    Hoare (fun s => MptDeleteBranchReady s ∧ globN s "scratch_ptr" ≤ sp)
      mptDeleteAfterKind (fun r t => r = none → MptDeleteDone sp t) := by
  apply mptHoare_seq (R := fun s => MptDeleteBranchReady s ∧ globN s "scratch_ptr" ≤ sp)
  · apply Hoare.ite
    · apply Hoare.of_false
      intro F s hp
      have hh := mptCondTrue_eq hp.2
      have hk := hp.1.1.2.2.1
      change locN s "k" = 0 at hh
      omega
    · apply Hoare.skip
      intro F s hp _
      exact hp.1
    · intro F s _ hr
      cases hr
  · apply mptHoare_seq (mptDeleteBranch_invalidate h sp)
    apply Hoare.ite
    · apply Hoare.of_false
      intro F s hp
      have hh := mptCondTrue_eq hp.2
      have hk := hp.1.1.2.2.1
      change locN s "k" = 1 at hh
      omega
    · apply Hoare.ite
      · apply Hoare.of_false
        intro F s hp
        have hh := mptCondTrue_eq hp.2
        have hk := hp.1.1.1.2.2.1
        change locN s "k" = 2 at hh
        omega
      · exact Hoare.mono (mptBranch_hoare h sp) (fun _ hp => hp.1.1)
      · intro F s _ hr
        cases hr
    · intro F s _ hr
      cases hr

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

/-! ### From MptDeleteKind3Prefix.lean -/


namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
theorem mptDelete_kind3_run (h : MptDeleteCallees)
    {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hp : MptDeleteActive s) (hk : mptKind s = 3)
    (hr : evaluateHOLFiniteState s mptDeleteBody = (none, t)) :
    MptDeleteHead t ∧ MptDeleteEffect s t := by
  have hnn : locN s "node" ≠ 0 := by
    intro hz
    simp [mptKind, hz] at hk
  have hkind : memW s (locN s "node") = 3 := by
    simpa only [mptKind, hnn, if_false] using hk
  obtain ⟨nw, hnw, hnwn⟩ := mptLocN_nonzero hnn
  obtain ⟨⟨ha, Nd, fs, hn, hst, hres, hact⟩, hgo⟩ := hp
  obtain ⟨hle, hroot, hkey⟩ := hact hgo
  have hnode : locN s "node" ∈ Nd := hroot.resolve_left hnn
  obtain ⟨s0, hreset, hrest⟩ := mptSeq_none hr
  obtain ⟨v, hv, _, hs0⟩ := mptAssign_none hreset
  have hv0 := evalAt_const s 0 v hv
  subst v
  subst s0
  rcases mptIte_none hrest with ⟨hz, _⟩ | ⟨_, hdec⟩
  · have hz0 := mptCondTrue_eq hz
    rw [mptSetVar_locN_ne s _ _ "node" (by decide)] at hz0
    exact (hnn hz0).elim
  · obtain ⟨kv, inner, hkv, hbody, ht⟩ := mptDec_none hdec
    let s0 := setVarHOLFinite (ofString "go") (.val (.word 0)) s
    have hnw0 : s0.locals.lookup (ofString "node") = some (.val (.word nw)) := by
      simp +decide only [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, if_false]
      exact hnw
    have haddr := mptAddConst_eval (s := s0) 0 hnw0
    obtain ⟨kw, rfl, hkwn⟩ := mptLoad_inv haddr hkv
    change kw.toNat = memW s (nw.toNat + 0) at hkwn
    have hkw3 : kw.toNat = 3 := by
      have hh : kw.toNat = memW s (locN s "node") := by
        simpa only [Nat.add_zero, hnwn] using hkwn
      exact hh.trans hkind
    let sk := setVarHOLFinite (ofString "k") (.val (.word kw)) s0
    have heq (n : String) (hname : n ∈ ["top", "res", "level", "klen", "node", "key"]) :
        locN sk n = locN s n := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
      rcases hname with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp +decide only [sk, s0, locN, setVarHOLFinite,
        HolFiniteMapExact.lookup_update_pointwise, if_false]
    have hready : MptDeleteBranchReady sk := by
      refine ⟨(arenaReady_with_locals s sk.locals s.clock).2 ha, ?_, ?_, Nd, fs,
        (mptNodeHeap_locals s sk.locals s.clock Nd).2 hn, ?_, ?_, ?_, ?_, ?_⟩
      · simp +decide only [sk, s0, locN, setVarHOLFinite,
          HolFiniteMapExact.lookup_update_pointwise, if_true, if_false]
      · simpa only [sk, mptSetVar_locN_word] using hkw3
      · rw [heq "top" (by simp)]
        exact (mptStack_locals s sk.locals s.clock Nd fs _).2 hst
      · rw [heq "res" (by simp)]; exact hres
      · rw [heq "level" (by simp), heq "klen" (by simp)]; exact hle
      · change locN sk "node" ∈ Nd ∧ memW s (locN sk "node") = 3
        rw [heq "node" (by simp)]
        exact ⟨hnode, hkind⟩
      · rw [heq "key" (by simp), heq "level" (by simp), heq "klen" (by simp)]
        exact (mptKeyIn_locals s sk.locals s.clock Nd _ _).2 hkey
    change evaluateHOLFiniteState sk mptDeleteAfterKind = (none, inner) at hbody
    have hdone := (mptDeleteAfterKind_hoare h (globN s "scratch_ptr")).run sk hc
      ⟨hready, Nat.le_refl _⟩ (by rw [hbody]; simp)
    rw [hbody] at hdone
    obtain ⟨hh, he⟩ := hdone rfl
    subst t
    refine ⟨mptHead_restore (ofString "k") _ ?_ hh, ?_⟩
    · simp +decide only [List.forall_mem_cons, List.forall_mem_nil, and_true]
    · rcases he with hstop | hdown
      · left
        have heqgo := resVarEq_lookup_ne inner.locals (ofString "k") (ofString "go")
          (s0.locals.lookup (ofString "k")) (by decide)
        exact mptLocN_locals heqgo |>.trans hstop
      · exact Or.inr hdown

end InitECandidate.Solver.Wave8GuestInv.GuardedBody

/-! ### From MptDeleteStep04Kind3.lean -/
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

/-- One iteration with node tag 3; shard 0 includes the null-root case.
Prove the bound and the continuing-state effect. No other kind shard is imported. -/
theorem mptDelete_kind3 (h : MptDeleteCallees) :
    MptStepAt MptDeleteActive MptDeleteHead MptDeleteEffect mptDeleteBody mptDeleteCost 3 := by
  intro F s hc hp hk
  refine ⟨mptDelete_body_bound h s hc hp.1.1.1, ?_⟩
  intro hflow
  have hnone : (evaluateHOLFiniteState s mptDeleteBody).1 = none :=
    hflow.resolve_right (evaluate_noTopContinue mptDeleteBody (by rfl) s)
  exact mptDelete_kind3_run h hc hp hk (Prod.ext hnone rfl)

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
