import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptCuts

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.Unwind
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

theorem nodeSize_bounds (k : Nat) : 32 ≤ nodeSize k ∧ nodeSize k ≤ 176 := by
  unfold nodeSize
  split <;> try omega
  split <;> try omega
  split <;> omega

theorem nodeHeap_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (c : Nat) (ns : List Nat) :
    NodeHeap { s with locals := ls, clock := c } ns ↔ NodeHeap s ns := Iff.rfl

theorem frame_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (c : Nat) (ns : List Nat) (p : Nat) :
    MptFrameOK { s with locals := ls, clock := c } ns p ↔ MptFrameOK s ns p := Iff.rfl

theorem stack_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (c : Nat) (ns : List Nat) :
    ∀ (fs : List Nat) (p : Nat),
      MptStack { s with locals := ls, clock := c } ns p fs ↔ MptStack s ns p fs
  | [], _ => Iff.rfl
  | _ :: fs, _ => by
    simp only [MptStack, frame_locals, stack_locals s ls c ns fs]
    rfl

theorem head_locals : LocalsOnly ["top", "res"] MptUnwindHead := by
  intro F s ls c hl h
  obtain ⟨ha, ns, fs, hn, hs, hr⟩ := h
  refine ⟨(arenaReady_with_locals s ls c).2 ha, ns, fs,
    (nodeHeap_locals s ls c ns).2 hn, ?_, ?_⟩
  · rw [locN_congr s ls c "top" (hl _ (by simp)), stack_locals]
    exact hs
  · rw [locN_congr s ls c "res" (hl _ (by simp))]
    exact hr

/-- An address rank avoids choosing a particular list witnessing the finite stack. -/
def rank {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  if locN s "top" = 0 then 0 else 2 ^ 64 - locN s "top"

theorem rank_le {F : Type} (s : PanSemStateFiniteExact 64 F) : rank s ≤ 2 ^ 64 := by
  unfold rank
  split <;> omega

theorem stack_pop {F : Type} {s : PanSemStateFiniteExact 64 F} {ns fs : List Nat}
    {p : Nat} (hs : MptStack s ns p fs) (hp : p ≠ 0) :
    ∃ qs, fs = p :: qs ∧ MptFrameOK s ns p ∧ MptStack s ns (memW s p) qs ∧
      (memW s p = 0 ∨ p + 40 ≤ memW s p) := by
  cases fs with
  | nil => exact (hp hs).elim
  | cons q qs =>
    obtain ⟨rfl, _, hf, hlt, hs⟩ := hs
    refine ⟨qs, rfl, hf, hs, ?_⟩
    cases qs with
    | nil => exact Or.inl hs
    | cons r rs => exact Or.inr (hs.1 ▸ hlt r (by simp))

theorem rank_pop {F : Type} {s t : PanSemStateFiniteExact 64 F} {ns fs : List Nat}
    (hs : MptStack s ns (locN s "top") fs) (hp : locN s "top" ≠ 0)
    (ht : locN t "top" = memW s (locN s "top")) : rank t < rank s := by
  obtain ⟨_, _, hf, _, hz | hlt⟩ := stack_pop hs hp
  · have hfit : locN s "top" < 2 ^ 64 := by
      have := hf.1.2
      have : scratchEnd < 2 ^ 64 := by decide
      omega
    simp only [rank, ht, hz, if_neg hp, ite_true]
    omega
  · have hfit : memW s (locN s "top") < 2 ^ 64 := RunFramesRace.memW_lt _ _
    have htne : memW s (locN s "top") ≠ 0 := by omega
    simp only [rank, ht, if_neg htne, if_neg hp]
    omega

/-- The portion of a node callee's exit contract needed to preserve saved frames. -/
structure Extension {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (ns nt : List Nat) : Prop where
  ready : ArenaReady t
  grows : AllocatorGrows s t
  subset : ∀ n ∈ ns, n ∈ nt
  kinds : ∀ n ∈ ns, memW t n = memW s n
  fresh : ∀ n ∈ nt, n ∈ ns ∨
    Inside (nodeIvl t n) (globN s "heap_ptr") (globN t "heap_ptr")
  frame : FrameOutside s t
    ((ns.map fun n => nodeIvl s n) ++
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
    (globN s "heap_ptr", heapLimit - globN s "heap_ptr")
  endian : t.be = s.be

theorem Extension.ivl {F : Type} {s t : PanSemStateFiniteExact 64 F} {ns nt : List Nat}
    (h : Extension s t ns nt) {n : Nat} (hn : n ∈ ns) : nodeIvl t n = nodeIvl s n := by
  simp only [nodeIvl, h.kinds n hn]

theorem Extension.scratch {F : Type} {s t : PanSemStateFiniteExact 64 F} {ns nt : List Nat}
    (h : Extension s t ns nt) (ha : ArenaReady s) (hn : NodeHeap s ns)
    (a : Nat) (ha0 : globN s "scratch_ptr" ≤ a) (ha1 : a < 2 ^ 64) :
    t.memory (BitVec.ofNat 64 a) = s.memory (BitVec.ofNat 64 a) := by
  have har := ha.2
  have hsp : heapLimit ≤ globN s "scratch_ptr" := by
    change scratchStart ≤ globN s "scratch_ptr"
    exact har.2.2.1.trans har.2.2.2.1
  apply h.frame
  · intro i hi
    rw [List.mem_append] at hi
    rcases hi with hi | hi
    · obtain ⟨n, hm, rfl⟩ := List.mem_map.mp hi
      have hb := (hn.1 n hm).2.2.1.2
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha1, CellHits]
      dsimp only [nodeIvl] at hb ⊢
      omega
    · simp only [List.mem_singleton] at hi
      subst i
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha1, CellHits]
      have := har.2.2.2.1
      omega
  · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha1, CellHits]
    have := har.2.1
    omega

theorem key_heap {F : Type} {s : PanSemStateFiniteExact 64 F} {ns : List Nat} {p l : Nat}
    (ha : ArenaReady s) (hk : KeyIn s ns p l) (hl : l ≠ 0) :
    p + l ≤ globN s "heap_ptr" := by
  obtain ⟨_, hal, hin, _⟩ := hk.resolve_left hl
  rcases hal with hal | hal
  · exact hal.2
  · have hsp : heapLimit ≤ globN s "scratch_ptr" := by
      change scratchStart ≤ globN s "scratch_ptr"
      exact ha.2.2.2.1.trans ha.2.2.2.2.1
    have := hal.1
    have := hin.2
    omega

theorem byteAlign_bounds (a : Nat) (ha : a < 2 ^ 64) :
    (panByteAlignHOL (BitVec.ofNat 64 a)).toNat = a / 8 * 8 := by
  have h8 : 2 ^ Nat.log2 (64 / 8) = 8 := by decide
  simp only [panByteAlignHOL, h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  rw [Nat.mod_eq_of_lt (show a / 8 * 8 < 2 ^ 64 by omega)]

theorem Extension.key {F : Type} {s t : PanSemStateFiniteExact 64 F} {ns nt : List Nat}
    (h : Extension s t ns nt) (ha : ArenaReady s) (hn : NodeHeap s ns)
    {p l : Nat} (hk : KeyIn s ns p l) : KeyIn t nt p l := by
  by_cases hl : l = 0
  · exact Or.inl hl
  have hheap := key_heap ha hk hl
  obtain ⟨hb, hal, hin, hd⟩ := hk.resolve_left hl
  right
  refine ⟨?_, h.grows.allocated hal, hin, ?_⟩
  · intro k hk
    have hab : p + k < 2 ^ 64 := by
      have := hin.2
      have : heapLimit < 2 ^ 64 := by decide
      omega
    have hc := byteAlign_bounds (p + k) hab
    have hm : t.memory (panByteAlignHOL (BitVec.ofNat 64 (p + k))) =
        s.memory (panByteAlignHOL (BitVec.ofNat 64 (p + k))) := by
      apply h.frame
      · intro i hi
        rw [List.mem_append] at hi
        rcases hi with hi | hi
        · obtain ⟨n, hm, rfl⟩ := List.mem_map.mp hi
          have hd := hd n hm
          have hw := (hn.1 n hm).2.2.2.1
          have hsize : nodeSize (memW s n) % 8 = 0 := hw.2.1
          have hbase : n % 8 = 0 := hw.1
          simp only [CellHits, hc, nodeIvl]
          dsimp only [Disj, nodeIvl] at hd
          omega
        · simp only [List.mem_singleton] at hi
          subst i
          have hfm : heapLimit ≤ globN s "frame_mem_ptr" := ha.2.2.2.1
          have hhp := ha.2.2.1
          have hh8 := ha.2.2.2.2.2.2.1
          simp only [CellHits, hc]
          omega
      · have hh8 := ha.2.2.2.2.2.2.1
        simp only [CellHits, hc]
        omega
    unfold memB
    rw [hm, h.endian]
    exact hb k hk
  · intro n hm
    rcases h.fresh n hm with hm | hm
    · rw [h.ivl hm]
      exact hd n hm
    · exact Or.inl (hheap.trans hm.1)

theorem Extension.frameOK {F : Type} {s t : PanSemStateFiniteExact 64 F} {ns nt : List Nat}
    (h : Extension s t ns nt) (ha : ArenaReady s) (hn : NodeHeap s ns)
    {p : Nat} (hf : MptFrameOK s ns p) : MptFrameOK t nt p := by
  have hm (o : Nat) (ho : o ≤ 32) : memW t (p + o) = memW s (p + o) := by
    unfold memW
    rw [h.scratch ha hn (p + o) (by have := hf.1.1; omega) (by
      have := hf.1.2
      have : scratchEnd < 2 ^ 64 := by decide
      omega)]
  refine ⟨⟨h.grows.2.trans hf.1.1, hf.1.2⟩, ?_, ?_⟩
  · obtain ⟨hpa, hsz, hw⟩ := hf.2.1
    refine ⟨hpa, hsz, fun k hk => ?_⟩
    obtain ⟨w, hdom, he⟩ := hw k hk
    refine ⟨w, ?_, ?_⟩
    · rw [h.ready.1.memaddrs, ← ha.1.memaddrs]
      exact hdom
    · rw [h.scratch ha hn (p + 8 * k) (by have := hf.1.1; omega) (by
        have := hf.1.2
        have : scratchEnd < 2 ^ 64 := by decide
        omega)]
      exact he
  · dsimp only
    rw [hm 8 (by omega), hm 16 (by omega), hm 24 (by omega), hm 32 (by omega)]
    obtain ⟨hmem, hk⟩ := hf.2.2
    refine ⟨h.subset _ hmem, ?_⟩
    rw [h.kinds _ hmem]
    rcases hk with ⟨h2, hn2, hkey⟩ | ⟨h3, hn3, hi⟩
    · exact Or.inl ⟨h2, hn2, h.key ha hn hkey⟩
    · exact Or.inr ⟨h3, hn3, hi⟩

theorem Extension.stack {F : Type} {s t : PanSemStateFiniteExact 64 F} {ns nt : List Nat}
    (h : Extension s t ns nt) (ha : ArenaReady s) (hn : NodeHeap s ns) :
    ∀ {fs : List Nat} {p : Nat}, MptStack s ns p fs → MptStack t nt p fs := by
  intro fs
  induction fs with
  | nil => exact fun hs => hs
  | cons q qs ih =>
    intro p hs
    obtain ⟨he, hz, hf, ho, hs⟩ := hs
    refine ⟨he, hz, h.frameOK ha hn hf, ho, ?_⟩
    have hm : memW t p = memW s p := by
      unfold memW
      rw [h.scratch ha hn p hf.1.1 (by
        have := hf.1.2
        have : scratchEnd < 2 ^ 64 := by decide
        omega)]
    rw [hm]
    exact ih hs

def storeWord {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) (w : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  { s with memory := fun b => if b = BitVec.ofNat 64 a then .word w else s.memory b }

theorem storeWord_memW {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : Nat)
    (w : BitVec 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    memW (storeWord s a w) b = if b = a then w.toNat else memW s b := by
  have he : BitVec.ofNat 64 b = BitVec.ofNat 64 a ↔ b = a := by
    constructor
    · intro hh
      have := congrArg BitVec.toNat hh
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
    · exact congrArg (BitVec.ofNat 64)
  simp only [memW, storeWord, he]
  split <;> rfl

/-- The caller's branch-child store preserves the node heap and every saved frame. -/
theorem store_child {F : Type} {s : PanSemStateFiniteExact 64 F} {ns : List Nat}
    (ha : ArenaReady s) (hn : NodeHeap s ns) {n i : Nat} (hmem : n ∈ ns)
    (hkind : memW s n = 3) (hi : i < 16) (w : BitVec 64) (hw : RootIn ns w.toNat) :
    let t := storeWord s (n + 32 + 8 * i) w
    Extension s t ns ns ∧ NodeHeap t ns := by
  let a := n + 32 + 8 * i
  let t := storeWord s a w
  change Extension s t ns ns ∧ NodeHeap t ns
  have hnsize : nodeSize (memW s n) = 176 := by simp [hkind, nodeSize]
  have hnend := (hn.1 n hmem).2.2.1.2
  change n + nodeSize (memW s n) ≤ heapLimit at hnend
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hafit : a < 2 ^ 64 := by dsimp [a]; omega
  have hmfit (m : Nat) (hm : m ∈ ns) : m + nodeSize (memW s m) ≤ heapLimit :=
    (hn.1 m hm).2.2.1.2
  have haway (m off : Nat) (hm : m ∈ ns) (hne : m ≠ n)
      (hoff : off < nodeSize (memW s m)) : memW t (m + off) = memW s (m + off) := by
    have hd := hn.2 m hm n hmem hne
    dsimp only [Disj, nodeIvl] at hd
    have he := hmfit m hm
    have hne' : m + off ≠ a := by dsimp [a]; omega
    rw [storeWord_memW s a (m + off) w hafit (by omega), if_neg hne']
  have hk (m : Nat) (hm : m ∈ ns) : memW t m = memW s m := by
    by_cases he : m = n
    · subst m
      have hne : n ≠ a := by dsimp [a]; omega
      rw [storeWord_memW s a n w hafit (by omega), if_neg hne]
    · simpa only [Nat.add_zero] using haway m 0 hm he (by
        have := (nodeSize_bounds (memW s m)).1
        omega)
  have ht : ArenaReady t := ⟨guestInv_congr (s := s) rfl rfl rfl rfl ha.1, ha.2⟩
  have hx : Extension s t ns ns :=
    { ready := ht
      grows := ⟨Nat.le_refl _, Nat.le_refl _⟩
      subset := fun _ hm => hm
      kinds := hk
      fresh := fun _ hm => Or.inl hm
      frame := by
        intro b hb _
        change (if b = BitVec.ofNat 64 a then HolWordLab.word w else s.memory b) = s.memory b
        split
        · rename_i he
          subst b
          exfalso
          apply hb (nodeIvl s n) (List.mem_append_left _ (List.mem_map.mpr ⟨n, hmem, rfl⟩))
          simp only [CellHits, nodeIvl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hafit]
          dsimp [a]
          omega
        · rfl
      endian := rfl }
  refine ⟨hx, ?_, ?_⟩
  · intro m hm
    obtain ⟨hbound, halloc, hins, hwords, hext, hbranch, hpath⟩ := hn.1 m hm
    rw [hk m hm, hx.ivl hm]
    refine ⟨hbound, halloc, hins, ?_, ?_, ?_, ?_⟩
    · obtain ⟨hb, hl, hdom⟩ := hwords
      refine ⟨hb, hl, fun j hj => ?_⟩
      obtain ⟨v, hd, _⟩ := hdom j hj
      cases he : t.memory (BitVec.ofNat 64 ((nodeIvl s m).1 + 8 * j)) with
      | word u => exact ⟨u, hd, he⟩
    · intro hm2
      have hne : m ≠ n := by intro he; subst m; omega
      have hsz : nodeSize (memW s m) = 56 := by simp [nodeSize, hm2]
      rw [haway m 48 hm hne (by omega)]
      exact hext hm2
    · intro hm3 j hj
      by_cases he : m = n
      · subst m
        have hfit : n + 32 + 8 * j < 2 ^ 64 := by omega
        rw [storeWord_memW s a (n + 32 + 8 * j) w hafit hfit]
        split
        · exact hw
        · exact hbranch hm3 j hj
      · have hsz : nodeSize (memW s m) = 176 := by simp [nodeSize, hm3]
        rw [show m + 32 + 8 * j = m + (32 + 8 * j) by omega,
          haway m (32 + 8 * j) hm he (by omega)]
        simpa only [Nat.add_assoc] using hbranch hm3 j hj
    · intro hm12
      have hne : m ≠ n := by intro he; subst m; rcases hm12 with hh | hh <;> omega
      have hsz : 40 < nodeSize (memW s m) := by
        rcases hm12 with hh | hh <;> simp [nodeSize, hh]
      rw [haway m 32 hm hne (by omega), haway m 40 hm hne hsz]
      exact hx.key ha hn (hpath hm12)
  · intro m hm v hv hne
    rw [hx.ivl hm, hx.ivl hv]
    exact hn.2 m hm v hv hne

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.Unwind
