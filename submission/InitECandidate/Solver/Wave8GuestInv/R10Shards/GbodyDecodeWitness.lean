import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07

/-! Scratch-stack invariant and ranking argument for the witness decoder. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.DecodeWitness

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

/-- Only heap containment is needed: the decoder's heap stores cannot hit its stack. -/
def HeapBlock {F : Type} (s : PanSemStateFiniteExact 64 F) (p n : Nat) : Prop :=
  sourceBase ≤ p ∧ p + n ≤ globN s "heap_ptr"

def ResultOK {F : Type} (s : PanSemStateFiniteExact 64 F) (p : Nat) : Prop :=
  p = 0 ∨ HeapBlock s p 32

def WordLocal {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String) : Prop :=
  ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))

theorem wordLocal_set {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String) (w : BitVec 64) :
    WordLocal (setVarHOLFinite (ofString n) (.val (.word w)) s) n := by
  exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩

theorem WordLocal.set_ne {F : Type} {s : PanSemStateFiniteExact 64 F} {n : String}
    (h : WordLocal s n) (m : MlS) (v : ValueHOL 64) (hne : ofString n ≠ m) :
    WordLocal (setVarHOLFinite m v s) n := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, ?_⟩
  simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hne] using hw

/-- A live frame is an extension or a branch with an unfinished child counter. -/
def FrameOK {F : Type} (s : PanSemStateFiniteExact 64 F) (p : Nat) : Prop :=
  p % 8 = 0 ∧ p + 88 ≤ scratchEnd ∧
    (memW s (p + 8) = 1 ∨
      (memW s (p + 8) = 2 ∧ memW s (p + 32) < 16 ∧
        HeapBlock s (memW s (p + 16)) 176))

/-- Stack records are in address order. Pushing allocates below the old head. -/
def Stack {F : Type} (s : PanSemStateFiniteExact 64 F) (lo top : Nat) : List Nat → Prop
  | [] => top = 0
  | p :: ps => top = p ∧ lo ≤ p ∧ p ≠ 0 ∧ FrameOK s p ∧
      Stack s (p + 88) (memW s p) ps

def frameCredit {F : Type} (s : PanSemStateFiniteExact 64 F) (p : Nat) : Nat :=
  if memW s (p + 8) = 1 then 1 else 3 * (16 - memW s (p + 32))

def credits {F : Type} (s : PanSemStateFiniteExact 64 F) (ps : List Nat) : Nat :=
  (ps.map (frameCredit s)).sum

theorem frameCredit_bounds {F : Type} {s : PanSemStateFiniteExact 64 F} {p : Nat}
    (h : FrameOK s p) : 0 < frameCredit s p ∧ frameCredit s p ≤ 48 := by
  rcases h.2.2 with h | ⟨h, hi, _⟩
  · simp [frameCredit, h]
  · simp only [frameCredit, h, if_neg (by decide : (2 : Nat) ≠ 1)]
    omega

theorem Stack.lower {F : Type} {s : PanSemStateFiniteExact 64 F} {lo top : Nat}
    {ps : List Nat} (h : Stack s lo top ps) {lo' : Nat} (hle : lo' ≤ lo) :
    Stack s lo' top ps := by
  cases ps with
  | nil => exact h
  | cons p ps => exact ⟨h.1, hle.trans h.2.1, h.2.2⟩

theorem Stack.unique {F : Type} {s : PanSemStateFiniteExact 64 F} {lo lo' top : Nat}
    {ps qs : List Nat} (h : Stack s lo top ps) (h' : Stack s lo' top qs) : ps = qs := by
  induction ps generalizing lo lo' top qs with
  | nil =>
    cases qs with
    | nil => rfl
    | cons q qs => exact (h'.2.2.1 (h'.1.symm.trans h)).elim
  | cons p ps ih =>
    cases qs with
    | nil => exact (h.2.2.1 (h.1.symm.trans h')).elim
    | cons q qs =>
      have hpq := h.1.symm.trans h'.1
      subst q
      exact congrArg (List.cons p) (ih h.2.2.2.2 h'.2.2.2.2)

theorem Stack.credit_bound {F : Type} {s : PanSemStateFiniteExact 64 F} {lo top : Nat}
    {ps : List Nat} (h : Stack s lo top ps) (hlo : lo ≤ scratchEnd) :
    credits s ps ≤ scratchEnd - lo := by
  induction ps generalizing lo top with
  | nil => simp [credits]
  | cons p ps ih =>
    have hp := h.2.2.2.1
    have hr := ih h.2.2.2.2 hp.2.1
    have hw := (frameCredit_bounds hp).2
    have hpEnd := hp.2.1
    simp only [credits, List.map_cons, List.sum_cons] at *
    have hlp := h.2.1
    omega

/-- The stack is uniquely determined by its links, independently of the lower bound. -/
noncomputable def stackList {F : Type} (s : PanSemStateFiniteExact 64 F) (top : Nat) : List Nat := by
  classical
  exact if h : ∃ ps, Stack s 0 top ps then Classical.choose h else []

theorem stackList_eq {F : Type} {s : PanSemStateFiniteExact 64 F} {lo top : Nat}
    {ps : List Nat} (h : Stack s lo top ps) : stackList s top = ps := by
  have hex : ∃ ps, Stack s 0 top ps := ⟨ps, h.lower (Nat.zero_le _)⟩
  rw [stackList, dif_pos hex]
  exact Stack.unique (Classical.choose_spec hex) h

noncomputable def stackCredit {F : Type} (s : PanSemStateFiniteExact 64 F) (top : Nat) : Nat :=
  credits s (stackList s top)

theorem stackCredit_eq {F : Type} {s : PanSemStateFiniteExact 64 F} {lo top : Nat}
    {ps : List Nat} (h : Stack s lo top ps) : stackCredit s top = credits s ps := by
  rw [stackCredit, stackList_eq h]

/-- The three modes are completed child, decode, and resolve, in increasing phase order. -/
def HeadInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "mode" ≤ 2 ∧ ResultOK s (locN s "result") ∧
    (∃ ps, Stack s (globN s "scratch_ptr") (locN s "top") ps) ∧
    (locN s "mode" = 2 → locN s "top" ≠ 0) ∧ WordLocal s "top" ∧ WordLocal s "result"

noncomputable def rank : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat :=
  fun s => if locN s "go" = 0 then 0 else
    globN s "scratch_ptr" + stackCredit s (locN s "top") + locN s "mode" + 1

theorem rank_bound {F : Type} {s : PanSemStateFiniteExact 64 F} (h : HeadInv s) :
    rank s ≤ 22621787712 := by
  obtain ⟨ha, hm, _, ⟨ps, hs⟩, _⟩ := h
  have hhi : globN s "scratch_ptr" ≤ scratchEnd := ha.2.2.2.2.2.1
  have hb := hs.credit_bound hhi
  rw [rank]
  split
  · omega
  · rw [stackCredit_eq hs]
    unfold scratchEnd at *
    omega

/-- A write frame with no explicit region protects all the caller's live scratch cells. -/
theorem frameOutside_scratch {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (ha : ArenaOK s)
    (hf : FrameOutside s t
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr"))
    {a : Nat} (hlo : globN s "scratch_ptr" ≤ a) (hhi : a < scratchEnd) :
    memW t a = memW s a := by
  have h64 : a < 2 ^ 64 := by unfold scratchEnd at hhi; omega
  have heq : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt h64
  have hmem := hf (BitVec.ofNat 64 a) (by
    intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    rw [heq]
    unfold CellHits
    have hgap := ha.2.2.2.1
    dsimp only
    omega) (by
    rw [heq]
    unfold CellHits
    have hh := ha.2.1
    have hlow := ha.2.2.1
    have hgap := ha.2.2.2.1
    dsimp only
    unfold heapLimit at *
    omega)
  unfold memW
  rw [hmem]

theorem HeapBlock.grow {F : Type} {s t : PanSemStateFiniteExact 64 F} {p n : Nat}
    (h : HeapBlock s p n) (hg : globN s "heap_ptr" ≤ globN t "heap_ptr") :
    HeapBlock t p n := ⟨h.1, h.2.trans hg⟩

theorem ResultOK.grow {F : Type} {s t : PanSemStateFiniteExact 64 F} {p : Nat}
    (h : ResultOK s p) (hg : globN s "heap_ptr" ≤ globN t "heap_ptr") :
    ResultOK t p := h.elim Or.inl (fun h => Or.inr (h.grow hg))

theorem FreshBlock.heapBlock {F : Type} {s t : PanSemStateFiniteExact 64 F} {p n : Nat}
    (h : FreshBlock s t p n) (ha : ArenaOK s) (hn : n % 8 = 0) : HeapBlock t p n := by
  have hr : (n + 7) / 8 * 8 = n := by omega
  exact ⟨ha.1.trans h.2.1.1, by simpa only [hr] using h.2.1.2⟩

theorem FrameOK.preserve {F : Type} {s t : PanSemStateFiniteExact 64 F} {p : Nat}
    (h : FrameOK s p) (hg : globN s "heap_ptr" ≤ globN t "heap_ptr")
    (he : ∀ a, p ≤ a → a < p + 88 → memW t a = memW s a) : FrameOK t p := by
  refine ⟨h.1, h.2.1, ?_⟩
  have h8 := he (p + 8) (by omega) (by omega)
  have h16 := he (p + 16) (by omega) (by omega)
  have h32 := he (p + 32) (by omega) (by omega)
  rw [h8, h16, h32]
  exact h.2.2.elim Or.inl (fun h => Or.inr ⟨h.1, h.2.1, h.2.2.grow hg⟩)

theorem Stack.preserve {F : Type} {s t : PanSemStateFiniteExact 64 F} {lo top : Nat}
    {ps : List Nat} (h : Stack s lo top ps)
    (hg : globN s "heap_ptr" ≤ globN t "heap_ptr")
    (he : ∀ a, lo ≤ a → a < scratchEnd → memW t a = memW s a) :
    Stack t lo top ps ∧ credits t ps = credits s ps := by
  induction ps generalizing lo top with
  | nil => exact ⟨h, rfl⟩
  | cons p ps ih =>
    have hp := h.2.2.2.1
    have hpEnd := hp.2.1
    have hlp := h.2.1
    have he' : ∀ a, p ≤ a → a < p + 88 → memW t a = memW s a :=
      fun a ha hb => he a (h.2.1.trans ha) (by omega)
    have hlink := he' p (by omega) (by omega)
    obtain ⟨hs, hc⟩ := ih h.2.2.2.2 (fun a ha hb => he a (by omega) hb)
    refine ⟨⟨h.1, h.2.1, h.2.2.1, hp.preserve hg he', ?_⟩, ?_⟩
    · rw [hlink]; exact hs
    · simp only [credits, List.map_cons, List.sum_cons] at hc ⊢
      rw [hc]
      unfold frameCredit
      rw [he' (p + 8) (by omega) (by omega), he' (p + 32) (by omega) (by omega)]

theorem headInv_locals : LocalsOnly ["mode", "result", "top"] HeadInv := by
  intro F s ls k hl h
  obtain ⟨ha, hm, hr, ⟨ps, hs⟩, ht, hwt, hwr⟩ := h
  have hmode := locN_congr s ls k "mode" (hl "mode" (by simp))
  have hresult := locN_congr s ls k "result" (hl "result" (by simp))
  have htop := locN_congr s ls k "top" (hl "top" (by simp))
  refine ⟨localsFree_arenaReady s ls k ha, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmode]; exact hm
  · rw [hresult]; exact hr
  · refine ⟨ps, ?_⟩
    rw [htop]
    exact (hs.preserve (t := { s with locals := ls, clock := k }) (Nat.le_refl _)
      (fun _ _ _ => rfl)).1
  · rw [hmode, htop]; exact ht
  · obtain ⟨w, hw⟩ := hwt
    exact ⟨w, (hl "top" (by simp)).trans hw⟩
  · obtain ⟨w, hw⟩ := hwr
    exact ⟨w, (hl "result" (by simp)).trans hw⟩

theorem rank_locals {F : Type} {s : PanSemStateFiniteExact 64 F}
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hl : ∀ n ∈ ["mode", "top", "go"], ls.lookup (ofString n) = s.locals.lookup (ofString n))
    {lo : Nat} {ps : List Nat} (hs : Stack s lo (locN s "top") ps) :
    rank { s with locals := ls, clock := k } = rank s := by
  have hmode := locN_congr s ls k "mode" (hl "mode" (by simp))
  have htop := locN_congr s ls k "top" (hl "top" (by simp))
  have hgo := locN_congr s ls k "go" (hl "go" (by simp))
  obtain ⟨ht, he⟩ := hs.preserve (t := { s with locals := ls, clock := k }) (Nat.le_refl _)
    (fun _ _ _ => rfl)
  simp only [rank, hmode, htop, hgo, stackCredit_eq hs, stackCredit_eq ht, he]
  rfl

theorem rank_pos {F : Type} {s : PanSemStateFiniteExact 64 F} (h : locN s "go" ≠ 0) :
    0 < rank s := by simp only [rank, if_neg h]; omega

theorem rank_decrease {F : Type} {s t : PanSemStateFiniteExact 64 F} {lo lo' : Nat}
    {ps qs : List Nat} (hs : Stack s lo (locN s "top") ps)
    (ht : Stack t lo' (locN t "top") qs) (ha : locN s "go" ≠ 0)
    (hd : globN t "scratch_ptr" + credits t qs + locN t "mode" <
      globN s "scratch_ptr" + credits s ps + locN s "mode") : rank t < rank s := by
  rw [rank, rank, if_neg ha, stackCredit_eq hs]
  split
  · omega
  · rw [stackCredit_eq ht]; omega

theorem rank_exit {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (ha : locN s "go" ≠ 0) (hz : locN t "go" = 0) : rank t < rank s := by
  rw [rank, if_pos hz]
  exact rank_pos ha

theorem push_credit_decrease {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {ps : List Nat} {p : Nat} (hp : FrameOK t p)
    (hg : globN t "scratch_ptr" + 88 ≤ globN s "scratch_ptr")
    (hc : credits t ps = credits s ps) :
    globN t "scratch_ptr" + credits t (p :: ps) + 2 <
      globN s "scratch_ptr" + credits s ps + 1 := by
  have hw := (frameCredit_bounds hp).2
  change globN t "scratch_ptr" + (frameCredit t p + credits t ps) + 2 < _
  rw [hc]
  omega

theorem pop_credit_decrease {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {ps : List Nat} {p : Nat} (hp : FrameOK s p)
    (hg : globN t "scratch_ptr" ≤ globN s "scratch_ptr")
    (hc : credits t ps = credits s ps) :
    globN t "scratch_ptr" + credits t ps <
      globN s "scratch_ptr" + credits s (p :: ps) := by
  have hw := (frameCredit_bounds hp).1
  change _ < globN s "scratch_ptr" + (frameCredit s p + credits s ps)
  rw [hc]
  omega

theorem next_credit_decrease {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {ps : List Nat} {p : Nat} (hs : memW s (p + 8) = 2) (ht : memW t (p + 8) = 2)
    (hi : memW s (p + 32) + 1 < 16) (hi' : memW t (p + 32) = memW s (p + 32) + 1)
    (hg : globN t "scratch_ptr" ≤ globN s "scratch_ptr")
    (hc : credits t ps = credits s ps) :
    globN t "scratch_ptr" + credits t (p :: ps) + 2 <
      globN s "scratch_ptr" + credits s (p :: ps) := by
  change globN t "scratch_ptr" + (frameCredit t p + credits t ps) + 2 <
    globN s "scratch_ptr" + (frameCredit s p + credits s ps)
  simp only [frameCredit, ht, hs, if_neg (by decide : (2 : Nat) ≠ 1), hi', hc]
  omega

def writeWord {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) (w : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  { s with memory := fun b => if b = BitVec.ofNat 64 a then .word w else s.memory b }

theorem memW_writeWord {F : Type} (s : PanSemStateFiniteExact 64 F) {a b : Nat}
    (w : BitVec 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    memW (writeWord s a w) b = if b = a then w.toNat else memW s b := by
  have he : (BitVec.ofNat 64 b = BitVec.ofNat 64 a) ↔ b = a := by
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
    · intro h; rw [h]
  simp only [memW, writeWord, he]
  split <;> rfl

theorem writeWord_arena {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : ArenaReady s) (a : Nat) (w : BitVec 64) : ArenaReady (writeWord s a w) :=
  ⟨guestInv_congr (s := s) rfl rfl rfl rfl h.1, h.2⟩

theorem FrameOK.writeWord {F : Type} {s : PanSemStateFiniteExact 64 F} {p a : Nat}
    (h : FrameOK s p) (w : BitVec 64) (ha : a < 2 ^ 64)
    (h8 : p + 8 ≠ a) (h16 : p + 16 ≠ a) (h32 : p + 32 ≠ a) :
    FrameOK (writeWord s a w) p := by
  have hpEnd := h.2.1
  have hp64 : p + 88 < 2 ^ 64 := by unfold scratchEnd at hpEnd; omega
  refine ⟨h.1, h.2.1, ?_⟩
  rw [memW_writeWord s w ha (by omega), if_neg h8,
    memW_writeWord s w ha (by omega), if_neg h32,
    memW_writeWord s w ha (by omega), if_neg h16]
  exact h.2.2

theorem Stack.below_write {F : Type} {s : PanSemStateFiniteExact 64 F} {lo top a : Nat}
    {ps : List Nat} (h : Stack s lo top ps) (w : BitVec 64) (ha : a < lo)
    (ha64 : a < 2 ^ 64) :
    Stack (writeWord s a w) lo top ps ∧ credits (writeWord s a w) ps = credits s ps := by
  apply h.preserve (t := writeWord s a w) (Nat.le_refl _)
  intro b hb hbEnd
  have hb64 : b < 2 ^ 64 := by unfold scratchEnd at hbEnd; omega
  rw [memW_writeWord s w ha64 hb64, if_neg (by omega)]

theorem Stack.heap_write {F : Type} {s : PanSemStateFiniteExact 64 F} {top a : Nat}
    {ps : List Nat} (h : Stack s (globN s "scratch_ptr") top ps) (ha : ArenaOK s)
    (w : BitVec 64) (haddr : a < heapLimit) :
    Stack (writeWord s a w) (globN s "scratch_ptr") top ps ∧
      credits (writeWord s a w) ps = credits s ps := by
  have hs : scratchStart ≤ globN s "scratch_ptr" := ha.2.2.1.trans ha.2.2.2.1
  apply h.below_write w
  · unfold heapLimit at haddr; omega
  · unfold heapLimit scratchStart at haddr; omega

theorem Stack.aux_write {F : Type} {s : PanSemStateFiniteExact 64 F} {lo p off : Nat}
    {ps : List Nat} (h : Stack s lo p (p :: ps)) (w : BitVec 64)
    (hoff : off = 40 ∨ off = 80) :
    Stack (writeWord s (p + off) w) lo p (p :: ps) ∧
      credits (writeWord s (p + off) w) (p :: ps) = credits s (p :: ps) := by
  have hp := h.2.2.2.1
  have hpEnd := hp.2.1
  have hp64 : p + 88 < 2 ^ 64 := by unfold scratchEnd at hpEnd; omega
  have ho : off < 88 := by omega
  have ha64 : p + off < 2 ^ 64 := by omega
  obtain ⟨ht, hc⟩ := h.2.2.2.2.below_write w (by omega : p + off < p + 88) ha64
  refine ⟨⟨rfl, h.2.1, h.2.2.1, hp.writeWord w ha64 (by omega) (by omega) (by omega), ?_⟩, ?_⟩
  · rw [memW_writeWord s w ha64 (by omega), if_neg (by omega)]
    exact ht
  · change frameCredit (writeWord s (p + off) w) p + credits (writeWord s (p + off) w) ps =
      frameCredit s p + credits s ps
    rw [hc]
    unfold frameCredit
    rw [memW_writeWord s w ha64 (show p + 8 < 2 ^ 64 by omega),
      if_neg (show p + 8 ≠ p + off by omega),
      memW_writeWord s w ha64 (show p + 32 < 2 ^ 64 by omega),
      if_neg (show p + 32 ≠ p + off by omega)]

theorem Stack.counter_write {F : Type} {s : PanSemStateFiniteExact 64 F} {lo p : Nat}
    {ps : List Nat} (h : Stack s lo p (p :: ps))
    (htag : memW s (p + 8) = 2) (w : BitVec 64) (hw : w.toNat < 16) :
    Stack (writeWord s (p + 32) w) lo p (p :: ps) ∧
      credits (writeWord s (p + 32) w) ps = credits s ps ∧
      memW (writeWord s (p + 32) w) (p + 8) = 2 ∧
      memW (writeWord s (p + 32) w) (p + 32) = w.toNat := by
  have hp := h.2.2.2.1
  have hpEnd := hp.2.1
  have hp64 : p + 88 < 2 ^ 64 := by unfold scratchEnd at hpEnd; omega
  have hbr : HeapBlock s (memW s (p + 16)) 176 := by
    rcases hp.2.2 with h1 | h2
    · omega
    · exact h2.2.2
  have h8 : memW (writeWord s (p + 32) w) (p + 8) = 2 := by
    rw [memW_writeWord s w (by omega) (by omega), if_neg (by omega), htag]
  have h32 : memW (writeWord s (p + 32) w) (p + 32) = w.toNat := by
    rw [memW_writeWord s w (by omega) (by omega), if_pos rfl]
  obtain ⟨ht, hc⟩ := h.2.2.2.2.below_write w (by omega : p + 32 < p + 88) (by omega)
  refine ⟨⟨rfl, h.2.1, h.2.2.1, ⟨hp.1, hp.2.1, Or.inr ⟨h8, ?_, ?_⟩⟩, ?_⟩, hc, h8, h32⟩
  · rw [h32]; exact hw
  · rw [memW_writeWord s w (by omega) (by omega), if_neg (by omega)]
    exact hbr
  · rw [memW_writeWord s w (by omega) (by omega), if_neg (by omega)]
    exact ht

theorem Stack.push {F : Type} {s : PanSemStateFiniteExact 64 F} {lo top p : Nat}
    {ps : List Nat} (h : Stack s lo top ps) (hp : FrameOK s p)
    (hbelow : p + 88 ≤ lo) (hp0 : p ≠ 0) (w : BitVec 64) (hw : w.toNat = top)
    {lo' : Nat} (hlo : lo' ≤ p) :
    Stack (writeWord s p w) lo' p (p :: ps) ∧
      credits (writeWord s p w) ps = credits s ps := by
  have hpEnd := hp.2.1
  have hp64 : p + 88 < 2 ^ 64 := by unfold scratchEnd at hpEnd; omega
  obtain ⟨ht, hc⟩ := h.below_write w (by omega : p < lo) (by omega)
  refine ⟨⟨rfl, hlo, hp0, hp.writeWord w (by omega) (by omega) (by omega) (by omega), ?_⟩, hc⟩
  rw [memW_writeWord s w (by omega) (by omega), if_pos rfl, hw]
  exact ht.lower hbelow

theorem freshScratch_space {F : Type} {s t : PanSemStateFiniteExact 64 F} {p : Nat}
    (h : FreshScratch s t p 88) (ha : ArenaOK s) :
    p ≠ 0 ∧ p + 88 ≤ globN s "scratch_ptr" ∧
      globN t "scratch_ptr" + 88 ≤ globN s "scratch_ptr" := by
  have hframe := ha.2.2.1
  have hp := h.2.1
  have hinside := h.2.2.1
  change globN t "scratch_ptr" ≤ p ∧ p + 88 ≤ globN s "scratch_ptr" at hinside
  unfold scratchStart at hframe
  omega

/-- The part of a callee's write contract used by the decoder. -/
def KeepsScratch {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  ArenaReady t ∧ AllocatorGrows s t ∧
    ∀ a, globN s "scratch_ptr" ≤ a → a < scratchEnd → memW t a = memW s a

theorem KeepsScratch.stack {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : KeepsScratch s t) {top : Nat} {ps : List Nat}
    (hs : Stack s (globN s "scratch_ptr") top ps) :
    Stack t (globN t "scratch_ptr") top ps ∧ credits t ps = credits s ps := by
  obtain ⟨ht, hc⟩ := hs.preserve h.2.1.1 h.2.2
  exact ⟨ht.lower h.2.1.2, hc⟩

theorem writes_return {fname : MlS} {gw : List String}
    (hw : WritesWithin (fun _ => []) gw fname) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64)) (b : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (v : ValueHOL 64) (t : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (ha : ArenaReady s)
    (hl : lookupCodeHOLFinite s.code.lookup fname values = some (b, callee, shape))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b = (some (.returned v), t)) :
    KeepsScratch s t := by
  have h := FunSpec.at_lookup hw s hc values b callee shape hl
    (localsFree_arenaReady s callee (s.clock - 1) ha) (by rw [hr]; simp)
  rw [hr] at h
  obtain ⟨hat, hh, hsp, hframe, _⟩ := h (Or.inl ⟨v, rfl⟩)
  refine ⟨hat, ⟨hh, hsp⟩, ?_⟩
  exact fun _ hlo hhi => frameOutside_scratch ha.2 hframe hlo hhi

theorem locN_lookup_eq {F : Type} {s t : PanSemStateFiniteExact 64 F} {n : String}
    (h : t.locals.lookup (ofString n) = s.locals.lookup (ofString n)) : locN t n = locN s n := by
  unfold locN; rw [h]

theorem KeepsScratch.head {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : KeepsScratch s t) (hs : HeadInv s)
    (hl : ∀ n ∈ ["mode", "top", "result"], t.locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    HeadInv t := by
  obtain ⟨ha, hm, hr, ⟨ps, hps⟩, htop, hwt, hwr⟩ := hs
  have em := locN_lookup_eq (hl "mode" (by simp))
  have et := locN_lookup_eq (hl "top" (by simp))
  have er := locN_lookup_eq (hl "result" (by simp))
  refine ⟨h.1, ?_, ?_, ⟨ps, ?_⟩, ?_, ?_, ?_⟩
  · rw [em]; exact hm
  · rw [er]; exact hr.grow h.2.1.1
  · rw [et]; exact (h.stack hps).1
  · rw [em, et]; exact htop
  · obtain ⟨w, hw⟩ := hwt; exact ⟨w, (hl "top" (by simp)).trans hw⟩
  · obtain ⟨w, hw⟩ := hwr; exact ⟨w, (hl "result" (by simp)).trans hw⟩

theorem KeepsScratch.rank_le {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : KeepsScratch s t) {ps : List Nat}
    (hs : Stack s (globN s "scratch_ptr") (locN s "top") ps)
    (hl : ∀ n ∈ ["mode", "top", "go"], t.locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    rank t ≤ rank s := by
  have em := locN_lookup_eq (hl "mode" (by simp))
  have et := locN_lookup_eq (hl "top" (by simp))
  have eg := locN_lookup_eq (hl "go" (by simp))
  obtain ⟨ht, he⟩ := h.stack hs
  simp only [rank, em, et, eg, stackCredit_eq hs, stackCredit_eq ht, he]
  have hsp := h.2.1.2
  split <;> omega

theorem HeadInv.set_result {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : HeadInv s) (w : BitVec 64) (hw : ResultOK s w.toNat) :
    HeadInv (setVarHOLFinite (ofString "result") (.val (.word w)) s) := by
  obtain ⟨ha, hm, hr, ⟨ps, hps⟩, ht, hwt, hwr⟩ := h
  let t := setVarHOLFinite (ofString "result") (.val (.word w)) s
  have em : locN t "mode" = locN s "mode" := locN_setVar_ne s _ _ _ (by decide)
  have et : locN t "top" = locN s "top" := locN_setVar_ne s _ _ _ (by decide)
  refine ⟨localsFree_arenaReady s _ _ ha, ?_, ?_, ⟨ps, ?_⟩, ?_,
    hwt.set_ne _ _ (by decide), wordLocal_set s "result" w⟩
  · rw [em]; exact hm
  · rw [locN_setVar_same]; exact hw
  · rw [et]
    exact (hps.preserve (t := t) (Nat.le_refl _) (fun _ _ _ => rfl)).1
  · rw [em, et]; exact ht

theorem HeadInv.set_mode {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : HeadInv s) (w : BitVec 64) (hw : w.toNat ≤ 2)
    (ht : w.toNat = 2 → locN s "top" ≠ 0) :
    HeadInv (setVarHOLFinite (ofString "mode") (.val (.word w)) s) := by
  obtain ⟨ha, hm, hr, ⟨ps, hps⟩, _, hwt, hwr⟩ := h
  let t := setVarHOLFinite (ofString "mode") (.val (.word w)) s
  have er : locN t "result" = locN s "result" := locN_setVar_ne s _ _ _ (by decide)
  have et : locN t "top" = locN s "top" := locN_setVar_ne s _ _ _ (by decide)
  refine ⟨localsFree_arenaReady s _ _ ha, ?_, ?_, ⟨ps, ?_⟩, ?_,
    hwt.set_ne _ _ (by decide), hwr.set_ne _ _ (by decide)⟩
  · rw [locN_setVar_same]; exact hw
  · rw [er]; exact hr
  · rw [et]
    exact (hps.preserve (t := t) (Nat.le_refl _) (fun _ _ _ => rfl)).1
  · rw [locN_setVar_same, et]; exact ht

theorem rank_set_result {F : Type} {s : PanSemStateFiniteExact 64 F} (h : HeadInv s)
    (w : BitVec 64) : rank (setVarHOLFinite (ofString "result") (.val (.word w)) s) = rank s := by
  obtain ⟨ps, hps⟩ := h.2.2.2.1
  apply rank_locals _ _ _ hps
  intro n hn
  simp at hn
  have hne : ofString "result" ≠ ofString n := by
    rcases hn with rfl | rfl | rfl <;> decide
  simp [HolFiniteMapExact.update, FUPDATE, hne]

theorem rank_set_mode_lt {F : Type} {s : PanSemStateFiniteExact 64 F} (h : HeadInv s)
    (hgo : locN s "go" ≠ 0) (w : BitVec 64) (hw : w.toNat < locN s "mode") :
    rank (setVarHOLFinite (ofString "mode") (.val (.word w)) s) < rank s := by
  obtain ⟨ps, hps⟩ := h.2.2.2.1
  let t := setVarHOLFinite (ofString "mode") (.val (.word w)) s
  have et : locN t "top" = locN s "top" := locN_setVar_ne s _ _ _ (by decide)
  obtain ⟨ht, he⟩ := hps.preserve (t := t) (Nat.le_refl _) (fun _ _ _ => rfl)
  apply rank_decrease hps (show Stack t (globN s "scratch_ptr") (locN t "top") ps by rw [et]; exact ht) hgo
  rw [he, locN_setVar_same]
  change globN s "scratch_ptr" + credits s ps + w.toNat < _
  omega

/-- Completing a decode (or an immediate resolution) consumes the mode phase. -/
theorem completed_transition {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hs : HeadInv s) (hk : KeepsScratch s t)
    (hl : ∀ n ∈ ["mode", "top", "result", "go"],
      t.locals.lookup (ofString n) = s.locals.lookup (ofString n))
    (hmode : 0 < locN s "mode") (hgo : locN s "go" ≠ 0)
    (w : BitVec 64) (hw : ResultOK t w.toNat) :
    let u := setVarHOLFinite (ofString "mode") (.val (.word 0))
      (setVarHOLFinite (ofString "result") (.val (.word w)) t)
    HeadInv u ∧ rank u < rank s := by
  have ht := hk.head hs (fun n hn => hl n (by simp at hn ⊢; tauto))
  have hle := hk.rank_le hs.2.2.2.1.choose_spec
    (fun n hn => hl n (by simp at hn ⊢; tauto))
  have hr := ht.set_result w hw
  refine ⟨hr.set_mode 0 (by decide) (by intro h; cases h), ?_⟩
  have hg : locN (setVarHOLFinite (ofString "result") (.val (.word w)) t) "go" ≠ 0 := by
    rw [locN_setVar_ne t "go" _ _ (by decide), locN_lookup_eq (hl "go" (by simp))]
    exact hgo
  have hm : (0 : BitVec 64).toNat < locN (setVarHOLFinite (ofString "result") (.val (.word w)) t) "mode" := by
    rw [locN_setVar_ne t "mode" _ _ (by decide), locN_lookup_eq (hl "mode" (by simp))]
    exact hmode
  have hlt := rank_set_mode_lt hr hg 0 hm
  rw [rank_set_result ht w] at hlt
  exact hlt.trans_le hle

theorem fresh_frame {F : Type} {s t : PanSemStateFiniteExact 64 F} {p : Nat}
    (ha : ArenaOK s) (hf : FreshScratch s t p 88)
    (htag : memW t (p + 8) = 1 ∨
      (memW t (p + 8) = 2 ∧ memW t (p + 32) = 0 ∧
        memW t (p + 40) = 0 ∧ FreshBlock s t (memW t (p + 16)) 176)) : FrameOK t p := by
  refine ⟨hf.1, ?_, ?_⟩
  · have hhi := ha.2.2.2.2.1
    have hp := hf.2.2.1.2
    change p + 88 ≤ globN s "scratch_ptr" at hp
    exact hp.trans hhi
  · rcases htag with h | ⟨h, hc, _, hb⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, by omega, FreshBlock.heapBlock hb ha (by decide)⟩

theorem decode_returns
    (hw : WritesWithin (fun _ => []) ["heap_ptr", "scratch_ptr"] (ofString "_decode_step"))
    (hp : PushesFrame (ofString "_decode_step")) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64)) (b : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (v : ValueHOL 64) (t : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (ha : ArenaReady s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "_decode_step") values = some (b, callee, shape))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b = (some (.returned v), t)) :
    KeepsScratch s t ∧ ∃ tag p : BitVec 64,
      v = .rStruct [.val (.word tag), .val (.word p)] ∧
      (tag.toNat = 0 → ResultOK t p.toNat) ∧
      (tag.toNat ≠ 0 → FreshScratch s t p.toNat 88 ∧ FrameOK t p.toNat) := by
  refine ⟨writes_return hw s values b callee shape v t hc ha hl hr, ?_⟩
  have h := FunSpec.at_lookup hp s hc values b callee shape hl
    (localsFree_arenaReady s callee (s.clock - 1) ha) (by rw [hr]; simp)
  rw [hr] at h
  obtain ⟨tag, p, hv, hz, hn⟩ := h v rfl
  refine ⟨tag, p, hv, ?_, ?_⟩
  · intro htag
    exact (hz htag).elim Or.inl (fun hf => Or.inr (FreshBlock.heapBlock hf ha.2 (by decide)))
  · intro htag
    obtain ⟨hf, hk⟩ := hn htag
    exact ⟨hf, fresh_frame ha.2 hf hk⟩

theorem resolve_returns
    (hw : WritesWithin (fun _ => []) ["heap_ptr", "scratch_ptr"] (ofString "_resolve_step"))
    (hp : ResolvesNode (ofString "_resolve_step")) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64)) (b : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (v : ValueHOL 64) (t : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (ha : ArenaReady s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "_resolve_step") values = some (b, callee, shape))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b = (some (.returned v), t)) :
    KeepsScratch s t ∧ ∃ tag p n hash : BitVec 64,
      v = .rStruct [.val (.word tag), .val (.word p), .val (.word n), .val (.word hash)] ∧
      (tag.toNat = 0 → ResultOK t p.toNat) := by
  refine ⟨writes_return hw s values b callee shape v t hc ha hl hr, ?_⟩
  have h := FunSpec.at_lookup hp s hc values b callee shape hl
    (localsFree_arenaReady s callee (s.clock - 1) ha) (by rw [hr]; simp)
  rw [hr] at h
  obtain ⟨tag, p, n, hash, hv, hz⟩ := h v rfl
  refine ⟨tag, p, n, hash, hv, ?_⟩
  intro htag
  exact (hz htag).elim Or.inl (fun hf => Or.inr (FreshBlock.heapBlock hf ha.2 (by decide)))

theorem extension_returns
    (hw : WritesWithin (fun _ => []) ["heap_ptr"] (ofString "node_new_ext"))
    (hp : Returns ArenaReady (fun s t p => FreshBlock s t p 56) (ofString "node_new_ext")) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64)) (b : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (v : ValueHOL 64) (t : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (ha : ArenaReady s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "node_new_ext") values = some (b, callee, shape))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b = (some (.returned v), t)) :
    KeepsScratch s t ∧ ∃ p : BitVec 64, v = .val (.word p) ∧ HeapBlock t p.toNat 56 := by
  refine ⟨writes_return hw s values b callee shape v t hc ha hl hr, ?_⟩
  have h := FunSpec.at_lookup hp s hc values b callee shape hl
    (localsFree_arenaReady s callee (s.clock - 1) ha) (by rw [hr]; simp)
  rw [hr] at h
  obtain ⟨p, hv, _, _, hf⟩ := h v rfl
  exact ⟨p, hv, FreshBlock.heapBlock hf ha.2 (by decide)⟩

/-- The concrete updates performed when `_decode_step` returns a fresh frame. -/
def pushState {F : Type} (t : PanSemStateFiniteExact 64 F) (b top slot : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "mode") (.val (.word 2))
    (setVarHOLFinite (ofString "slot") (.val (.word slot))
      (setVarHOLFinite (ofString "top") (.val (.word b)) (writeWord t b.toNat top)))

theorem pushed_transition {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hs : HeadInv s) (hk : KeepsScratch s t)
    (hl : ∀ n ∈ ["mode", "top", "result", "go"],
      t.locals.lookup (ofString n) = s.locals.lookup (ofString n))
    (hm : locN s "mode" = 1) (hgo : locN s "go" ≠ 0)
    (b top slot : BitVec 64) (htop : top.toNat = locN s "top")
    (hp : FrameOK t b.toNat) (hf : FreshScratch s t b.toNat 88) :
    HeadInv (pushState t b top slot) ∧ rank (pushState t b top slot) < rank s := by
  obtain ⟨ps, hps⟩ := hs.2.2.2.1
  obtain ⟨ht, hc⟩ := hps.preserve hk.2.1.1 hk.2.2
  obtain ⟨hb0, hbelow, hsp⟩ := freshScratch_space hf hs.1.2
  obtain ⟨hpush, hcredit⟩ := ht.push hp hbelow hb0 top htop hf.2.2.1.1
  let u := pushState t b top slot
  have huTop : locN u "top" = b.toNat := by
    change locN (pushState t b top slot) "top" = _
    rw [pushState, locN_setVar_ne _ "top" _ _ (by decide),
      locN_setVar_ne _ "top" _ _ (by decide), locN_setVar_same]
  have huMode : locN u "mode" = 2 := locN_setVar_same _ "mode" 2
  have huResult : locN u "result" = locN s "result" := by
    change locN (pushState t b top slot) "result" = _
    rw [pushState, locN_setVar_ne _ "result" _ _ (by decide),
      locN_setVar_ne _ "result" _ _ (by decide), locN_setVar_ne _ "result" _ _ (by decide)]
    exact locN_lookup_eq (hl "result" (by simp))
  obtain ⟨huStack, huCredit⟩ := hpush.preserve (t := u) (Nat.le_refl _) (fun _ _ _ => rfl)
  have huTopWord : WordLocal u "top" :=
    ((wordLocal_set _ "top" b).set_ne _ _ (by decide)).set_ne _ _ (by decide)
  have huResultWord : WordLocal u "result" := by
    obtain ⟨w, hw⟩ := hs.2.2.2.2.2.2
    have htword : WordLocal (writeWord t b.toNat top) "result" :=
      ⟨w, (hl "result" (by simp)).trans hw⟩
    exact ((htword.set_ne _ _ (by decide)).set_ne _ _ (by decide)).set_ne _ _ (by decide)
  have huStack' : Stack u (globN u "scratch_ptr") (locN u "top") (b.toNat :: ps) := by
    rw [huTop]; exact huStack
  refine ⟨⟨localsFree_arenaReady (writeWord t b.toNat top) _ _
    (writeWord_arena hk.1 _ _), by rw [huMode], ?_, ⟨_, huStack'⟩,
    by rw [huTop]; exact fun _ => hb0, huTopWord, huResultWord⟩, ?_⟩
  · rw [huResult]
    exact hs.2.2.1.grow hk.2.1.1
  · apply rank_decrease hps huStack' hgo
    rw [huCredit]
    change globN t "scratch_ptr" +
      (frameCredit (writeWord t b.toNat top) b.toNat + credits (writeWord t b.toNat top) ps) +
      locN u "mode" < _
    rw [hcredit, hc, huMode, hm]
    have hp' := hpush.2.2.2.1
    have hbCredit := (frameCredit_bounds hp').2
    omega

def popState {F : Type} (s : PanSemStateFiniteExact 64 F) (top result : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "result") (.val (.word result))
    (setVarHOLFinite (ofString "top") (.val (.word top)) s)

theorem popped_transition {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (ha : ArenaReady t) (hg : globN t "scratch_ptr" ≤ globN s "scratch_ptr")
    {p : Nat} {ps : List Nat} (hps : Stack s (globN s "scratch_ptr") (locN s "top") (p :: ps))
    (hm : locN s "mode" = 0) (htm : locN t "mode" = 0) (hgo : locN s "go" ≠ 0)
    (top result : BitVec 64) (ht : Stack t (globN t "scratch_ptr") top.toNat ps)
    (hc : credits t ps ≤ credits s ps) (hr : ResultOK t result.toNat) :
    HeadInv (popState t top result) ∧ rank (popState t top result) < rank s := by
  let u := popState t top result
  have huTop : locN u "top" = top.toNat := by
    dsimp only [u, popState]
    rw [locN_setVar_ne _ "top" _ _ (by decide), locN_setVar_same]
  have huMode : locN u "mode" = 0 := by
    dsimp only [u, popState]
    rw [locN_setVar_ne _ "mode" _ _ (by decide),
      locN_setVar_ne _ "mode" _ _ (by decide), htm]
  obtain ⟨huStack, huCredits⟩ := ht.preserve (t := u) (Nat.le_refl _) (fun _ _ _ => rfl)
  have huStack' : Stack u (globN u "scratch_ptr") (locN u "top") ps := by
    rw [huTop]; exact huStack
  have huModeTop : locN u "mode" = 2 → locN u "top" ≠ 0 := by omega
  refine ⟨⟨localsFree_arenaReady t _ _ ha, by rw [huMode]; decide, ?_, ⟨_, huStack'⟩,
    huModeTop,
    (wordLocal_set _ "top" top).set_ne _ _ (by decide), wordLocal_set _ "result" result⟩, ?_⟩
  · rw [popState, locN_setVar_same]; exact hr
  · apply rank_decrease hps huStack' hgo
    rw [huCredits, huMode, hm]
    have hp := (frameCredit_bounds hps.2.2.2.1).1
    change globN t "scratch_ptr" + credits t ps + 0 <
      globN s "scratch_ptr" + (frameCredit s p + credits s ps) + 0
    omega

def nextState {F : Type} (s : PanSemStateFiniteExact 64 F) (slot : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "mode") (.val (.word 2))
    (setVarHOLFinite (ofString "slot") (.val (.word slot)) s)

theorem advanced_transition {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (ht : HeadInv t) (hg : globN t "scratch_ptr" ≤ globN s "scratch_ptr")
    {p : Nat} {ps : List Nat}
    (hps : Stack s (globN s "scratch_ptr") (locN s "top") (p :: ps))
    (hpt : Stack t (globN t "scratch_ptr") (locN t "top") (p :: ps))
    (hm : locN s "mode" = 0) (hgo : locN s "go" ≠ 0)
    (hsTag : memW s (p + 8) = 2) (htTag : memW t (p + 8) = 2)
    (hi : memW s (p + 32) + 1 < 16) (hi' : memW t (p + 32) = memW s (p + 32) + 1)
    (hc : credits t ps = credits s ps) (slot : BitVec 64) :
    HeadInv (nextState t slot) ∧ rank (nextState t slot) < rank s := by
  let u := nextState t slot
  have hslot : HeadInv (setVarHOLFinite (ofString "slot") (.val (.word slot)) t) :=
    headInv_locals.setVar (by decide) _ t ht
  have huMode : locN u "mode" = 2 := locN_setVar_same _ "mode" 2
  have huTop : locN u "top" = locN t "top" := by
    dsimp only [u, nextState]
    rw [locN_setVar_ne _ "top" _ _ (by decide),
      locN_setVar_ne _ "top" _ _ (by decide)]
  obtain ⟨huStack, huCredits⟩ := hpt.preserve (t := u) (Nat.le_refl _) (fun _ _ _ => rfl)
  have huStack' : Stack u (globN u "scratch_ptr") (locN u "top") (p :: ps) := by
    rw [huTop]; exact huStack
  refine ⟨hslot.set_mode 2 (by decide) ?_, ?_⟩
  · intro _
    rw [locN_setVar_ne _ "top" _ _ (by decide), hpt.1]
    exact hpt.2.2.1
  · apply rank_decrease hps huStack' hgo
    rw [huCredits, huMode, hm, Nat.add_zero]
    exact next_credit_decrease hsTag htTag hi hi' hg hc

/-- A triple for the fall-through path. All exceptional paths end the loop iteration. -/
abbrev Falls (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (p : ProgHOL 64)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) : Prop :=
  Hoare P p (fun r s => r = none → Q s)

/-- A `decCall` continuation runs only when the returned value has its declared shape. -/
def DecCallResumeValid (P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (name : MlS) (shape : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64)) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
    (b : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (t : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → P s →
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
    lookupCodeHOLFinite s.code.lookup fname values = some (b, callee, ret) →
    evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b = (some (.returned v), t) →
    shapeEqHOL (shapeOfHOLExact v) shape = true →
    Q (setVarHOLFinite name v { t with locals := s.locals })

section FallRules
variable {P R Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}

theorem Falls.seq {p q : ProgHOL 64} (hp : Falls P p R) (hq : Falls R q Q) :
    Falls P (.seq p q) Q := by
  apply Hoare.seq (R := R) ?_ hq
  refine ⟨fun s hc hP hnt => ⟨hp.run s hc hP hnt, ?_⟩⟩
  intro hne heq
  exact (hne heq).elim

theorem Falls.ite {c : ExpHOL 64} {p q : ProgHOL 64}
    (hp : Falls (fun s => P s ∧ CondTrue c s) p Q)
    (hq : Falls (fun s => P s ∧ CondFalse c s) q Q) : Falls P (.ite c p q) Q :=
  Hoare.ite hp hq (fun _ _ h => by cases h)

theorem Falls.assign {kind : VarKind} {name : MlS} {e : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      evalAt s e = some v → Q (setKvarHOLFinite kind name v s)) :
    Falls P (.assign kind name e) Q :=
  Hoare.assign (fun s v hp he _ => h s v hp he) (fun _ _ h => by cases h)

theorem Falls.skip (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q s) :
    Falls P .skip Q := Hoare.skip (fun s hp _ => h s hp)

theorem Falls.mono {P' Q' : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p : ProgHOL 64} (h : Falls P p Q)
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P' s → P s)
    (ho : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), Q s → Q' s) : Falls P' p Q' :=
  ⟨fun s hc hp hnt hr => ho _ (h.run s hc (hi s hp) hnt hr)⟩

theorem Falls.call_readOnly {names : List String} {fname : MlS} (args : List (ExpHOL 64))
    (hf : ReadOnlyFn fname) (hP : LocalsOnly names P)
    (hg : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s) :
    Falls P (.call (some (none, none)) fname args) P := by
  apply Hoare.call0 hf (callEntryOn_of_imp localsFree_guestInv hg _ _)
  · intro F s callee t v hc hp hq _
    have he := hq (Or.inl ⟨v, rfl⟩)
    rw [he]
    exact hP s s.locals t.clock (fun _ _ => rfl) hp
  · intro F r s hn _ he
    exact (hn he).elim

theorem Falls.dec {names : List String} {name : MlS} {shape : ShapeHOL} {e : ExpHOL 64}
    {p : ProgHOL 64} (hn : ∀ n ∈ names, ofString n ≠ name)
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      evalAt s e = some v → R (setVarHOLFinite name v s))
    (hp : Falls R p Q) (hQ : LocalsOnly names Q) : Falls P (.dec name shape e p) Q :=
  Hoare.dec hn hi hp
    (fun _ s ls hl h hr => hQ s ls s.clock hl (h hr)) (fun _ _ h => by cases h)

theorem Falls.decCall {names : List String} {name fname : MlS} {shape : ShapeHOL}
    {args : List (ExpHOL 64)} {p : ProgHOL 64}
    (hn : ∀ n ∈ names, ofString n ≠ name) (hr : DecCallResumeValid P R name shape fname args)
    (hp : Falls R p Q) (hQ : LocalsOnly names Q) : Falls P (.decCall name shape fname args p) Q := by
  refine ⟨fun {F} s hc hP hnt hfall => ?_⟩
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hfall ⊢
  simp only [evalListHOLFinite] at hfall ⊢
  cases ha : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => simp [ha] at hfall
  | some values =>
    simp only [ha] at hfall ⊢
    cases hl : lookupCodeHOLFinite s.code.lookup fname values with
    | none => simp [hl] at hfall
    | some installed =>
      obtain ⟨b, callee, ret⟩ := installed
      simp only [hl] at hfall ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hfall
      · simp only [hz, ↓reduceIte] at hfall ⊢
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) b).1
        cases he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b with
        | mk r t =>
          simp only [he] at hfall hmeta ⊢
          cases r with
          | none => simp at hfall
          | some r =>
            cases r with
            | returned v =>
              by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) shape &&
                  shapeEqHOL (shapeOfHOLExact v) ret) = true
              · simp only [hsh, ↓reduceIte] at hfall ⊢
                let u := setVarHOLFinite name v { t with locals := s.locals }
                have hu : R u := hr s values b callee ret v t hc hP ha hl he (by
                  simp only [Bool.and_eq_true] at hsh
                  exact hsh.1)
                have huc : u.code = originalRuntimeCode := hmeta.trans hc
                have hnone : (evaluateHOLFiniteState u p).1 = none := hfall
                have ht := hp.run u huc hu (by rw [hnone]; simp) hnone
                exact hQ _ _ _ (fun n hm => resVarEq_lookup_ne _ _ _ _ (hn n hm)) ht
              · simp only [hsh] at hfall
                cases hfall
            | _ => simp_all

theorem Falls.store {a e : ExpHOL 64}
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      evalAt s e = some v → ∃ w : BitVec 64, v = .val (.word w))
    (hq : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (a' w : BitVec 64), P s →
      evalAt s a = some (.val (.word a')) → evalAt s e = some (.val (.word w)) →
      Q (writeWord s a'.toNat w)) : Falls P (.store a e) Q := by
  refine ⟨fun {F} s _ hP _ hfall => ?_⟩
  rw [evaluateHOLFiniteState_store] at hfall ⊢
  split
  · rename_i a' ha
    simp only [ha] at hfall
    split
    · rename_i v he
      simp only [he] at hfall
      obtain ⟨w, rfl⟩ := hv s v hP he
      simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hfall ⊢
      split
      · rename_i memory hm
        have hmem : memory = fun b => if b = a' then HolWordLab.word w else s.memory b := by
          split at hm <;> simp_all
        subst memory
        simpa only [writeWord, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hq s a' w hP ha he
      · simp_all
    · simp_all
  · simp_all

end FallRules

theorem shape_one_word {v : ValueHOL 64} (h : shapeEqHOL (shapeOfHOLExact v) .one = true) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  cases v with
  | val w => cases w with | word w => exact ⟨w, rfl⟩
  | rStruct vs => simp [shapeOfHOLExact, shapeEqHOL] at h
  | nStruct n vs => simp [shapeOfHOLExact, shapeEqHOL] at h

theorem shape_four_words {v : ValueHOL 64}
    (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one, .one]) = true) :
    ∃ a b c d : BitVec 64, v = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)] := by
  cases v with
  | val w => simp [shapeOfHOLExact, shapeEqHOL] at h
  | nStruct n vs => simp [shapeOfHOLExact, shapeEqHOL] at h
  | rStruct vs =>
    have he := (shapeEqHOL_eq_true _ _).mp h
    simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at he
    have hlen : vs.length = 4 := by
      have := congrArg List.length he
      simpa using this
    cases vs with
    | nil => simp_all
    | cons a xs =>
      cases xs with
      | nil => simp_all
      | cons b xs =>
        cases xs with
        | nil => simp_all
        | cons c xs =>
          cases xs with
          | nil => simp_all
          | cons d xs =>
            cases xs with
            | cons e xs => simp only [List.length_cons] at hlen; omega
            | nil =>
              simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
              obtain ⟨a', rfl⟩ := shape_one_word ((shapeEqHOL_eq_true _ _).mpr he.1)
              obtain ⟨b', rfl⟩ := shape_one_word ((shapeEqHOL_eq_true _ _).mpr he.2.1)
              obtain ⟨c', rfl⟩ := shape_one_word ((shapeEqHOL_eq_true _ _).mpr he.2.2.1)
              obtain ⟨d', rfl⟩ := shape_one_word ((shapeEqHOL_eq_true _ _).mpr he.2.2.2)
              exact ⟨a', b', c', d', rfl⟩

theorem eval_local_word {F : Type} {s : PanSemStateFiniteExact 64 F} {n : String}
    {v : ValueHOL 64} (hw : WordLocal s n) (h : evalAt s (.var .local (ofString n)) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat = locN s n := by
  obtain ⟨w, hw⟩ := hw
  have hv : v = .val (.word w) := by
    change s.locals.lookup (ofString n) = some v at h
    rw [hw] at h
    exact (Option.some.inj h).symm
  exact ⟨w, hv, evalAt_local s n w (by rw [← hv]; exact h)⟩

theorem cond_eq_true {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64} {k : BitVec 64}
    (h : CondTrue (.cmp .equal e (.const k)) s) : evalAt s e = some (.val (.word k)) := by
  obtain ⟨w, hw, hn⟩ := h
  obtain ⟨a, b, ha, hb, rfl⟩ := evalAt_cmp s .equal e (.const k) w hw
  cases evalAt_const s k _ hb
  have hab : a = k := by
    by_cases h : a = k
    · exact h
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h] at hn
  simpa only [hab] using ha

theorem cond_eq_false {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64} {k : BitVec 64}
    (h : CondFalse (.cmp .equal e (.const k)) s) :
    ∃ w : BitVec 64, evalAt s e = some (.val (.word w)) ∧ w ≠ k := by
  obtain ⟨a, b, ha, hb, hz⟩ := evalAt_cmp s .equal e (.const k) 0 h
  cases evalAt_const s k _ hb
  refine ⟨a, ha, ?_⟩
  intro hab
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hab] at hz

theorem cond_local_eq_true {F : Type} {s : PanSemStateFiniteExact 64 F} {n : String} {k : BitVec 64}
    (h : CondTrue (.cmp .equal (.var .local (ofString n)) (.const k)) s) : locN s n = k.toNat :=
  (evalAt_local s n k (cond_eq_true h)).symm

theorem cond_local_eq_false {F : Type} {s : PanSemStateFiniteExact 64 F} {n : String} {k : BitVec 64}
    (h : CondFalse (.cmp .equal (.var .local (ofString n)) (.const k)) s) : locN s n ≠ k.toNat := by
  obtain ⟨w, hw, hn⟩ := cond_eq_false h
  rw [← evalAt_local s n w hw]
  exact fun he => hn (BitVec.eq_of_toNat_eq he)

theorem evalAt_loadL' {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k a : BitVec 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString g), .const k])) =
      some (.val (.word a))) :
    a.toNat = memW t (locN t g + k.toNat) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hg : t.locals.lookup (ofString g) with _ | v
  · simp [hg] at h
  · rcases v with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
        have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by
          rw [BitVec.add_def]
        simp only [locN, memW, hg, hadd, h.2]
    · simp [hg, valueIsWord] at h
    · simp [hg, valueIsWord] at h

/-- A one-word load from `local + k` that succeeds yields the word `memW t (locN t g + k)`. -/
theorem evalAt_loadL {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k : BitVec 64)
    (v : ValueHOL 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString g), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t (locN t g + k.toNat) := by
  have hv : ∃ a : BitVec 64, v = .val (.word a) := by
    simp [evalAt, evalHOLExact, evalListHOLExact] at h
    rcases hg : t.locals.lookup (ofString g) with _ | w
    · simp [hg] at h
    · rcases w with x | fs | ⟨nm, fs⟩
      · cases x with
        | word x =>
          simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
          rcases hm : t.memory (x + k) with ⟨y⟩
          exact ⟨y, by rw [← h.2, hm]⟩
      · simp [hg, valueIsWord] at h
      · simp [hg, valueIsWord] at h
  obtain ⟨a, rfl⟩ := hv
  exact ⟨a, rfl, evalAt_loadL' t g k a h⟩

theorem eval_add {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ExpHOL 64}
    {x y : BitVec 64} (hx : evalAt s a = some (.val (.word x)))
    (hy : evalAt s b = some (.val (.word y))) :
    evalAt s (.op .add [a, b]) = some (.val (.word (x + y))) := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hx hy ⊢
  simp [hx, hy, valueIsWord, valueWord, wordOpHOL, wordOp]

theorem eval_add_local_const {F : Type} {s : PanSemStateFiniteExact 64 F} {n : String}
    {k : BitVec 64} (hw : WordLocal s n) {v : ValueHOL 64}
    (h : evalAt s (.op .add [.var .local (ofString n), .const k]) = some v) :
    v = .val (.word (BitVec.ofNat 64 (locN s n + k.toNat))) := by
  obtain ⟨w, hw⟩ := hw
  have he : evalAt s (.var .local (ofString n)) = some (.val (.word w)) := hw
  rw [eval_add he rfl] at h
  have hwNat := evalAt_local s n w he
  rw [← hwNat, ← BitVec.add_def]
  exact (Option.some.inj h).symm

theorem eval_rfield {F : Type} {s : PanSemStateFiniteExact 64 F} {n : String}
    {vs : List (ValueHOL 64)} (h : s.locals.lookup (ofString n) = some (.rStruct vs)) (i : Nat) :
    evalAt s (.rfield i (.var .local (ofString n))) = vs[i]? := by
  simp only [evalAt, evalHOLExact]
  rw [h]

theorem eval_rfield_set {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String)
    (vs : List (ValueHOL 64)) (i : Nat) :
    evalAt (setVarHOLFinite (ofString n) (.rStruct vs) s)
      (.rfield i (.var .local (ofString n))) = vs[i]? := by
  apply eval_rfield
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- A fall-through postcondition at a fixed state, for symbolic execution of a branch. -/
structure At {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (Q : PanSemStateFiniteExact 64 F → Prop) : Prop where
  run : (evaluateHOLFiniteState s p).1 = none → Q (evaluateHOLFiniteState s p).2

namespace At
variable {F : Type} {s : PanSemStateFiniteExact 64 F} {Q : PanSemStateFiniteExact 64 F → Prop}

theorem seq {p q : ProgHOL 64} (h : At s p (fun t => At t q Q)) : At s (.seq p q) Q := by
  refine ⟨fun he => ?_⟩
  rw [evaluateHOLFiniteState_seq_line780] at he ⊢
  cases hp : evaluateHOLFiniteState s p with
  | mk r t =>
    simp only [hp] at he ⊢
    cases r with
    | none =>
      have ht : At t q Q := by simpa only [hp] using h.run (by rw [hp])
      exact ht.run he
    | some r => cases he

theorem assign {name : MlS} {e : ExpHOL 64} {v : ValueHOL 64}
    (he : evalAt s e = some v) (h : Q (setVarHOLFinite name v s)) :
    At s (.assign .local name e) Q := by
  classical
  refine ⟨fun hr => ?_⟩
  rw [evaluateHOLFiniteState_assign] at hr ⊢
  change evalHOLExact s.toExact e = some v at he
  simp only [he] at hr ⊢
  split
  · exact h
  · simp_all

theorem skip (h : Q s) : At s .skip Q := by
  refine ⟨fun _ => ?_⟩
  simpa only [evaluateHOLFiniteState_skip] using h

theorem ite {c : ExpHOL 64} {p q : ProgHOL 64}
    (hy : CondTrue c s → At s p Q) (hn : CondFalse c s → At s q Q) : At s (.ite c p q) Q := by
  refine ⟨fun hr => ?_⟩
  rw [evaluateHOLFiniteState_ite] at hr ⊢
  split
  · rename_i w hw
    split
    · rename_i hz
      subst w
      simp only [hw] at hr
      exact (hn hw).run hr
    · rename_i hz
      simp only [hw, if_neg hz] at hr
      exact (hy ⟨w, hw, hz⟩).run hr
  · simp_all

theorem store {a e : ExpHOL 64} {addr w : BitVec 64}
    (ha : evalAt s a = some (.val (.word addr)))
    (he : evalAt s e = some (.val (.word w)))
    (h : Q (writeWord s addr.toNat w)) : At s (.store a e) Q := by
  classical
  refine ⟨fun hr => ?_⟩
  rw [evaluateHOLFiniteState_store] at hr ⊢
  change evalHOLExact s.toExact a = some (.val (.word addr)) at ha
  change evalHOLExact s.toExact e = some (.val (.word w)) at he
  simp only [ha, he, flattenHOL, panMemStoresHOL, panMemStoreHOL] at hr ⊢
  by_cases hd : s.memaddrs addr
  · simpa only [hd, ↓reduceIte, writeWord, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h
  · simp [hd] at hr

theorem dec {names : List String} {name : MlS} {shape : ShapeHOL} {e : ExpHOL 64} {p : ProgHOL 64}
    (hn : ∀ n ∈ names, ofString n ≠ name)
    (hQ : ∀ t ls, (∀ n ∈ names, ls.lookup (ofString n) = t.locals.lookup (ofString n)) →
      Q t → Q { t with locals := ls })
    (hb : ∀ v, evalAt s e = some v → At (setVarHOLFinite name v s) p Q) :
    At s (.dec name shape e p) Q := by
  refine ⟨fun hr => ?_⟩
  rw [evaluateHOLFiniteState_dec_total] at hr ⊢
  dsimp only at hr ⊢
  split
  · simp_all
  · rename_i v hv
    split
    · rename_i hshape
      have hnone : (evaluateHOLFiniteState (setVarHOLFinite name v s) p).1 = none := by
        simpa only [hv, hshape, ↓reduceIte] using hr
      exact hQ _ _ (fun n hm => resVarEq_lookup_ne _ _ _ _ (hn n hm)) ((hb v hv).run hnone)
    · simp_all

theorem decCall {names : List String} {name fname : MlS} {shape : ShapeHOL}
    {args : List (ExpHOL 64)} {p : ProgHOL 64}
    (hn : ∀ n ∈ names, ofString n ≠ name)
    (hQ : ∀ t ls, (∀ n ∈ names, ls.lookup (ofString n) = t.locals.lookup (ofString n)) →
      Q t → Q { t with locals := ls })
    (hb : ∀ values b callee ret v t,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (b, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b = (some (.returned v), t) →
      shapeEqHOL (shapeOfHOLExact v) shape = true →
      At (setVarHOLFinite name v { t with locals := s.locals }) p Q) :
    At s (.decCall name shape fname args p) Q := by
  refine ⟨fun hr => ?_⟩
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr ⊢
  simp only [evalListHOLFinite] at hr ⊢
  cases ha : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => simp [ha] at hr
  | some values =>
    simp only [ha] at hr ⊢
    cases hl : lookupCodeHOLFinite s.code.lookup fname values with
    | none => simp [hl] at hr
    | some installed =>
      obtain ⟨b, callee, ret⟩ := installed
      simp only [hl] at hr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hr
      · simp only [hz, ↓reduceIte] at hr ⊢
        cases he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b with
        | mk r t =>
          simp only [he] at hr ⊢
          cases r with
          | none => cases hr
          | some r =>
            cases r with
            | returned v =>
              by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) shape && shapeEqHOL (shapeOfHOLExact v) ret) = true
              · simp only [hsh, ↓reduceIte] at hr ⊢
                exact hQ _ _ (fun n hm => resVarEq_lookup_ne _ _ _ _ (hn n hm))
                  ((hb values b callee ret v t ha hl he (by simp only [Bool.and_eq_true] at hsh; exact hsh.1)).run hr)
              · simp [hsh] at hr
            | _ => cases hr

end At

namespace At
variable {F : Type} {s : PanSemStateFiniteExact 64 F} {Q : PanSemStateFiniteExact 64 F → Prop}

theorem assign_any {name : MlS} {e : ExpHOL 64}
    (h : ∀ v, evalAt s e = some v → Q (setVarHOLFinite name v s)) :
    At s (.assign .local name e) Q := by
  refine ⟨fun hr => ?_⟩
  rw [evaluateHOLFiniteState_assign] at hr ⊢
  split
  · simp_all
  · rename_i v he
    split
    · exact h v he
    · simp_all

theorem store_any {a e : ExpHOL 64} {addr : BitVec 64}
    (ha : evalAt s a = some (.val (.word addr)))
    (hv : ∀ v, evalAt s e = some v → ∃ w : BitVec 64, v = .val (.word w))
    (h : ∀ w, evalAt s e = some (.val (.word w)) → Q (writeWord s addr.toNat w)) :
    At s (.store a e) Q := by
  classical
  refine ⟨fun hr => ?_⟩
  rw [evaluateHOLFiniteState_store] at hr ⊢
  change evalHOLExact s.toExact a = some (.val (.word addr)) at ha
  simp only [ha] at hr ⊢
  split
  · rename_i v he
    obtain ⟨w, rfl⟩ := hv v he
    have hh := (store ha he (h w he)).run
    rw [evaluateHOLFiniteState_store] at hh
    simp only [ha, he] at hh hr ⊢
    exact hh hr
  · simp_all

theorem call0 {fname : MlS} {args : List (ExpHOL 64)}
    (hb : ∀ values b callee ret v t,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (b, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b = (some (.returned v), t) →
      Q { t with locals := s.locals }) :
    At s (.call (some (none, none)) fname args) Q := by
  refine ⟨fun hr => ?_⟩
  rw [evaluateHOLFiniteState_call] at hr ⊢
  simp only [evalListHOLFinite] at hr ⊢
  cases ha : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => simp [ha] at hr
  | some values =>
    simp only [ha] at hr ⊢
    cases hl : lookupCodeHOLFinite s.code.lookup fname values with
    | none => simp [hl] at hr
    | some installed =>
      obtain ⟨b, callee, ret⟩ := installed
      simp only [hl] at hr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hr
      · simp only [hz, ↓reduceIte] at hr ⊢
        cases he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b with
        | mk r t =>
          simp only [he] at hr ⊢
          cases r with
          | none => cases hr
          | some r =>
            cases r with
            | returned v =>
              dsimp only at hr ⊢
              split
              · exact hb values b callee ret v t ha hl he
              · simp_all
            | _ => cases hr

theorem readOnly {fname : MlS} {args : List (ExpHOL 64)} (hf : ReadOnlyFn fname)
    (hc : s.code = originalRuntimeCode) (hs : GuestInv s)
    (h : ∀ k, Q { s with clock := k }) :
    At s (.call (some (none, none)) fname args) Q := by
  apply call0
  intro values b callee ret v t _ hl hr
  have hh := FunSpec.at_lookup hf s hc values b callee ret hl
    (localsFree_guestInv s callee (s.clock - 1) hs) (by rw [hr]; simp)
  rw [hr] at hh
  have ht := hh (Or.inl ⟨v, rfl⟩)
  dsimp only at ht
  rw [ht]
  exact h t.clock

end At

/-- A declaration may establish a stronger guard for its body. -/
theorem bounded_dec_init
    {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {name : MlS} {shape : ShapeHOL} {e : ExpHOL 64} {p : ProgHOL 64} {K : Nat}
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      evalAt s e = some v → Q (setVarHOLFinite name v s))
    (hp : TerminatingProgBoundedOn Q p K) :
    TerminatingProgBoundedOn P (.dec name shape e p) K := by
  intro F s hc hP hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · rename_i v he
    revert hnt
    split <;> intro hnt
    · exact hp (setVarHOLFinite name v s) hc (hi s v hP he) hnt
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

def TopZero : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "top" = 0 ∧ WordLocal s "top"

def BothZero : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TopZero s ∧ locN s "result" = 0 ∧ WordLocal s "result"

theorem bothZero_locals : LocalsOnly ["top", "result"] BothZero := by
  intro F s ls k hl h
  refine ⟨⟨localsFree_arenaReady s ls k h.1.1, ?_, ?_⟩, ?_, ?_⟩
  · rw [locN_congr s ls k "top" (hl "top" (by simp))]; exact h.1.2.1
  · obtain ⟨w, hw⟩ := h.1.2.2
    exact ⟨w, (hl "top" (by simp)).trans hw⟩
  · rw [locN_congr s ls k "result" (hl "result" (by simp))]; exact h.2.1
  · obtain ⟨w, hw⟩ := h.2.2
    exact ⟨w, (hl "result" (by simp)).trans hw⟩

def code : ProgHOL 64 :=
  (sourceFunctionEntry Guest.Software.guestFn__decode_witness_node_body).2.2.1

def condition : ExpHOL 64 := .cmp .notEqual (.var .local (ofString "go")) (.const 0)

def body : ProgHOL 64 :=
  match code with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _
      (.dec _ _ _ (.seq (.while _ b) _))))))) => b
  | _ => .skip

def decodeBranch : ProgHOL 64 := match body with | .ite _ p _ => p | _ => .skip
def resolveBranch : ProgHOL 64 := match body with | .ite _ _ (.ite _ p _) => p | _ => .skip
def finishBranch : ProgHOL 64 :=
  match body with | .ite _ _ (.ite _ _ (.ite _ _ p)) => p | _ => .skip

theorem body_eq : body =
    .ite (.cmp .equal (.var .local (ofString "mode")) (.const 1)) decodeBranch
      (.ite (.cmp .equal (.var .local (ofString "mode")) (.const 2)) resolveBranch
        (.ite (.cmp .equal (.var .local (ofString "top")) (.const 0))
          (.assign .local (ofString "go") (.const 0)) finishBranch)) := rfl

theorem lookup : originalRuntimeCode.lookup (ofString "_decode_witness_node_body") =
    some ((sourceFunctionEntry Guest.Software.guestFn__decode_witness_node_body).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 262 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__decode_witness_node_body) rfl

theorem code_eq : code =
    .dec (ofString "top") .one (.const 0)
    (.dec (ofString "result") .one (.const 0)
    (.dec (ofString "cur_p") .one (.var .local (ofString "p"))
    (.dec (ofString "cur_n") .one (.var .local (ofString "n"))
    (.dec (ofString "mode") .one (.const 1)
    (.dec (ofString "slot") .one (.const 0)
    (.dec (ofString "go") .one (.const 1)
    (.seq (.while condition body) (.return (.var .local (ofString "result")))))))))) := rfl

def bodyCost : Nat :=
  max (K.«_decode_step» + 1)
    (max (K.«_resolve_step» + 1)
      (max 0
        (max (max (K.mpt_fail + 1) 0 + max (K.mpt_fail + 1) 0 + (K.node_new_ext + 1))
          (max 0 ((K.rlp_item + 1) + max (K.mpt_fail + 1) 0)))))

theorem budget_eq : K.«_decode_witness_node_body» = (22621787712 + 1) * (bodyCost + 1) := rfl

/-- The straight-line iteration costs only its selected callee paths. -/
theorem body_bounded
    (hd : TerminatingFunBoundedOn GuestInv (ofString "_decode_step") K.«_decode_step»)
    (hr : TerminatingFunBoundedOn GuestInv (ofString "_resolve_step") K.«_resolve_step»)
    (hf : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.mpt_fail)
    (he : TerminatingFunBoundedOn GuestInv (ofString "node_new_ext") K.node_new_ext)
    (hi : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.rlp_item) :
    TerminatingProgBoundedOn GuestInv body bodyCost := by
  unfold body code
  simp only [sourceFunctionEntry, Guest.Software.guestFn__decode_witness_node_body,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.ite_on
      (TerminatingProgBoundedOn.decCall_guestInv hd _ _ _
        (TerminatingProgBoundedOn.ite_on
          (TerminatingProgBoundedOn.seq_guestInv
            (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
            (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _)))
          (TerminatingProgBoundedOn.seq_guestInv
            (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
            (TerminatingProgBoundedOn.seq_guestInv
              (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
              (TerminatingProgBoundedOn.seq_guestInv
                (TerminatingProgBoundedOn.ite_on
                  (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                  (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _)))
                (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _)))))))
      (TerminatingProgBoundedOn.ite_on
        (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
          (TerminatingProgBoundedOn.decCall_guestInv hr _ _ _
            (TerminatingProgBoundedOn.ite_on
              (TerminatingProgBoundedOn.seq_guestInv
                (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                (TerminatingProgBoundedOn.seq_guestInv
                  (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                  (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))))
              (TerminatingProgBoundedOn.seq_guestInv
                (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                (TerminatingProgBoundedOn.seq_guestInv
                  (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                  (TerminatingProgBoundedOn.seq_guestInv
                    (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                    (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))))))))
        (TerminatingProgBoundedOn.ite_on
          (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
          (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
            (TerminatingProgBoundedOn.seq_guestInv
              (TerminatingProgBoundedOn.ite_on
                (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
              (TerminatingProgBoundedOn.ite_on
                (TerminatingProgBoundedOn.seq_guestInv
                  (TerminatingProgBoundedOn.ite_on
                    (TerminatingProgBoundedOn.call_guestInv hf _ _)
                    (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                  (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
                    (TerminatingProgBoundedOn.seq_guestInv
                      (TerminatingProgBoundedOn.ite_on
                        (TerminatingProgBoundedOn.call_guestInv hf _ _)
                        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                      (TerminatingProgBoundedOn.decCall_guestInv he _ _ _
                        (TerminatingProgBoundedOn.seq_guestInv
                          (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                          (TerminatingProgBoundedOn.seq_guestInv
                            (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                            (TerminatingProgBoundedOn.seq_guestInv
                              (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                              (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _)))))))))
                (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
                  (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
                    (TerminatingProgBoundedOn.seq_guestInv
                      (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                      (TerminatingProgBoundedOn.seq_guestInv
                        (TerminatingProgBoundedOn.ite_on
                          (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                          (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                        (TerminatingProgBoundedOn.seq_guestInv
                          (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                          (TerminatingProgBoundedOn.ite_on
                            (TerminatingProgBoundedOn.seq_guestInv
                              (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                              (TerminatingProgBoundedOn.seq_guestInv
                                (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                                (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))))
                            (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
                              (TerminatingProgBoundedOn.decCall_guestInv hi _ _ _
                                (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
                                  (TerminatingProgBoundedOn.seq_guestInv
                                    (TerminatingProgBoundedOn.ite_on
                                      (TerminatingProgBoundedOn.seq_guestInv
                                        (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                        (TerminatingProgBoundedOn.seq_guestInv
                                          (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                          (TerminatingProgBoundedOn.ite_on
                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))))
                                      (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                                    (TerminatingProgBoundedOn.seq_guestInv
                                      (TerminatingProgBoundedOn.ite_on
                                        (TerminatingProgBoundedOn.call_guestInv hf _ _)
                                        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                                      (TerminatingProgBoundedOn.seq_guestInv
                                        (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                        (TerminatingProgBoundedOn.seq_guestInv
                                          (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                          (TerminatingProgBoundedOn.seq_guestInv
                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _)))))))))))))))))))))) ?_
  simp only [Nat.add_zero, Nat.zero_add, bodyCost]
  omega

theorem body_no_continue {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s body).1 ≠ some .continue :=
  evaluate_noTopContinue body (by decide) s

/-- The sole remaining semantic obligation: a continuing iteration decreases the rank. -/
def StepSpec : Prop := ∀ r : Nat,
  Falls (fun s => HeadInv s ∧ rank s = r ∧ locN s "go" ≠ 0) body
    (fun s => HeadInv s ∧ rank s < r)

def ModePre (mode r : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => HeadInv s ∧ rank s = r ∧ locN s "go" ≠ 0 ∧ locN s "mode" = mode

def StepPost (r : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => HeadInv s ∧ rank s < r

theorem stepPost_locals (r : Nat) : LocalsOnly ["mode", "top", "result", "go"] (StepPost r) := by
  intro F s ls k hl h
  refine ⟨headInv_locals s ls k (fun n hn => hl n (by simp at hn ⊢; tauto)) h.1, ?_⟩
  obtain ⟨ps, hp⟩ := h.1.2.2.2.1
  rw [rank_locals ls k (fun n hn => hl n (by simp at hn ⊢; tauto)) hp]
  exact h.2

private abbrev localE (n : String) : ExpHOL 64 := .var .local (ofString n)
private abbrev fieldE (n : String) (i : Nat) : ExpHOL 64 := .rfield i (localE n)
private abbrev offsetE (n : String) (k : BitVec 64) : ExpHOL 64 := .op .add [localE n, .const k]

private def decodeCont : ProgHOL 64 :=
  .ite (.cmp .equal (fieldE "d" 0) (.const 0))
    (.seq (.assign .local (ofString "result") (fieldE "d" 1))
      (.assign .local (ofString "mode") (.const 0)))
    (.seq (.store (.op .add [fieldE "d" 1, .const 0]) (localE "top"))
      (.seq (.assign .local (ofString "top") (fieldE "d" 1))
        (.seq (.ite (.cmp .equal (.load .one (offsetE "top" 8)) (.const 1))
          (.assign .local (ofString "slot") (.const 1))
          (.assign .local (ofString "slot") (.const 0)))
          (.assign .local (ofString "mode") (.const 2)))))

private theorem decodeBranch_eq : decodeBranch =
    .decCall (ofString "d") (.comb [.one, .one]) (ofString "_decode_step")
      [localE "db", localE "cur_p", localE "cur_n"] decodeCont := rfl

private theorem decode_branch
    (hw : WritesWithin (fun _ => []) ["heap_ptr", "scratch_ptr"] (ofString "_decode_step"))
    (hp : PushesFrame (ofString "_decode_step")) (r : Nat) :
    Falls (ModePre 1 r) decodeBranch (StepPost r) := by
  refine ⟨fun {F} s hc hs _ => ?_⟩
  suffices h : At s decodeBranch (StepPost r) from h.run
  rw [decodeBranch_eq]
  apply At.decCall (names := ["mode", "top", "result", "go"]) (by decide)
    (fun t ls hl h => stepPost_locals r t ls t.clock hl h)
  intro values b callee ret v t _ hl hr _
  obtain ⟨hk, tag, p, hv, hz, hn⟩ := decode_returns hw hp s values b callee ret v t hc hs.1.1 hl hr
  subst v
  let u := setVarHOLFinite (ofString "d") (.rStruct [.val (.word tag), .val (.word p)])
    { t with locals := s.locals }
  have hku : KeepsScratch s u := ⟨localsFree_arenaReady t _ _ hk.1, hk.2⟩
  have hlu : ∀ n ∈ ["mode", "top", "result", "go"],
      u.locals.lookup (ofString n) = s.locals.lookup (ofString n) := by
    intro n hm
    simp at hm
    rcases hm with rfl | rfl | rfl | rfl <;>
      simp +decide [u, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have hd0 : evalAt u (fieldE "d" 0) = some (.val (.word tag)) := by
    exact eval_rfield_set _ "d" _ 0
  have hd1 : evalAt u (fieldE "d" 1) = some (.val (.word p)) := by
    exact eval_rfield_set _ "d" _ 1
  change At u decodeCont (StepPost r)
  unfold decodeCont
  apply At.ite
  · intro htag
    have ht : tag.toNat = 0 := by
      have h := cond_eq_true htag
      rw [hd0] at h
      cases h
      rfl
    apply At.seq
    apply At.assign hd1
    apply At.assign (show evalAt _ (.const 0) = _ from rfl)
    have hdone := completed_transition hs.1 hku hlu (by rw [hs.2.2.2]; decide) hs.2.2.1 p (hz ht)
    simpa only [StepPost, hs.2.1] using hdone
  · intro htag
    have ht : tag.toNat ≠ 0 := by
      obtain ⟨tag', htag', hne⟩ := cond_eq_false htag
      rw [hd0] at htag'
      cases htag'
      intro he
      exact hne (BitVec.eq_of_toNat_eq he)
    obtain ⟨hf, hframe⟩ := hn ht
    obtain ⟨top, htop⟩ := hs.1.2.2.2.2.2.1
    have etop : evalAt u (localE "top") = some (.val (.word top)) :=
      (hlu "top" (by simp)).trans htop
    have htopN := evalAt_local s "top" top (show evalAt s (localE "top") = _ from htop)
    apply At.seq
    apply At.store (show evalAt u (.op .add [fieldE "d" 1, .const 0]) =
      some (.val (.word p)) from by simpa using eval_add hd1 (show evalAt u (.const 0) = _ from rfl)) etop
    apply At.seq
    have ed1 : evalAt (writeWord u p.toNat top) (fieldE "d" 1) = some (.val (.word p)) := hd1
    apply At.assign ed1
    apply At.seq
    have hend (slot : BitVec 64) : At
        (setVarHOLFinite (ofString "slot") (.val (.word slot))
          (setVarHOLFinite (ofString "top") (.val (.word p)) (writeWord u p.toNat top)))
        (.assign .local (ofString "mode") (.const 2)) (StepPost r) := by
      apply At.assign rfl
      have hdone := pushed_transition hs.1 hku hlu hs.2.2.2 hs.2.2.1 p top slot htopN hframe hf
      simpa only [StepPost, hs.2.1, pushState] using hdone
    apply At.ite
    · intro _; exact At.assign rfl (hend 1)
    · intro _; exact At.assign rfl (hend 0)

private theorem head_aux_write {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : HeadInv s) (ht : locN s "top" ≠ 0) (off : Nat) (ho : off = 40 ∨ off = 80)
    (w : BitVec 64) :
    HeadInv (writeWord s (locN s "top" + off) w) ∧
      rank (writeWord s (locN s "top" + off) w) = rank s := by
  obtain ⟨ps, hps⟩ := hs.2.2.2.1
  cases ps with
  | nil => exact (ht hps).elim
  | cons p ps =>
    have he : locN s "top" = p := hps.1
    have hps' : Stack s (globN s "scratch_ptr") p (p :: ps) := by simpa only [he] using hps
    obtain ⟨hp, hc⟩ := hps'.aux_write w ho
    let t := writeWord s (p + off) w
    have hp' : Stack t (globN t "scratch_ptr") (locN t "top") (p :: ps) := by
      change Stack t (globN s "scratch_ptr") (locN s "top") (p :: ps)
      rw [he]; exact hp
    rw [he]
    refine ⟨⟨writeWord_arena hs.1 _ _, hs.2.1, hs.2.2.1, ⟨_, hp'⟩, hs.2.2.2.2⟩, ?_⟩
    change rank t = rank s
    simp only [rank, stackCredit_eq hp', stackCredit_eq hps]
    change (if locN s "go" = 0 then 0 else globN s "scratch_ptr" + credits t (p :: ps) + locN s "mode" + 1) = _
    rw [hc]

private theorem rank_set_aux {F : Type} {s : PanSemStateFiniteExact 64 F} (hs : HeadInv s)
    (name : MlS) (v : ValueHOL 64)
    (hn : ∀ n ∈ ["mode", "top", "go"], ofString n ≠ name) :
    rank (setVarHOLFinite name v s) = rank s := by
  obtain ⟨ps, hps⟩ := hs.2.2.2.1
  apply rank_locals _ _ _ hps
  intro n hm
  simp only [HolFiniteMapExact.update, FUPDATE]
  simp [Ne.symm (hn n hm)]

private theorem complete_head {F : Type} {s : PanSemStateFiniteExact 64 F} {r : Nat}
    (hs : HeadInv s) (hle : rank s ≤ r) (hm : 0 < locN s "mode") (hg : locN s "go" ≠ 0)
    (w : BitVec 64) (hw : ResultOK s w.toNat) :
    StepPost r (setVarHOLFinite (ofString "mode") (.val (.word 0))
      (setVarHOLFinite (ofString "result") (.val (.word w)) s)) := by
  have hr := hs.set_result w hw
  refine ⟨hr.set_mode 0 (by decide) (by intro h; cases h), ?_⟩
  have hg' : locN (setVarHOLFinite (ofString "result") (.val (.word w)) s) "go" ≠ 0 := by
    rw [locN_setVar_ne _ "go" _ _ (by decide)]; exact hg
  have hm' : (0 : BitVec 64).toNat < locN (setVarHOLFinite (ofString "result") (.val (.word w)) s) "mode" := by
    rw [locN_setVar_ne _ "mode" _ _ (by decide)]; exact hm
  have hlt := rank_set_mode_lt hr hg' 0 hm'
  rw [rank_set_result hs w] at hlt
  exact hlt.trans_le hle

private theorem modePre_locals (m r : Nat) : LocalsOnly ["mode", "top", "result", "go"] (ModePre m r) := by
  intro F s ls k hl hs
  refine ⟨headInv_locals s ls k (fun n hn => hl n (by simp at hn ⊢; tauto)) hs.1, ?_, ?_, ?_⟩
  · rw [rank_locals ls k (fun n hn => hl n (by simp at hn ⊢; tauto)) hs.1.2.2.2.1.choose_spec]
    exact hs.2.1
  · rw [locN_congr s ls k "go" (hl "go" (by simp))]; exact hs.2.2.1
  · rw [locN_congr s ls k "mode" (hl "mode" (by simp))]; exact hs.2.2.2

private def resolveArgs : List (ExpHOL 64) :=
  [localE "db",
    .load .one (.op .add [localE "arr", .panop .mul [localE "slot", .const 16]]),
    .load .one (.op .add [localE "arr", .panop .mul [localE "slot", .const 16], .const 8])]

private def resolveCont : ProgHOL 64 :=
  .ite (.cmp .equal (fieldE "r" 0) (.const 0))
    (.seq (.store (offsetE "top" 80) (.const 0))
      (.seq (.assign .local (ofString "result") (fieldE "r" 1))
        (.assign .local (ofString "mode") (.const 0))))
    (.seq (.store (offsetE "top" 80) (fieldE "r" 3))
      (.seq (.assign .local (ofString "cur_p") (fieldE "r" 1))
        (.seq (.assign .local (ofString "cur_n") (fieldE "r" 2))
          (.assign .local (ofString "mode") (.const 1)))))

private theorem resolveBranch_eq : resolveBranch =
    .dec (ofString "arr") .one (.load .one (offsetE "top" 24))
      (.decCall (ofString "r") (.comb [.one, .one, .one, .one]) (ofString "_resolve_step")
        resolveArgs resolveCont) := rfl

private theorem resolve_branch
    (hw : WritesWithin (fun _ => []) ["heap_ptr", "scratch_ptr"] (ofString "_resolve_step"))
    (hp : ResolvesNode (ofString "_resolve_step")) (r : Nat) :
    Falls (ModePre 2 r) resolveBranch (StepPost r) := by
  refine ⟨fun {F} s hc hs _ => ?_⟩
  suffices h : At s resolveBranch (StepPost r) from h.run
  rw [resolveBranch_eq]
  apply At.dec (names := ["mode", "top", "result", "go"]) (by decide)
    (fun t ls hl h => stepPost_locals r t ls t.clock hl h)
  intro arr _
  let s' := setVarHOLFinite (ofString "arr") arr s
  have hs' : ModePre 2 r s' := LocalsOnly.setVar (modePre_locals 2 r) (by decide) _ s hs
  apply At.decCall (names := ["mode", "top", "result", "go"]) (by decide)
    (fun t ls hl h => stepPost_locals r t ls t.clock hl h)
  intro values b callee ret v t _ hl hr _
  obtain ⟨hk, tag, p, n, hash, hv, hz⟩ := resolve_returns hw hp s' values b callee ret v t hc hs'.1.1 hl hr
  subst v
  let u := setVarHOLFinite (ofString "r")
    (.rStruct [.val (.word tag), .val (.word p), .val (.word n), .val (.word hash)])
    { t with locals := s'.locals }
  have hku : KeepsScratch s' u := ⟨localsFree_arenaReady t _ _ hk.1, hk.2⟩
  have hlu : ∀ k ∈ ["mode", "top", "result", "go"],
      u.locals.lookup (ofString k) = s'.locals.lookup (ofString k) := by
    intro k hm
    simp at hm
    rcases hm with rfl | rfl | rfl | rfl <;>
      simp +decide [u, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have hu : HeadInv u := hku.head hs'.1 (fun k hk => hlu k (by simp at hk ⊢; tauto))
  have hur : rank u ≤ r := by
    have h := hku.rank_le hs'.1.2.2.2.1.choose_spec
      (fun k hk => hlu k (by simp at hk ⊢; tauto))
    rwa [hs'.2.1] at h
  have hum : locN u "mode" = 2 := (locN_lookup_eq (hlu "mode" (by simp))).trans hs'.2.2.2
  have hug : locN u "go" ≠ 0 := by rw [locN_lookup_eq (hlu "go" (by simp))]; exact hs'.2.2.1
  have hut : locN u "top" ≠ 0 := hu.2.2.2.2.1 hum
  obtain ⟨top, htop⟩ := hu.2.2.2.2.2.1
  have htopNat : top.toNat = locN u "top" := evalAt_local u "top" top htop
  have ea : evalAt u (offsetE "top" 80) = some (.val (.word (top + 80))) := eval_add htop rfl
  have eaNat : (top + 80).toNat = locN u "top" + 80 := by
    obtain ⟨ps, hps⟩ := hu.2.2.2.1
    cases ps with
    | nil => exact (hut hps).elim
    | cons q qs =>
      have hbound := hps.2.2.2.1.2.1
      have he := hps.1
      rw [BitVec.toNat_add, htopNat]
      apply Nat.mod_eq_of_lt
      change locN u "top" + 80 < 2 ^ 64
      unfold scratchEnd at hbound
      omega
  have ef (i : Nat) : evalAt u (fieldE "r" i) =
      ([.val (.word tag), .val (.word p), .val (.word n), .val (.word hash)] : List (ValueHOL 64))[i]? :=
    eval_rfield_set _ "r" _ i
  have aux (w : BitVec 64) : HeadInv (writeWord u (top + 80).toNat w) ∧
      rank (writeWord u (top + 80).toNat w) = rank u := by
    rw [eaNat]; exact head_aux_write hu hut 80 (Or.inr rfl) w
  change At u resolveCont (StepPost r)
  unfold resolveCont
  apply At.ite
  · intro htag
    have ht : tag.toNat = 0 := by
      have h := cond_eq_true htag
      rw [ef 0] at h
      cases h
      rfl
    apply At.seq
    apply At.store ea rfl
    apply At.seq
    apply At.assign (show evalAt (writeWord u (top + 80).toNat 0) (fieldE "r" 1) =
      some (.val (.word p)) from ef 1)
    apply At.assign rfl
    have hi := (aux 0).1
    have hle : rank (writeWord u (top + 80).toNat 0) ≤ r := by rw [(aux 0).2]; exact hur
    exact complete_head hi hle (by change 0 < locN u "mode"; rw [hum]; decide) hug p (hz ht)
  · intro _
    apply At.seq
    apply At.store ea (ef 3)
    apply At.seq
    apply At.assign (show evalAt (writeWord u (top + 80).toNat hash) (fieldE "r" 1) =
      some (.val (.word p)) from ef 1)
    let u0 := writeWord u (top + 80).toNat hash
    let u1 := setVarHOLFinite (ofString "cur_p") (.val (.word p)) u0
    have hi0 : HeadInv u0 := (aux hash).1
    have hi1 : HeadInv u1 := headInv_locals.setVar (by decide) _ u0 hi0
    apply At.seq
    have en : evalAt u1 (fieldE "r" 2) = some (.val (.word n)) := by
      simp +decide [u1, u0, u, evalAt, evalHOLExact,
        setVarHOLFinite, writeWord, HolFiniteMapExact.update, FUPDATE]
    apply At.assign en
    let u2 := setVarHOLFinite (ofString "cur_n") (.val (.word n)) u1
    have hi2 : HeadInv u2 := headInv_locals.setVar (by decide) _ u1 hi1
    apply At.assign rfl
    have em : locN u2 "mode" = 2 := by
      dsimp only [u2, u1]
      rw [locN_setVar_ne _ "mode" _ _ (by decide), locN_setVar_ne _ "mode" _ _ (by decide)]
      exact hum
    have eg : locN u2 "go" ≠ 0 := by
      dsimp only [u2, u1]
      rw [locN_setVar_ne _ "go" _ _ (by decide), locN_setVar_ne _ "go" _ _ (by decide)]
      exact hug
    have erk : rank u2 ≤ r := by
      rw [rank_set_aux hi1 _ _ (by decide), rank_set_aux hi0 _ _ (by decide)]
      exact ((aux hash).2.le.trans hur)
    refine ⟨hi2.set_mode 1 (by decide) (by intro h; cases h), ?_⟩
    exact (rank_set_mode_lt hi2 eg 1 (by rw [em]; decide)).trans_le erk

private def FinishInv (r : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => HeadInv s ∧ rank s ≤ r ∧ locN s "mode" = 0 ∧ locN s "top" ≠ 0 ∧ locN s "go" ≠ 0

private theorem finishInv_locals (r : Nat) : LocalsOnly ["mode", "top", "result", "go"] (FinishInv r) := by
  intro F s ls k hl hs
  refine ⟨headInv_locals s ls k (fun n hn => hl n (by simp at hn ⊢; tauto)) hs.1, ?_, ?_, ?_, ?_⟩
  · rw [rank_locals ls k (fun n hn => hl n (by simp at hn ⊢; tauto)) hs.1.2.2.2.1.choose_spec]
    exact hs.2.1
  · rw [locN_congr s ls k "mode" (hl "mode" (by simp))]; exact hs.2.2.1
  · rw [locN_congr s ls k "top" (hl "top" (by simp))]; exact hs.2.2.2.1
  · rw [locN_congr s ls k "go" (hl "go" (by simp))]; exact hs.2.2.2.2

private theorem finish_keep {F : Type} {s t : PanSemStateFiniteExact 64 F} {r : Nat}
    (hs : FinishInv r s) (hk : KeepsScratch s t)
    (hl : ∀ n ∈ ["mode", "top", "result", "go"],
      t.locals.lookup (ofString n) = s.locals.lookup (ofString n)) : FinishInv r t := by
  refine ⟨hk.head hs.1 (fun n hn => hl n (by simp at hn ⊢; tauto)), ?_, ?_, ?_, ?_⟩
  · exact (hk.rank_le hs.1.2.2.2.1.choose_spec
      (fun n hn => hl n (by simp at hn ⊢; tauto))).trans hs.2.1
  · rw [locN_lookup_eq (hl "mode" (by simp))]; exact hs.2.2.1
  · rw [locN_lookup_eq (hl "top" (by simp))]; exact hs.2.2.2.1
  · rw [locN_lookup_eq (hl "go" (by simp))]; exact hs.2.2.2.2

private theorem heap_write_keeps {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : ArenaReady s) {a : Nat} (ha : a < heapLimit) (w : BitVec 64) :
    KeepsScratch s (writeWord s a w) := by
  refine ⟨writeWord_arena hs _ _, ⟨Nat.le_refl _, Nat.le_refl _⟩, ?_⟩
  intro b hb hbe
  have hlo : scratchStart ≤ globN s "scratch_ptr" := hs.2.2.2.1.trans hs.2.2.2.2.1
  have ha64 : a < 2 ^ 64 := by unfold heapLimit scratchStart at ha; omega
  have hb64 : b < 2 ^ 64 := by unfold scratchEnd at hbe; omega
  rw [memW_writeWord s w ha64 hb64, if_neg (by unfold heapLimit at ha; omega)]

private theorem finish_heap_write {F : Type} {s : PanSemStateFiniteExact 64 F} {r a : Nat}
    (hs : FinishInv r s) (ha : a < heapLimit) (w : BitVec 64) : FinishInv r (writeWord s a w) :=
  finish_keep hs (heap_write_keeps hs.1.1 ha w) (fun _ _ => rfl)

private theorem finish_aux_write {F : Type} {s : PanSemStateFiniteExact 64 F} {r : Nat}
    (hs : FinishInv r s) {off : Nat} (ho : off = 40 ∨ off = 80) (w : BitVec 64) :
    FinishInv r (writeWord s (locN s "top" + off) w) := by
  have h := head_aux_write hs.1 hs.2.2.2.1 off ho w
  exact ⟨h.1, h.2.le.trans hs.2.1, hs.2.2⟩

private theorem head_stack {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : HeadInv s) (ht : locN s "top" ≠ 0) :
    ∃ ps, Stack s (globN s "scratch_ptr") (locN s "top") (locN s "top" :: ps) := by
  obtain ⟨ps, hps⟩ := hs.2.2.2.1
  cases ps with
  | nil => exact (ht hps).elim
  | cons p ps =>
    refine ⟨ps, ?_⟩
    simpa only [hps.1] using hps

private theorem top_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : HeadInv s) (ht : locN s "top" ≠ 0) : locN s "top" + 88 ≤ scratchEnd := by
  obtain ⟨ps, hps⟩ := head_stack hs ht
  exact hps.2.2.2.1.2.1

private theorem top_offset_eval {F : Type} {s : PanSemStateFiniteExact 64 F} {r : Nat}
    (hs : FinishInv r s) (k : BitVec 64) (hk : k.toNat < 88) :
    evalAt s (offsetE "top" k) = some (.val (.word (BitVec.ofNat 64 (locN s "top" + k.toNat)))) ∧
      (BitVec.ofNat 64 (locN s "top" + k.toNat)).toNat = locN s "top" + k.toNat := by
  obtain ⟨top, ht⟩ := hs.1.2.2.2.2.2.1
  have hn := evalAt_local s "top" top ht
  have hb := top_bound hs.1 hs.2.2.2.1
  refine ⟨?_, ?_⟩
  · have h := eval_add (show evalAt s (localE "top") = _ from ht) (show evalAt s (.const k) = _ from rfl)
    rw [BitVec.add_def, hn] at h
    exact h
  · apply Nat.mod_eq_of_lt
    unfold scratchEnd at hb
    omega

private theorem heap_offset_eval {F : Type} {s : PanSemStateFiniteExact 64 F} {name : String}
    {p k : BitVec 64} {n : Nat} (ha : ArenaOK s)
    (hl : s.locals.lookup (ofString name) = some (.val (.word p)))
    (hp : HeapBlock s p.toNat n) (hk : k.toNat < n) :
    evalAt s (offsetE name k) = some (.val (.word (p + k))) ∧
      (p + k).toNat < heapLimit := by
  refine ⟨eval_add hl rfl, ?_⟩
  have hb := hp.2.trans ha.2.1
  have h64 : p.toNat + k.toNat < 2 ^ 64 := by unfold heapLimit scratchStart at hb; omega
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h64]
  omega

private theorem finish_pop {F : Type} {s : PanSemStateFiniteExact 64 F} {r : Nat}
    (hs : FinishInv r s) (top result : BitVec 64)
    (htop : top.toNat = memW s (locN s "top")) (hresult : ResultOK s result.toNat) :
    StepPost r (popState s top result) := by
  obtain ⟨ps, hps⟩ := head_stack hs.1 hs.2.2.2.1
  have htail : Stack s (globN s "scratch_ptr") top.toNat ps := by
    rw [htop]
    exact hps.2.2.2.2.lower (by have h := hps.2.1; omega)
  have h := popped_transition hs.1.1 (Nat.le_refl _) hps hs.2.2.1 hs.2.2.1
    hs.2.2.2.2 top result htail (Nat.le_refl _) hresult
  exact ⟨h.1, h.2.trans_le hs.2.1⟩

private def cachePop (name : String) : ProgHOL 64 :=
  .seq (.store (offsetE name 8) (.load .one (offsetE "top" 48)))
    (.seq (.store (offsetE name 16) (.load .one (offsetE "top" 56)))
      (.seq (.assign .local (ofString "top") (.load .one (offsetE "top" 0)))
        (.assign .local (ofString "result") (localE name))))

private theorem cachePop_run {F : Type} (s : PanSemStateFiniteExact 64 F) {r : Nat}
    (hs : FinishInv r s) (name : String) (hne : ofString name ≠ ofString "top")
    (p : BitVec 64) {n : Nat} (hn : 32 ≤ n)
    (hl : s.locals.lookup (ofString name) = some (.val (.word p))) (hp : HeapBlock s p.toNat n) :
    At s (cachePop name) (StepPost r) := by
  unfold cachePop
  apply At.seq
  obtain ⟨ha8, hb8⟩ := heap_offset_eval hs.1.1.2 hl hp (show (8 : BitVec 64).toNat < n by change 8 < n; omega)
  apply At.store_any ha8
  · intro v he
    obtain ⟨w, hw, _⟩ := evalAt_loadL s "top" 48 v he
    exact ⟨w, hw⟩
  intro w48 _
  let s1 := writeWord s (p + 8).toNat w48
  have hs1 : FinishInv r s1 := finish_heap_write hs hb8 w48
  apply At.seq
  obtain ⟨ha16, hb16⟩ := heap_offset_eval hs1.1.1.2 (show s1.locals.lookup (ofString name) = _ from hl)
    (show HeapBlock s1 p.toNat n from hp) (show (16 : BitVec 64).toNat < n by change 16 < n; omega)
  apply At.store_any ha16
  · intro v he
    obtain ⟨w, hw, _⟩ := evalAt_loadL s1 "top" 56 v he
    exact ⟨w, hw⟩
  intro w56 _
  let s2 := writeWord s1 (p + 16).toNat w56
  have hs2 : FinishInv r s2 := finish_heap_write hs1 hb16 w56
  apply At.seq
  apply At.assign_any
  intro v he
  obtain ⟨next, rfl, hnext⟩ := evalAt_loadL s2 "top" 0 v he
  have ep : evalAt (setVarHOLFinite (ofString "top") (.val (.word next)) s2) (localE name) =
      some (.val (.word p)) := by
    have hl2 : s2.locals.lookup (ofString name) = some (.val (.word p)) := hl
    change (s2.locals.update (ofString "top", .val (.word next))).lookup (ofString name) = _
    simpa [HolFiniteMapExact.update, FUPDATE, Ne.symm hne] using hl2
  apply At.assign ep
  apply finish_pop hs2 next p
  · change next.toNat = memW s2 (locN s2 "top" + 0) at hnext
    simpa only [Nat.add_zero] using hnext
  · exact Or.inr ⟨hp.1, by have h := hp.2; change p.toNat + 32 ≤ globN s "heap_ptr"; omega⟩

private def extensionCode : ProgHOL 64 :=
  .seq (.ite (.cmp .equal (localE "result") (.const 0))
    (.call (some (none, none)) (ofString "mpt_fail") [.const 8]) .skip)
    (.dec (ofString "ck") .one (.load .one (offsetE "result" 0))
      (.seq (.ite (.op .and [
          .cmp .notEqual (.const 0) (.cmp .notEqual (localE "ck") (.const 3)),
          .cmp .notEqual (.const 0) (.cmp .notEqual (localE "ck") (.const 0))])
        (.call (some (none, none)) (ofString "mpt_fail") [.const 8]) .skip)
        (.decCall (ofString "ex") .one (ofString "node_new_ext")
          [.load .one (offsetE "top" 64), .load .one (offsetE "top" 72), localE "result"]
          (cachePop "ex"))))

private def extensionCall : ProgHOL 64 :=
  .decCall (ofString "ex") .one (ofString "node_new_ext")
    [.load .one (offsetE "top" 64), .load .one (offsetE "top" 72), localE "result"] (cachePop "ex")

private theorem extension_call
    (hw : WritesWithin (fun _ => []) ["heap_ptr"] (ofString "node_new_ext"))
    (hp : Returns ArenaReady (fun s t p => FreshBlock s t p 56) (ofString "node_new_ext"))
    {F : Type} (s : PanSemStateFiniteExact 64 F) {r : Nat} (hc : s.code = originalRuntimeCode)
    (hs : FinishInv r s) : At s extensionCall (StepPost r) := by
  unfold extensionCall
  apply At.decCall (names := ["mode", "top", "result", "go"]) (by decide)
    (fun t ls hl h => stepPost_locals r t ls t.clock hl h)
  intro values b callee ret v t _ hl hr _
  obtain ⟨hk, p, rfl, hblock⟩ := extension_returns hw hp s values b callee ret v t hc hs.1.1 hl hr
  let u := setVarHOLFinite (ofString "ex") (.val (.word p)) { t with locals := s.locals }
  have hku : KeepsScratch s u := ⟨localsFree_arenaReady t _ _ hk.1, hk.2⟩
  have hlu : ∀ k ∈ ["mode", "top", "result", "go"],
      u.locals.lookup (ofString k) = s.locals.lookup (ofString k) := by
    intro k hm
    simp at hm
    rcases hm with rfl | rfl | rfl | rfl <;>
      simp +decide [u, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  apply cachePop_run u (finish_keep hs hku hlu) "ex" (by decide) p (n := 56) (by decide)
  · simp [u, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · exact hblock

private theorem ite_readOnly {F : Type} (s : PanSemStateFiniteExact 64 F)
    {Q : PanSemStateFiniteExact 64 F → Prop} (hf : ReadOnlyFn (ofString "mpt_fail"))
    (hc : s.code = originalRuntimeCode) (hs : GuestInv s)
    (c : ExpHOL 64) (args : List (ExpHOL 64)) (h : ∀ k, Q { s with clock := k }) :
    At s (.ite c (.call (some (none, none)) (ofString "mpt_fail") args) .skip) Q := by
  apply At.ite
  · intro _; exact At.readOnly hf hc hs h
  · intro _; exact At.skip (h s.clock)

private theorem extension_branch
    (hf : ReadOnlyFn (ofString "mpt_fail"))
    (hw : WritesWithin (fun _ => []) ["heap_ptr"] (ofString "node_new_ext"))
    (hp : Returns ArenaReady (fun s t p => FreshBlock s t p 56) (ofString "node_new_ext"))
    {F : Type} (s : PanSemStateFiniteExact 64 F) {r : Nat} (hc : s.code = originalRuntimeCode)
    (hs : FinishInv r s) : At s extensionCode (StepPost r) := by
  unfold extensionCode
  apply At.seq
  apply ite_readOnly s hf hc hs.1.1.1
  intro k
  let s0 := { s with clock := k }
  have hs0 : FinishInv r s0 := finishInv_locals r s s.locals k (fun _ _ => rfl) hs
  apply At.dec (names := ["mode", "top", "result", "go"]) (by decide)
    (fun t ls hl h => stepPost_locals r t ls t.clock hl h)
  intro ck _
  let s1 := setVarHOLFinite (ofString "ck") ck s0
  have hs1 : FinishInv r s1 := LocalsOnly.setVar (finishInv_locals r) (by decide) _ s0 hs0
  apply At.seq
  apply ite_readOnly s1 hf hc hs1.1.1.1
  intro k'
  exact extension_call hw hp { s1 with clock := k' } hc
    (finishInv_locals r s1 s1.locals k' (fun _ _ => rfl) hs1)

private def valueAfter : ProgHOL 64 :=
  .seq (.ite (.cmp .lower (localE "occ") (.const 2))
    (.call (some (none, none)) (ofString "mpt_fail") [.const 9]) .skip) (cachePop "br")

private theorem value_after (hf : ReadOnlyFn (ofString "mpt_fail"))
    {F : Type} (s : PanSemStateFiniteExact 64 F) {r : Nat} (hc : s.code = originalRuntimeCode)
    (hs : FinishInv r s) (br : BitVec 64)
    (hl : s.locals.lookup (ofString "br") = some (.val (.word br)))
    (hp : HeapBlock s br.toNat 176) : At s valueAfter (StepPost r) := by
  unfold valueAfter
  apply At.seq
  apply ite_readOnly s hf hc hs.1.1.1
  intro k
  exact cachePop_run { s with clock := k }
    (finishInv_locals r s s.locals k (fun _ _ => rfl) hs) "br" (by decide) br (by decide) hl hp

private def valueStores : ProgHOL 64 :=
  .ite (.cmp .equal (fieldE "bv" 0) (.const 0))
    (.seq (.store (offsetE "br" 160) (fieldE "bv" 1))
      (.seq (.store (offsetE "br" 168) (fieldE "bv" 2))
        (.ite (.cmp .notEqual (fieldE "bv" 2) (.const 0))
          (.assign .local (ofString "occ") (.op .add [localE "occ", .const 1])) .skip))) .skip

private theorem value_stores (hf : ReadOnlyFn (ofString "mpt_fail"))
    {F : Type} (s : PanSemStateFiniteExact 64 F) {r : Nat} (hc : s.code = originalRuntimeCode)
    (hs : FinishInv r s) (br a b c d : BitVec 64)
    (hl : s.locals.lookup (ofString "br") = some (.val (.word br)))
    (hp : HeapBlock s br.toNat 176)
    (hv : s.locals.lookup (ofString "bv") = some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)])) :
    At s (.seq valueStores valueAfter) (StepPost r) := by
  apply At.seq
  unfold valueStores
  apply At.ite
  · intro _
    apply At.seq
    obtain ⟨ea160, eb160⟩ := heap_offset_eval hs.1.1.2 hl hp (show (160 : BitVec 64).toNat < 176 by decide)
    apply At.store ea160 (show evalAt s (fieldE "bv" 1) = some (.val (.word b)) from eval_rfield hv 1)
    let s1 := writeWord s (br + 160).toNat b
    have hs1 : FinishInv r s1 := finish_heap_write hs eb160 b
    apply At.seq
    obtain ⟨ea168, eb168⟩ := heap_offset_eval hs1.1.1.2 (show s1.locals.lookup (ofString "br") = _ from hl)
      (show HeapBlock s1 br.toNat 176 from hp) (show (168 : BitVec 64).toNat < 176 by decide)
    apply At.store ea168 (show evalAt s1 (fieldE "bv" 2) = some (.val (.word c)) from eval_rfield hv 2)
    let s2 := writeWord s1 (br + 168).toNat c
    have hs2 : FinishInv r s2 := finish_heap_write hs1 eb168 c
    apply At.ite
    · intro _
      apply At.assign_any
      intro v _
      let s3 := setVarHOLFinite (ofString "occ") v s2
      have hs3 : FinishInv r s3 := LocalsOnly.setVar (finishInv_locals r) (by decide) _ s2 hs2
      apply value_after hf s3 hc hs3 br
      · have hl2 : s2.locals.lookup (ofString "br") = some (.val (.word br)) := hl
        simpa +decide [s3, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using hl2
      · exact hp
    · intro _
      exact At.skip (value_after hf s2 hc hs2 br hl hp)
  · intro _
    exact At.skip (value_after hf s hc hs br hl hp)

private def branchValueArgs : List (ExpHOL 64) :=
  [.load .one (.op .add [localE "arr2", .panop .mul [.const 16, .const 16]]),
    .load .one (.op .add [localE "arr2", .panop .mul [.const 16, .const 16], .const 8])]

private def branchValue : ProgHOL 64 :=
  .dec (ofString "arr2") .one (.load .one (offsetE "top" 24))
    (.decCall (ofString "bv") (.comb [.one, .one, .one, .one]) (ofString "rlp_item") branchValueArgs
      (.dec (ofString "occ") .one (.load .one (offsetE "top" 40)) (.seq valueStores valueAfter)))

private theorem branch_value
    (hf : ReadOnlyFn (ofString "mpt_fail"))
    (hw : WritesWithin (fun _ => []) ["scratch_ptr"] (ofString "rlp_item"))
    {F : Type} (s : PanSemStateFiniteExact 64 F) {r : Nat} (hc : s.code = originalRuntimeCode)
    (hs : FinishInv r s) (br : BitVec 64)
    (hl : s.locals.lookup (ofString "br") = some (.val (.word br)))
    (hp : HeapBlock s br.toNat 176) : At s branchValue (StepPost r) := by
  unfold branchValue
  apply At.dec (names := ["mode", "top", "result", "go"]) (by decide)
    (fun t ls hl h => stepPost_locals r t ls t.clock hl h)
  intro arr _
  let s0 := setVarHOLFinite (ofString "arr2") arr s
  have hs0 : FinishInv r s0 := LocalsOnly.setVar (finishInv_locals r) (by decide) _ s hs
  have hbr0 : s0.locals.lookup (ofString "br") = some (.val (.word br)) := by
    simpa +decide [s0, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using hl
  apply At.decCall (names := ["mode", "top", "result", "go"]) (by decide)
    (fun t ls hl h => stepPost_locals r t ls t.clock hl h)
  intro values b callee ret v t _ hlook hrun hshape
  have hk := writes_return hw s0 values b callee ret v t hc hs0.1.1 hlook hrun
  obtain ⟨a, b', c, d, rfl⟩ := shape_four_words hshape
  let u := setVarHOLFinite (ofString "bv")
    (.rStruct [.val (.word a), .val (.word b'), .val (.word c), .val (.word d)])
    { t with locals := s0.locals }
  have hku : KeepsScratch s0 u := ⟨localsFree_arenaReady t _ _ hk.1, hk.2⟩
  have hlu : ∀ k ∈ ["mode", "top", "result", "go"],
      u.locals.lookup (ofString k) = s0.locals.lookup (ofString k) := by
    intro k hm
    simp at hm
    rcases hm with rfl | rfl | rfl | rfl <;>
      simp +decide [u, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have hu : FinishInv r u := finish_keep hs0 hku hlu
  have hup : HeapBlock u br.toNat 176 := hp.grow hk.2.1.1
  have hubr : u.locals.lookup (ofString "br") = some (.val (.word br)) := by
    simpa +decide [u, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using hbr0
  have huv : u.locals.lookup (ofString "bv") =
      some (.rStruct [.val (.word a), .val (.word b'), .val (.word c), .val (.word d)]) := by
    simp [u, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have huc : u.code = originalRuntimeCode := by
    have hm := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s0 callee) b).1
    rw [hrun] at hm
    exact hm.trans hc
  apply At.dec (names := ["mode", "top", "result", "go"]) (by decide)
    (fun t ls hl h => stepPost_locals r t ls t.clock hl h)
  intro occ _
  let u0 := setVarHOLFinite (ofString "occ") occ u
  have hu0 : FinishInv r u0 := LocalsOnly.setVar (finishInv_locals r) (by decide) _ u hu
  apply value_stores hf u0 huc hu0 br a b' c d
  · simpa +decide [u0, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using hubr
  · exact hup
  · simpa +decide [u0, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using huv

private theorem finish_advance {F : Type} (s : PanSemStateFiniteExact 64 F) {r : Nat}
    (hs : FinishInv r s) (w : BitVec 64)
    (htag : memW s (locN s "top" + 8) = 2)
    (hw : w.toNat = memW s (locN s "top" + 32) + 1) (hi : w.toNat < 16) :
    StepPost r (nextState (writeWord s (locN s "top" + 32) w) w) := by
  obtain ⟨ps, hps⟩ := head_stack hs.1 hs.2.2.2.1
  obtain ⟨hpt, hcredits, httag, hti⟩ := hps.counter_write htag w hi
  let t := writeWord s (locN s "top" + 32) w
  have ht : HeadInv t := ⟨writeWord_arena hs.1.1 _ _, hs.1.2.1, hs.1.2.2.1,
    ⟨_, hpt⟩, hs.1.2.2.2.2⟩
  have h := advanced_transition (s := s) (t := t) ht (Nat.le_refl _) hps hpt hs.2.2.1 hs.2.2.2.2
    htag httag (by omega) (hti.trans hw) hcredits w
  exact ⟨h.1, h.2.trans_le hs.2.1⟩

private theorem cond_less_small {F : Type} {s : PanSemStateFiniteExact 64 F}
    {w : BitVec 64} (hl : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hb : w.toNat ≤ 16) (h : CondTrue (.cmp .less (localE "i") (.const 16)) s) :
    w.toNat < 16 := by
  obtain ⟨v, hv, hn⟩ := h
  obtain ⟨a, b, ha, hb', rfl⟩ := evalAt_cmp s .less (localE "i") (.const 16) v hv
  have ea : a = w := by rw [show evalAt s (localE "i") = _ from hl] at ha; simpa using ha.symm
  subst a
  cases evalAt_const s 16 _ hb'
  have hi : w.toNat < 2 ^ (64 - 1) := by omega
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess] at hn
  omega

private def branchNext : ProgHOL 64 :=
  .seq (.store (offsetE "top" 32) (localE "i"))
    (.seq (.assign .local (ofString "slot") (localE "i"))
      (.assign .local (ofString "mode") (.const 2)))

private def branchIncrement : ProgHOL 64 :=
  .seq (.assign .local (ofString "i") (.op .add [localE "i", .const 1]))
    (.ite (.cmp .less (localE "i") (.const 16)) branchNext branchValue)

private theorem branch_increment
    (hf : ReadOnlyFn (ofString "mpt_fail"))
    (hw : WritesWithin (fun _ => []) ["scratch_ptr"] (ofString "rlp_item"))
    {F : Type} (s : PanSemStateFiniteExact 64 F) {r : Nat} (hc : s.code = originalRuntimeCode)
    (hs : FinishInv r s) (br i : BitVec 64)
    (hl : s.locals.lookup (ofString "br") = some (.val (.word br)))
    (hp : HeapBlock s br.toNat 176)
    (hli : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hi : i.toNat < 16) (hcounter : memW s (locN s "top" + 32) = i.toNat)
    (htag : memW s (locN s "top" + 8) = 2) : At s branchIncrement (StepPost r) := by
  unfold branchIncrement
  apply At.seq
  apply At.assign (eval_add (show evalAt s (localE "i") = _ from hli) rfl)
  let u := setVarHOLFinite (ofString "i") (.val (.word (i + 1))) s
  have hu : FinishInv r u := LocalsOnly.setVar (finishInv_locals r) (by decide) _ s hs
  have hut : locN u "top" = locN s "top" := locN_setVar_ne s "top" _ _ (by decide)
  have hui : u.locals.lookup (ofString "i") = some (.val (.word (i + 1))) := by
    simp [u, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have hin : (i + 1).toNat = i.toNat + 1 := by
    rw [BitVec.toNat_add]
    change (i.toNat + 1) % 2 ^ 64 = i.toNat + 1
    exact Nat.mod_eq_of_lt (by omega)
  apply At.ite
  · intro htest
    have hi' : (i + 1).toNat < 16 := cond_less_small hui (by omega) htest
    unfold branchNext
    apply At.seq
    obtain ⟨e32, b32⟩ := top_offset_eval hu 32 (by decide)
    apply At.store e32 (show evalAt u (localE "i") = _ from hui)
    change At (writeWord u ((BitVec.ofNat 64 (locN u "top" + 32)).toNat) (i + 1)) _ _
    change (BitVec.ofNat 64 (locN u "top" + 32)).toNat = locN u "top" + 32 at b32
    rw [b32]
    apply At.seq
    apply At.assign (show evalAt (writeWord u (locN u "top" + 32) (i + 1)) (localE "i") = _ from hui)
    apply At.assign (show evalAt _ (.const 2) = some (.val (.word 2)) from rfl)
    apply finish_advance u hu (i + 1)
    · change memW s (locN u "top" + 8) = 2
      rw [hut]; exact htag
    · change (i + 1).toNat = memW s (locN u "top" + 32) + 1
      rw [hut, hcounter, hin]
    · exact hi'
  · intro _
    apply branch_value hf hw u hc hu br
    · simpa +decide [u, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using hl
    · exact hp

private theorem eval_op_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (op : BinOp) (args : List (ExpHOL 64)) (v : ValueHOL 64)
    (h : evalAt s (.op op args) = some v) : ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [evalAt, evalHOLExact] at h
  split at h
  · split at h
    · obtain ⟨w, _, hv⟩ := Option.map_eq_some_iff.mp h
      exact ⟨w, hv.symm⟩
    · cases h
  · cases h

private def branchOccupancy : ProgHOL 64 :=
  .seq (.ite (.cmp .notEqual (localE "result") (.const 0))
      (.store (offsetE "top" 40) (.op .add [.load .one (offsetE "top" 40), .const 1])) .skip)
    branchIncrement

private theorem branch_occupancy
    (hf : ReadOnlyFn (ofString "mpt_fail"))
    (hw : WritesWithin (fun _ => []) ["scratch_ptr"] (ofString "rlp_item"))
    {F : Type} (s : PanSemStateFiniteExact 64 F) {r : Nat} (hc : s.code = originalRuntimeCode)
    (hs : FinishInv r s) (br i : BitVec 64)
    (hl : s.locals.lookup (ofString "br") = some (.val (.word br)))
    (hp : HeapBlock s br.toNat 176)
    (hli : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hi : i.toNat < 16) (hcounter : memW s (locN s "top" + 32) = i.toNat)
    (htag : memW s (locN s "top" + 8) = 2) : At s branchOccupancy (StepPost r) := by
  unfold branchOccupancy
  apply At.seq
  apply At.ite
  · intro _
    obtain ⟨e40, b40⟩ := top_offset_eval hs 40 (by decide)
    apply At.store_any e40 (eval_op_word s .add _)
    intro w _
    change At (writeWord s ((BitVec.ofNat 64 (locN s "top" + 40)).toNat) w) _ _
    change (BitVec.ofNat 64 (locN s "top" + 40)).toNat = locN s "top" + 40 at b40
    rw [b40]
    let u := writeWord s (locN s "top" + 40) w
    have hu : FinishInv r u := finish_aux_write hs (Or.inl rfl) w
    apply branch_increment hf hw u hc hu br i hl hp hli hi
    · have hb := top_bound hs.1 hs.2.2.2.1
      change memW (writeWord s (locN s "top" + 40) w) (locN s "top" + 32) = i.toNat
      rw [memW_writeWord s w (by unfold scratchEnd at hb; omega)
        (by unfold scratchEnd at hb; omega), if_neg (by omega)]
      exact hcounter
    · have hb := top_bound hs.1 hs.2.2.2.1
      change memW (writeWord s (locN s "top" + 40) w) (locN s "top" + 8) = 2
      rw [memW_writeWord s w (by unfold scratchEnd at hb; omega)
        (by unfold scratchEnd at hb; omega), if_neg (by omega)]
      exact htag
  · intro _
    exact At.skip (branch_increment hf hw s hc hs br i hl hp hli hi hcounter htag)

private def branchSlotAddress : ExpHOL 64 :=
  .op .add [localE "br", .const 32, .panop .mul [localE "i", .const 8]]

private theorem branch_slot_address {F : Type} (s : PanSemStateFiniteExact 64 F)
    (br i : BitVec 64)
    (hl : s.locals.lookup (ofString "br") = some (.val (.word br)))
    (hli : s.locals.lookup (ofString "i") = some (.val (.word i))) :
    evalAt s branchSlotAddress = some (.val (.word (br + 32 + i * 8))) := by
  simp [branchSlotAddress, localE, evalAt, evalHOLExact, evalListHOLExact,
    hl, hli, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp, BitVec.add_assoc]

private theorem scratch_field_keeps {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {r : Nat} (hs : FinishInv r s) (hk : KeepsScratch s t) (k : Nat) (hb : k < 88) :
    memW t (locN s "top" + k) = memW s (locN s "top" + k) := by
  obtain ⟨ps, hps⟩ := head_stack hs.1 hs.2.2.2.1
  exact hk.2.2 _ (by have h := hps.2.1; omega) (by have h := top_bound hs.1 hs.2.2.2.1; omega)

private def branchSlots : ProgHOL 64 :=
  .seq (.store branchSlotAddress (localE "result")) branchOccupancy

private theorem branch_slots
    (hf : ReadOnlyFn (ofString "mpt_fail"))
    (hw : WritesWithin (fun _ => []) ["scratch_ptr"] (ofString "rlp_item"))
    {F : Type} (s : PanSemStateFiniteExact 64 F) {r : Nat} (hc : s.code = originalRuntimeCode)
    (hs : FinishInv r s) (br i : BitVec 64)
    (hl : s.locals.lookup (ofString "br") = some (.val (.word br)))
    (hp : HeapBlock s br.toNat 176)
    (hli : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hi : i.toNat < 16) (hcounter : memW s (locN s "top" + 32) = i.toNat)
    (htag : memW s (locN s "top" + 8) = 2) : At s branchSlots (StepPost r) := by
  unfold branchSlots
  apply At.seq
  obtain ⟨result, hr⟩ := hs.1.2.2.2.2.2.2
  apply At.store (branch_slot_address s br i hl hli) (show evalAt s (localE "result") = _ from hr)
  have hbound : (br + 32 + i * 8).toNat < heapLimit := by
    have hheap := hp.2.trans hs.1.1.2.2.1
    have hmul : (i * 8).toNat = i.toNat * 8 := by
      rw [BitVec.toNat_mul]
      change (i.toNat * 8) % 2 ^ 64 = i.toNat * 8
      exact Nat.mod_eq_of_lt (by omega)
    have h32 : (br + 32).toNat = br.toNat + 32 := by
      rw [BitVec.toNat_add]
      change (br.toNat + 32) % 2 ^ 64 = br.toNat + 32
      apply Nat.mod_eq_of_lt
      unfold heapLimit scratchStart at hheap
      omega
    rw [BitVec.toNat_add, h32, hmul, Nat.mod_eq_of_lt (by unfold heapLimit scratchStart at hheap; omega)]
    omega
  let u := writeWord s (br + 32 + i * 8).toNat result
  have hk : KeepsScratch s u := heap_write_keeps hs.1.1 hbound result
  apply branch_occupancy hf hw u hc (finish_heap_write hs hbound result) br i hl hp hli hi
  · exact (scratch_field_keeps hs hk 32 (by decide)).trans hcounter
  · exact (scratch_field_keeps hs hk 8 (by decide)).trans htag

private def branchCode : ProgHOL 64 :=
  .dec (ofString "br") .one (.load .one (offsetE "top" 16))
    (.dec (ofString "i") .one (.load .one (offsetE "top" 32)) branchSlots)

private theorem branch_code
    (hf : ReadOnlyFn (ofString "mpt_fail"))
    (hw : WritesWithin (fun _ => []) ["scratch_ptr"] (ofString "rlp_item"))
    {F : Type} (s : PanSemStateFiniteExact 64 F) {r : Nat} (hc : s.code = originalRuntimeCode)
    (hs : FinishInv r s) (htag : memW s (locN s "top" + 8) = 2) :
    At s branchCode (StepPost r) := by
  obtain ⟨ps, hps⟩ := head_stack hs.1 hs.2.2.2.1
  have hframe := hps.2.2.2.1
  have hb : memW s (locN s "top" + 32) < 16 ∧ HeapBlock s (memW s (locN s "top" + 16)) 176 := by
    rcases hframe.2.2 with h1 | h2
    · omega
    · exact h2.2
  unfold branchCode
  apply At.dec (names := ["mode", "top", "result", "go"]) (by decide)
    (fun t ls hl h => stepPost_locals r t ls t.clock hl h)
  intro v he
  obtain ⟨br, rfl, hbr⟩ := evalAt_loadL s "top" 16 v he
  change br.toNat = memW s (locN s "top" + 16) at hbr
  let u := setVarHOLFinite (ofString "br") (.val (.word br)) s
  have hu : FinishInv r u := LocalsOnly.setVar (finishInv_locals r) (by decide) _ s hs
  have hut : locN u "top" = locN s "top" := locN_setVar_ne s "top" _ _ (by decide)
  have hup : HeapBlock u br.toNat 176 := by rw [hbr]; exact hb.2
  have hul : u.locals.lookup (ofString "br") = some (.val (.word br)) := by
    simp [u, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  apply At.dec (names := ["mode", "top", "result", "go"]) (by decide)
    (fun t ls hl h => stepPost_locals r t ls t.clock hl h)
  intro v he
  obtain ⟨i, rfl, hi⟩ := evalAt_loadL u "top" 32 v he
  change i.toNat = memW s (locN u "top" + 32) at hi
  rw [hut] at hi
  let t := setVarHOLFinite (ofString "i") (.val (.word i)) u
  have ht : FinishInv r t := LocalsOnly.setVar (finishInv_locals r) (by decide) _ u hu
  have htt : locN t "top" = locN s "top" := (locN_setVar_ne u "top" _ _ (by decide)).trans hut
  apply branch_slots hf hw t hc ht br i
  · simpa +decide [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using hul
  · exact hup
  · simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · omega
  · change memW s (locN t "top" + 32) = i.toNat
    rw [htt]; exact hi.symm
  · change memW s (locN t "top" + 8) = 2
    rw [htt]; exact htag

private def finishTag : ProgHOL 64 :=
  .ite (.cmp .equal (.load .one (offsetE "top" 8)) (.const 1)) extensionCode branchCode

private theorem finish_tag
    (hf : ReadOnlyFn (ofString "mpt_fail"))
    (hw : WritesWithin (fun _ => []) ["heap_ptr"] (ofString "node_new_ext"))
    (hp : Returns ArenaReady (fun s t p => FreshBlock s t p 56) (ofString "node_new_ext"))
    (hi : WritesWithin (fun _ => []) ["scratch_ptr"] (ofString "rlp_item"))
    {F : Type} (s : PanSemStateFiniteExact 64 F) {r : Nat} (hc : s.code = originalRuntimeCode)
    (hs : FinishInv r s) : At s finishTag (StepPost r) := by
  unfold finishTag
  apply At.ite
  · intro _; exact extension_branch hf hw hp s hc hs
  · intro htest
    obtain ⟨w, he, hw⟩ := cond_eq_false htest
    have hn := evalAt_loadL' s "top" 8 w he
    have hne : memW s (locN s "top" + 8) ≠ 1 := by
      intro h
      apply hw
      apply BitVec.eq_of_toNat_eq
      exact hn.trans h
    obtain ⟨ps, hps⟩ := head_stack hs.1 hs.2.2.2.1
    have htag : memW s (locN s "top" + 8) = 2 := by
      rcases hps.2.2.2.1.2.2 with h1 | h2
      · exact (hne h1).elim
      · exact h2.1
    exact branch_code hf hi s hc hs htag

private def finishHash : ProgHOL 64 :=
  .seq (.ite (.op .and [
      .cmp .notEqual (.const 0) (.cmp .notEqual (localE "hash") (.const 0)),
      .cmp .notEqual (.const 0) (.cmp .notEqual (localE "result") (.const 0))])
    (.store (offsetE "result" 24) (localE "hash")) .skip) finishTag

private theorem finish_hash
    (hf : ReadOnlyFn (ofString "mpt_fail"))
    (hw : WritesWithin (fun _ => []) ["heap_ptr"] (ofString "node_new_ext"))
    (hp : Returns ArenaReady (fun s t p => FreshBlock s t p 56) (ofString "node_new_ext"))
    (hi : WritesWithin (fun _ => []) ["scratch_ptr"] (ofString "rlp_item"))
    {F : Type} (s : PanSemStateFiniteExact 64 F) {r : Nat} (hc : s.code = originalRuntimeCode)
    (hs : FinishInv r s) (hash : BitVec 64)
    (hl : s.locals.lookup (ofString "hash") = some (.val (.word hash))) :
    At s finishHash (StepPost r) := by
  unfold finishHash
  apply At.seq
  apply At.ite
  · intro _
    obtain ⟨result, hr⟩ := hs.1.2.2.2.2.2.2
    have hn : result.toNat = locN s "result" := evalAt_local s "result" result hr
    have hb : (result + 24).toNat < heapLimit := by
      rcases hs.1.2.2.1 with hz | hh
      · have hz' : result = 0 := BitVec.eq_of_toNat_eq (hn.trans hz)
        rw [hz']; decide
      · have hh' : HeapBlock s result.toNat 32 := by rw [hn]; exact hh
        exact (heap_offset_eval hs.1.1.2 hr hh' (show (24 : BitVec 64).toNat < 32 by decide)).2
    apply At.store (eval_add (show evalAt s (localE "result") = _ from hr) rfl)
      (show evalAt s (localE "hash") = _ from hl)
    exact finish_tag hf hw hp hi _ hc (finish_heap_write hs hb hash)
  · intro _; exact At.skip (finish_tag hf hw hp hi s hc hs)

private theorem finishBranch_eq : finishBranch =
    .dec (ofString "hash") .one (.load .one (offsetE "top" 80)) finishHash := rfl

private theorem finish_branch
    (hf : ReadOnlyFn (ofString "mpt_fail"))
    (hw : WritesWithin (fun _ => []) ["heap_ptr"] (ofString "node_new_ext"))
    (hp : Returns ArenaReady (fun s t p => FreshBlock s t p 56) (ofString "node_new_ext"))
    (hi : WritesWithin (fun _ => []) ["scratch_ptr"] (ofString "rlp_item")) (r : Nat) :
    Falls (fun s => ModePre 0 r s ∧ locN s "top" ≠ 0) finishBranch (StepPost r) := by
  refine ⟨fun {F} s hc hs _ => ?_⟩
  suffices h : At s finishBranch (StepPost r) from h.run
  have hs' : FinishInv r s := ⟨hs.1.1, hs.1.2.1.le, hs.1.2.2.2, hs.2, hs.1.2.2.1⟩
  rw [finishBranch_eq]
  apply At.dec (names := ["mode", "top", "result", "go"]) (by decide)
    (fun t ls hl h => stepPost_locals r t ls t.clock hl h)
  intro v he
  obtain ⟨hash, rfl, _⟩ := evalAt_loadL s "top" 80 v he
  apply finish_hash hf hw hp hi (setVarHOLFinite (ofString "hash") (.val (.word hash)) s) hc
    (LocalsOnly.setVar (finishInv_locals r) (by decide) _ s hs') hash
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- The outer tests and the empty-stack exit reduce the iteration to three branches. -/
theorem step_of_branches
    (hd : ∀ r, Falls (ModePre 1 r) decodeBranch (StepPost r))
    (hr : ∀ r, Falls (ModePre 2 r) resolveBranch (StepPost r))
    (hf : ∀ r, Falls (fun s => ModePre 0 r s ∧ locN s "top" ≠ 0) finishBranch (StepPost r)) :
    StepSpec := by
  intro r
  rw [body_eq]
  apply Falls.ite
  · apply (hd r).mono _ (fun _ h => h)
    intro F s h
    exact ⟨h.1.1, h.1.2.1, h.1.2.2, cond_local_eq_true h.2⟩
  · apply Falls.ite
    · apply (hr r).mono _ (fun _ h => h)
      intro F s h
      exact ⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2, cond_local_eq_true h.2⟩
    · apply Falls.ite
      · apply Falls.assign
        intro F s v h he
        cases evalAt_const s 0 v he
        have hs := h.1.1.1.1
        have hg := h.1.1.1.2.2
        have hq := h.1.1.1.2.1
        refine ⟨headInv_locals.setVar (by decide) _ s hs, ?_⟩
        rw [← hq]
        exact rank_exit hg (locN_setVar_same s "go" 0)
      · apply (hf r).mono _ (fun _ h => h)
        intro F s h
        have hm := h.1.1.1.1.2.1
        have hn1 := cond_local_eq_false h.1.1.2
        have hn2 := cond_local_eq_false h.1.2
        have htop := cond_local_eq_false h.2
        refine ⟨⟨h.1.1.1.1, h.1.1.1.2.1, h.1.1.1.2.2, ?_⟩, htop⟩
        change locN s "mode" ≠ 1 at hn1
        change locN s "mode" ≠ 2 at hn2
        omega

theorem bounded_of_step
    (hd : TerminatingFunBoundedOn GuestInv (ofString "_decode_step") K.«_decode_step»)
    (hr : TerminatingFunBoundedOn GuestInv (ofString "_resolve_step") K.«_resolve_step»)
    (hf : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.mpt_fail)
    (he : TerminatingFunBoundedOn GuestInv (ofString "node_new_ext") K.node_new_ext)
    (hi : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.rlp_item)
    (hstep : StepSpec) :
    TerminatingFunBoundedOn ArenaReady (ofString "_decode_witness_node_body")
      K.«_decode_witness_node_body» := by
  have hloop : TerminatingProgBoundedOn HeadInv (.while condition body)
      ((22621787712 + 1) * (bodyCost + 1)) := by
    refine TerminatingProgBoundedOn.while_rank_active rank
      (fun s hs => headInv_locals.decClock s hs)
      (fun s hc hs => body_bounded hd hr hf he hi s hc hs.1.1.1)
      (fun _ _ hs _ => rank_bound hs) ?_
    intro F s hc hs ha hflow
    have hgo : locN s "go" ≠ 0 := condTrue_local_ne0 ha
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none :=
      hflow.elim id (fun h => (body_no_continue _ h).elim)
    obtain ⟨ps, hps⟩ := hs.2.2.2.1
    have hrc : rank (decClockHOLFinite s) = rank s :=
      rank_locals s.locals (s.clock - 1) (fun _ _ => rfl) hps
    exact (hstep (rank s)).run (decClockHOLFinite s) hc
      ⟨headInv_locals.decClock s hs, hrc, hgo⟩ (by rw [hnone]; simp) hnone
  have htail : TerminatingProgBoundedOn HeadInv
      (.seq (.while condition body) (.return (.var .local (ofString "result"))))
      K.«_decode_witness_node_body» := by
    have h : TerminatingProgBoundedOn HeadInv
        (.seq (.while condition body) (.return (.var .local (ofString "result"))))
        (((22621787712 + 1) * (bodyCost + 1)) + 0) :=
      TerminatingProgBoundedOn.seq_guestInv_after hloop (fun _ hs => hs.1.1)
      (TerminatingProgBoundedOn.of_clock (fun s => clock_return s (.var .local (ofString "result"))))
    intro F s hc hs
    simpa only [Nat.add_zero, budget_eq] using h s hc hs
  refine ⟨_, code, _, lookup, ?_⟩
  rw [code_eq]
  apply bounded_dec_init (Q := TopZero)
  · intro F s v ha hv
    cases evalAt_const s 0 v hv
    exact ⟨localsFree_arenaReady s _ _ ha, locN_setVar_same s "top" 0, wordLocal_set s "top" 0⟩
  apply bounded_dec_init (Q := BothZero)
  · intro F s v hs hv
    cases evalAt_const s 0 v hv
    refine ⟨⟨localsFree_arenaReady s _ _ hs.1, ?_, hs.2.2.set_ne _ _ (by decide)⟩,
      locN_setVar_same s "result" 0, wordLocal_set s "result" 0⟩
    rw [locN_setVar_ne s "top" (ofString "result") _ (by decide)]
    exact hs.2.1
  apply TerminatingProgBoundedOn.dec_onLocals bothZero_locals _ (by decide)
  apply TerminatingProgBoundedOn.dec_onLocals bothZero_locals _ (by decide)
  apply bounded_dec_init (Q := HeadInv)
  · intro F s v hs hv
    cases evalAt_const s 1 v hv
    have hmode := locN_setVar_same s "mode" 1
    have htop : locN (setVarHOLFinite (ofString "mode") (.val (.word 1)) s) "top" = 0 := by
      rw [locN_setVar_ne s "top" (ofString "mode") _ (by decide)]; exact hs.1.2.1
    have hresult : locN (setVarHOLFinite (ofString "mode") (.val (.word 1)) s) "result" = 0 := by
      rw [locN_setVar_ne s "result" (ofString "mode") _ (by decide)]; exact hs.2.1
    refine ⟨localsFree_arenaReady s _ _ hs.1.1, ?_, Or.inl hresult, ⟨[], htop⟩, ?_,
      hs.1.2.2.set_ne _ _ (by decide), hs.2.2.set_ne _ _ (by decide)⟩
    · rw [hmode]; decide
    · rw [hmode]; intro h; cases h
  apply TerminatingProgBoundedOn.dec_onLocals headInv_locals _ (by decide)
  apply TerminatingProgBoundedOn.dec_onLocals headInv_locals _ (by decide)
  exact htail

/-- The decoder bound from precisely its five callee bounds and eight contracts. -/
theorem bounded
    (hd : TerminatingFunBoundedOn GuestInv (ofString "_decode_step") K.«_decode_step»)
    (hr : TerminatingFunBoundedOn GuestInv (ofString "_resolve_step") K.«_resolve_step»)
    (hf : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.mpt_fail)
    (he : TerminatingFunBoundedOn GuestInv (ofString "node_new_ext") K.node_new_ext)
    (hi : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.rlp_item)
    (hwd : WritesWithin (fun _ => []) ["heap_ptr", "scratch_ptr"] (ofString "_decode_step"))
    (hpd : PushesFrame (ofString "_decode_step"))
    (hwr : WritesWithin (fun _ => []) ["heap_ptr", "scratch_ptr"] (ofString "_resolve_step"))
    (hpr : ResolvesNode (ofString "_resolve_step"))
    (hrf : ReadOnlyFn (ofString "mpt_fail"))
    (hwe : WritesWithin (fun _ => []) ["heap_ptr"] (ofString "node_new_ext"))
    (hpe : Returns ArenaReady (fun s t p => FreshBlock s t p 56) (ofString "node_new_ext"))
    (hwi : WritesWithin (fun _ => []) ["scratch_ptr"] (ofString "rlp_item")) :
    TerminatingFunBoundedOn ArenaReady (ofString "_decode_witness_node_body")
      K.«_decode_witness_node_body» :=
  bounded_of_step hd hr hf he hi (step_of_branches
    (decode_branch hwd hpd) (resolve_branch hwr hpr) (finish_branch hrf hwe hpe hwi))

end InitECandidate.Solver.Wave8GuestInv.DecodeWitness
