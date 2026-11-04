import InitECandidate.Solver.Wave8Stage.WordCostCertificates
import InitECandidate.Solver.Wave8Stage.WordCostCompilerControl

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordCostPreAllocationPreservation
open Flapjack WordCostEffects WordCostCertificates WordCostControl
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend

/-! ## Algebraic and Subeffects monotonicity for `Effects` combinators -/

theorem covers_join_iff (a b : Budget) (cost : Int) :
    Covers (join a b) cost ↔ Covers a cost ∨ Covers b cost := by
  cases a <;> cases b <;> simp [join, Covers] <;> omega

theorem covers_add_iff (a b : Budget) (cost : Int) :
    Covers (add a b) cost ↔ ∃ ca cb, Covers a ca ∧ Covers b cb ∧ cost ≤ ca + cb := by
  cases a with
  | none => simp [add, Covers]
  | some va =>
    cases b with
    | none => simp [add, Covers]
    | some vb =>
      simp only [add, covers_some]
      constructor
      · intro h
        exact ⟨va, vb, Int.le_refl _, Int.le_refl _, h⟩
      · rintro ⟨ca, cb, ha, hb, h⟩
        omega

theorem subeffects_refl (e : Effects) : Subeffects e e :=
  fun _ _ h => h

theorem subeffects_trans {a b c : Effects} (h1 : Subeffects a b) (h2 : Subeffects b c) :
    Subeffects a c :=
  fun exit cost h => h2 exit cost (h1 exit cost h)

theorem subeffects_bot (e : Effects) : Subeffects (fun _ => none) e :=
  fun _ _ h => (covers_none _ h).elim

theorem subeffects_merge_left (a b : Effects) : Subeffects a (merge a b) :=
  fun exit cost h => covers_join_left _ _ cost h

theorem subeffects_merge_right (a b : Effects) : Subeffects b (merge a b) :=
  fun exit cost h => covers_join_right _ _ cost h

theorem subeffects_merge {a1 a2 b1 b2 : Effects}
    (ha : Subeffects a1 a2) (hb : Subeffects b1 b2) :
    Subeffects (merge a1 b1) (merge a2 b2) := by
  intro exit cost h
  rw [merge, covers_join_iff] at h ⊢
  rcases h with h | h
  · exact Or.inl (ha exit cost h)
  · exact Or.inr (hb exit cost h)

theorem subeffects_seq {a1 a2 b1 b2 : Effects}
    (ha : Subeffects a1 a2) (hb : Subeffects b1 b2) :
    Subeffects (WordCostEffects.seq a1 b1) (WordCostEffects.seq a2 b2) := by
  intro exit cost h
  rw [WordCostEffects.seq, covers_join_iff] at h ⊢
  rcases h with h | h
  · left
    by_cases hf : exit = .fall
    · simp [hf] at h
    · simp only [hf, if_false] at h ⊢
      exact ha exit cost h
  · right
    rw [covers_add_iff] at h ⊢
    obtain ⟨ca, cb, hca, hcb, hle⟩ := h
    exact ⟨ca, cb, ha .fall ca hca, hb exit cb hcb, hle⟩

theorem seq_atom_fall_zero_left (e : Effects) :
    Subeffects (WordCostEffects.seq (atom .fall 0) e) e := by
  intro exit cost h
  rw [WordCostEffects.seq, covers_join_iff] at h
  rcases h with h | h
  · by_cases hf : exit = .fall
    · simp [hf] at h
    · simp [atom, hf] at h
  · rw [covers_add_iff] at h
    obtain ⟨ca, cb, hca, hcb, hle⟩ := h
    simp only [atom, if_true, covers_some] at hca
    exact covers_mono hcb (by omega)

theorem seq_atom_fall_zero_left_rev (e : Effects) :
    Subeffects e (WordCostEffects.seq (atom .fall 0) e) := by
  intro exit cost h
  rw [WordCostEffects.seq, covers_join_iff]
  right
  rw [covers_add_iff]
  exact ⟨0, cost, by simp [atom], h, by omega⟩

theorem seq_atom_fall_zero_right (e : Effects) :
    Subeffects (WordCostEffects.seq e (atom .fall 0)) e := by
  intro exit cost h
  rw [WordCostEffects.seq, covers_join_iff] at h
  rcases h with h | h
  · by_cases hf : exit = .fall
    · simp [hf] at h
    · simp only [hf, if_false] at h
      exact h
  · rw [covers_add_iff] at h
    obtain ⟨ca, cb, hca, hcb, hle⟩ := h
    by_cases hf : exit = .fall
    · subst hf
      simp only [atom, if_true, covers_some] at hcb
      exact covers_mono hca (by omega)
    · simp [atom, hf] at hcb

theorem seq_atom_fall_zero_right_rev (e : Effects) :
    Subeffects e (WordCostEffects.seq e (atom .fall 0)) := by
  intro exit cost h
  rw [WordCostEffects.seq, covers_join_iff]
  by_cases hf : exit = .fall
  · subst hf
    right
    rw [covers_add_iff]
    exact ⟨cost, 0, h, by simp [atom], by omega⟩
  · left
    simp only [hf, if_false]
    exact h

theorem seq_assoc_sub (a b c : Effects) :
    Subeffects (WordCostEffects.seq (WordCostEffects.seq a b) c)
      (WordCostEffects.seq a (WordCostEffects.seq b c)) := by
  intro exit cost h
  rw [WordCostEffects.seq, covers_join_iff] at h ⊢
  rcases h with h | h
  · by_cases hf : exit = .fall
    · simp [hf] at h
    · simp only [hf, if_false] at h ⊢
      rw [WordCostEffects.seq, covers_join_iff] at h
      rcases h with h | h
      · simp only [hf, if_false] at h
        exact Or.inl h
      · right
        rw [covers_add_iff] at h ⊢
        obtain ⟨ca, cb, hca, hcb, hle⟩ := h
        refine ⟨ca, cb, hca, ?_, hle⟩
        rw [WordCostEffects.seq, covers_join_iff]
        left
        simp [hf, hcb]
  · rw [covers_add_iff] at h
    obtain ⟨cab, cc, hcab, hcc, hle⟩ := h
    rw [WordCostEffects.seq, covers_join_iff] at hcab
    rcases hcab with hcab | hcab
    · simp at hcab
    · rw [covers_add_iff] at hcab
      obtain ⟨ca, cb, hca, hcb, hle2⟩ := hcab
      right
      rw [covers_add_iff]
      refine ⟨ca, cb + cc, hca, ?_, by omega⟩
      rw [WordCostEffects.seq, covers_join_iff]
      right
      rw [covers_add_iff]
      exact ⟨cb, cc, hcb, hcc, Int.le_refl _⟩

theorem seq_assoc_sub_rev (a b c : Effects) :
    Subeffects (WordCostEffects.seq a (WordCostEffects.seq b c))
      (WordCostEffects.seq (WordCostEffects.seq a b) c) := by
  intro exit cost h
  rw [WordCostEffects.seq, covers_join_iff] at h ⊢
  rcases h with h | h
  · by_cases hf : exit = .fall
    · simp [hf] at h
    · simp only [hf, if_false] at h ⊢
      left
      rw [WordCostEffects.seq, covers_join_iff]
      left
      simp [hf, h]
  · rw [covers_add_iff] at h
    obtain ⟨ca, cbc, hca, hcbc, hle⟩ := h
    rw [WordCostEffects.seq, covers_join_iff] at hcbc
    rcases hcbc with hcbc | hcbc
    · by_cases hf : exit = .fall
      · simp [hf] at hcbc
      · simp only [hf, if_false] at hcbc
        left
        simp only [hf, if_false]
        rw [WordCostEffects.seq, covers_join_iff]
        right
        rw [covers_add_iff]
        exact ⟨ca, cbc, hca, hcbc, hle⟩
    · rw [covers_add_iff] at hcbc
      obtain ⟨cb, cc, hcb, hcc, hle2⟩ := hcbc
      right
      rw [covers_add_iff]
      refine ⟨ca + cb, cc, ?_, hcc, by omega⟩
      rw [WordCostEffects.seq, covers_join_iff]
      right
      rw [covers_add_iff]
      exact ⟨ca, cb, hca, hcb, Int.le_refl _⟩

theorem seq_no_fall {a b : Effects} (hfall : a .fall = none) :
    Subeffects a (WordCostEffects.seq a b) := by
  intro exit cost h
  rw [WordCostEffects.seq, covers_join_iff]
  by_cases hf : exit = .fall
  · subst hf; rw [hfall] at h; exact (covers_none _ h).elim
  · left; simp [hf, h]

theorem seq_no_fall_drop {a b : Effects} (hfall : a .fall = none) :
    Subeffects (WordCostEffects.seq a b) a := by
  intro exit cost h
  rw [WordCostEffects.seq, covers_join_iff] at h
  rcases h with h | h
  · by_cases hf : exit = .fall
    · simp [hf] at h
    · simp only [hf, if_false] at h; exact h
  · rw [covers_add_iff] at h
    obtain ⟨ca, _, hca, _, _⟩ := h
    rw [hfall] at hca
    exact (covers_none _ hca).elim

theorem seq_merge_distrib_right (a1 a2 b : Effects) :
    Subeffects (merge (WordCostEffects.seq a1 b) (WordCostEffects.seq a2 b))
      (WordCostEffects.seq (merge a1 a2) b) := by
  intro exit cost h
  rw [merge, covers_join_iff] at h
  rcases h with h | h
  · exact subeffects_seq (subeffects_merge_left a1 a2) (subeffects_refl b) exit cost h
  · exact subeffects_seq (subeffects_merge_right a1 a2) (subeffects_refl b) exit cost h

theorem push_out_if_left_sub {a b : Effects} (hfall : a .fall = none) :
    Subeffects (WordCostEffects.seq (merge a (atom .fall 0)) b) (merge a b) := by
  intro exit cost h
  rw [WordCostEffects.seq, covers_join_iff] at h
  rw [merge, covers_join_iff]
  rcases h with h | h
  · by_cases hf : exit = .fall
    · simp [hf] at h
    · simp only [hf, if_false, merge, covers_join_iff] at h
      rcases h with h | h
      · exact Or.inl h
      · simp [atom, hf] at h
  · rw [covers_add_iff] at h
    obtain ⟨ca, cb, hca, hcb, hle⟩ := h
    rw [merge, covers_join_iff] at hca
    rcases hca with hca | hca
    · rw [hfall] at hca; exact (covers_none _ hca).elim
    · simp only [atom, if_true, covers_some] at hca
      exact Or.inr (covers_mono hcb (by omega))

theorem push_out_if_right_sub {a b : Effects} (hfall : b .fall = none) :
    Subeffects (WordCostEffects.seq (merge (atom .fall 0) b) a) (merge a b) := by
  intro exit cost h
  rw [WordCostEffects.seq, covers_join_iff] at h
  rw [merge, covers_join_iff]
  rcases h with h | h
  · by_cases hf : exit = .fall
    · simp [hf] at h
    · simp only [hf, if_false, merge, covers_join_iff] at h
      rcases h with h | h
      · simp [atom, hf] at h
      · exact Or.inr h
  · rw [covers_add_iff] at h
    obtain ⟨ca, cb, hca, hcb, hle⟩ := h
    rw [merge, covers_join_iff] at hca
    rcases hca with hca | hca
    · simp only [atom, if_true, covers_some] at hca
      exact Or.inl (covers_mono hcb (by omega))
    · rw [hfall] at hca; exact (covers_none _ hca).elim

theorem subeffects_loopEffects {a b : Effects} (h : Subeffects a b) :
    Subeffects (loopEffects a) (loopEffects b) := by
  intro exit cost hc
  cases exit <;> simp only [loopEffects] at hc ⊢ <;> exact h _ cost hc

theorem cycle_of_subeffects {a b : Effects} (h : Subeffects a b)
    (cycle : AtMost (join (b .fall) (b (.continueTo 0))) 1) :
    AtMost (join (a .fall) (a (.continueTo 0))) 1 := by
  intro cost hc
  apply cycle cost
  rw [covers_join_iff] at hc ⊢
  rcases hc with hc | hc
  · exact Or.inl (h .fall cost hc)
  · exact Or.inr (h (.continueTo 0) cost hc)

theorem subeffects_returningEffects_none {callee c1 c2 : Effects}
    (hc : Subeffects c1 c2) :
    Subeffects (returningEffects callee c1 none) (returningEffects callee c2 none) := by
  intro exit cost h
  simp only [returningEffects] at h ⊢
  rw [covers_join_iff] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · right
    rw [covers_join_iff] at h ⊢
    rcases h with h | h
    · left
      rw [covers_add_iff] at h ⊢
      obtain ⟨ca, cb, hca, hcb, hle⟩ := h
      exact ⟨ca, cb, hca, hc exit cb hcb, hle⟩
    · exact Or.inr h

theorem subeffects_returningEffects_some {callee c1 c2 h1 h2 : Effects}
    (hc : Subeffects c1 c2) (hh : Subeffects h1 h2) :
    Subeffects (returningEffects callee c1 (some h1)) (returningEffects callee c2 (some h2)) := by
  intro exit cost h
  simp only [returningEffects] at h ⊢
  rw [covers_join_iff] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · right
    rw [covers_join_iff] at h ⊢
    rcases h with h | h
    · left
      rw [covers_add_iff] at h ⊢
      obtain ⟨ca, cb, hca, hcb, hle⟩ := h
      exact ⟨ca, cb, hca, hc exit cb hcb, hle⟩
    · right
      rw [covers_add_iff] at h ⊢
      obtain ⟨ca, cb, hca, hcb, hle⟩ := h
      exact ⟨ca, cb, hca, hh exit cb hcb, hle⟩

/-! ## Helper: programs built solely from `.skip`-erased instructions and `.seq` -/

abbrev DerivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (p : WordLangProgHOL (BitVec width)) (target : Effects) : Prop :=
  ∃ effects, Derives defs terminal p effects ∧ Subeffects effects target

@[simp] theorem erase_skip {width : Nat} [NeZero width] :
    erase (.skip : WordLangProgHOL (BitVec width)) = .skip := by simp [erase]
@[simp] theorem erase_move {width : Nat} [NeZero width] (pri : Nat) (ls : List (Nat × Nat)) :
    erase (.move pri ls : WordLangProgHOL (BitVec width)) = .skip := by simp [erase]
@[simp] theorem erase_inst {width : Nat} [NeZero width] (i : WordLangInst (BitVec width)) :
    erase (.inst i) = .skip := by simp [erase]
@[simp] theorem erase_assign {width : Nat} [NeZero width] (v : Nat) (e : WordLangExpHOL (BitVec width)) :
    erase (.assign v e) = .skip := by simp [erase]
@[simp] theorem erase_get {width : Nat} [NeZero width] (v : Nat) (s : WordStoreHOL) :
    erase (.get v s : WordLangProgHOL (BitVec width)) = .skip := by simp [erase]
@[simp] theorem erase_set {width : Nat} [NeZero width] (s : WordStoreHOL) (e : WordLangExpHOL (BitVec width)) :
    erase (.set s e) = .skip := by simp [erase]
@[simp] theorem erase_store {width : Nat} [NeZero width] (e : WordLangExpHOL (BitVec width)) (v : Nat) :
    erase (.store e v) = .skip := by simp [erase]
@[simp] theorem erase_storeConsts {width : Nat} [NeZero width]
    (a b c d : Nat) (ws : List (Bool × BitVec width)) :
    erase (.storeConsts a b c d ws) = .skip := by simp [erase]
@[simp] theorem erase_opCurrHeap {width : Nat} [NeZero width] (b : BinOp) (r1 r2 : Nat) :
    erase (.opCurrHeap b r1 r2 : WordLangProgHOL (BitVec width)) = .skip := by simp [erase]
@[simp] theorem erase_locValue {width : Nat} [NeZero width] (r l : Nat) :
    erase (.locValue r l : WordLangProgHOL (BitVec width)) = .skip := by simp [erase]
@[simp] theorem erase_codeBufferWrite {width : Nat} [NeZero width] (r1 r2 : Nat) :
    erase (.codeBufferWrite r1 r2 : WordLangProgHOL (BitVec width)) = .skip := by simp [erase]
@[simp] theorem erase_dataBufferWrite {width : Nat} [NeZero width] (r1 r2 : Nat) :
    erase (.dataBufferWrite r1 r2 : WordLangProgHOL (BitVec width)) = .skip := by simp [erase]

theorem derivesSub_skip {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool) :
    DerivesSub defs terminal (.skip : WordLangProgHOL (BitVec width)) (atom .fall 0) :=
  ⟨atom .fall 0, Derives.normal (.skip : WordLangProgHOL (BitVec width)) (by simp), subeffects_refl _⟩

theorem derivesSub_normal {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (p : WordLangProgHOL (BitVec width)) (h : erase p = .skip := by simp) :
    DerivesSub defs terminal p (atom .fall 0) :=
  ⟨atom .fall 0, Derives.normal p h, subeffects_refl _⟩

theorem derivesSub_move {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (pri : Nat) (ls : List (Nat × Nat)) :
    DerivesSub defs terminal (.move pri ls : WordLangProgHOL (BitVec width)) (atom .fall 0) :=
  ⟨atom .fall 0, Derives.normal (.move pri ls : WordLangProgHOL (BitVec width)) (by simp), subeffects_refl _⟩

theorem derivesSub_inst {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (i : WordLangInst (BitVec width)) :
    DerivesSub defs terminal (.inst i) (atom .fall 0) :=
  ⟨atom .fall 0, Derives.normal (.inst i) (by simp), subeffects_refl _⟩

theorem derivesSub_mono {width : Nat} [NeZero width]
    {defs : Option Nat → Effects} {terminal : Basis.Pure.MlString.MlString → Bool}
    {p : WordLangProgHOL (BitVec width)} {e1 e2 : Effects}
    (h : DerivesSub defs terminal p e1) (hle : Subeffects e1 e2) :
    DerivesSub defs terminal p e2 := by
  obtain ⟨e, hd, hs⟩ := h
  exact ⟨e, hd, subeffects_trans hs hle⟩

theorem derivesSub_seq {width : Nat} [NeZero width]
    {defs : Option Nat → Effects} {terminal : Basis.Pure.MlString.MlString → Bool}
    {p1 p2 : WordLangProgHOL (BitVec width)} {e1 e2 : Effects}
    (h1 : DerivesSub defs terminal p1 e1) (h2 : DerivesSub defs terminal p2 e2) :
    DerivesSub defs terminal (.seq p1 p2) (WordCostEffects.seq e1 e2) := by
  obtain ⟨a, ha, hsa⟩ := h1
  obtain ⟨b, hb, hsb⟩ := h2
  exact ⟨WordCostEffects.seq a b, Derives.seq ha hb, subeffects_seq hsa hsb⟩

theorem derivesSub_seq_zero_left {width : Nat} [NeZero width]
    {defs : Option Nat → Effects} {terminal : Basis.Pure.MlString.MlString → Bool}
    {p1 p2 : WordLangProgHOL (BitVec width)} {e : Effects}
    (h1 : DerivesSub defs terminal p1 (atom .fall 0))
    (h2 : DerivesSub defs terminal p2 e) :
    DerivesSub defs terminal (.seq p1 p2) e :=
  derivesSub_mono (derivesSub_seq h1 h2) (seq_atom_fall_zero_left e)

theorem derivesSub_seq_zero_right {width : Nat} [NeZero width]
    {defs : Option Nat → Effects} {terminal : Basis.Pure.MlString.MlString → Bool}
    {p1 p2 : WordLangProgHOL (BitVec width)} {e : Effects}
    (h1 : DerivesSub defs terminal p1 e)
    (h2 : DerivesSub defs terminal p2 (atom .fall 0)) :
    DerivesSub defs terminal (.seq p1 p2) e :=
  derivesSub_mono (derivesSub_seq h1 h2) (seq_atom_fall_zero_right e)

theorem derivesSub_smartSeq_zero_left {width : Nat} [NeZero width]
    {defs : Option Nat → Effects} {terminal : Basis.Pure.MlString.MlString → Bool}
    {p1 p2 : WordLangProgHOL (BitVec width)} {e : Effects}
    (h1 : DerivesSub defs terminal p1 (atom .fall 0))
    (h2 : DerivesSub defs terminal p2 e) :
    DerivesSub defs terminal (WordSimp.smartSeqHOL p1 p2) e := by
  unfold WordSimp.smartSeqHOL
  split
  · exact h2
  · exact derivesSub_seq_zero_left h1 h2

theorem derivesSub_smartSeq {width : Nat} [NeZero width]
    {defs : Option Nat → Effects} {terminal : Basis.Pure.MlString.MlString → Bool}
    {p1 p2 : WordLangProgHOL (BitVec width)} {e1 e2 : Effects}
    (hskip : p1 = .skip → Subeffects e2 (WordCostEffects.seq e1 e2))
    (h1 : DerivesSub defs terminal p1 e1)
    (h2 : DerivesSub defs terminal p2 e2) :
    DerivesSub defs terminal (WordSimp.smartSeqHOL p1 p2) (WordCostEffects.seq e1 e2) := by
  cases p1 with
  | skip =>
    simpa [WordSimp.smartSeqHOL] using derivesSub_mono h2 (hskip rfl)
  | _ =>
    simpa [WordSimp.smartSeqHOL] using derivesSub_seq h1 h2

theorem derivesSub_branch {width : Nat} [NeZero width]
    {defs : Option Nat → Effects} {terminal : Basis.Pure.MlString.MlString → Bool}
    (cmp : Cmp) (reg : Nat) (operand : WordRegImm (BitVec width))
    {p1 p2 : WordLangProgHOL (BitVec width)} {e1 e2 : Effects}
    (h1 : DerivesSub defs terminal p1 e1) (h2 : DerivesSub defs terminal p2 e2) :
    DerivesSub defs terminal (.ite cmp reg operand p1 p2) (merge e1 e2) := by
  obtain ⟨a, ha, hsa⟩ := h1
  obtain ⟨b, hb, hsb⟩ := h2
  exact ⟨merge a b, Derives.branch cmp reg operand ha hb, subeffects_merge hsa hsb⟩

theorem derivesSub_loop {width : Nat} [NeZero width]
    {defs : Option Nat → Effects} {terminal : Basis.Pure.MlString.MlString → Bool}
    (names exits : WordLangNumSetHOL)
    {body : WordLangProgHOL (BitVec width)} {e : Effects}
    (hbody : DerivesSub defs terminal body e)
    (cycle : AtMost (join (e .fall) (e (.continueTo 0))) 1) :
    DerivesSub defs terminal (.loop names body exits) (loopEffects e) := by
  obtain ⟨a, ha, hsa⟩ := hbody
  exact ⟨loopEffects a, Derives.loop names exits ha (cycle_of_subeffects hsa cycle),
    subeffects_loopEffects hsa⟩

theorem derivesSub_returning_none {width : Nat} [NeZero width]
    {defs : Option Nat → Effects} {terminal : Basis.Pure.MlString.MlString → Bool}
    (names : List Nat) (live : WordLangCutsetsHOL)
    {next : WordLangProgHOL (BitVec width)} (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat) {contEffects : Effects}
    (hcont : DerivesSub defs terminal next contEffects) :
    DerivesSub defs terminal (.call (some (names, live, next, l1, l2)) dest args none)
      (returningEffects (defs dest) contEffects none) := by
  obtain ⟨c, hc, hsc⟩ := hcont
  refine ⟨returningEffects (defs dest) c none, ?_, subeffects_returningEffects_none hsc⟩
  exact Derives.returning names live next l1 l2 dest args none c (fun _ => none) hc
    (by intro _ _ _ _ eq; cases eq)

theorem derivesSub_returning_some {width : Nat} [NeZero width]
    {defs : Option Nat → Effects} {terminal : Basis.Pure.MlString.MlString → Bool}
    (names : List Nat) (live : WordLangCutsetsHOL)
    {next : WordLangProgHOL (BitVec width)} (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (hname : Nat) {hbody : WordLangProgHOL (BitVec width)} (h1 h2 : Nat)
    {contEffects handlerEffects : Effects}
    (hcont : DerivesSub defs terminal next contEffects)
    (hhand : DerivesSub defs terminal hbody handlerEffects) :
    DerivesSub defs terminal
      (.call (some (names, live, next, l1, l2)) dest args (some (hname, hbody, h1, h2)))
      (returningEffects (defs dest) contEffects (some handlerEffects)) := by
  obtain ⟨c, hc, hsc⟩ := hcont
  obtain ⟨h, hh, hsh⟩ := hhand
  refine ⟨returningEffects (defs dest) c (some h), ?_, subeffects_returningEffects_some hsc hsh⟩
  refine Derives.returning names live next l1 l2 dest args (some (hname, hbody, h1, h2)) c h hc ?_
  intro _ _ _ _ eq
  simp only [Option.some.injEq, Prod.mk.injEq] at eq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := eq
  exact hh

/-! ## Pass 1: `WordSimp.compileExp` (`seqAssoc`, `constFp`, `simpDuplicateIf`, `pushOutIf`) -/

theorem derives_skip_inv {width : Nat} [NeZero width]
    {defs : Option Nat → Effects} {terminal : Basis.Pure.MlString.MlString → Bool}
    {e : Effects}
    (h : Derives defs terminal (.skip : WordLangProgHOL (BitVec width)) e) :
    e = atom .fall 0 := by
  cases h
  rfl

theorem seqAssoc_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (q : WordLangProgHOL (BitVec width)) {e2 : Effects}
    (hq : Derives defs terminal q e2) :
    ∀ (p1 : WordLangProgHOL (BitVec width)) {e1 : Effects},
      (p1 = .skip → e1 = atom .fall 0) →
      DerivesSub defs terminal p1 e1 →
      DerivesSub defs terminal (WordSimp.seqAssoc p1 q) (WordCostEffects.seq e1 e2) := by
  induction hq with
  | normal q h =>
    cases q with
    | skip =>
      intro p1 e1 _ hp1
      have rfl_e2 : atom .fall 0 = atom .fall 0 := rfl
      simpa only [WordSimp.seqAssoc] using
        derivesSub_mono hp1 (seq_atom_fall_zero_right_rev e1)
    | move _ _ | inst _ | assign _ _ | get _ _ | set _ _ | store _ _ | storeConsts _ _ _ _ _
    | opCurrHeap _ _ _ | locValue _ _ | codeBufferWrite _ _ | dataBufferWrite _ _ =>
      intro p1 e1 hskip hp1
      simp only [WordSimp.seqAssoc]
      refine derivesSub_smartSeq ?_ hp1 (derivesSub_normal defs terminal _ h)
      intro hp1_skip; rw [hskip hp1_skip]; exact seq_atom_fall_zero_left_rev _
    | tick | shareInst _ _ _ | raise _ | «return» _ _ | ffi _ _ _ _ _ _
    | «break» _ | «continue» _ | seq _ _ | ite _ _ _ _ _ | loop _ _ _
    | alloc _ _ | install _ _ _ _ _ | mustTerminate _ =>
      simp [erase] at h
    | call ret dest args handler =>
      rcases ret with _ | ⟨_, _, _, _, _⟩ <;> rcases handler with _ | ⟨_, _, _, _⟩ <;>
        simp [erase] at h
  | tick =>
    intro p1 e1 hskip hp1
    simp only [WordSimp.seqAssoc]
    refine derivesSub_smartSeq ?_ hp1 ⟨_, Derives.tick, subeffects_refl _⟩
    intro hp1_skip; rw [hskip hp1_skip]; exact seq_atom_fall_zero_left_rev _
  | share op reg exp =>
    intro p1 e1 hskip hp1
    simp only [WordSimp.seqAssoc]
    refine derivesSub_smartSeq ?_ hp1 ⟨_, Derives.share op reg exp, subeffects_refl _⟩
    intro hp1_skip; rw [hskip hp1_skip]; exact seq_atom_fall_zero_left_rev _
  | raise reg =>
    intro p1 e1 hskip hp1
    simp only [WordSimp.seqAssoc]
    refine derivesSub_smartSeq ?_ hp1 ⟨_, Derives.raise reg, subeffects_refl _⟩
    intro hp1_skip; rw [hskip hp1_skip]; exact seq_atom_fall_zero_left_rev _
  | result reg regs =>
    intro p1 e1 hskip hp1
    simp only [WordSimp.seqAssoc]
    refine derivesSub_smartSeq ?_ hp1 ⟨_, Derives.result reg regs, subeffects_refl _⟩
    intro hp1_skip; rw [hskip hp1_skip]; exact seq_atom_fall_zero_left_rev _
  | breakTo label =>
    intro p1 e1 hskip hp1
    simp only [WordSimp.seqAssoc]
    refine derivesSub_smartSeq ?_ hp1 ⟨_, Derives.breakTo label, subeffects_refl _⟩
    intro hp1_skip; rw [hskip hp1_skip]; exact seq_atom_fall_zero_left_rev _
  | continueTo label =>
    intro p1 e1 hskip hp1
    simp only [WordSimp.seqAssoc]
    refine derivesSub_smartSeq ?_ hp1 ⟨_, Derives.continueTo label, subeffects_refl _⟩
    intro hp1_skip; rw [hskip hp1_skip]; exact seq_atom_fall_zero_left_rev _
  | ffi name r1 l1 r2 l2 names =>
    intro p1 e1 hskip hp1
    simp only [WordSimp.seqAssoc]
    refine derivesSub_smartSeq ?_ hp1 ⟨_, Derives.ffi name r1 l1 r2 l2 names, subeffects_refl _⟩
    intro hp1_skip; rw [hskip hp1_skip]; exact seq_atom_fall_zero_left_rev _
  | @seq q1 q2 a b _ _ ih1 ih2 =>
    intro p1 e1 hskip hp1
    simp only [WordSimp.seqAssoc]
    have hstep1 := ih1 p1 hskip hp1
    have hstep2 : DerivesSub defs terminal (WordSimp.seqAssoc (WordSimp.seqAssoc p1 q1) q2)
        (WordCostEffects.seq (WordCostEffects.seq e1 a) b) := by
      obtain ⟨mid, hmid_d, hmid_s⟩ := hstep1
      have hraw := ih2 (WordSimp.seqAssoc p1 q1) (fun hmid_skip => by rw [hmid_skip] at hmid_d; exact derives_skip_inv hmid_d)
        ⟨mid, hmid_d, subeffects_refl mid⟩
      exact derivesSub_mono hraw (subeffects_seq hmid_s (subeffects_refl b))
    exact derivesSub_mono hstep2 (seq_assoc_sub e1 a b)
  | branch cmp reg operand left right ih1 ih2 =>
    intro p1 e1 hskip hp1
    simp only [WordSimp.seqAssoc]
    have hb1 := derivesSub_mono (ih1 .skip (fun _ => rfl) (derivesSub_skip defs terminal))
      (seq_atom_fall_zero_left _)
    have hb2 := derivesSub_mono (ih2 .skip (fun _ => rfl) (derivesSub_skip defs terminal))
      (seq_atom_fall_zero_left _)
    refine derivesSub_smartSeq ?_ hp1 (derivesSub_branch cmp reg operand hb1 hb2)
    intro hp1_skip; rw [hskip hp1_skip]; exact seq_atom_fall_zero_left_rev _
  | loop names exits bodyRule cycle ih =>
    intro p1 e1 hskip hp1
    simp only [WordSimp.seqAssoc]
    have hb := derivesSub_mono (ih .skip (fun _ => rfl) (derivesSub_skip defs terminal))
      (seq_atom_fall_zero_left _)
    refine derivesSub_smartSeq ?_ hp1 (derivesSub_loop names exits hb cycle)
    intro hp1_skip; rw [hskip hp1_skip]; exact seq_atom_fall_zero_left_rev _
  | tail dest args =>
    intro p1 e1 hskip hp1
    simp only [WordSimp.seqAssoc]
    refine derivesSub_smartSeq ?_ hp1 ⟨_, Derives.tail dest args, subeffects_refl _⟩
    intro hp1_skip; rw [hskip hp1_skip]; exact seq_atom_fall_zero_left_rev _
  | returning names live next l1 l2 dest args handler contEffects handlerEffects cont handlers ihCont ihHand =>
    intro p1 e1 hskip hp1
    have hc := derivesSub_mono (ihCont .skip (fun _ => rfl) (derivesSub_skip defs terminal))
      (seq_atom_fall_zero_left _)
    cases handler with
    | none =>
      simp only [WordSimp.seqAssoc]
      refine derivesSub_smartSeq ?_ hp1 (derivesSub_returning_none names live l1 l2 dest args hc)
      intro hp1_skip; rw [hskip hp1_skip]; exact seq_atom_fall_zero_left_rev _
    | some h =>
      rcases h with ⟨hname, hbody, h1, h2⟩
      simp only [WordSimp.seqAssoc]
      have hh := derivesSub_mono
        (ihHand hname hbody h1 h2 rfl .skip (fun _ => rfl) (derivesSub_skip defs terminal))
        (seq_atom_fall_zero_left _)
      refine derivesSub_smartSeq ?_ hp1
        (derivesSub_returning_some names live l1 l2 dest args hname h1 h2 hc hh)
      intro hp1_skip; rw [hskip hp1_skip]; exact seq_atom_fall_zero_left_rev _

theorem seqAssoc_skip_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : DerivesSub defs terminal p e) :
    DerivesSub defs terminal (WordSimp.seqAssoc .skip p) e := by
  obtain ⟨ef, hd, hs⟩ := hp
  have h := seqAssoc_derivesSub defs terminal p hd .skip (fun _ => rfl) (derivesSub_skip defs terminal)
  exact derivesSub_mono h (subeffects_trans (seq_atom_fall_zero_left ef) hs)

theorem dropConsts_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (cs : Spt (BitVec width)) (ns : List Nat) :
    DerivesSub defs terminal (WordSimp.dropConsts cs ns) (atom .fall 0) := by
  induction ns with
  | nil => exact derivesSub_skip defs terminal
  | cons n ns ih =>
    simp only [WordSimp.dropConsts]
    cases sptLookup n cs with
    | none => exact ih
    | some w =>
      exact derivesSub_smartSeq_zero_left ih
        (derivesSub_normal defs terminal (.assign n (.const w) : WordLangProgHOL (BitVec width)))

theorem constFpLoop_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : Derives defs terminal p e) :
    ∀ cs : Spt (BitVec width),
      DerivesSub defs terminal (WordSimp.constFpLoop p cs).1 e := by
  induction hp with
  | normal p h =>
    intro cs
    cases p with
    | skip | move _ _ | inst _ | get _ _ | opCurrHeap _ _ _ | locValue _ _
    | storeConsts _ _ _ _ _ | store _ _ | set _ _ | codeBufferWrite _ _ | dataBufferWrite _ _ =>
      exact derivesSub_normal defs terminal _ (by simp [WordSimp.constFpLoop])
    | assign v exp =>
      simp only [WordSimp.constFpLoop]
      cases WordSimp.constFpExp exp cs <;> exact derivesSub_normal defs terminal _
    | tick | shareInst _ _ _ | raise _ | «return» _ _ | ffi _ _ _ _ _ _
    | «break» _ | «continue» _ | seq _ _ | ite _ _ _ _ _ | loop _ _ _
    | alloc _ _ | install _ _ _ _ _ | mustTerminate _ =>
      simp [erase] at h
    | call ret dest args handler =>
      rcases ret with _ | ⟨_, _, _, _, _⟩ <;> rcases handler with _ | ⟨_, _, _, _⟩ <;>
        simp [erase] at h
  | tick => intro cs; exact ⟨_, Derives.tick, subeffects_refl _⟩
  | share op reg exp =>
    intro cs
    cases op <;> exact ⟨_, Derives.share _ reg _, subeffects_refl _⟩
  | raise reg => intro cs; exact ⟨_, Derives.raise reg, subeffects_refl _⟩
  | result reg regs => intro cs; exact ⟨_, Derives.result reg regs, subeffects_refl _⟩
  | breakTo label => intro cs; exact ⟨_, Derives.breakTo label, subeffects_refl _⟩
  | continueTo label => intro cs; exact ⟨_, Derives.continueTo label, subeffects_refl _⟩
  | ffi name r1 l1 r2 l2 names =>
    intro cs
    simp only [WordSimp.constFpLoop]
    exact derivesSub_smartSeq_zero_left (dropConsts_derivesSub defs terminal cs [r1, l1, r2, l2])
      ⟨_, Derives.ffi name r1 l1 r2 l2 names, subeffects_refl _⟩
  | seq left right ih1 ih2 =>
    intro cs
    simp only [WordSimp.constFpLoop]
    exact derivesSub_seq (ih1 cs) (ih2 (WordSimp.constFpLoop _ cs).2)
  | branch cmp reg operand left right ih1 ih2 =>
    intro cs
    simp only [WordSimp.constFpLoop]
    cases sptLookup reg cs with
    | none => exact derivesSub_branch cmp reg operand (ih1 cs) (ih2 cs)
    | some clhs =>
      cases WordSimp.getVarImmCs operand cs with
      | none => exact derivesSub_branch cmp reg operand (ih1 cs) (ih2 cs)
      | some crhs =>
        dsimp only
        split
        · exact derivesSub_mono (ih1 cs) (subeffects_merge_left _ _)
        · exact derivesSub_mono (ih2 cs) (subeffects_merge_right _ _)
  | loop names exits bodyRule cycle ih =>
    intro cs
    simp only [WordSimp.constFpLoop]
    exact derivesSub_loop names exits (ih .ln) cycle
  | tail dest args =>
    intro cs
    simp only [WordSimp.constFpLoop]
    exact derivesSub_smartSeq_zero_left (dropConsts_derivesSub defs terminal cs args)
      ⟨_, Derives.tail dest args, subeffects_refl _⟩
  | returning names live next l1 l2 dest args handler contEffects handlerEffects cont handlers ihCont ihHand =>
    intro cs
    cases handler with
    | none =>
      simp only [WordSimp.constFpLoop]
      exact derivesSub_smartSeq_zero_left (dropConsts_derivesSub defs terminal cs args)
        (derivesSub_returning_none names live l1 l2 dest args (ihCont _))
    | some h =>
      rcases h with ⟨hname, hbody, h1, h2⟩
      simp only [WordSimp.constFpLoop]
      exact derivesSub_smartSeq_zero_left (dropConsts_derivesSub defs terminal cs args)
        (derivesSub_returning_some names live l1 l2 dest args hname h1 h2
          ⟨contEffects, cont, subeffects_refl _⟩
          ⟨handlerEffects, handlers hname hbody h1 h2 rfl, subeffects_refl _⟩)

theorem constFp_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : DerivesSub defs terminal p e) :
    DerivesSub defs terminal (WordSimp.constFp p) e := by
  obtain ⟨ef, hd, hs⟩ := hp
  exact derivesSub_mono (constFpLoop_derivesSub defs terminal hd .ln) hs

theorem tryIfHoist2_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool) :
    ∀ (n : Nat) (p1 interm dummy p2 p3 : WordLangProgHOL (BitVec width))
      {e1 ei e2 : Effects},
      DerivesSub defs terminal p1 e1 →
      DerivesSub defs terminal interm ei →
      DerivesSub defs terminal p2 e2 →
      WordSimp.tryIfHoist2 n p1 interm dummy p2 = some p3 →
      DerivesSub defs terminal p3 (WordCostEffects.seq (WordCostEffects.seq e1 ei) e2)
  | 0, _, _, _, _, _, _, _, _, _, _, _, h => by simp [WordSimp.tryIfHoist2] at h
  | n + 1, p1, interm, dummy, p2, p3, e1, ei, e2, hp1, hi, hp2, h => by
    cases p1 with
    | ite cmp lhs rhs br1 br2 =>
      simp only [WordSimp.tryIfHoist2] at h
      split at h
      · cases h
      · split at h
        · cases h
        · simp only [Option.some.injEq] at h
          subst h
          obtain ⟨e_ite, hd_ite, hs_ite⟩ := hp1
          cases hd_ite with
          | normal _ her => simp [erase] at her
          | @branch _ _ _ _ _ a1 a2 hd1 hd2 =>
            have hbr1 : DerivesSub defs terminal (.seq (.seq br1 interm) p2)
                (WordCostEffects.seq (WordCostEffects.seq a1 ei) e2) :=
              derivesSub_seq (derivesSub_seq ⟨a1, hd1, subeffects_refl _⟩ hi) hp2
            have hbr2 : DerivesSub defs terminal (.seq (.seq br2 interm) p2)
                (WordCostEffects.seq (WordCostEffects.seq a2 ei) e2) :=
              derivesSub_seq (derivesSub_seq ⟨a2, hd2, subeffects_refl _⟩ hi) hp2
            have hite := derivesSub_branch cmp lhs rhs hbr1 hbr2
            have hcfp := constFp_derivesSub defs terminal hite
            refine derivesSub_mono hcfp ?_
            refine subeffects_trans (seq_merge_distrib_right _ _ e2) ?_
            refine subeffects_seq ?_ (subeffects_refl e2)
            refine subeffects_trans (seq_merge_distrib_right a1 a2 ei) ?_
            exact subeffects_seq hs_ite (subeffects_refl ei)
    | seq q1 q2 =>
      simp only [WordSimp.tryIfHoist2] at h
      obtain ⟨e_seq, hd_seq, hs_seq⟩ := hp1
      cases hd_seq with
      | normal _ her => simp [erase] at her
      | @seq _ _ eq1 eq2 hd1 hd2 =>
        cases hdest : WordSimp.destIf q2 with
        | some val =>
          rcases val with ⟨cmp0, lhs0, rhs0, br1, br2⟩
          simp only [hdest] at h
          cases q2 with
          | ite cmpQ lhsQ rhsQ b1Q b2Q =>
            simp only [WordSimp.destIf, Option.some.injEq, Prod.mk.injEq] at hdest
            rcases hdest with ⟨rfl, rfl, rfl, rfl, rfl⟩
            split at h
            · cases h
            · split at h
              · cases h
              · simp only [Option.some.injEq] at h
                subst h
                cases hd2 with
                | normal _ her => simp [erase] at her
                | @branch _ _ _ _ _ a1 a2 hdb1 hdb2 =>
                  have hbr1 := derivesSub_seq (derivesSub_seq ⟨a1, hdb1, subeffects_refl _⟩ hi) hp2
                  have hbr2 := derivesSub_seq (derivesSub_seq ⟨a2, hdb2, subeffects_refl _⟩ hi) hp2
                  have hcfp := constFp_derivesSub defs terminal
                    (derivesSub_branch cmpQ lhsQ rhsQ hbr1 hbr2)
                  have hseq := derivesSub_seq ⟨eq1, hd1, subeffects_refl _⟩ hcfp
                  refine derivesSub_mono hseq ?_
                  have hdist : Subeffects
                      (merge (WordCostEffects.seq (WordCostEffects.seq a1 ei) e2)
                        (WordCostEffects.seq (WordCostEffects.seq a2 ei) e2))
                      (WordCostEffects.seq (WordCostEffects.seq (merge a1 a2) ei) e2) :=
                    subeffects_trans (seq_merge_distrib_right _ _ e2)
                      (subeffects_seq (seq_merge_distrib_right a1 a2 ei) (subeffects_refl e2))
                  refine subeffects_trans (subeffects_seq (subeffects_refl eq1) hdist) ?_
                  refine subeffects_trans (seq_assoc_sub_rev eq1 (WordCostEffects.seq (merge a1 a2) ei) e2) ?_
                  refine subeffects_seq ?_ (subeffects_refl e2)
                  refine subeffects_trans (seq_assoc_sub_rev eq1 (merge a1 a2) ei) ?_
                  exact subeffects_seq hs_seq (subeffects_refl ei)
          | _ => simp [WordSimp.destIf] at hdest
        | none =>
          simp only [hdest] at h
          split at h
          · have hrec := tryIfHoist2_derivesSub defs terminal n q1 (.seq q2 interm) dummy p2 p3
              ⟨eq1, hd1, subeffects_refl _⟩
              (derivesSub_seq ⟨eq2, hd2, subeffects_refl _⟩ hi)
              hp2 h
            refine derivesSub_mono hrec ?_
            refine subeffects_seq ?_ (subeffects_refl e2)
            refine subeffects_trans (seq_assoc_sub_rev eq1 eq2 ei) ?_
            exact subeffects_seq hs_seq (subeffects_refl ei)
          · cases h
    | _ => simp [WordSimp.tryIfHoist2] at h

theorem tryIfHoist1_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    {p1 p2 p3 : WordLangProgHOL (BitVec width)} {e1 e2 : Effects}
    (hp1 : DerivesSub defs terminal p1 e1)
    (hp2 : DerivesSub defs terminal p2 e2)
    (h : WordSimp.tryIfHoist1 p1 p2 = some p3) :
    DerivesSub defs terminal p3 (WordCostEffects.seq e1 e2) := by
  unfold WordSimp.tryIfHoist1 at h
  cases hdest : WordSimp.destIf p2 with
  | none => simp [hdest] at h
  | some val =>
    rcases val with ⟨cmp, lhs, rhs, _, _⟩
    simp only [hdest] at h
    have h2 := tryIfHoist2_derivesSub defs terminal WordSimp.rewriteDuplicateIfMaxReassoc
      p1 .skip (.ite cmp lhs rhs (.raise 1) (.raise 2)) p2 p3
      hp1 (derivesSub_skip defs terminal) hp2 h
    exact derivesSub_mono h2 (subeffects_seq (seq_atom_fall_zero_right e1) (subeffects_refl e2))

theorem simpDuplicateIf_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : Derives defs terminal p e) :
    DerivesSub defs terminal (WordSimp.simpDuplicateIf p) e := by
  induction hp with
  | normal p h =>
    cases p with
    | skip | move _ _ | inst _ | assign _ _ | get _ _ | set _ _ | store _ _ | storeConsts _ _ _ _ _
    | opCurrHeap _ _ _ | locValue _ _ | codeBufferWrite _ _ | dataBufferWrite _ _ =>
      exact derivesSub_normal defs terminal _ h
    | tick | shareInst _ _ _ | raise _ | «return» _ _ | ffi _ _ _ _ _ _
    | «break» _ | «continue» _ | seq _ _ | ite _ _ _ _ _ | loop _ _ _
    | alloc _ _ | install _ _ _ _ _ | mustTerminate _ =>
      simp [erase] at h
    | call ret dest args handler =>
      rcases ret with _ | ⟨_, _, _, _, _⟩ <;> rcases handler with _ | ⟨_, _, _, _⟩ <;>
        simp [erase] at h
  | tick => exact ⟨_, Derives.tick, subeffects_refl _⟩
  | share op reg exp => exact ⟨_, Derives.share op reg exp, subeffects_refl _⟩
  | raise reg => exact ⟨_, Derives.raise reg, subeffects_refl _⟩
  | result reg regs => exact ⟨_, Derives.result reg regs, subeffects_refl _⟩
  | breakTo label => exact ⟨_, Derives.breakTo label, subeffects_refl _⟩
  | continueTo label => exact ⟨_, Derives.continueTo label, subeffects_refl _⟩
  | ffi name r1 l1 r2 l2 names => exact ⟨_, Derives.ffi name r1 l1 r2 l2 names, subeffects_refl _⟩
  | @seq q1 q2 _ _ _ _ ih1 ih2 =>
    simp only [WordSimp.simpDuplicateIf]
    cases htry : WordSimp.tryIfHoist1 (WordSimp.simpDuplicateIf q1) (WordSimp.simpDuplicateIf q2) with
    | none => exact derivesSub_seq ih1 ih2
    | some p3 =>
      exact seqAssoc_skip_derivesSub defs terminal (tryIfHoist1_derivesSub defs terminal ih1 ih2 htry)
  | branch cmp reg operand left right ih1 ih2 =>
    exact derivesSub_branch cmp reg operand ih1 ih2
  | loop names exits bodyRule cycle ih =>
    exact derivesSub_loop names exits ih cycle
  | tail dest args => exact ⟨_, Derives.tail dest args, subeffects_refl _⟩
  | returning names live next l1 l2 dest args handler contEffects handlerEffects cont handlers ihCont ihHand =>
    cases handler with
    | none => exact derivesSub_returning_none names live l1 l2 dest args ihCont
    | some h =>
      rcases h with ⟨hname, hbody, h1, h2⟩
      exact derivesSub_returning_some names live l1 l2 dest args hname h1 h2 ihCont
        (ihHand hname hbody h1 h2 rfl)

theorem pushOutIfAux_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (hdefsFall : ∀ dest, defs dest .fall = none)
    {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : Derives defs terminal p e) :
    DerivesSub defs terminal (WordSimp.pushOutIfAux p).1 e ∧
      ((WordSimp.pushOutIfAux p).2 = true → e .fall = none) := by
  induction hp with
  | normal p h =>
    cases p with
    | skip | move _ _ | inst _ | assign _ _ | get _ _ | set _ _ | store _ _ | storeConsts _ _ _ _ _
    | opCurrHeap _ _ _ | locValue _ _ | codeBufferWrite _ _ | dataBufferWrite _ _ =>
      exact ⟨derivesSub_normal defs terminal _ h, by simp [WordSimp.pushOutIfAux]⟩
    | tick | shareInst _ _ _ | raise _ | «return» _ _ | ffi _ _ _ _ _ _
    | «break» _ | «continue» _ | seq _ _ | ite _ _ _ _ _ | loop _ _ _
    | alloc _ _ | install _ _ _ _ _ | mustTerminate _ =>
      simp [erase] at h
    | call ret dest args handler =>
      rcases ret with _ | ⟨_, _, _, _, _⟩ <;> rcases handler with _ | ⟨_, _, _, _⟩ <;>
        simp [erase] at h
  | tick => exact ⟨⟨_, Derives.tick, subeffects_refl _⟩, by simp [WordSimp.pushOutIfAux]⟩
  | share op reg exp =>
    exact ⟨⟨_, Derives.share op reg exp, subeffects_refl _⟩, by simp [WordSimp.pushOutIfAux]⟩
  | raise reg =>
    exact ⟨⟨_, Derives.raise reg, subeffects_refl _⟩, fun _ => rfl⟩
  | result reg regs =>
    exact ⟨⟨_, Derives.result reg regs, subeffects_refl _⟩, fun _ => rfl⟩
  | breakTo label =>
    exact ⟨⟨_, Derives.breakTo label, subeffects_refl _⟩, by simp [WordSimp.pushOutIfAux]⟩
  | continueTo label =>
    exact ⟨⟨_, Derives.continueTo label, subeffects_refl _⟩, by simp [WordSimp.pushOutIfAux]⟩
  | ffi name r1 l1 r2 l2 names =>
    exact ⟨⟨_, Derives.ffi name r1 l1 r2 l2 names, subeffects_refl _⟩, by simp [WordSimp.pushOutIfAux]⟩
  | @seq c1 c2 a b left right ih1 ih2 =>
    rcases ih1 with ⟨hd1, hb1⟩
    rcases ih2 with ⟨hd2, hb2⟩
    simp only [WordSimp.pushOutIfAux]
    rcases hp1 : WordSimp.pushOutIfAux c1 with ⟨c1', b1⟩
    simp only [hp1] at hd1 hb1 ⊢
    cases b1 with
    | true =>
      have hfall1 : a .fall = none := hb1 rfl
      refine ⟨derivesSub_seq hd1 ⟨b, right, subeffects_refl _⟩, fun _ => ?_⟩
      simp [WordCostEffects.seq, hfall1, add, join]
    | false =>
      rcases hp2 : WordSimp.pushOutIfAux c2 with ⟨c2', b2⟩
      simp only [hp2] at hd2 hb2 ⊢
      refine ⟨derivesSub_seq hd1 hd2, fun hb => ?_⟩
      have hfall2 : b .fall = none := hb2 hb
      cases a .fall <;> simp [WordCostEffects.seq, hfall2, add, join]
  | @branch cmp reg operand c1 c2 a b _ _ ih1 ih2 =>
    rcases ih1 with ⟨hd1, hb1⟩
    rcases ih2 with ⟨hd2, hb2⟩
    simp only [WordSimp.pushOutIfAux]
    rcases hp1 : WordSimp.pushOutIfAux c1 with ⟨c1', b1⟩
    rcases hp2 : WordSimp.pushOutIfAux c2 with ⟨c2', b2⟩
    simp only [hp1, hp2] at hd1 hb1 hd2 hb2 ⊢
    cases b1 <;> cases b2
    · exact ⟨derivesSub_branch cmp reg operand hd1 hd2, by simp⟩
    · refine ⟨?_, by simp⟩
      have hite := derivesSub_branch cmp reg operand (derivesSub_skip defs terminal) hd2
      exact derivesSub_mono (derivesSub_seq hite hd1) (push_out_if_right_sub (hb2 rfl))
    · refine ⟨?_, by simp⟩
      have hite := derivesSub_branch cmp reg operand hd1 (derivesSub_skip defs terminal)
      exact derivesSub_mono (derivesSub_seq hite hd2) (push_out_if_left_sub (hb1 rfl))
    · refine ⟨derivesSub_branch cmp reg operand hd1 hd2, fun _ => ?_⟩
      simp [merge, hb1 rfl, hb2 rfl, join]
  | loop names exits bodyRule cycle ih =>
    simp only [WordSimp.pushOutIfAux]
    exact ⟨derivesSub_loop names exits ih.1 cycle, by simp⟩
  | tail dest args =>
    exact ⟨⟨_, Derives.tail dest args, subeffects_refl _⟩, fun _ => by simp [shift, hdefsFall dest, add]⟩
  | returning names live next l1 l2 dest args handler contEffects handlerEffects cont handlers _ _ =>
    cases handler with
    | none =>
      refine ⟨⟨_, Derives.returning names live next l1 l2 dest args none contEffects
        handlerEffects cont handlers, subeffects_refl _⟩, by simp [WordSimp.pushOutIfAux]⟩
    | some h =>
      refine ⟨⟨_, Derives.returning names live next l1 l2 dest args (some h) contEffects
        handlerEffects cont handlers, subeffects_refl _⟩, by simp [WordSimp.pushOutIfAux]⟩

theorem compileExp_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (hdefsFall : ∀ dest, defs dest .fall = none)
    {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : DerivesSub defs terminal p e) :
    DerivesSub defs terminal (WordSimp.compileExp p) e := by
  unfold WordSimp.compileExp
  have h1 := seqAssoc_skip_derivesSub defs terminal hp
  have h2 := constFp_derivesSub defs terminal h1
  obtain ⟨e2, hd2, hs2⟩ := h2
  have h3 := derivesSub_mono (simpDuplicateIf_derivesSub defs terminal hd2) hs2
  obtain ⟨e3, hd3, hs3⟩ := h3
  exact derivesSub_mono (pushOutIfAux_derivesSub defs terminal hdefsFall hd3).1 hs3

/-! ## Pass 2: `WordInst.instSelectExecutable` -/

theorem instSelectExp_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (c : AsmConfigExact width) (tar temp : Nat) (exp : WordLangExpHOL (BitVec width)) :
    DerivesSub defs terminal (WordInst.instSelectExp c tar temp exp) (atom .fall 0) := by
  refine (measure (sizeOf : WordLangExpHOL (BitVec width) → Nat)).wf.induction
    (C := fun e => ∀ tar temp, DerivesSub defs terminal (WordInst.instSelectExp c tar temp e) (atom .fall 0))
    exp ?_ tar temp
  intro e ih tar temp
  cases e with
  | const w =>
    simpa [WordInst.instSelectExp] using derivesSub_normal defs terminal _
  | var v =>
    simpa [WordInst.instSelectExp] using derivesSub_normal defs terminal _
  | lookup storeName =>
    simpa [WordInst.instSelectExp] using derivesSub_normal defs terminal _
  | load inner =>
    have hrec_inner : DerivesSub defs terminal (WordInst.instSelectExp c temp temp inner) (atom .fall 0) :=
      ih inner (by simp_wf) temp temp
    have hmem0 : DerivesSub defs terminal
        (.inst (.mem .load tar (.addr temp (0 : BitVec width)))) (atom .fall 0) :=
      derivesSub_inst defs terminal _
    cases inner with
    | op op args =>
      cases op with
      | add =>
        cases args with
        | nil =>
          simpa [WordInst.instSelectExp] using derivesSub_seq_zero_left hrec_inner hmem0
        | cons exp' rest =>
          cases rest with
          | nil =>
            simpa [WordInst.instSelectExp] using derivesSub_seq_zero_left hrec_inner hmem0
          | cons e2 rest2 =>
            cases e2 with
            | const w =>
              cases rest2 with
              | nil =>
                simp only [WordInst.instSelectExp]
                split
                · exact derivesSub_seq_zero_left
                    (ih exp' (by simp_wf; omega) temp temp)
                    (derivesSub_inst defs terminal _)
                · exact derivesSub_seq_zero_left
                    (by simpa [WordInst.instSelectExp] using hrec_inner) hmem0
              | cons _ _ =>
                simpa [WordInst.instSelectExp] using derivesSub_seq_zero_left hrec_inner hmem0
            | _ =>
              simpa [WordInst.instSelectExp] using derivesSub_seq_zero_left hrec_inner hmem0
      | _ =>
        simpa [WordInst.instSelectExp] using derivesSub_seq_zero_left hrec_inner hmem0
    | _ =>
      simpa [WordInst.instSelectExp] using derivesSub_seq_zero_left hrec_inner hmem0
  | op op args =>
    cases args with
    | nil =>
      simpa [WordInst.instSelectExp] using derivesSub_skip defs terminal
    | cons e1 rest =>
      cases rest with
      | nil =>
        simpa [WordInst.instSelectExp] using derivesSub_skip defs terminal
      | cons e2 rest2 =>
        cases rest2 with
        | cons _ _ =>
          simpa [WordInst.instSelectExp] using derivesSub_skip defs terminal
        | nil =>
          simp only [WordInst.instSelectExp]
          split
          · exact derivesSub_seq_zero_left
              (ih e1 (by simp_wf; omega) temp temp)
              (derivesSub_normal defs terminal _)
          · split
            · exact derivesSub_seq_zero_left
                (ih e2 (by simp_wf; omega) temp temp)
                (derivesSub_normal defs terminal _)
            · have hp1 := ih e1 (by simp_wf; omega) temp temp
              cases e2 with
              | const w =>
                dsimp only
                split
                · exact derivesSub_seq_zero_left hp1 (derivesSub_normal defs terminal _)
                · split
                  · exact derivesSub_seq_zero_left hp1 (derivesSub_normal defs terminal _)
                  · exact derivesSub_seq_zero_left hp1
                      (derivesSub_seq_zero_left (derivesSub_normal defs terminal _)
                        (derivesSub_normal defs terminal _))
              | _ =>
                exact derivesSub_seq_zero_left hp1
                  (derivesSub_seq_zero_left (ih _ (by simp_wf; omega) (temp + 1) (temp + 1))
                    (derivesSub_normal defs terminal _))
  | shift sh exp e1 =>
    cases e1 with
    | const shiftLen =>
      simp only [WordInst.instSelectExp]
      split
      · split
        · exact derivesSub_seq_zero_left (ih exp (by simp_wf; omega) temp temp)
            (derivesSub_move defs terminal _ _)
        · exact derivesSub_seq_zero_left (ih exp (by simp_wf; omega) temp temp)
            (derivesSub_inst defs terminal _)
      · exact derivesSub_inst defs terminal _
    | var v =>
      have he1 := ih (.var v) (by simp_wf; omega) (temp + 1) (temp + 1)
      simp only [WordInst.instSelectExp]
      exact derivesSub_seq_zero_left (ih exp (by simp_wf; omega) temp temp)
        (derivesSub_seq_zero_left (by simpa [WordInst.instSelectExp] using he1)
          (derivesSub_inst defs terminal _))
    | lookup s =>
      have he1 := ih (.lookup s) (by simp_wf; omega) (temp + 1) (temp + 1)
      simp only [WordInst.instSelectExp]
      exact derivesSub_seq_zero_left (ih exp (by simp_wf; omega) temp temp)
        (derivesSub_seq_zero_left (by simpa [WordInst.instSelectExp] using he1)
          (derivesSub_inst defs terminal _))
    | load a =>
      have he1 := ih (.load a) (by simp_wf; omega) (temp + 1) (temp + 1)
      simp only [WordInst.instSelectExp]
      exact derivesSub_seq_zero_left (ih exp (by simp_wf; omega) temp temp)
        (derivesSub_seq_zero_left he1 (derivesSub_inst defs terminal _))
    | op bop ls =>
      have he1 := ih (.op bop ls) (by simp_wf; omega) (temp + 1) (temp + 1)
      simp only [WordInst.instSelectExp]
      exact derivesSub_seq_zero_left (ih exp (by simp_wf; omega) temp temp)
        (derivesSub_seq_zero_left he1 (derivesSub_inst defs terminal _))
    | shift sh2 a b =>
      have he1 := ih (.shift sh2 a b) (by simp_wf; omega) (temp + 1) (temp + 1)
      simp only [WordInst.instSelectExp]
      exact derivesSub_seq_zero_left (ih exp (by simp_wf; omega) temp temp)
        (derivesSub_seq_zero_left he1 (derivesSub_inst defs terminal _))

theorem instSelectExecutable_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (c : AsmConfigExact width) (temp : Nat)
    {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : Derives defs terminal p e) :
    DerivesSub defs terminal (WordInst.instSelectExecutable c temp p) e := by
  induction hp with
  | normal p h =>
    cases p with
    | skip | move _ _ | inst _ | get _ _ | opCurrHeap _ _ _ | locValue _ _
    | storeConsts _ _ _ _ _ | codeBufferWrite _ _ | dataBufferWrite _ _ =>
      exact derivesSub_normal defs terminal _ h
    | assign v exp =>
      simpa [WordInst.instSelectExecutable] using
        instSelectExp_derivesSub defs terminal c v temp _
    | set store exp =>
      simp only [WordInst.instSelectExecutable]
      exact derivesSub_seq_zero_left (instSelectExp_derivesSub defs terminal c temp temp _)
        (derivesSub_normal defs terminal _)
    | store exp var =>
      simp only [WordInst.instSelectExecutable]
      cases WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable exp) with
      | op op args =>
        cases op with
        | add =>
          cases args with
          | cons exp' rest =>
            cases rest with
            | cons e2 rest2 =>
              cases e2 with
              | const w =>
                cases rest2 with
                | nil =>
                  dsimp only
                  split
                  · exact derivesSub_seq_zero_left (instSelectExp_derivesSub defs terminal c temp temp _)
                      (derivesSub_normal defs terminal _)
                  · exact derivesSub_seq_zero_left (instSelectExp_derivesSub defs terminal c temp temp _)
                      (derivesSub_normal defs terminal _)
                | cons _ _ =>
                  exact derivesSub_seq_zero_left (instSelectExp_derivesSub defs terminal c temp temp _)
                    (derivesSub_normal defs terminal _)
              | _ =>
                exact derivesSub_seq_zero_left (instSelectExp_derivesSub defs terminal c temp temp _)
                  (derivesSub_normal defs terminal _)
            | nil =>
              exact derivesSub_seq_zero_left (instSelectExp_derivesSub defs terminal c temp temp _)
                (derivesSub_normal defs terminal _)
          | nil =>
            exact derivesSub_seq_zero_left (instSelectExp_derivesSub defs terminal c temp temp _)
              (derivesSub_normal defs terminal _)
        | _ =>
          exact derivesSub_seq_zero_left (instSelectExp_derivesSub defs terminal c temp temp _)
            (derivesSub_normal defs terminal _)
      | _ =>
        exact derivesSub_seq_zero_left (instSelectExp_derivesSub defs terminal c temp temp _)
          (derivesSub_normal defs terminal _)
    | tick | shareInst _ _ _ | raise _ | «return» _ _ | ffi _ _ _ _ _ _
    | «break» _ | «continue» _ | seq _ _ | ite _ _ _ _ _ | loop _ _ _
    | alloc _ _ | install _ _ _ _ _ | mustTerminate _ =>
      simp [erase] at h
    | call ret dest args handler =>
      rcases ret with _ | ⟨_, _, _, _, _⟩ <;> rcases handler with _ | ⟨_, _, _, _⟩ <;>
        simp [erase] at h
  | tick => exact ⟨_, Derives.tick, subeffects_refl _⟩
  | share op reg exp =>
    simp only [WordInst.instSelectExecutable]
    have hshare : ∀ exp' : WordLangExpHOL (BitVec width),
        DerivesSub defs terminal (.shareInst op reg exp')
          (merge (atom .fall 1) (atom .final 1)) :=
      fun exp' => ⟨_, Derives.share op reg exp', subeffects_refl _⟩
    cases WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable exp) with
    | op bop args =>
      cases bop with
      | add =>
        cases args with
        | cons exp' rest =>
          cases rest with
          | cons e2 rest2 =>
            cases e2 with
            | const w =>
              cases rest2 with
              | nil =>
                dsimp only
                split
                · exact derivesSub_seq_zero_left (instSelectExp_derivesSub defs terminal c temp temp _)
                    (hshare _)
                · exact derivesSub_seq_zero_left (instSelectExp_derivesSub defs terminal c temp temp _)
                    (hshare _)
              | cons _ _ =>
                exact derivesSub_seq_zero_left (instSelectExp_derivesSub defs terminal c temp temp _)
                  (hshare _)
            | _ =>
              exact derivesSub_seq_zero_left (instSelectExp_derivesSub defs terminal c temp temp _)
                (hshare _)
          | nil =>
            exact derivesSub_seq_zero_left (instSelectExp_derivesSub defs terminal c temp temp _)
              (hshare _)
        | nil =>
          exact derivesSub_seq_zero_left (instSelectExp_derivesSub defs terminal c temp temp _)
            (hshare _)
      | _ =>
        exact derivesSub_seq_zero_left (instSelectExp_derivesSub defs terminal c temp temp _)
          (hshare _)
    | _ =>
      exact derivesSub_seq_zero_left (instSelectExp_derivesSub defs terminal c temp temp _)
        (hshare _)
  | raise reg => exact ⟨_, Derives.raise reg, subeffects_refl _⟩
  | result reg regs => exact ⟨_, Derives.result reg regs, subeffects_refl _⟩
  | breakTo label => exact ⟨_, Derives.breakTo label, subeffects_refl _⟩
  | continueTo label => exact ⟨_, Derives.continueTo label, subeffects_refl _⟩
  | ffi name r1 l1 r2 l2 names => exact ⟨_, Derives.ffi name r1 l1 r2 l2 names, subeffects_refl _⟩
  | seq _ _ ih1 ih2 => exact derivesSub_seq ih1 ih2
  | branch cmp reg operand _ _ ih1 ih2 => exact derivesSub_branch cmp reg operand ih1 ih2
  | loop names exits _ cycle ih => exact derivesSub_loop names exits ih cycle
  | tail dest args => exact ⟨_, Derives.tail dest args, subeffects_refl _⟩
  | returning names live next l1 l2 dest args handler _ _ _ _ ihCont ihHand =>
    cases handler with
    | none => exact derivesSub_returning_none names live l1 l2 dest args ihCont
    | some h =>
      rcases h with ⟨hname, hbody, h1, h2⟩
      exact derivesSub_returning_some names live l1 l2 dest args hname h1 h2 ihCont
        (ihHand hname hbody h1 h2 rfl)

/-! ## Pass 3: `WordAlloc.fullSsaCcTrans` -/

theorem fakeMove_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool) (v : Nat) :
    DerivesSub defs terminal (WordAlloc.fakeMove (width := width) v) (atom .fall 0) :=
  derivesSub_inst defs terminal (.const v 0)

theorem fakeMoves_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (prio : Option (Unit ⊕ Unit)) (ls : List Nat) (ssaL ssaR : Spt Nat) (na : Nat) :
    DerivesSub defs terminal (WordAlloc.fakeMoves (width := width) prio ls ssaL ssaR na).1 (atom .fall 0) ∧
      DerivesSub defs terminal (WordAlloc.fakeMoves (width := width) prio ls ssaL ssaR na).2.1 (atom .fall 0) := by
  induction ls with
  | nil =>
    exact ⟨derivesSub_skip defs terminal, derivesSub_skip defs terminal⟩
  | cons x xs ih =>
    rcases hrec : WordAlloc.fakeMoves (width := width) prio xs ssaL ssaR na with
      ⟨seqL, seqR, na', ssaL', ssaR'⟩
    simp only [hrec] at ih
    simp only [WordAlloc.fakeMoves, hrec]
    cases sptLookup x ssaL' <;> cases sptLookup x ssaR'
    · exact ih
    · exact ⟨derivesSub_seq_zero_left ih.1 (fakeMove_derivesSub defs terminal _),
        derivesSub_seq_zero_left ih.2 (derivesSub_normal defs terminal _)⟩
    · exact ⟨derivesSub_seq_zero_left ih.1 (derivesSub_normal defs terminal _),
        derivesSub_seq_zero_left ih.2 (fakeMove_derivesSub defs terminal _)⟩
    · exact ih

theorem fixInconsistencies_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (prio : Option (Unit ⊕ Unit)) (ssaL ssaR : Spt Nat) (na : Nat) :
    DerivesSub defs terminal (WordAlloc.fixInconsistencies (width := width) prio ssaL ssaR na).1 (atom .fall 0) ∧
      DerivesSub defs terminal (WordAlloc.fixInconsistencies (width := width) prio ssaL ssaR na).2.1 (atom .fall 0) := by
  unfold WordAlloc.fixInconsistencies
  dsimp only
  rcases hmerge : WordAlloc.mergeMoves ((sptToAList (sptUnion ssaL ssaR)).map Prod.fst) ssaL ssaR na with
    ⟨lmov, rmov, na', ssaL', ssaR'⟩
  have hf := fakeMoves_derivesSub (width := width) defs terminal prio
    ((sptToAList (sptUnion ssaL ssaR)).map Prod.fst) ssaL' ssaR' na'
  rcases hfake : WordAlloc.fakeMoves (width := width) prio
      ((sptToAList (sptUnion ssaL ssaR)).map Prod.fst) ssaL' ssaR' na' with
    ⟨lseq, rseq, na'', ssaL'', ssaR''⟩
  simp only [hfake] at hf ⊢
  exact ⟨derivesSub_seq_zero_left (derivesSub_normal defs terminal _) hf.1,
    derivesSub_seq_zero_left (derivesSub_normal defs terminal _) hf.2⟩

theorem listNextVarRenameMove_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (ssa : Spt Nat) (n : Nat) (ls : List Nat) :
    DerivesSub defs terminal (WordAlloc.listNextVarRenameMove (width := width) ssa n ls).1 (atom .fall 0) := by
  unfold WordAlloc.listNextVarRenameMove
  exact derivesSub_normal defs terminal _

theorem ssaReconcile_derivesSub {width : Nat} [NeZero width] {β : Type}
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (curSsa tgtSsa : Spt Nat) (ns : Spt β) :
    DerivesSub defs terminal (WordAlloc.ssaReconcile (width := width) curSsa tgtSsa ns) (atom .fall 0) := by
  unfold WordAlloc.ssaReconcile
  dsimp only
  split
  · exact derivesSub_skip defs terminal
  · exact derivesSub_normal defs terminal _

theorem foldr_fakeMove_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (rs : List Nat) :
    DerivesSub defs terminal
      ((rs.map fun r => WordAlloc.fakeMove (width := width) r).foldr .seq .skip) (atom .fall 0) := by
  induction rs with
  | nil => exact derivesSub_skip defs terminal
  | cons r rs ih =>
    exact derivesSub_seq_zero_left (fakeMove_derivesSub defs terminal r) ih

theorem loopSetup_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (names exitNames : Spt Unit) (ssa : Spt Nat) (na : Nat) :
    DerivesSub defs terminal (WordAlloc.loopSetup (width := width) names exitNames ssa na).1 (atom .fall 0) := by
  unfold WordAlloc.loopSetup
  dsimp only
  exact derivesSub_seq_zero_left (foldr_fakeMove_derivesSub defs terminal _)
    (listNextVarRenameMove_derivesSub defs terminal _ _ _)

theorem ssaCcTransInst_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (inst : WordLangInst (BitVec width)) (ssa : Spt Nat) (na : Nat) :
    DerivesSub defs terminal (WordAlloc.ssaCcTransInst inst ssa na).1 (atom .fall 0) := by
  cases inst with
  | skip =>
    simpa [WordAlloc.ssaCcTransInst] using derivesSub_skip defs terminal
  | const reg w =>
    simpa [WordAlloc.ssaCcTransInst] using derivesSub_inst defs terminal _
  | arith a =>
    cases a with
    | binop bop r1 r2 ri =>
      cases ri <;> simpa [WordAlloc.ssaCcTransInst] using derivesSub_inst defs terminal _
    | shift sh r1 r2 ri =>
      cases ri with
      | reg r3 =>
        simp only [WordAlloc.ssaCcTransInst]
        exact derivesSub_seq_zero_left (derivesSub_move defs terminal _ _)
          (derivesSub_inst defs terminal _)
      | imm _ =>
        simpa [WordAlloc.ssaCcTransInst] using derivesSub_inst defs terminal _
    | div r1 r2 r3 =>
      simpa [WordAlloc.ssaCcTransInst] using derivesSub_inst defs terminal _
    | addCarry r1 r2 r3 r4 =>
      simp only [WordAlloc.ssaCcTransInst]
      exact derivesSub_seq_zero_left (derivesSub_move defs terminal _ _)
        (derivesSub_seq_zero_left (derivesSub_inst defs terminal _)
          (derivesSub_move defs terminal _ _))
    | addOverflow r1 r2 r3 r4 =>
      simp only [WordAlloc.ssaCcTransInst]
      exact derivesSub_seq_zero_left (derivesSub_inst defs terminal _)
        (derivesSub_move defs terminal _ _)
    | subOverflow r1 r2 r3 r4 =>
      simp only [WordAlloc.ssaCcTransInst]
      exact derivesSub_seq_zero_left (derivesSub_inst defs terminal _)
        (derivesSub_move defs terminal _ _)
    | longMul r1 r2 r3 r4 =>
      simp only [WordAlloc.ssaCcTransInst]
      exact derivesSub_seq_zero_left (derivesSub_move defs terminal _ _)
        (derivesSub_seq_zero_left (derivesSub_inst defs terminal _)
          (derivesSub_move defs terminal _ _))
    | longDiv r1 r2 r3 r4 r5 =>
      simp only [WordAlloc.ssaCcTransInst]
      exact derivesSub_seq_zero_left (derivesSub_move defs terminal _ _)
        (derivesSub_seq_zero_left (derivesSub_inst defs terminal _)
          (derivesSub_move defs terminal _ _))
  | mem op r addr =>
    rcases addr with ⟨a, w⟩
    cases op <;> simpa [WordAlloc.ssaCcTransInst] using derivesSub_inst defs terminal _

theorem ssaCcTrans_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : Derives defs terminal p e) :
    ∀ (ssa : Spt Nat) (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      DerivesSub defs terminal (WordAlloc.ssaCcTrans p ssa na lt).1 e := by
  induction hp with
  | normal p h =>
    intro ssa na lt
    cases p with
    | skip => simpa [WordAlloc.ssaCcTrans] using derivesSub_skip defs terminal
    | move pri ls => simpa [WordAlloc.ssaCcTrans] using derivesSub_move defs terminal _ _
    | storeConsts a b c d ws =>
      simp only [WordAlloc.ssaCcTrans]
      exact derivesSub_seq_zero_left (derivesSub_move defs terminal _ _)
        (derivesSub_seq_zero_left (derivesSub_normal defs terminal _ (by simp))
          (derivesSub_move defs terminal _ _))
    | inst i =>
      simpa [WordAlloc.ssaCcTrans] using ssaCcTransInst_derivesSub defs terminal i ssa na
    | assign num exp =>
      simpa [WordAlloc.ssaCcTrans] using derivesSub_normal defs terminal _ (by simp)
    | get num store =>
      simpa [WordAlloc.ssaCcTrans] using derivesSub_normal defs terminal _ (by simp)
    | store exp num =>
      simpa [WordAlloc.ssaCcTrans] using derivesSub_normal defs terminal _ (by simp)
    | opCurrHeap b dst src =>
      simpa [WordAlloc.ssaCcTrans] using derivesSub_normal defs terminal _ (by simp)
    | locValue r l1 =>
      simpa [WordAlloc.ssaCcTrans] using derivesSub_normal defs terminal _ (by simp)
    | set n exp =>
      simpa [WordAlloc.ssaCcTrans] using derivesSub_normal defs terminal _ (by simp)
    | codeBufferWrite r1 r2 =>
      simpa [WordAlloc.ssaCcTrans] using derivesSub_normal defs terminal _ (by simp)
    | dataBufferWrite r1 r2 =>
      simpa [WordAlloc.ssaCcTrans] using derivesSub_normal defs terminal _ (by simp)
    | tick | shareInst _ _ _ | raise _ | «return» _ _ | ffi _ _ _ _ _ _
    | «break» _ | «continue» _ | seq _ _ | ite _ _ _ _ _ | loop _ _ _
    | alloc _ _ | install _ _ _ _ _ | mustTerminate _ =>
      simp [erase] at h
    | call ret dest args handler =>
      rcases ret with _ | ⟨_, _, _, _, _⟩ <;> rcases handler with _ | ⟨_, _, _, _⟩ <;>
        simp [erase] at h
  | tick => intro ssa na lt; exact ⟨_, Derives.tick, subeffects_refl _⟩
  | share op reg exp =>
    intro ssa na lt
    simp only [WordAlloc.ssaCcTrans]
    split
    · exact ⟨_, Derives.share op _ _, subeffects_refl _⟩
    · exact ⟨_, Derives.share op _ _, subeffects_refl _⟩
  | raise reg =>
    intro ssa na lt
    simp only [WordAlloc.ssaCcTrans]
    exact derivesSub_seq_zero_left (derivesSub_normal defs terminal _)
      ⟨_, Derives.raise 2, subeffects_refl _⟩
  | result reg regs =>
    intro ssa na lt
    simp only [WordAlloc.ssaCcTrans]
    exact derivesSub_seq_zero_left (derivesSub_normal defs terminal _)
      ⟨_, Derives.result _ _, subeffects_refl _⟩
  | breakTo label =>
    intro ssa na lt
    simp only [WordAlloc.ssaCcTrans]
    cases lt[label]? with
    | none => exact ⟨_, Derives.breakTo label, subeffects_refl _⟩
    | some val =>
      rcases val with ⟨tgtSsa, _names, exitNames⟩
      have hrec := ssaReconcile_derivesSub (width := width) defs terminal ssa tgtSsa exitNames
      dsimp only
      split
      · exact ⟨_, Derives.breakTo label, subeffects_refl _⟩
      · exact derivesSub_seq_zero_left hrec ⟨_, Derives.breakTo label, subeffects_refl _⟩
  | continueTo label =>
    intro ssa na lt
    simp only [WordAlloc.ssaCcTrans]
    cases lt[label]? with
    | none => exact ⟨_, Derives.continueTo label, subeffects_refl _⟩
    | some val =>
      rcases val with ⟨tgtSsa, names, _exitNames⟩
      have hrec := ssaReconcile_derivesSub (width := width) defs terminal ssa tgtSsa names
      dsimp only
      split
      · exact ⟨_, Derives.continueTo label, subeffects_refl _⟩
      · exact derivesSub_seq_zero_left hrec ⟨_, Derives.continueTo label, subeffects_refl _⟩
  | ffi name r1 l1 r2 l2 names =>
    intro ssa na lt
    simp only [WordAlloc.ssaCcTrans]
    exact derivesSub_seq_zero_left (listNextVarRenameMove_derivesSub defs terminal _ _ _)
      (derivesSub_seq_zero_left (derivesSub_normal defs terminal _)
        (derivesSub_seq_zero_right ⟨_, Derives.ffi name 2 4 6 8 _, subeffects_refl _⟩
          (listNextVarRenameMove_derivesSub defs terminal _ _ _)))
  | seq _ _ ih1 ih2 =>
    intro ssa na lt
    simp only [WordAlloc.ssaCcTrans]
    exact derivesSub_seq (ih1 ssa na lt) (ih2 _ _ lt)
  | @branch cmp reg operand e2 e3 a b _ _ ih1 ih2 =>
    intro ssa na lt
    simp only [WordAlloc.ssaCcTrans]
    rcases hr1 : WordAlloc.ssaCcTrans e2 ssa na lt with ⟨e2', ssa2, na2⟩
    rcases hr2 : WordAlloc.ssaCcTrans e3 ssa na2 lt with ⟨e3', ssa3, na3⟩
    have h1 : DerivesSub defs terminal e2' a := by simpa [hr1] using ih1 ssa na lt
    have h2 : DerivesSub defs terminal e3' b := by simpa [hr2] using ih2 ssa na2 lt
    have hfix := fixInconsistencies_derivesSub (width := width) defs terminal
      (WordAlloc.mkPrio e2' e3') ssa2 ssa3 na3
    rcases hfx : WordAlloc.fixInconsistencies (width := width)
        (WordAlloc.mkPrio e2' e3') ssa2 ssa3 na3 with ⟨e2Cons, e3Cons, naFin, ssaFin⟩
    simp only [hfx] at hfix
    exact derivesSub_branch cmp _ _
      (derivesSub_seq_zero_right h1 hfix.1)
      (derivesSub_seq_zero_right h2 hfix.2)
  | @loop names exits body eff _ cycle ih =>
    intro ssa na lt
    simp only [WordAlloc.ssaCcTrans]
    have hsetup := loopSetup_derivesSub (width := width) defs terminal names exits ssa na
    rcases hls : WordAlloc.loopSetup (width := width) names exits ssa na with
      ⟨setupProg, ssaRefreshed, naRefreshed⟩
    simp only [hls] at hsetup
    rcases hbd : WordAlloc.ssaCcTrans body (sptInter ssaRefreshed names) naRefreshed
        ((ssaRefreshed, names, exits) :: lt) with ⟨body', ssa', na'⟩
    have hbody : DerivesSub defs terminal body' eff := by
      simpa [hbd] using ih (sptInter ssaRefreshed names) naRefreshed
        ((ssaRefreshed, names, exits) :: lt)
    have hback := ssaReconcile_derivesSub (width := width) defs terminal
      ssa' ssaRefreshed names
    have hbodyFinal : DerivesSub defs terminal
        (match WordAlloc.ssaReconcile (width := width) ssa' ssaRefreshed names with
         | .skip => body'
         | _ => .seq body'
             (WordAlloc.ssaReconcile (width := width) ssa' ssaRefreshed names)) eff := by
      split
      · exact hbody
      · exact derivesSub_seq_zero_right hbody hback
    exact derivesSub_seq_zero_left hsetup (derivesSub_loop _ _ hbodyFinal cycle)
  | tail dest args =>
    intro ssa na lt
    simp only [WordAlloc.ssaCcTrans]
    exact derivesSub_seq_zero_left (derivesSub_normal defs terminal _)
      ⟨_, Derives.tail dest _, subeffects_refl _⟩
  | returning names live next l1 l2 dest args handler contEffects handlerEffects _ _ ihCont ihHand =>
    intro ssa na lt
    cases handler with
    | none =>
      simp only [WordAlloc.ssaCcTrans]
      rcases hsm : WordAlloc.listNextVarRenameMove (width := width) ssa (na + 2)
          ((sptToAList (sptUnion live.1 live.2)).map Prod.fst) with ⟨stackMov, ssa', na'⟩
      rcases hrm : WordAlloc.listNextVarRenameMove (width := width)
          (sptInter ssa' (sptUnion live.1 live.2)) (na' + 2)
          ((sptToAList (sptUnion live.1 live.2)).map Prod.fst) with ⟨retMov, ssa'', na''⟩
      rcases hrv : WordAlloc.listNextVarRename names ssa'' na'' with ⟨ret', ssa2p, na2p⟩
      rcases hrc : WordAlloc.ssaCcTrans next ssa2p na2p lt with ⟨renRetHandler, ssa2, na2⟩
      have hsm_d : DerivesSub defs terminal stackMov (atom .fall 0) := by
        have h := listNextVarRenameMove_derivesSub (width := width) defs terminal ssa (na + 2)
          ((sptToAList (sptUnion live.1 live.2)).map Prod.fst)
        simpa [hsm] using h
      have hrm_d : DerivesSub defs terminal retMov (atom .fall 0) := by
        have h := listNextVarRenameMove_derivesSub (width := width) defs terminal
          (sptInter ssa' (sptUnion live.1 live.2)) (na' + 2)
          ((sptToAList (sptUnion live.1 live.2)).map Prod.fst)
        simpa [hrm] using h
      have hcont_d : DerivesSub defs terminal renRetHandler contEffects := by
        simpa [hrc] using ihCont ssa2p na2p lt
      let regs := (List.range names.length).map fun x => 2 * (x + 1)
      have hmovRet := derivesSub_seq_zero_left hrm_d
        (derivesSub_seq_zero_left (derivesSub_move defs terminal 1 (ret'.zip regs)) hcont_d)
      exact derivesSub_seq_zero_left hsm_d
        (derivesSub_seq_zero_left (derivesSub_move defs terminal _ _)
          (derivesSub_returning_none _ _ l1 l2 dest _ hmovRet))
    | some h =>
      rcases h with ⟨hname, hbody, h1, h2⟩
      simp only [WordAlloc.ssaCcTrans]
      rcases hsm : WordAlloc.listNextVarRenameMove (width := width) ssa (na + 2)
          ((sptToAList (sptUnion live.1 live.2)).map Prod.fst) with ⟨stackMov, ssa', na'⟩
      rcases hrm : WordAlloc.listNextVarRenameMove (width := width)
          (sptInter ssa' (sptUnion live.1 live.2)) (na' + 2)
          ((sptToAList (sptUnion live.1 live.2)).map Prod.fst) with ⟨retMov, ssa'', na''⟩
      rcases hrv : WordAlloc.listNextVarRename names ssa'' na'' with ⟨ret', ssa2p, na2p⟩
      rcases hrc : WordAlloc.ssaCcTrans next ssa2p na2p lt with ⟨renRetHandler, ssa2, na2⟩
      rcases hnv : WordAlloc.nextVarRename hname ssa'' na2 with ⟨n', ssa3p, na3p⟩
      rcases hre : WordAlloc.ssaCcTrans hbody ssa3p na3p lt with ⟨renExcHandler, ssa3, na3⟩
      have hsm_d : DerivesSub defs terminal stackMov (atom .fall 0) := by
        have h := listNextVarRenameMove_derivesSub (width := width) defs terminal ssa (na + 2)
          ((sptToAList (sptUnion live.1 live.2)).map Prod.fst)
        simpa [hsm] using h
      have hrm_d : DerivesSub defs terminal retMov (atom .fall 0) := by
        have h := listNextVarRenameMove_derivesSub (width := width) defs terminal
          (sptInter ssa' (sptUnion live.1 live.2)) (na' + 2)
          ((sptToAList (sptUnion live.1 live.2)).map Prod.fst)
        simpa [hrm] using h
      have hcont_d : DerivesSub defs terminal renRetHandler contEffects := by
        simpa [hrc] using ihCont ssa2p na2p lt
      have hexc_d : DerivesSub defs terminal renExcHandler handlerEffects := by
        simpa [hre] using ihHand hname hbody h1 h2 rfl ssa3p na3p lt
      let regs := (List.range names.length).map fun x => 2 * (x + 1)
      let movRetHandler := WordLangProgHOL.seq retMov (.seq (.move 1 (ret'.zip regs)) renRetHandler)
      let movExcHandler := WordLangProgHOL.seq retMov (.seq (.move 1 [(n', 2)]) renExcHandler)
      have hmovRet : DerivesSub defs terminal movRetHandler contEffects :=
        derivesSub_seq_zero_left hrm_d
          (derivesSub_seq_zero_left (derivesSub_move defs terminal 1 (ret'.zip regs)) hcont_d)
      have hmovExc : DerivesSub defs terminal movExcHandler handlerEffects :=
        derivesSub_seq_zero_left hrm_d
          (derivesSub_seq_zero_left (derivesSub_move defs terminal 1 [(n', 2)]) hexc_d)
      have hfix := fixInconsistencies_derivesSub (width := width) defs terminal
        (WordAlloc.mkPrio movRetHandler movExcHandler) ssa2 ssa3 na3
      rcases hfx : WordAlloc.fixInconsistencies (width := width)
          (WordAlloc.mkPrio movRetHandler movExcHandler) ssa2 ssa3 na3 with
        ⟨retCons, excCons, naFin, ssaFin⟩
      simp only [hfx] at hfix
      exact derivesSub_seq_zero_left hsm_d
        (derivesSub_seq_zero_left (derivesSub_move defs terminal _ _)
          (derivesSub_returning_some _ _ l1 l2 dest _ 2 h1 h2
            (derivesSub_seq_zero_right hmovRet hfix.1)
            (derivesSub_seq_zero_right hmovExc hfix.2)))

theorem fullSsaCcTrans_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (arity : Nat) {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : DerivesSub defs terminal p e) :
    DerivesSub defs terminal (WordAlloc.fullSsaCcTrans arity p) e := by
  obtain ⟨ef, hd, hs⟩ := hp
  unfold WordAlloc.fullSsaCcTrans
  have hmov : DerivesSub defs terminal
      (WordAlloc.setupSSA (outputWidth := width) arity (WordAlloc.limitVar p) p).1 (atom .fall 0) := by
    unfold WordAlloc.setupSSA
    dsimp only
    rcases WordAlloc.listNextVarRename (WordAlloc.evenList arity) .ln (WordAlloc.limitVar p) with
      ⟨names, ssa, next⟩
    exact derivesSub_normal defs terminal _
  exact derivesSub_mono
    (derivesSub_seq_zero_left hmov (ssaCcTrans_derivesSub defs terminal hd _ _ [])) hs

/-! ## Pass 4 & 9: `Flapjack.WordAlloc.removeDeadProg` -/

theorem merge_atom_fall_zero_self :
    Subeffects (atom .fall 0) (merge (atom .fall 0) (atom .fall 0)) :=
  subeffects_merge_left (atom .fall 0) (atom .fall 0)

theorem removeDead_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : Derives defs terminal p e) :
    ∀ (live : Spt Unit) (nlive : List WordStoreHOL)
      (lt : List (Spt Unit × Spt Unit)),
      DerivesSub defs terminal (Flapjack.WordAlloc.removeDead p live nlive lt).1 e ∧
        ((Flapjack.WordAlloc.removeDead p live nlive lt).1 = .skip →
          Subeffects (atom .fall 0) e) := by
  induction hp with
  | normal p h =>
    intro live nlive lt
    have hsub : Subeffects (atom .fall 0) (atom .fall 0) := subeffects_refl _
    refine ⟨?_, fun _ => hsub⟩
    cases p with
    | skip => simpa [Flapjack.WordAlloc.removeDead] using derivesSub_skip defs terminal
    | move pri ls =>
      simp only [Flapjack.WordAlloc.removeDead]
      split <;> exact derivesSub_normal defs terminal _
    | inst i =>
      simp only [Flapjack.WordAlloc.removeDead]
      split <;> exact derivesSub_normal defs terminal _
    | get num store =>
      simp only [Flapjack.WordAlloc.removeDead]
      split <;> exact derivesSub_normal defs terminal _
    | opCurrHeap b num src =>
      simp only [Flapjack.WordAlloc.removeDead]
      split <;> exact derivesSub_normal defs terminal _
    | locValue r l1 =>
      simp only [Flapjack.WordAlloc.removeDead]
      split <;> exact derivesSub_normal defs terminal _
    | set storeName exp =>
      cases exp with
      | var r =>
        simp only [Flapjack.WordAlloc.removeDead]
        split <;> exact derivesSub_normal defs terminal _
      | const _ | lookup _ | load _ | op _ _ | shift _ _ _ =>
        simpa [Flapjack.WordAlloc.removeDead] using derivesSub_normal defs terminal _ (by simp)
    | assign _ _ | store _ _ | storeConsts _ _ _ _ _
    | codeBufferWrite _ _ | dataBufferWrite _ _ =>
      simpa [Flapjack.WordAlloc.removeDead] using derivesSub_normal defs terminal _ h
    | tick | shareInst _ _ _ | raise _ | «return» _ _ | ffi _ _ _ _ _ _
    | «break» _ | «continue» _ | seq _ _ | ite _ _ _ _ _ | loop _ _ _
    | alloc _ _ | install _ _ _ _ _ | mustTerminate _ =>
      simp [erase] at h
    | call ret dest args handler =>
      rcases ret with _ | ⟨_, _, _, _, _⟩ <;> rcases handler with _ | ⟨_, _, _, _⟩ <;>
        simp [erase] at h
  | tick =>
    intro live nlive lt
    simp only [Flapjack.WordAlloc.removeDead]
    exact ⟨⟨_, Derives.tick, subeffects_refl _⟩, fun hs => by cases hs⟩
  | share op reg exp =>
    intro live nlive lt
    simp only [Flapjack.WordAlloc.removeDead]
    exact ⟨⟨_, Derives.share op reg exp, subeffects_refl _⟩, fun hs => by cases hs⟩
  | raise reg =>
    intro live nlive lt
    simp only [Flapjack.WordAlloc.removeDead]
    exact ⟨⟨_, Derives.raise reg, subeffects_refl _⟩, fun hs => by cases hs⟩
  | result reg regs =>
    intro live nlive lt
    simp only [Flapjack.WordAlloc.removeDead]
    exact ⟨⟨_, Derives.result reg regs, subeffects_refl _⟩, fun hs => by cases hs⟩
  | breakTo label =>
    intro live nlive lt
    simp only [Flapjack.WordAlloc.removeDead]
    exact ⟨⟨_, Derives.breakTo label, subeffects_refl _⟩, fun hs => by cases hs⟩
  | continueTo label =>
    intro live nlive lt
    simp only [Flapjack.WordAlloc.removeDead]
    exact ⟨⟨_, Derives.continueTo label, subeffects_refl _⟩, fun hs => by cases hs⟩
  | ffi name r1 l1 r2 l2 names =>
    intro live nlive lt
    simp only [Flapjack.WordAlloc.removeDead]
    exact ⟨⟨_, Derives.ffi name r1 l1 r2 l2 names, subeffects_refl _⟩, fun hs => by cases hs⟩
  | @seq p1 p2 a b _ _ ih1 ih2 =>
    intro live nlive lt
    simp only [Flapjack.WordAlloc.removeDead]
    rcases hr2 : Flapjack.WordAlloc.removeDead p2 live nlive lt with ⟨s2, s2live, s2nlive⟩
    have h2 := ih2 live nlive lt
    simp only [hr2] at h2
    rcases hr1 : Flapjack.WordAlloc.removeDead p1 s2live s2nlive lt with ⟨s1, s1live, s1nlive⟩
    have h1 := ih1 s2live s2nlive lt
    simp only [hr1] at h1
    dsimp only
    cases s1 with
    | skip =>
      have ha : Subeffects (atom .fall 0) a := h1.2 rfl
      refine ⟨derivesSub_mono h2.1 (subeffects_trans (seq_atom_fall_zero_left_rev b)
        (subeffects_seq ha (subeffects_refl b))), fun hs2 => ?_⟩
      have hb : Subeffects (atom .fall 0) b := h2.2 hs2
      exact subeffects_trans (seq_atom_fall_zero_left_rev (atom .fall 0)) (subeffects_seq ha hb)
    | _ =>
      cases s2 with
      | skip =>
        have hb : Subeffects (atom .fall 0) b := h2.2 rfl
        refine ⟨derivesSub_mono h1.1 (subeffects_trans (seq_atom_fall_zero_right_rev a)
          (subeffects_seq (subeffects_refl a) hb)), fun hs1 => by simp at hs1⟩
      | _ =>
        exact ⟨derivesSub_seq h1.1 h2.1, fun hs => by simp at hs⟩
  | @branch cmp reg operand p1 p2 a b _ _ ih1 ih2 =>
    intro live nlive lt
    simp only [Flapjack.WordAlloc.removeDead]
    rcases hr1 : Flapjack.WordAlloc.removeDead p1 live nlive lt with ⟨s1, s1live, s1nlive⟩
    rcases hr2 : Flapjack.WordAlloc.removeDead p2 live nlive lt with ⟨s2, s2live, s2nlive⟩
    have h1 := ih1 live nlive lt
    have h2 := ih2 live nlive lt
    simp only [hr1] at h1
    simp only [hr2] at h2
    dsimp only
    cases s1 with
    | skip =>
      cases s2 with
      | skip =>
        have hsub : Subeffects (atom .fall 0) (merge a b) :=
          subeffects_trans merge_atom_fall_zero_self (subeffects_merge (h1.2 rfl) (h2.2 rfl))
        exact ⟨derivesSub_mono (derivesSub_skip defs terminal) hsub, fun _ => hsub⟩
      | _ =>
        exact ⟨derivesSub_branch cmp reg operand h1.1 h2.1, fun hs => by simp at hs⟩
    | _ =>
      exact ⟨derivesSub_branch cmp reg operand h1.1 h2.1, fun hs => by simp at hs⟩
  | loop names exits _ cycle ih =>
    intro live nlive lt
    simp only [Flapjack.WordAlloc.removeDead]
    exact ⟨derivesSub_loop names exits (ih names [] ((names, exits) :: lt)).1 cycle,
      fun hs => by simp at hs⟩
  | tail dest args =>
    intro live nlive lt
    simp only [Flapjack.WordAlloc.removeDead]
    exact ⟨⟨_, Derives.tail dest args, subeffects_refl _⟩, fun hs => by cases hs⟩
  | returning names liveCut next l1 l2 dest args handler _ _ _ _ ihCont ihHand =>
    intro live nlive lt
    cases handler with
    | none =>
      simp only [Flapjack.WordAlloc.removeDead]
      exact ⟨derivesSub_returning_none names liveCut l1 l2 dest args (ihCont live nlive lt).1,
        fun hs => by simp at hs⟩
    | some h =>
      rcases h with ⟨hname, hbody, h1, h2⟩
      simp only [Flapjack.WordAlloc.removeDead]
      exact ⟨derivesSub_returning_some names liveCut l1 l2 dest args hname h1 h2
        (ihCont live nlive lt).1 (ihHand hname hbody h1 h2 rfl live nlive lt).1,
        fun hs => by simp at hs⟩

theorem removeDeadProg_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : DerivesSub defs terminal p e) :
    DerivesSub defs terminal (Flapjack.WordAlloc.removeDeadProg p) e := by
  obtain ⟨ef, hd, hs⟩ := hp
  exact derivesSub_mono (removeDead_derivesSub defs terminal hd .ln [] []).1 hs

/-! ## Pass 5: `WordCse.wordCommonSubexpElim` -/

theorem addToDataAux_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (data : WordCse.Knowledge) (dest : Nat) (key : List Nat)
    {orig : WordLangProgHOL (BitVec width)}
    (horig : erase orig = .skip) :
    DerivesSub defs terminal (WordCse.addToDataAux data dest key orig).2 (atom .fall 0) := by
  unfold WordCse.addToDataAux
  cases Misc.BalancedMap.lookup WordCse.listCmp key data.instrsMem with
  | some _ =>
    dsimp only
    split <;> exact derivesSub_normal defs terminal _
  | none =>
    dsimp only
    split <;> exact derivesSub_normal defs terminal _ horig

theorem addToLoadAux_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (data : WordCse.Knowledge) (dest : Nat) (key : List Nat)
    {orig : WordLangProgHOL (BitVec width)}
    (horig : erase orig = .skip) :
    DerivesSub defs terminal (WordCse.addToLoadAux data dest key orig).2 (atom .fall 0) := by
  unfold WordCse.addToLoadAux
  cases Misc.BalancedMap.lookup WordCse.listCmp key data.loadsMem with
  | some _ =>
    dsimp only
    split <;> exact derivesSub_normal defs terminal _
  | none =>
    dsimp only
    split <;> exact derivesSub_normal defs terminal _ horig

theorem addToDataConst_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (data : WordCse.Knowledge) (dest : Nat) (w : BitVec width) :
    DerivesSub defs terminal (WordCse.addToDataConst data dest w).2 (atom .fall 0) := by
  unfold WordCse.addToDataConst
  dsimp only
  cases Misc.BalancedMap.lookup WordCse.listCmp
      (WordCse.instToNumList (.const dest w)) data.instrsMem <;>
    exact derivesSub_normal defs terminal _

theorem wordCseInst_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (data : WordCse.Knowledge) (i : HolInst width) :
    DerivesSub defs terminal (WordCse.wordCseInst data i).2 (atom .fall 0) := by
  cases i with
  | skip =>
    simpa [WordCse.wordCseInst] using derivesSub_inst defs terminal _
  | const r w =>
    simp only [WordCse.wordCseInst]
    split
    · exact derivesSub_inst defs terminal _
    · exact addToDataConst_derivesSub defs terminal _ r w
  | arith a =>
    simp only [WordCse.wordCseInst]
    split
    · exact addToDataAux_derivesSub defs terminal _ _ _ (by simp)
    · exact derivesSub_inst defs terminal _
  | mem op r addr =>
    rcases addr with ⟨a, ofs⟩
    simp only [WordCse.wordCseInst]
    split
    · exact derivesSub_inst defs terminal _
    · split
      · exact derivesSub_inst defs terminal _
      · exact addToLoadAux_derivesSub defs terminal _ _ _ (by simp)

theorem getClause_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (data : WordCse.Knowledge) (dest : Nat) (store : WordStoreHOL) :
    DerivesSub defs terminal (WordCse.getClause (width := width) data dest store).2 (atom .fall 0) := by
  unfold WordCse.getClause
  dsimp only
  cases (WordCse.invalidateData data dest).getsMem.lookup store with
  | none =>
    dsimp only
    split <;> exact derivesSub_normal defs terminal _
  | some _ =>
    dsimp only
    split <;> exact derivesSub_normal defs terminal _

theorem setClause_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (data : WordCse.Knowledge) (store : WordStoreHOL) (exp : WordLangExpHOL (BitVec width)) :
    DerivesSub defs terminal (WordCse.setClause data store exp).2 (atom .fall 0) := by
  unfold WordCse.setClause
  split
  · exact derivesSub_normal defs terminal _
  · dsimp only
    cases WordCse.destVar exp with
    | none => exact derivesSub_normal defs terminal _
    | some _ =>
      dsimp only
      split <;> exact derivesSub_normal defs terminal _

theorem wordCse_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : Derives defs terminal p e) :
    ∀ data : WordCse.Knowledge,
      DerivesSub defs terminal (WordCse.wordCse data p).2 e := by
  induction hp with
  | normal p h =>
    intro data
    cases p with
    | skip => simpa [WordCse.wordCse] using derivesSub_skip defs terminal
    | move r rs => simpa [WordCse.wordCse] using derivesSub_move defs terminal r rs
    | inst i =>
      simpa [WordCse.wordCse] using wordCseInst_derivesSub defs terminal data (HolInst.ofWordLangInst i)
    | get r x => simpa [WordCse.wordCse] using getClause_derivesSub defs terminal data r x
    | set x exp => simpa [WordCse.wordCse] using setClause_derivesSub defs terminal data x exp
    | opCurrHeap b r1 r2 =>
      simp only [WordCse.wordCse]
      split
      · exact derivesSub_normal defs terminal _ (by simp)
      · exact addToDataAux_derivesSub defs terminal _ _ _ (by simp)
    | locValue r l =>
      simp only [WordCse.wordCse]
      exact addToDataAux_derivesSub defs terminal _ _ _ (by simp)
    | store _ _ | assign _ _ | codeBufferWrite _ _ | dataBufferWrite _ _
    | storeConsts _ _ _ _ _ =>
      simpa [WordCse.wordCse] using derivesSub_normal defs terminal _ h
    | tick | shareInst _ _ _ | raise _ | «return» _ _ | ffi _ _ _ _ _ _
    | «break» _ | «continue» _ | seq _ _ | ite _ _ _ _ _ | loop _ _ _
    | alloc _ _ | install _ _ _ _ _ | mustTerminate _ =>
      simp [erase] at h
    | call ret dest args handler =>
      rcases ret with _ | ⟨_, _, _, _, _⟩ <;> rcases handler with _ | ⟨_, _, _, _⟩ <;>
        simp [erase] at h
  | tick => intro _; exact ⟨_, Derives.tick, subeffects_refl _⟩
  | share op reg exp => intro _; exact ⟨_, Derives.share op reg exp, subeffects_refl _⟩
  | raise reg => intro _; exact ⟨_, Derives.raise reg, subeffects_refl _⟩
  | result reg regs => intro _; exact ⟨_, Derives.result reg regs, subeffects_refl _⟩
  | breakTo label => intro _; exact ⟨_, Derives.breakTo label, subeffects_refl _⟩
  | continueTo label => intro _; exact ⟨_, Derives.continueTo label, subeffects_refl _⟩
  | ffi name r1 l1 r2 l2 names =>
    intro _; exact ⟨_, Derives.ffi name r1 l1 r2 l2 names, subeffects_refl _⟩
  | seq _ _ ih1 ih2 =>
    intro data
    simp only [WordCse.wordCse]
    exact derivesSub_seq (ih1 data) (ih2 _)
  | branch cmp reg operand _ _ ih1 ih2 =>
    intro data
    simp only [WordCse.wordCse]
    exact derivesSub_branch cmp reg operand (ih1 data) (ih2 data)
  | loop names exits _ cycle ih =>
    intro _
    simp only [WordCse.wordCse]
    exact derivesSub_loop names exits (ih WordCse.emptyData) cycle
  | tail dest args =>
    intro _; exact ⟨_, Derives.tail dest args, subeffects_refl _⟩
  | returning names live next l1 l2 dest args handler contEffects handlerEffects cont handlers _ _ =>
    intro _
    exact ⟨_, Derives.returning names live next l1 l2 dest args handler contEffects
      handlerEffects cont handlers, subeffects_refl _⟩

theorem wordCommonSubexpElim_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : DerivesSub defs terminal p e) :
    DerivesSub defs terminal (WordCse.wordCommonSubexpElim p) e := by
  obtain ⟨ef, hd, hs⟩ := hp
  exact derivesSub_mono (wordCse_derivesSub defs terminal hd WordCse.emptyData) hs

/-! ## Pass 6: `WordCopy.copyProp` -/

theorem copyPropInst_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (i : WordLangInst (BitVec width)) (cs : WordCopy.CopyState) :
    DerivesSub defs terminal (WordCopy.copyPropInst i cs).1 (atom .fall 0) := by
  cases i with
  | skip => simpa [WordCopy.copyPropInst] using derivesSub_skip defs terminal
  | const reg w => simpa [WordCopy.copyPropInst] using derivesSub_inst defs terminal _
  | arith a =>
    cases a <;> simpa [WordCopy.copyPropInst] using derivesSub_inst defs terminal _
  | mem op r addr =>
    rcases addr with ⟨a, w⟩
    cases op <;> simpa [WordCopy.copyPropInst] using derivesSub_inst defs terminal _

theorem copyPropProg_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : Derives defs terminal p e) :
    ∀ cs : WordCopy.CopyState,
      DerivesSub defs terminal (WordCopy.copyPropProg p cs).1 e := by
  induction hp with
  | normal p h =>
    intro cs
    cases p with
    | skip => simpa [WordCopy.copyPropProg] using derivesSub_skip defs terminal
    | move pri xs =>
      simp only [WordCopy.copyPropProg]
      split <;> exact derivesSub_move defs terminal _ _
    | inst i => simpa [WordCopy.copyPropProg] using copyPropInst_derivesSub defs terminal i cs
    | opCurrHeap b dst src =>
      simpa [WordCopy.copyPropProg] using derivesSub_normal defs terminal _ (by simp)
    | set name exp =>
      cases exp <;> simpa [WordCopy.copyPropProg] using derivesSub_normal defs terminal _ (by simp)
    | get n name =>
      simp only [WordCopy.copyPropProg]
      cases WordCopy.lookupStoreEq cs name with
      | none => exact derivesSub_normal defs terminal _ (by simp)
      | some v =>
        dsimp only
        split
        · exact derivesSub_move defs terminal _ _
        · exact derivesSub_skip defs terminal
    | codeBufferWrite _ _ | dataBufferWrite _ _ =>
      simpa [WordCopy.copyPropProg] using derivesSub_normal defs terminal _ (by simp)
    | storeConsts _ _ _ _ _ | locValue _ _
    | assign _ _ | store _ _ =>
      simpa [WordCopy.copyPropProg] using derivesSub_normal defs terminal _ h
    | tick | shareInst _ _ _ | raise _ | «return» _ _ | ffi _ _ _ _ _ _
    | «break» _ | «continue» _ | seq _ _ | ite _ _ _ _ _ | loop _ _ _
    | alloc _ _ | install _ _ _ _ _ | mustTerminate _ =>
      simp [erase] at h
    | call ret dest args handler =>
      rcases ret with _ | ⟨_, _, _, _, _⟩ <;> rcases handler with _ | ⟨_, _, _, _⟩ <;>
        simp [erase] at h
  | tick => intro _; exact ⟨_, Derives.tick, subeffects_refl _⟩
  | share op reg exp =>
    intro cs; exact ⟨_, Derives.share op reg (WordCopy.copyPropShare exp cs), subeffects_refl _⟩
  | raise reg =>
    intro cs; exact ⟨_, Derives.raise (WordCopy.lookupEq cs reg), subeffects_refl _⟩
  | result reg regs =>
    intro cs; exact ⟨_, Derives.result _ _, subeffects_refl _⟩
  | breakTo label => intro _; exact ⟨_, Derives.breakTo label, subeffects_refl _⟩
  | continueTo label => intro _; exact ⟨_, Derives.continueTo label, subeffects_refl _⟩
  | ffi name r1 l1 r2 l2 names =>
    intro _; exact ⟨_, Derives.ffi name r1 l1 r2 l2 names, subeffects_refl _⟩
  | seq _ _ ih1 ih2 =>
    intro cs
    simp only [WordCopy.copyPropProg]
    exact derivesSub_seq (ih1 cs) (ih2 _)
  | branch cmp reg operand _ _ ih1 ih2 =>
    intro cs
    simp only [WordCopy.copyPropProg]
    exact derivesSub_branch cmp _ _ (ih1 cs) (ih2 cs)
  | loop names exits _ cycle ih =>
    intro _
    simp only [WordCopy.copyPropProg]
    exact derivesSub_loop names exits (ih WordCopy.emptyEq) cycle
  | tail dest args =>
    intro _; exact ⟨_, Derives.tail dest args, subeffects_refl _⟩
  | returning names live next l1 l2 dest args handler contEffects handlerEffects cont handlers _ _ =>
    intro _
    exact ⟨_, Derives.returning names live next l1 l2 dest args handler contEffects
      handlerEffects cont handlers, subeffects_refl _⟩

theorem copyProp_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : DerivesSub defs terminal p e) :
    DerivesSub defs terminal (WordCopy.copyProp p) e := by
  obtain ⟨ef, hd, hs⟩ := hp
  exact derivesSub_mono (copyPropProg_derivesSub defs terminal hd WordCopy.emptyEq) hs

/-! ## Pass 7: `WordInst.threeToTwoRegProg` -/

theorem threeToTwoReg_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : Derives defs terminal p e) :
    DerivesSub defs terminal (WordInst.threeToTwoReg p) e := by
  induction hp with
  | normal p h =>
    cases p with
    | skip | move _ _ | assign _ _ | get _ _ | set _ _ | store _ _ | storeConsts _ _ _ _ _
    | locValue _ _ | codeBufferWrite _ _ | dataBufferWrite _ _ =>
      simpa [WordInst.threeToTwoReg] using derivesSub_normal defs terminal _ h
    | opCurrHeap bop r1 r2 =>
      simp only [WordInst.threeToTwoReg]
      exact derivesSub_seq_zero_left (derivesSub_move defs terminal _ _)
        (derivesSub_normal defs terminal _ (by simp))
    | inst i =>
      cases i with
      | skip | const _ _ | mem _ _ _ =>
        simpa [WordInst.threeToTwoReg] using derivesSub_inst defs terminal _
      | arith a =>
        cases a with
        | div _ _ _ | longMul _ _ _ _ | longDiv _ _ _ _ _ =>
          simpa [WordInst.threeToTwoReg] using derivesSub_inst defs terminal _
        | binop _ _ _ _ | shift _ _ _ _ | addCarry _ _ _ _
        | addOverflow _ _ _ _ | subOverflow _ _ _ _ =>
          simp only [WordInst.threeToTwoReg]
          exact derivesSub_seq_zero_left (derivesSub_move defs terminal _ _)
            (derivesSub_inst defs terminal _)
    | tick | shareInst _ _ _ | raise _ | «return» _ _ | ffi _ _ _ _ _ _
    | «break» _ | «continue» _ | seq _ _ | ite _ _ _ _ _ | loop _ _ _
    | alloc _ _ | install _ _ _ _ _ | mustTerminate _ =>
      simp [erase] at h
    | call ret dest args handler =>
      rcases ret with _ | ⟨_, _, _, _, _⟩ <;> rcases handler with _ | ⟨_, _, _, _⟩ <;>
        simp [erase] at h
  | tick => exact ⟨_, Derives.tick, subeffects_refl _⟩
  | share op reg exp => exact ⟨_, Derives.share op reg exp, subeffects_refl _⟩
  | raise reg => exact ⟨_, Derives.raise reg, subeffects_refl _⟩
  | result reg regs => exact ⟨_, Derives.result reg regs, subeffects_refl _⟩
  | breakTo label => exact ⟨_, Derives.breakTo label, subeffects_refl _⟩
  | continueTo label => exact ⟨_, Derives.continueTo label, subeffects_refl _⟩
  | ffi name r1 l1 r2 l2 names => exact ⟨_, Derives.ffi name r1 l1 r2 l2 names, subeffects_refl _⟩
  | seq _ _ ih1 ih2 => exact derivesSub_seq ih1 ih2
  | branch cmp reg operand _ _ ih1 ih2 => exact derivesSub_branch cmp reg operand ih1 ih2
  | loop names exits _ cycle ih => exact derivesSub_loop names exits ih cycle
  | tail dest args => exact ⟨_, Derives.tail dest args, subeffects_refl _⟩
  | returning names live next l1 l2 dest args handler _ _ _ _ ihCont ihHand =>
    cases handler with
    | none => exact derivesSub_returning_none names live l1 l2 dest args ihCont
    | some h =>
      rcases h with ⟨hname, hbody, h1, h2⟩
      exact derivesSub_returning_some names live l1 l2 dest args hname h1 h2 ihCont
        (ihHand hname hbody h1 h2 rfl)

theorem threeToTwoRegProg_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (twoRegs : Bool) {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : DerivesSub defs terminal p e) :
    DerivesSub defs terminal (WordInst.threeToTwoRegProg twoRegs p) e := by
  cases twoRegs with
  | false => exact hp
  | true =>
    obtain ⟨ef, hd, hs⟩ := hp
    exact derivesSub_mono (threeToTwoReg_derivesSub defs terminal hd) hs

/-! ## Pass 8: `WordUnreach.removeUnreach` -/

theorem destSeqMove_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    {p2 rest : WordLangProgHOL (BitVec width)} {n2 : Nat} {l2 : List (Nat × Nat)}
    {e2 : Effects}
    (hp2 : DerivesSub defs terminal p2 e2)
    (hd : WordUnreach.destSeqMove p2 = some (n2, l2, rest)) :
    (rest = .skip → Subeffects (atom .fall 0) e2) ∧ DerivesSub defs terminal rest e2 := by
  cases p2 with
  | move n l =>
    simp only [WordUnreach.destSeqMove, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl, rfl⟩ := hd
    obtain ⟨ef, hder, hsub⟩ := hp2
    cases hder
    exact ⟨fun _ => hsub, derivesSub_mono (derivesSub_skip defs terminal) hsub⟩
  | seq q1 q2 =>
    cases q1 with
    | move n l =>
      simp only [WordUnreach.destSeqMove, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      obtain ⟨ef, hder, hsub⟩ := hp2
      cases hder with
      | normal _ her => simp [erase] at her
      | @seq _ _ eq1 eq2 hd1 hd2 =>
        cases hd1
        have hsub2 : Subeffects eq2 e2 :=
          subeffects_trans (seq_atom_fall_zero_left_rev eq2) hsub
        refine ⟨fun hrest => ?_, ⟨eq2, hd2, hsub2⟩⟩
        subst hrest
        cases hd2
        exact hsub2
    | _ => simp [WordUnreach.destSeqMove] at hd
  | _ => simp [WordUnreach.destSeqMove] at hd

theorem simpSeq_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    {p1 p2 : WordLangProgHOL (BitVec width)} {e1 e2 : Effects}
    (hskip2 : p2 = .skip → e2 = atom .fall 0)
    (hskip1 : p1 = .skip → e1 = atom .fall 0)
    (hraise : ∀ r, p1 = .raise r → e1 .fall = none)
    (hret : ∀ r rs, p1 = .return r rs → e1 .fall = none)
    (hbrk : ∀ k, p1 = .break k → e1 .fall = none)
    (hcont : ∀ k, p1 = .continue k → e1 .fall = none)
    (hp1 : DerivesSub defs terminal p1 e1)
    (hp2 : DerivesSub defs terminal p2 e2) :
    DerivesSub defs terminal (WordUnreach.simpSeq p1 p2) (WordCostEffects.seq e1 e2) := by
  unfold WordUnreach.simpSeq
  split
  · next h2 =>
    rw [hskip2 h2]
    exact derivesSub_mono hp1 (seq_atom_fall_zero_right_rev e1)
  · cases p1 with
    | skip =>
      rw [hskip1 rfl]
      exact derivesSub_mono hp2 (seq_atom_fall_zero_left_rev e2)
    | raise r =>
      exact derivesSub_mono hp1 (seq_no_fall (b := e2) (hraise r rfl))
    | «return» r rs =>
      exact derivesSub_mono hp1 (seq_no_fall (b := e2) (hret r rs rfl))
    | «break» k =>
      exact derivesSub_mono hp1 (seq_no_fall (b := e2) (hbrk k rfl))
    | «continue» k =>
      exact derivesSub_mono hp1 (seq_no_fall (b := e2) (hcont k rfl))
    | move n1 l1 =>
      obtain ⟨ef1, hd1, hs1⟩ := hp1
      cases hd1
      cases hdest : WordUnreach.destSeqMove p2 with
      | none => exact derivesSub_seq (derivesSub_mono (derivesSub_normal defs terminal _) hs1) hp2
      | some val =>
        rcases val with ⟨n2, l2, rest⟩
        have ⟨hrest_skip, hrest_der⟩ := destSeqMove_derivesSub defs terminal hp2 hdest
        dsimp only
        split
        · next hr =>
          have hsub : Subeffects (atom .fall 0) (WordCostEffects.seq e1 e2) :=
            subeffects_trans (seq_atom_fall_zero_left_rev (atom .fall 0))
              (subeffects_seq hs1 (hrest_skip hr))
          exact derivesSub_mono (derivesSub_normal defs terminal _) hsub
        · have hsub : Subeffects e2 (WordCostEffects.seq e1 e2) :=
            subeffects_trans (seq_atom_fall_zero_left_rev e2)
              (subeffects_seq hs1 (subeffects_refl e2))
          exact derivesSub_seq_zero_left (derivesSub_normal defs terminal _)
            (derivesSub_mono hrest_der hsub)
    | _ => exact derivesSub_seq hp1 hp2

theorem seqAssocRight_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (hdefsFall : ∀ dest, defs dest .fall = none)
    {p : WordLangProgHOL (BitVec width)} {e1 : Effects}
    (hp : Derives defs terminal p e1) :
    ∀ (acc : WordLangProgHOL (BitVec width)) {e2 : Effects},
      (acc = .skip → e2 = atom .fall 0) →
      DerivesSub defs terminal acc e2 →
      DerivesSub defs terminal (WordUnreach.seqAssocRight p acc) (WordCostEffects.seq e1 e2) := by
  induction hp with
  | normal p h =>
    intro acc e2 hacc_skip hacc
    cases p with
    | skip =>
      simpa only [WordUnreach.seqAssocRight] using
        derivesSub_mono hacc (seq_atom_fall_zero_left_rev e2)
    | move _ _ | inst _ | assign _ _ | get _ _ | set _ _ | store _ _ | storeConsts _ _ _ _ _
    | opCurrHeap _ _ _ | locValue _ _ | codeBufferWrite _ _ | dataBufferWrite _ _ =>
      simp only [WordUnreach.seqAssocRight]
      exact simpSeq_derivesSub defs terminal hacc_skip
        (by intro hs; cases hs) (by intro _ hs; cases hs) (by intro _ _ hs; cases hs)
        (by intro _ hs; cases hs) (by intro _ hs; cases hs)
        (derivesSub_normal defs terminal _ h) hacc
    | tick | shareInst _ _ _ | raise _ | «return» _ _ | ffi _ _ _ _ _ _
    | «break» _ | «continue» _ | seq _ _ | ite _ _ _ _ _ | loop _ _ _
    | alloc _ _ | install _ _ _ _ _ | mustTerminate _ =>
      simp [erase] at h
    | call ret dest args handler =>
      rcases ret with _ | ⟨_, _, _, _, _⟩ <;> rcases handler with _ | ⟨_, _, _, _⟩ <;>
        simp [erase] at h
  | tick =>
    intro acc e2 hacc_skip hacc
    simp only [WordUnreach.seqAssocRight]
    exact simpSeq_derivesSub defs terminal hacc_skip
      (by intro hs; cases hs) (by intro _ hs; cases hs) (by intro _ _ hs; cases hs)
      (by intro _ hs; cases hs) (by intro _ hs; cases hs)
      ⟨_, Derives.tick, subeffects_refl _⟩ hacc
  | share op reg exp =>
    intro acc e2 hacc_skip hacc
    simp only [WordUnreach.seqAssocRight]
    exact simpSeq_derivesSub defs terminal hacc_skip
      (by intro hs; cases hs) (by intro _ hs; cases hs) (by intro _ _ hs; cases hs)
      (by intro _ hs; cases hs) (by intro _ hs; cases hs)
      ⟨_, Derives.share op reg exp, subeffects_refl _⟩ hacc
  | raise reg =>
    intro acc e2 hacc_skip hacc
    simp only [WordUnreach.seqAssocRight]
    exact simpSeq_derivesSub defs terminal hacc_skip
      (by intro hs; cases hs) (fun _ _ => rfl) (by intro _ _ hs; cases hs)
      (by intro _ hs; cases hs) (by intro _ hs; cases hs)
      ⟨_, Derives.raise reg, subeffects_refl _⟩ hacc
  | result reg regs =>
    intro acc e2 hacc_skip hacc
    simp only [WordUnreach.seqAssocRight]
    exact simpSeq_derivesSub defs terminal hacc_skip
      (by intro hs; cases hs) (by intro _ hs; cases hs) (fun _ _ _ => rfl)
      (by intro _ hs; cases hs) (by intro _ hs; cases hs)
      ⟨_, Derives.result reg regs, subeffects_refl _⟩ hacc
  | breakTo label =>
    intro acc e2 hacc_skip hacc
    simp only [WordUnreach.seqAssocRight]
    exact simpSeq_derivesSub defs terminal hacc_skip
      (by intro hs; cases hs) (by intro _ hs; cases hs) (by intro _ _ hs; cases hs)
      (fun _ _ => rfl) (by intro _ hs; cases hs)
      ⟨_, Derives.breakTo label, subeffects_refl _⟩ hacc
  | continueTo label =>
    intro acc e2 hacc_skip hacc
    simp only [WordUnreach.seqAssocRight]
    exact simpSeq_derivesSub defs terminal hacc_skip
      (by intro hs; cases hs) (by intro _ hs; cases hs) (by intro _ _ hs; cases hs)
      (by intro _ hs; cases hs) (fun _ _ => rfl)
      ⟨_, Derives.continueTo label, subeffects_refl _⟩ hacc
  | ffi name r1 l1 r2 l2 names =>
    intro acc e2 hacc_skip hacc
    simp only [WordUnreach.seqAssocRight]
    exact simpSeq_derivesSub defs terminal hacc_skip
      (by intro hs; cases hs) (by intro _ hs; cases hs) (by intro _ _ hs; cases hs)
      (by intro _ hs; cases hs) (by intro _ hs; cases hs)
      ⟨_, Derives.ffi name r1 l1 r2 l2 names, subeffects_refl _⟩ hacc
  | @seq q1 q2 a b _ _ ih1 ih2 =>
    intro acc e2 hacc_skip hacc
    simp only [WordUnreach.seqAssocRight]
    have hstep2 := ih2 acc hacc_skip hacc
    obtain ⟨mid, hmid_d, hmid_s⟩ := hstep2
    have hstep1 := ih1 (WordUnreach.seqAssocRight q2 acc)
      (fun hskip => by rw [hskip] at hmid_d; exact derives_skip_inv hmid_d)
      ⟨mid, hmid_d, subeffects_refl mid⟩
    exact derivesSub_mono hstep1
      (subeffects_trans (subeffects_seq (subeffects_refl a) hmid_s) (seq_assoc_sub_rev a b e2))
  | branch cmp reg operand _ _ ih1 ih2 =>
    intro acc e2 hacc_skip hacc
    simp only [WordUnreach.seqAssocRight]
    have hb1 := derivesSub_mono (ih1 .skip (fun _ => rfl) (derivesSub_skip defs terminal))
      (seq_atom_fall_zero_right _)
    have hb2 := derivesSub_mono (ih2 .skip (fun _ => rfl) (derivesSub_skip defs terminal))
      (seq_atom_fall_zero_right _)
    exact simpSeq_derivesSub defs terminal hacc_skip
      (by intro hs; cases hs) (by intro _ hs; cases hs) (by intro _ _ hs; cases hs)
      (by intro _ hs; cases hs) (by intro _ hs; cases hs)
      (derivesSub_branch cmp reg operand hb1 hb2) hacc
  | loop names exits _ cycle ih =>
    intro acc e2 hacc_skip hacc
    simp only [WordUnreach.seqAssocRight]
    have hb := derivesSub_mono (ih .skip (fun _ => rfl) (derivesSub_skip defs terminal))
      (seq_atom_fall_zero_right _)
    exact simpSeq_derivesSub defs terminal hacc_skip
      (by intro hs; cases hs) (by intro _ hs; cases hs) (by intro _ _ hs; cases hs)
      (by intro _ hs; cases hs) (by intro _ hs; cases hs)
      (derivesSub_loop names exits hb cycle) hacc
  | tail dest args =>
    intro acc e2 _ _
    simp only [WordUnreach.seqAssocRight]
    have hfall : (shift (some (-1)) (defs dest)) .fall = none := by
      simp [shift, hdefsFall dest, add]
    exact derivesSub_mono ⟨_, Derives.tail dest args, subeffects_refl _⟩
      (seq_no_fall (b := e2) hfall)
  | returning names live next l1 l2 dest args handler _ _ _ _ ihCont ihHand =>
    intro acc e2 hacc_skip hacc
    have hc := derivesSub_mono (ihCont .skip (fun _ => rfl) (derivesSub_skip defs terminal))
      (seq_atom_fall_zero_right _)
    cases handler with
    | none =>
      simp only [WordUnreach.seqAssocRight]
      exact simpSeq_derivesSub defs terminal hacc_skip
        (by intro hs; cases hs) (by intro _ hs; cases hs) (by intro _ _ hs; cases hs)
        (by intro _ hs; cases hs) (by intro _ hs; cases hs)
        (derivesSub_returning_none names live l1 l2 dest args hc) hacc
    | some h =>
      rcases h with ⟨hname, hbody, h1, h2⟩
      simp only [WordUnreach.seqAssocRight]
      have hh := derivesSub_mono
        (ihHand hname hbody h1 h2 rfl .skip (fun _ => rfl) (derivesSub_skip defs terminal))
        (seq_atom_fall_zero_right _)
      exact simpSeq_derivesSub defs terminal hacc_skip
        (by intro hs; cases hs) (by intro _ hs; cases hs) (by intro _ _ hs; cases hs)
        (by intro _ hs; cases hs) (by intro _ hs; cases hs)
        (derivesSub_returning_some names live l1 l2 dest args hname h1 h2 hc hh) hacc

theorem removeUnreach_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (hdefsFall : ∀ dest, defs dest .fall = none)
    {p : WordLangProgHOL (BitVec width)} {e : Effects}
    (hp : DerivesSub defs terminal p e) :
    DerivesSub defs terminal (WordUnreach.removeUnreach p) e := by
  obtain ⟨ef, hd, hs⟩ := hp
  have h := seqAssocRight_derivesSub defs terminal hdefsFall hd .skip (fun _ => rfl)
    (derivesSub_skip defs terminal)
  exact derivesSub_mono h (subeffects_trans (seq_atom_fall_zero_right ef) hs)

/-! ## Complete 9-pass `WordCostCompilerControl.preAllocation` preservation theorem -/

theorem preAllocation_derivesSub {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (hdefsFall : ∀ dest, defs dest .fall = none)
    (ac : AsmConfigExact width) (twoRegisters : Bool) (arity : Nat)
    {program : WordLangProgHOL (BitVec width)} {target : Effects}
    (hp : DerivesSub defs terminal program target) :
    DerivesSub defs terminal
      (WordCostCompilerControl.preAllocation ac twoRegisters arity program) target := by
  unfold WordCostCompilerControl.preAllocation
  have h1 := compileExp_derivesSub defs terminal hdefsFall hp
  obtain ⟨e1, hd1, hs1⟩ := h1
  have h2 := derivesSub_mono
    (instSelectExecutable_derivesSub defs terminal ac (maxVarHOL (WordSimp.compileExp program) + 1) hd1)
    hs1
  have h3 := fullSsaCcTrans_derivesSub defs terminal arity h2
  have h4 := removeDeadProg_derivesSub defs terminal h3
  have h5 := wordCommonSubexpElim_derivesSub defs terminal h4
  have h6 := copyProp_derivesSub defs terminal h5
  have h7 := threeToTwoRegProg_derivesSub defs terminal twoRegisters h6
  have h8 := removeUnreach_derivesSub defs terminal hdefsFall h7
  exact removeDeadProg_derivesSub defs terminal h8

end InitECandidate.Solver.Wave8Stage.WordCostPreAllocationPreservation
