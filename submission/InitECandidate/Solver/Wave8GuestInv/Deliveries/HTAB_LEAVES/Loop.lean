import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_LEAVES.Base

/-! The no-repeat `while` rule, ported from `wave8/step0-opus55`
(`submission/InitECandidate/Solver/PanTerminatingNoRepeat.lean`, proved there; that file is not
on this branch's cone). It is restated over the spec's `LoopActive`, `evaluate_ne_of_clock_lt`
and `while_unfold_continue`, which revision 3 copies verbatim from the same file.

`while_oneWord` instantiates it for the read-only loops of the table code (`htab_find_leaf`,
the `htab_set` descent): a loop-free body that writes only locals, of which only one word `x`
survives the iteration. Then every active loop head is determined up to the clock by the value
of `x`, so a non-`.timeOut` run makes at most `2^64` iterations, for ARBITRARY memory. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8GuestInv.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

section NoRepeat

variable (P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
  (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
  {N : Nat} (κ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Fin N)
  (condition : ExpHOL 64) (body : ProgHOL 64) (B : Nat)

structure NoRepeatLoop : Prop where
  body_bound : TerminatingProgBoundedOn Q body B
  entry : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (word : BitVec 64),
    state.code = originalRuntimeCode → P state →
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      condition = some (.val (.word word)) →
    word ≠ 0 → state.clock ≠ 0 → Q (decClockHOLFinite state)
  step : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (word : BitVec 64),
    state.code = originalRuntimeCode → P state →
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      condition = some (.val (.word word)) →
    word ≠ 0 → state.clock ≠ 0 →
    let output := evaluateHOLFiniteState (decClockHOLFinite state) body
    output.1 ≠ some .timeOut → (output.1 = none ∨ output.1 = some .continue) →
      P output.2 ∧ R state output.2
  trans : ∀ {F : Type} (a b c : PanSemStateFiniteExact 64 F), R a b → R b c → R a c
  key : ∀ {F : Type} (a b : PanSemStateFiniteExact 64 F), R a b →
    LoopActive condition a → LoopActive condition b → κ a = κ b →
    b = { a with clock := b.clock }

variable {P Q R κ condition body B}

def VisitedHeads (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
    (κ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Fin N) (condition : ExpHOL 64)
    (body : ProgHOL 64) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (visited : Finset (Fin N)) : Prop :=
  ∀ k ∈ visited, ∃ earlier : PanSemStateFiniteExact 64 F, κ earlier = k ∧ R earlier state ∧
    LoopActive condition earlier ∧ state.clock < earlier.clock ∧
    evaluateHOLFiniteState earlier (.while condition body) =
      evaluateHOLFiniteState state (.while condition body)

theorem key_fresh (hloop : NoRepeatLoop P Q R κ condition body B)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (visited : Finset (Fin N))
    (hact : LoopActive condition state) (hvis : VisitedHeads R κ condition body state visited)
    (hnt : (evaluateHOLFiniteState state (.while condition body)).1 ≠ some .timeOut) :
    κ state ∉ visited := by
  intro hmem
  obtain ⟨earlier, hk, hR, hactE, hlt, hsame⟩ := hvis _ hmem
  have heq := hloop.key earlier state hR hactE hact hk
  exact evaluate_ne_of_clock_lt _ state earlier (by rw [heq]) hlt hsame hnt

theorem card_insert_key_le {F : Type} (κ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Fin N)
    (state : PanSemStateFiniteExact 64 F) (visited : Finset (Fin N)) (hfresh : κ state ∉ visited) :
    visited.card + 1 ≤ N := by
  have hle : (insert (κ state) visited).card ≤ N := by
    simpa using Finset.card_le_univ (insert (κ state) visited)
  rwa [Finset.card_insert_of_notMem hfresh] at hle

theorem while_noRepeat_aux (hloop : NoRepeatLoop P Q R κ condition body B) :
    ∀ (n : Nat) {F : Type} (state : PanSemStateFiniteExact 64 F) (visited : Finset (Fin N)),
      state.code = originalRuntimeCode → P state → N ≤ visited.card + n →
      VisitedHeads R κ condition body state visited →
      TerminatingRunBounded state (.while condition body) (n * (B + 1)) := by
  intro n
  induction n with
  | zero =>
    intro F state visited hcode hP hcard hvis hnt
    have hnt0 := hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split
    · rename_i word hword
      simp only [hword] at hnt
      by_cases hzero : word = 0
      · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · have hfresh := key_fresh hloop state visited ⟨word, hword, hzero⟩ hvis hnt0
        have := card_insert_key_le κ state visited hfresh
        omega
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | succ n ih =>
    intro F state visited hcode hP hcard hvis hnt
    have hone : B + 1 ≤ (n + 1) * (B + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have hnt0 := hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split
    · rename_i word hword
      simp only [hword] at hnt
      by_cases hzero : word = 0
      · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · rw [if_pos hzero] at hnt ⊢
        by_cases hclock : state.clock = 0
        · rw [if_pos hclock] at hnt; exact absurd rfl hnt
        · rw [if_neg hclock] at hnt ⊢
          have hact : LoopActive condition state := ⟨word, hword, hzero⟩
          have hfresh := key_fresh hloop state visited hact hvis hnt0
          have hQ := hloop.entry state word hcode hP hword hzero hclock
          have hb := hloop.body_bound (decClockHOLFinite state) hcode hQ
          have hstep := hloop.step state word hcode hP hword hzero hclock
          have hunfold := while_unfold_continue condition body state word hword hzero hclock
          have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite state) body).1
          unfold TerminatingRunBounded at hb
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨result, post⟩
          simp only [hrun] at hnt hb hstep hunfold hmeta
          dsimp only at hb hstep hunfold hmeta hnt ⊢
          change post.code = state.code at hmeta
          have hcont (hflow : result = none ∨ result = some .continue) :
              state.clock ≤ (evaluateHOLFiniteState post (.while condition body)).2.clock +
                (n + 1) * (B + 1) ∧
              (evaluateHOLFiniteState post (.while condition body)).2.clock ≤ state.clock := by
            have hsafe : result ≠ some .timeOut := by
              rcases hflow with h | h <;> simp [h]
            obtain ⟨hspent, hkept⟩ := hb hsafe
            change state.clock - 1 ≤ post.clock + B at hspent
            change post.clock ≤ state.clock - 1 at hkept
            obtain ⟨hPpost, hRpost⟩ := hstep hsafe hflow
            have hsame := hunfold hflow
            have hntPost : (evaluateHOLFiniteState post (.while condition body)).1 ≠
                some .timeOut := by
              rw [← hsame]; exact hnt0
            obtain ⟨htail, htailKept⟩ := ih post (insert (κ state) visited)
              (hmeta.trans hcode) hPpost
              (by rw [Finset.card_insert_of_notMem hfresh]; omega)
              (by
                intro k hk
                rcases Finset.mem_insert.mp hk with rfl | hk
                · exact ⟨state, rfl, hRpost, hact, by omega, hsame⟩
                · obtain ⟨earlier, hke, hRe, hactE, hlt, hsameE⟩ := hvis k hk
                  exact ⟨earlier, hke, hloop.trans _ _ _ hRe hRpost, hactE, by omega,
                    hsameE.trans hsame⟩)
              hntPost
            have hmul : n * (B + 1) + (B + 1) = (n + 1) * (B + 1) := by
              rw [Nat.succ_mul]
            exact ⟨by omega, by omega⟩
          cases result with
          | none => exact hcont (Or.inl rfl)
          | some r =>
            cases r with
            | «continue» => exact hcont (Or.inr rfl)
            | timeOut => exact absurd rfl hnt
            | _ =>
              obtain ⟨hspent, hkept⟩ := hb (by simp)
              change state.clock - 1 ≤ post.clock + B at hspent
              change post.clock ≤ state.clock - 1 at hkept
              simp only
              exact ⟨by omega, by omega⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem while_noRepeat
    (hloop : NoRepeatLoop P Q R κ condition body B) :
    TerminatingProgBoundedOn P (.while condition body) ((N + 1) * (B + 1)) :=
  fun state hcode hP =>
    (while_noRepeat_aux hloop N state ∅ hcode hP (by simp) (by simp [VisitedHeads])).weaken
      (Nat.mul_le_mul_right _ (Nat.le_succ N))

end NoRepeat

/-! ## Read-only loops carrying one word -/

/-- The word value of the local `x`, as a key in `Fin (2^64)` (`0` if `x` is not a word). -/
def wordKey (x : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Fin (2 ^ 64) :=
  match s.locals.lookup x with
  | some (.val (.word w)) => ⟨w.toNat, w.isLt⟩
  | _ => ⟨0, by decide⟩

/-- Frame of a read-only loop: only the clock and the local `x` change. -/
def OneWordFrame (x : MlS) {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  LocFrame s t ∧ ∀ y, y ≠ x → t.locals.lookup y = s.locals.lookup y

theorem locals_ext {m1 m2 : HolFiniteMapExact MlS (ValueHOL 64)}
    (h : ∀ k, m1.lookup k = m2.lookup k) : m1 = m2 := by
  cases m1; cases m2
  simp only [HolFiniteMapExact.mk.injEq]
  exact funext h

theorem wordKey_eq {x : MlS} {F : Type} {a b : PanSemStateFiniteExact 64 F}
    {wa wb : BitVec 64} (ha : a.locals.lookup x = some (.val (.word wa)))
    (hb : b.locals.lookup x = some (.val (.word wb))) (h : wordKey x a = wordKey x b) :
    b.locals.lookup x = a.locals.lookup x := by
  simp only [wordKey, ha, hb, Fin.mk.injEq] at h
  rw [ha, hb, BitVec.eq_of_toNat_eq h]

/-- `while c body` where `c` can only be an active word test if `x` holds a word, `body` is
loop-free, writes only locals, and keeps every local but `x`: at most `2^64` iterations. -/
theorem while_oneWord {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (x : MlS) {condition : ExpHOL 64} {body : ProgHOL 64} {B : Nat}
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hP : ∀ {F : Type} (s t : PanSemStateFiniteExact 64 F), P s → LocFrame s t →
      (∀ y, y ≠ x → t.locals.lookup y = s.locals.lookup y) → P t)
    (hbody : TerminatingProgBoundedOn P body B)
    (hloc : locOnly body = true)
    (havoid : ∀ y, y ≠ x → avoidsLocal y body = true)
    (hact : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LoopActive condition s →
      ∃ w, s.locals.lookup x = some (.val (.word w))) :
    TerminatingProgBoundedOn P (.while condition body) ((2 ^ 64 + 1) * (B + 1)) := by
  have hstepFrame : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
      OneWordFrame x s (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
    intro F s hflow
    refine ⟨?_, ?_⟩
    · have := locFrame_eval body hloc (decClockHOLFinite s)
      unfold LocFrame at this ⊢
      rw [this]; rfl
    · intro y hy
      have := evaluate_avoidsLocal_flowing y body (havoid y hy) (decClockHOLFinite s)
        (by rcases hflow with h | h <;> simp [Flowing, h])
      exact this
  have hloop : NoRepeatLoop P P (OneWordFrame x) (wordKey x) condition body B :=
    { body_bound := hbody
      entry := fun s _ _ hPs _ _ _ => hdec s hPs
      step := by
        intro F s w _ hPs _ _ _ _ hflow
        intro hflow
        have hfr := hstepFrame s hflow
        exact ⟨hP s _ hPs hfr.1 hfr.2, hfr⟩
      trans := fun a b c hab hbc =>
        ⟨hab.1.trans hbc.1, fun y hy => (hbc.2 y hy).trans (hab.2 y hy)⟩
      key := by
        intro F a b hab hacta hactb hk
        obtain ⟨wa, ha⟩ := hact a hacta
        obtain ⟨wb, hb⟩ := hact b hactb
        have hx := wordKey_eq ha hb hk
        have hl : b.locals = a.locals := locals_ext fun y => by
          by_cases hy : y = x
          · subst hy; exact hx
          · exact hab.2 y hy
        have hfr := hab.1
        unfold LocFrame at hfr
        rw [hl] at hfr
        exact hfr }
  intro F s hc hPs
  exact while_noRepeat hloop s hc hPs

/-- The test `x != k` (any comparison of the local `x` with anything) is active only if `x`
holds a word. -/
theorem active_cmp_var {F : Type} (op : Cmp) (x : MlS) (e : ExpHOL 64)
    (s : PanSemStateFiniteExact 64 F) (h : LoopActive (.cmp op (.var .local x) e) s) :
    ∃ w, s.locals.lookup x = some (.val (.word w)) := by
  obtain ⟨word, hw, _⟩ := h
  change evalAt s _ = _ at hw
  obtain ⟨a, b, ha, _, _⟩ := evalAt_cmp s op _ e word hw
  simp only [evalAt, evalHOLExact] at ha
  exact ⟨a, by simpa using ha⟩

end InitECandidate.Solver.Wave8GuestInv.Htab
