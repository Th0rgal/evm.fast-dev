import Flapjack.Pancake.Semantics.LoopProps.EvaluateClockExact

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.LoopAcyclicClock

open Flapjack LoopSemStateFiniteExact

/-- A static upper bound on ticks in a Loop fragment with no calls or loops.
An `ite` may consume one additional tick when cutting its outgoing locals. -/
def staticCost {width : Nat} [NeZero width] : HolLoopProg width → Option Nat
  | .seq first second => do
      let a ← staticCost first
      let b ← staticCost second
      pure (a + b)
  | .ite _ _ _ first second _ => do
      let a ← staticCost first
      let b ← staticCost second
      pure (max a b + 1)
  | .mark body => staticCost body
  | .tick => some 1
  | .loop .. | .call .. => none
  | _ => some 0

private theorem cutRes_bound {width : Nat} [NeZero width] {F : Type}
    (live : NumSet) (r : Option (LoopResultExact width))
    (s : LoopSemStateFiniteExact width F)
    (hnt : r ≠ some .timeOut) (hpos : 0 < s.clock) :
    (cutRes live (r, s)).1 ≠ some .timeOut ∧
      s.clock ≤ (cutRes live (r, s)).2.clock + 1 := by
  cases r with
  | some r => simpa only [cutRes] using And.intro hnt (Nat.le_add_right s.clock 1)
  | none =>
    simp only [cutRes]
    cases hc : cutState live s with
    | none => simp
    | some t =>
      have ht := cutState_clock hc
      simp only
      rw [if_neg (by omega : t.clock ≠ 0)]
      simp only [decClock, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
      omega

private theorem shMemOp_notTimeOut {width : Nat} [NeZero width] {F : Type}
    (op : WordMemOp) (v : Nat) (a : BitVec width)
    (s : LoopSemStateFiniteExact width F) :
    (shMemOp op v a s).1 ≠ some .timeOut := by
  cases op <;> simp only [shMemOp, shMemLoad, shMemStore] <;>
    (repeat' split) <;> simp

/-- Sufficient static fuel prevents timeout and bounds the consumed clock,
including executions that stop early with an error or an FFI result. -/
theorem evaluate_bound {width : Nat} [NeZero width] {F : Type}
    (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (b : Nat) (hcost : staticCost p = some b) (hbudget : b ≤ s.clock) :
    (evaluate p s).1 ≠ some .timeOut ∧
      s.clock ≤ (evaluate p s).2.clock + b := by
  revert hcost
  cases hp : p <;> intro hcost
  case seq first second =>
    have ih1 := evaluate_bound (F := F) first
    have ih2 := evaluate_bound (F := F) second
    cases ha : staticCost first with
    | none => simp [staticCost, ha] at hcost
    | some a =>
      cases hb : staticCost second with
      | none => simp [staticCost, ha, hb] at hcost
      | some c =>
        simp [staticCost, ha, hb] at hcost
        subst b
        have h1 := ih1 s a ha (by omega)
        rw [evaluate, fix_clock_evaluate]
        cases he : evaluate first s with
        | mk r t =>
          rw [he] at h1
          cases r with
          | none =>
            have h2 := ih2 t c hb (by dsimp only at h1; omega)
            dsimp only
            exact ⟨h2.1, by dsimp only at h1; omega⟩
          | some r =>
            dsimp only at h1 ⊢
            exact ⟨h1.1, by omega⟩
  case ite cmp reg operand first second live =>
    have ih1 := evaluate_bound (F := F) first
    have ih2 := evaluate_bound (F := F) second
    cases ha : staticCost first with
    | none => simp [staticCost, ha] at hcost
    | some a =>
      cases hb : staticCost second with
      | none => simp [staticCost, ha, hb] at hcost
      | some c =>
        simp [staticCost, ha, hb] at hcost
        subst b
        have step (q : HolLoopProg width) (d : Nat)
            (ih : ∀ (s : LoopSemStateFiniteExact width F) b,
              staticCost q = some b → b ≤ s.clock →
              (evaluate q s).1 ≠ some .timeOut ∧
                s.clock ≤ (evaluate q s).2.clock + b)
            (hd : staticCost q = some d) (hle : d ≤ max a c) :
            (cutRes live (evaluate q s)).1 ≠ some .timeOut ∧
              s.clock ≤ (cutRes live (evaluate q s)).2.clock + (max a c + 1) := by
          have hq := ih s d hd (by omega)
          rcases he : evaluate q s with ⟨r, t⟩
          rw [he] at hq
          have ht := cutRes_bound live r t hq.1 (by dsimp only at hq; omega)
          dsimp only at hq ht ⊢
          exact ⟨ht.1, by omega⟩
        rw [evaluate]
        split
        · split
          · exact step first a ih1 ha (Nat.le_max_left _ _)
          · exact step second c ih2 hb (Nat.le_max_right _ _)
        · simp
  case mark body =>
    rw [evaluate]
    exact evaluate_bound body s b hcost hbudget
  case loop => simp [staticCost] at hcost
  case call => simp [staticCost] at hcost
  case tick =>
    have hb : b = 1 := by simpa only [staticCost, Option.some.injEq] using hcost.symm
    subst b
    rw [evaluate, if_neg (by omega : s.clock ≠ 0)]
    simp only [decClock, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    omega
  all_goals
    have hb : b = 0 := by simpa only [staticCost, Option.some.injEq] using hcost.symm
    subst b
    rw [evaluate]
    all_goals (repeat' split)
    all_goals try have hm := memStore_clock ‹_›
    all_goals try have ha := loopArith_clock ‹_›
    all_goals try have hc := cutState_clock ‹_›
    all_goals try exact ⟨shMemOp_notTimeOut _ _ _ _, by rw [shMemOp_clock]; omega⟩
    all_goals simp_all [setVar, setVars, setGlobals, LoopSemStateFiniteExact.callEnv]

termination_by sizeOf p
decreasing_by all_goals subst p; simp +arith

/-- The same consumption bound applies to every completed execution, even
when the initial clock is below the conservative static bound. -/
theorem consumed_le {width : Nat} [NeZero width] {F : Type}
    (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (b : Nat) (hcost : staticCost p = some b)
    (hnt : (evaluate p s).1 ≠ some .timeOut) :
    s.clock ≤ (evaluate p s).2.clock + b := by
  rcases he : evaluate p s with ⟨r, t⟩
  rw [he] at hnt
  have hlift := evaluate_add_clock_eq p s r t b he hnt
  have hbound := evaluate_bound p { s with clock := s.clock + b } b hcost
    (Nat.le_add_left _ _)
  rw [hlift] at hbound
  dsimp only at hbound ⊢
  omega

/-- In a clock-preserving simulation the existential offset is at most the
static fragment cost. This keeps the actual simulation witness unchanged. -/
theorem offset_le {width : Nat} [NeZero width] {F : Type}
    (p : HolLoopProg width) (s t : LoopSemStateFiniteExact width F)
    (b extra : Nat) (r : Option (LoopResultExact width))
    (hcost : staticCost p = some b)
    (hrun : evaluate p { s with clock := s.clock + extra } = (r, t))
    (hnt : r ≠ some .timeOut) (hclock : s.clock = t.clock) : extra ≤ b := by
  have hc := consumed_le p { s with clock := s.clock + extra } b hcost
    (by rw [hrun]; exact hnt)
  rw [hrun] at hc
  dsimp only at hc
  omega


end InitECandidate.Solver.Wave8Stage.LoopAcyclicClock
