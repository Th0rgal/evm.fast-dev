import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsHalfStep

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingCombinators

def BlsHalfNormalPost {F : Type} (counter coefficient : MlS)
    (before : PanSemStateFiniteExact 64 F) (a : Limbs384)
    (after : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ r y : Limbs384, ∃ k : Nat,
    after.locals.lookup counter = some r.toValue ∧
    after.locals.lookup coefficient = some y.toValue ∧
    r.toNat % 2 = 1 ∧ a.toNat = r.toNat * 2 ^ k ∧
    ∀ key, key ≠ counter → key ≠ coefficient → after.locals.lookup key = before.locals.lookup key

/-- A typed halving loop either times out or exits with an odd operand obtained
by removing a power of two; unrelated locals are preserved. -/
theorem bls_half_normalizes {F : Type} (counter coefficient : MlS)
    (hcx : counter ≠ coefficient)
    (s : PanSemStateFiniteExact 64 F) (a x : Limbs384)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup counter = some a.toValue)
    (hx : s.locals.lookup coefficient = some x.toValue) :
    let out := evaluateHOLFiniteState s
      (.while (inverseEvenExpr counter) (blsHalfStep counter coefficient))
    out.1 = some .timeOut ∨ (out.1 = none ∧ BlsHalfNormalPost counter coefficient s a out.2) := by
  have hall : ∀ n (s : PanSemStateFiniteExact 64 F) (a x : Limbs384),
      s.clock = n → s.code = originalRuntimeCode →
      s.locals.lookup counter = some a.toValue →
      s.locals.lookup coefficient = some x.toValue →
      let out := evaluateHOLFiniteState s
        (.while (inverseEvenExpr counter) (blsHalfStep counter coefficient))
      out.1 = some .timeOut ∨ (out.1 = none ∧ BlsHalfNormalPost counter coefficient s a out.2) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s a x hn hc ha hx
      dsimp only
      have hg := blsEvenExpr_eval s counter a ha
      change evalHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z))
        (inverseEvenExpr counter) = _ at hg
      rw [evaluateHOLFiniteState_while_fixClockRewrite, hg]
      by_cases heven : a.toNat % 2 = 0
      · rw [if_pos heven]
        dsimp only
        rw [if_pos (show (1 : BitVec 64) ≠ 0 by decide)]
        by_cases hz : s.clock = 0
        · simp [hz]
        · rw [if_neg hz]
          have ht := blsHalfStep_typed (decClockHOLFinite s) counter coefficient a x hcx hc ha hx
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite s)
              (blsHalfStep counter coefficient) with ⟨res, post⟩
          rw [hrun] at ht
          rcases ht with ht | ⟨y, hr, hlocals⟩
          · dsimp only at ht
            subst res
            exact Or.inl rfl
          · dsimp only at hr hlocals
            subst res
            dsimp only
            have hpc : post.code = originalRuntimeCode := by
              have h := evalP_code (decClockHOLFinite s) (blsHalfStep counter coefficient)
              rw [hrun] at h
              exact h.trans hc
            have hpa : post.locals.lookup counter = some (half384 a).toValue := by
              rw [hlocals]
              simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hcx]
            have hpy : post.locals.lookup coefficient = some y.toValue := by
              rw [hlocals]
              simp [HolFiniteMapExact.lookup_update, FUPDATE]
            have hclock := evaluateHOLFiniteState_clock_le (decClockHOLFinite s)
              (blsHalfStep counter coefficient)
            rw [hrun] at hclock
            change post.clock ≤ s.clock - 1 at hclock
            have hind := ih post.clock (by omega) post (half384 a) y rfl hpc hpa hpy
            rcases hind with htimeout | ⟨hnone, r, z, k, hrc, hzc, hodd, hfactor, hrest⟩
            · exact Or.inl htimeout
            · refine Or.inr ⟨hnone, r, z, k + 1, hrc, hzc, hodd, ?_, ?_⟩
              · calc
                  a.toNat = (half384 a).toNat * 2 := by rw [half384_toNat]; omega
                  _ = (r.toNat * 2 ^ k) * 2 := by rw [hfactor]
                  _ = r.toNat * 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_assoc]
              · intro key hkc hkx
                rw [hrest key hkc hkx, hlocals]
                simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hkc, Ne.symm hkx, decClockHOLFinite]
      · rw [if_neg heven]
        dsimp only
        rw [if_neg (show ¬ (0 : BitVec 64) ≠ 0 by simp)]
        refine Or.inr ⟨rfl, a, x, 0, ha, hx, by omega, ?_, ?_⟩
        · simp
        · intro key _ _
          rfl
  exact hall s.clock s a x rfl hc ha hx
end InitECandidate.Solver.Wave8GuestInv.Arith
