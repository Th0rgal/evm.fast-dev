import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ModHalfCallExact
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseCongruence

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingCombinators

theorem inverseHalfStep_exact_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (counter coefficient : MlS) (a x m : Limbs256)
    (hcx : counter ≠ coefficient) (hcm : counter ≠ ofString "m")
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup counter = some a.toValue)
    (hx : s.locals.lookup coefficient = some x.toValue)
    (hm : s.locals.lookup (ofString "m") = some m.toValue)
    (hr : evaluateHOLFiniteState s (inverseHalfStep counter coefficient) = (none, post)) :
    post.locals = (s.locals.update (counter, (half256 a).toValue)).update
      (coefficient, (modHalf256 x m).toValue) := by
  unfold inverseHalfStep at hr
  rw [evaluateHOLFiniteState_seq_line780, inverseHalf_assign s counter a ha] at hr
  exact modHalf_call_exact_none (s := setVarHOLFinite counter (half256 a).toValue s) coefficient coefficient (ofString "m") x m hc
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hcx, hx])
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hcm, hm]) hr

def HalfCongruencePost {F : Type} (counter coefficient : MlS) (input : Nat) (m : Limbs256)
    (before : PanSemStateFiniteExact 64 F) (a : Limbs256)
    (after : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ r y : Limbs256, ∃ k : Nat,
    after.locals.lookup counter = some r.toValue ∧
    after.locals.lookup coefficient = some y.toValue ∧
    r.toNat % 2 = 1 ∧ a.toNat = r.toNat * 2 ^ k ∧
    InverseCongruence input m.toNat r.toNat y.toNat ∧ y.toNat < m.toNat ∧
    ∀ key, key ≠ counter → key ≠ coefficient → after.locals.lookup key = before.locals.lookup key

/-- A typed halving loop either times out or exits with an odd operand obtained
by removing a power of two; unrelated locals are preserved. -/
theorem inverse_half_congruence {F : Type} (counter coefficient : MlS)
    (hcx : counter ≠ coefficient) (hcm : counter ≠ ofString "m")
    (hxm : coefficient ≠ ofString "m")
    (s : PanSemStateFiniteExact 64 F) (a x m : Limbs256) (input : Nat)
    (hmOdd : m.toNat % 2 = 1) (hxRange : x.toNat < m.toNat)
    (hinv : InverseCongruence input m.toNat a.toNat x.toNat)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup counter = some a.toValue)
    (hx : s.locals.lookup coefficient = some x.toValue)
    (hm : s.locals.lookup (ofString "m") = some m.toValue) :
    let out := evaluateHOLFiniteState s
      (.while (inverseEvenExpr counter) (inverseHalfStep counter coefficient))
    out.1 = some .timeOut ∨ (out.1 = none ∧ HalfCongruencePost counter coefficient input m s a out.2) := by
  have hall : ∀ n (s : PanSemStateFiniteExact 64 F) (a x m : Limbs256),
      m.toNat % 2 = 1 → x.toNat < m.toNat →
      InverseCongruence input m.toNat a.toNat x.toNat →
      s.clock = n → s.code = originalRuntimeCode →
      s.locals.lookup counter = some a.toValue →
      s.locals.lookup coefficient = some x.toValue →
      s.locals.lookup (ofString "m") = some m.toValue →
      let out := evaluateHOLFiniteState s
        (.while (inverseEvenExpr counter) (inverseHalfStep counter coefficient))
      out.1 = some .timeOut ∨ (out.1 = none ∧ HalfCongruencePost counter coefficient input m s a out.2) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s a x m hmOdd hxRange hinv hn hc ha hx hm
      dsimp only
      have hg := inverseEvenExpr_eval s counter a ha
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
          have ht := inverseHalfStep_typed (decClockHOLFinite s) counter coefficient a x m hcx hcm hc ha hx hm
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite s)
              (inverseHalfStep counter coefficient) with ⟨res, post⟩
          rw [hrun] at ht
          rcases ht with ht | ⟨unused, hr, hlocalsOld⟩
          · dsimp only at ht
            subst res
            exact Or.inl rfl
          · dsimp only at hr hlocalsOld
            subst res
            dsimp only
            let y := modHalf256 x m
            have hlocals := inverseHalfStep_exact_none (s := decClockHOLFinite s) counter coefficient a x m hcx hcm hc ha hx hm hrun
            have hyRange : y.toNat < m.toNat := modHalf256_lt_modulus x m hxRange
            have hyInv : InverseCongruence input m.toNat (half256 a).toNat y.toNat := by
              simpa only [half256_toNat] using inverseCongruence_half input a.toNat x m hmOdd heven hinv
            have hpc : post.code = originalRuntimeCode := by
              have h := evalP_code (decClockHOLFinite s) (inverseHalfStep counter coefficient)
              rw [hrun] at h
              exact h.trans hc
            have hpa : post.locals.lookup counter = some (half256 a).toValue := by
              rw [hlocals]
              simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hcx]
            have hpy : post.locals.lookup coefficient = some y.toValue := by
              rw [hlocals]
              simp [HolFiniteMapExact.lookup_update, FUPDATE, y]
            have hpm : post.locals.lookup (ofString "m") = some m.toValue := by
              rw [hlocals]
              simpa [HolFiniteMapExact.lookup_update, FUPDATE, hcm, hxm, decClockHOLFinite] using hm
            have hclock := evaluateHOLFiniteState_clock_le (decClockHOLFinite s)
              (inverseHalfStep counter coefficient)
            rw [hrun] at hclock
            change post.clock ≤ s.clock - 1 at hclock
            have hind := ih post.clock (by omega) post (half256 a) y m hmOdd hyRange hyInv rfl hpc hpa hpy hpm
            rcases hind with htimeout | ⟨hnone, r, z, k, hrc, hzc, hodd, hfactor, hzinv, hzRange, hrest⟩
            · exact Or.inl htimeout
            · refine Or.inr ⟨hnone, r, z, k + 1, hrc, hzc, hodd, ?_, hzinv, hzRange, ?_⟩
              · calc
                  a.toNat = (half256 a).toNat * 2 := by rw [half256_toNat]; omega
                  _ = (r.toNat * 2 ^ k) * 2 := by rw [hfactor]
                  _ = r.toNat * 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_assoc]
              · intro key hkc hkx
                rw [hrest key hkc hkx, hlocals]
                simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hkc, Ne.symm hkx, decClockHOLFinite]
      · rw [if_neg heven]
        dsimp only
        rw [if_neg (show ¬ (0 : BitVec 64) ≠ 0 by simp)]
        refine Or.inr ⟨rfl, a, x, 0, ha, hx, by omega, ?_, hinv, hxRange, ?_⟩
        · simp
        · intro key _ _
          rfl
  exact hall s.clock s a x m hmOdd hxRange hinv rfl hc ha hx hm

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
