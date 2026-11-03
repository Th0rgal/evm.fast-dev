import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.PanTerminatingCombinators

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A guard that remains true and a body that can only continue within the trap
or time out make every finite-clock execution time out. This handles the zero
halving case without pretending that zero decreases under a right shift. -/
theorem while_timeout_of_trap {F : Type}
    (P : PanSemStateFiniteExact 64 F → Prop) (condition : ExpHOL 64) (body : ProgHOL 64)
    (hentry : ∀ s, P s → P (decClockHOLFinite s))
    (hguard : ∀ s, P s → ∃ w : BitVec 64,
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition =
        some (.val (.word w)) ∧ w ≠ 0)
    (hbody : ∀ s, P s →
      (evaluateHOLFiniteState s body).1 = some .timeOut ∨
      ((evaluateHOLFiniteState s body).1 = none ∧ P (evaluateHOLFiniteState s body).2))
    (s : PanSemStateFiniteExact 64 F) (hp : P s) :
    (evaluateHOLFiniteState s (.while condition body)).1 = some .timeOut := by
  have hall : ∀ n (s : PanSemStateFiniteExact 64 F), s.clock = n → P s →
      (evaluateHOLFiniteState s (.while condition body)).1 = some .timeOut := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hn hp
      obtain ⟨w, hw, hw0⟩ := hguard s hp
      rw [evaluateHOLFiniteState_while_fixClockRewrite, hw]
      dsimp only
      rw [if_pos hw0]
      by_cases hz : s.clock = 0
      · simp [hz]
      · rw [if_neg hz]
        rcases hrun : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨result, post⟩
        have hb := hbody (decClockHOLFinite s) (hentry s hp)
        rw [hrun] at hb
        rcases hb with ht | ⟨hcontinue, hpost⟩
        · dsimp only at ht
          subst result
          rfl
        · dsimp only at hcontinue hpost
          subst result
          dsimp only
          have hc := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rw [hrun] at hc
          change post.clock ≤ s.clock - 1 at hc
          exact ih post.clock (by omega) post rfl hpost
  exact hall s.clock s rfl hp

end InitECandidate.Solver.Wave8GuestInv.Arith
