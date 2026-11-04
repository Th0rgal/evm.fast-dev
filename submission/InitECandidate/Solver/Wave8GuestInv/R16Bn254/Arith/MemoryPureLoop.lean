import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryPure

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestCodeLookup

theorem MemoryPure.loop (e : ExpHOL 64) {p : ProgHOL 64}
    (hp : MemoryPure p) : MemoryPure (.while e p) := by
  intro F s hc
  have hall : ∀ n (s : PanSemStateFiniteExact 64 F), s.clock = n →
      s.code = originalRuntimeCode →
      (evaluateHOLFiniteState s (.while e p)).2.memory = s.memory := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hn hc
      rw [evaluateHOLFiniteState_while_fixClockRewrite]
      split
      · split
        · split
          · rfl
          · rename_i hclock
            have hm := hp (decClockHOLFinite s) hc
            have hmeta := (evaluateHOLFiniteState_metadata (decClockHOLFinite s) p).1
            have hbound := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) p
            cases hr : evaluateHOLFiniteState (decClockHOLFinite s) p with
            | mk result mid =>
              rw [hr] at hm hmeta hbound
              have hsmall : mid.clock < n := by
                change mid.clock ≤ s.clock - 1 at hbound
                omega
              have hnext := ih mid.clock hsmall mid rfl (hmeta.trans hc)
              cases result with
              | none => exact hnext.trans hm
              | some result =>
                cases result <;> first | exact hm | exact hnext.trans hm
        · rfl
      · rfl
  exact hall s.clock s rfl hc

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
