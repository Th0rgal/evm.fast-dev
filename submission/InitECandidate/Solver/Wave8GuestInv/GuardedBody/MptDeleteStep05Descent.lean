import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptCuts
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

/-- Count descent via strictly decreasing scratch_ptr on every continuing step.
The continuation receives a finite typed stack, even after a zero-extension cycle. -/
theorem mptDelete_descent
    (steps : MptSteps MptDeleteActive MptDeleteHead MptDeleteEffect mptDeleteBody mptDeleteCost)
    {tail : ProgHOL 64} {b : Nat} (htail : TerminatingProgBoundedOn MptUnwindHead tail b) :
    TerminatingProgBoundedOn MptDeleteHead (.seq (.while mptGo mptDeleteBody) tail)
      (mptDeleteBudget + b) := by
  sorry

/-- Only three constant declarations; tail is arbitrary. -/
theorem mptDelete_initialize {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn MptDeleteHead tail b) :
    TerminatingProgBoundedOn MptReady (mptInit "top" "res" tail) b := by
  sorry

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
