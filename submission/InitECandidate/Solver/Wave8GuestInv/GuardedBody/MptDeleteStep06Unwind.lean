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

/-- Pop typed 40-byte frames; use the saved kind, segment and branch index.
The rank is the finite stack length (or increasing top address), not trie depth. -/
theorem mptDelete_unwind (h : MptDeleteCallees) :
    TerminatingProgBoundedOn MptUnwindHead (.while mptTop mptUnwindBody) mptUnwindBudget := by
  sorry

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
