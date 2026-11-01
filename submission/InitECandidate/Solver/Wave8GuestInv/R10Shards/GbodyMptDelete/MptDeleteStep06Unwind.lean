import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptUnwindStep
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
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
  apply TerminatingProgBoundedOn.while_rank Unwind.rank
    (fun s hs => Unwind.head_locals.decClock s hs)
    (fun s hc hs => Unwind.body_bound h s hc hs.1.1)
    (fun s _ _ _ => Unwind.rank_le s)
  intro F s hc hs hactive hflow
  have hp : locN s "top" ≠ 0 := condTrue_local_ne0 hactive
  have hsdec := Unwind.head_locals.decClock s hs
  obtain ⟨hpost, htop⟩ := Unwind.body_step h (s := decClockHOLFinite s) hc hsdec hp hflow
  refine ⟨hpost, ?_⟩
  obtain ⟨ns, fs, _, hstack, _⟩ := hs.2
  exact Unwind.rank_pop hstack hp htop


end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
