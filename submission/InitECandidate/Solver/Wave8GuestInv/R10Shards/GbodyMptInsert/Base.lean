import InitECandidate.Solver.Wave8GuestInv.ContractParts.C09
/-! Compatibility aliases for helpers shared with the existing R10 contracts. -/

namespace InitECandidate.Solver.Wave8GuestInv.RunFramesRace
export InitECandidate.Solver.Wave8GuestInv (evalAt evalAt_const evalAt_local
  locN_setVar_same locN_setVar_ne cond_local condTrue_local_ne0 localsFree_arenaReady
  clock_assign clock_skip clock_return)
namespace TerminatingProgBoundedOn
export InitECandidate.Solver.Wave8GuestInv.TerminatingProgBoundedOn
  (mono_bound of_clock seq_guestInv_after)
end TerminatingProgBoundedOn
end InitECandidate.Solver.Wave8GuestInv.RunFramesRace
