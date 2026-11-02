import InitECandidate.Solver.Wave8GuestInv.Spec
import InitECandidate.Solver.Wave8GuestInv.Deliveries.GBODY_RUNFRAMES_SOL.RunFrames
import InitECandidate.Solver.Wave8GuestInv.Deliveries.GBODY_RUNFRAMES_SOL.OpDispatch

/-! Final acceptance check against the full split spec at integration 6109dbfbe,
ported from frozen rev9 8a79d9f28. This file must compile before claiming final
acceptance; compiling a bootstrap theorem alone does not complete this check. -/
namespace InitECandidate.Solver.Wave8GuestInv

example : (type_of% RunFramesRace.gbody_run_frames) = GBody.run_frames := rfl
example : (type_of% RunFramesRace.gbody_op_dispatch) = GBody.op_dispatch := rfl


end InitECandidate.Solver.Wave8GuestInv
