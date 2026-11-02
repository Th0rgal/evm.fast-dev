import InitECandidate.Solver.Wave8Stage.PipelineTransfer

/-! Public parameterized Stage 5 interface. This replaces the earlier
unusable shifted-base draft and avoids importing the heavy concrete pipeline.
The explicit compiler, true-base relation, oracle tie and bootstrap hypotheses
are exactly those of PipelineTransfer. -/
set_option autoImplicit false
namespace InitECandidate.Solver.Wave8Stage.Stage5

theorem stage5_lab_to_target_affine_not_timeOut :
    type_of% @PipelineTransfer.stage5_lab_to_target_affine_not_timeOut :=
  @PipelineTransfer.stage5_lab_to_target_affine_not_timeOut

#print axioms stage5_lab_to_target_affine_not_timeOut
end InitECandidate.Solver.Wave8Stage.Stage5
