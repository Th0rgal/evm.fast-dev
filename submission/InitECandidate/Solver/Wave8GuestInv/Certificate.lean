import InitECandidate.Solver.Wave8GuestInv.Target
import InitECandidate.Solver.Wave8GuestInv.LeanBridge

set_option autoImplicit false
set_option maxRecDepth 200000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv

open InitE Flapjack
open InitECandidate.Solver
open LeanBridge

def submission : InitE.Submission :=
  LeanBridge.finiteSubmission K_target

def TargetClockBound : Prop :=
  FiniteRebudget.UniformNotTimeOut ArtifactEnv.baselineSubmission K_target

def StageTransfer : Prop :=
  UniformSourceClock.CoveredSourceUniformNotTimeOut K_pan → TargetClockBound

theorem source_not_timeOut_of_primitives (P : Primitives) :
    UniformSourceClock.CoveredSourceUniformNotTimeOut K_pan :=
  UniformSourceClock.covered_source_uniform_not_timeOut_of_has_clock_within
    (UniformSourceClock.covered_source_has_clock_within_of_ticks_bounded (assembly P))

theorem source_not_timeOut_K_pan :
    UniformSourceClock.CoveredSourceUniformNotTimeOut K_pan :=
  UniformSourceClock.covered_source_uniform_not_timeOut_of_has_clock_within
    (UniformSourceClock.covered_source_has_clock_within_of_ticks_bounded
      coveredSourceTicksConsumedBounded_K_pan)

theorem certificate_of_primitives
    (w : ConcreteOracleCompilationWitness) (transfer : StageTransfer)
    (P : Primitives) : InitE.Certificate submission (.finite K_target) :=
  LeanBridge.finite_certificate_of_witness w K_target
    (transfer (source_not_timeOut_of_primitives P))

theorem certificate_of_stage_transfer
    (w : ConcreteOracleCompilationWitness) (transfer : StageTransfer) :
    InitE.Certificate submission (.finite K_target) :=
  LeanBridge.finite_certificate_of_witness w K_target
    (transfer source_not_timeOut_K_pan)

end InitECandidate.Solver.Wave8GuestInv
