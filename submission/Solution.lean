import InitE.Challenge
import InitECandidate.Solver.ConcreteOracleWitness
import InitECandidate.Solver.Wave8GuestInv.Certificate
import InitECandidate.Solver.Wave8Stage.StageTransfer

set_option autoImplicit false
set_option maxRecDepth 200000
set_option exponentiation.threshold 2000

namespace InitE.Challenge

open InitECandidate.Solver.Wave8GuestInv

def submission : InitE.Submission :=
  InitECandidate.Solver.Wave8GuestInv.submission

def claimedScore : InitE.NatE :=
  .finite 4485583972239622846094745952947494668730166169983861635240711046121178727100250811132783957037278517212881661013543329547

theorem claimedScore_eq_K_target :
    claimedScore = .finite K_target := rfl

private noncomputable def pendingCompilationWitness :
    LeanBridge.ConcreteOracleCompilationWitness :=
  let w := InitECandidate.Solver.ConcreteOracleWitness.concreteOracleWitness
  { oracles := w.oracles
    c := w.c
    depth := w.depth
    hlab := w.hlab
    compiled := w.compiled
    depthBound := w.depthBound }

private theorem pendingStageTransfer : StageTransfer :=
  InitECandidate.Solver.Wave8Stage.StageTransfer.stageTransfer pendingCompilationWitness rfl

theorem certificate : InitE.Certificate submission claimedScore := by
  rw [claimedScore_eq_K_target]
  exact certificate_of_stage_transfer pendingCompilationWitness pendingStageTransfer

end InitE.Challenge
