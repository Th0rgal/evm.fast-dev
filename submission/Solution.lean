import InitE.Challenge
import InitECandidate.Solver.Wave8GuestInv.Certificate

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
    LeanBridge.ConcreteOracleCompilationWitness := sorry

private theorem pendingStageTransfer : StageTransfer := sorry

theorem certificate : InitE.Certificate submission claimedScore := by
  rw [claimedScore_eq_K_target]
  exact certificate_of_stage_transfer pendingCompilationWitness pendingStageTransfer

end InitE.Challenge
