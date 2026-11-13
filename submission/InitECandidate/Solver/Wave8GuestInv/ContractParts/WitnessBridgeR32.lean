import InitECandidate.Solver.ConcreteCompilationWitness
import InitECandidate.Solver.Wave8Stage.StageTransfer

/-! Wave 8 R32 (WitnessBridgeR32): the compilation-witness bridge.

The tree carries two field-identical compilation-witness structures:
`SelfContainedConcretePipelineMaster.ConcreteOracleCompilationWitness`
(`Solver.ConcreteCompilationWitness`), which
`ConcreteOracleWitness.concreteOracleWitness` inhabits, and
`Wave8GuestInv.LeanBridge.ConcreteOracleCompilationWitness`, which the stage
transfer and the certificate route consume. `bridge` copies the first into
the second field by field and keeps the oracle table (`bridge_oracles`), so
the stage transfer follows from any master witness carrying the
`ConcreteM7313` oracle table (`stageTransfer_of_master`).

This module stays clear of the compiler-correctness proof tree
(`InitECandidate.Proofs.FullBaseline` and its stage modules): it does not
import `Solver.ConcreteOracleWitness`, and nothing on the `Solution` import
path may, since that tree alone exceeds the import-closure budget of the
final cutover check. The witness therefore stays a premise of the
certificate; this bridge only records that either witness structure serves. -/

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.WitnessBridgeR32

open InitECandidate.Solver
open InitECandidate.Solver.Wave8GuestInv

/-- A master compilation witness, repackaged field by field as the
`LeanBridge` witness structure. -/
def bridge (v : SelfContainedConcretePipelineMaster.ConcreteOracleCompilationWitness) :
    LeanBridge.ConcreteOracleCompilationWitness :=
  { oracles := v.oracles
    c := v.c
    depth := v.depth
    hlab := v.hlab
    compiled := v.compiled
    depthBound := v.depthBound }

/-- `bridge` keeps the oracle table. -/
theorem bridge_oracles
    (v : SelfContainedConcretePipelineMaster.ConcreteOracleCompilationWitness) :
    (bridge v).oracles = v.oracles := rfl

/-- `Wave8GuestInv.StageTransfer` from any master compilation witness that
carries the `ConcreteM7313` oracle table. -/
theorem stageTransfer_of_master
    (v : SelfContainedConcretePipelineMaster.ConcreteOracleCompilationWitness)
    (same : v.oracles = InitECandidate.Solver.Wave8Stage.ConcreteM7313.oracles) :
    Wave8GuestInv.StageTransfer :=
  InitECandidate.Solver.Wave8Stage.StageTransfer.stageTransfer (bridge v) same

end InitECandidate.Solver.Wave8GuestInv.ContractParts.WitnessBridgeR32
