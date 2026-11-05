import InitECandidate.Solver.Wave8Stage.ConcreteM7313.StackPasses

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open StackPasses StackToLabClock

/-- The stack runtime stubs have the required budget independently of the
register-allocation oracle table. -/
theorem stubs_bounded (oracles : List (Option (Spt Nat))) :
    ∀ e ∈ (StackRemove.initStubs (width := 64)
        (StackToLab.isGenGc (oracleCompilerConfig oracles).dataConf.gcKind)
        (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig oracles).dataConf - 1) pointer
        BvlToBvi.initGlobalsLocation ++
      (StackAlloc.stubs (oracleCompilerConfig oracles).dataConf).map
        (StackRemove.progComp (oracleCompilerConfig oracles).stackConf.jump
          riscvConfig.addrOffset pointer)), stepCost e.2 ≤ 7313 := by
  change ∀ e ∈ (StackRemove.initStubs (width := 64)
        (StackToLab.isGenGc (oracleCompilerConfig []).dataConf.gcKind)
        (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig []).dataConf - 1) pointer
        BvlToBvi.initGlobalsLocation ++
      (StackAlloc.stubs (oracleCompilerConfig []).dataConf).map
        (StackRemove.progComp (oracleCompilerConfig []).stackConf.jump
          riscvConfig.addrOffset pointer)), stepCost e.2 ≤ 7313
  decide +kernel

end InitECandidate.Solver.Wave8Stage.ConcreteM7313
