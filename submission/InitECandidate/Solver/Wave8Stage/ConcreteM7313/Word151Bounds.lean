import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151ColourCheck

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 16000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151Bounds
open Flapjack InitE Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition PrefixChecks.Shard87

noncomputable def coloured :=
  WordAlloc.applyColour (WordAlloc.totalColour (oracle151.getD .ln)) prefixProgram

theorem stackBounds : everyStackVarHOL (fun x => decide (2 * registers ≤ x)) coloured = true := by
  decide +kernel

theorem forcedBounds : (WordAlloc.getForced riscvConfig prefixProgram []).all
    (fun (x, y) => WordAlloc.totalColour (oracle151.getD .ln) x !=
      WordAlloc.totalColour (oracle151.getD .ln) y) = true := by
  decide +kernel

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151Bounds
