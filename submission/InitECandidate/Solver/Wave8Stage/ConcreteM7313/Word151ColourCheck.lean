import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151ClashTree
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracle151

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 16000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151ColourCheck
open Flapjack

theorem even : WordAlloc.everyEvenColour (oracle151.getD .ln) = true := by
  decide +kernel

theorem checked : (RegAlloc.checkClashTree
    (WordAlloc.totalColour (oracle151.getD .ln))
    Word151ClashTree.part0TreeSuffix .ln .ln).isSome = true := by
  decide +kernel

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151ColourCheck
