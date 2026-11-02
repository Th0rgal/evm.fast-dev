import InitE.SourceDeclarationsCore
import Flapjack.Pancake.PanToWord
import InitECandidate.Solver.Wave8Stage.CertifiedListSpine
import InitECandidate.Solver.Wave8Stage.CertifiedReduction
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000
open InitE Flapjack Lean
/-! Kernel-certified declaration-list structure; function-body reductions
are deliberately deferred to the individual concrete function checks. -/

namespace InitECandidate.Solver.Wave8Stage.ConcreteCompilerSource
wave8_list_spine source := sourceDeclarations
#print axioms source_eq
end InitECandidate.Solver.Wave8Stage.ConcreteCompilerSource
