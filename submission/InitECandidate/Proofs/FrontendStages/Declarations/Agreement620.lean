import Guest.SoftwareAst
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify620
import InitECandidate.Proofs.FrontendStages.Declarations.Agreement604
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
theorem original620_eq : original620 = Flapjack.Pancake.PanLang.declToHOL Guest.Software.guestFn_blake2b_f := by
  with_unfolding_all rfl
#print axioms original620_eq
end InitECandidate.Proofs.FrontendStages.Declarations
