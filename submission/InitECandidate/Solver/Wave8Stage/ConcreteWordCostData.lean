import InitECandidate.Solver.Wave8Stage.WordCostEffects

/-! The executable concrete annotations, independent of semantic transfer
theorems and initialization proofs. Shared by the finite checks and their
soundness/application modules. -/
set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage
open Flapjack WordCostEffects

namespace ConcreteWordCostAnnotations
def summaries (dest : Option Nat) : Effects
  | .returned | .raised => some 1
  | .final => some (if dest == some 66 || dest == none then 3
      else if dest == some 90 then 2 else 1)
  | _ => none
end ConcreteWordCostAnnotations

namespace WordSourceOracle
open Flapjack.Basis.Pure.MlString
def terminal (name : MlString) : Bool :=
  name == ofString "halt" || name == ofString "trap"
end WordSourceOracle
end InitECandidate.Solver.Wave8Stage
