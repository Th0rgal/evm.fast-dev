import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify710
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body726_0 : Prog (BitVec 64) :=
Flapjack.Prog.call none "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.var Flapjack.VarKind.local "a"]

def originalData726 : Decl (BitVec 64) :=
.function { name := "fp2_dbl", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body726_0, returnShape := (Flapjack.Shape.one) }
def simplifiedData726 : Decl (BitVec 64) :=
.function { name := "fp2_dbl", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body726_0, returnShape := (Flapjack.Shape.one) }
def original726 := Pancake.PanLang.declToHOL originalData726
def simplified726 := Pancake.PanLang.declToHOL simplifiedData726
end InitECandidate.Proofs.FrontendStages.Declarations
