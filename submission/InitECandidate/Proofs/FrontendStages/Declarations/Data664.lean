import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify648
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body664_0 : Prog (BitVec 64) :=
Flapjack.Prog.call none "is_zero_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.const 32#64]]

def originalData664 : Decl (BitVec 64) :=
.function { name := "fe_is_zero", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body664_0, returnShape := (Flapjack.Shape.one) }
def simplifiedData664 : Decl (BitVec 64) :=
.function { name := "fe_is_zero", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body664_0, returnShape := (Flapjack.Shape.one) }
def original664 := Pancake.PanLang.declToHOL originalData664
def simplified664 := Pancake.PanLang.declToHOL simplifiedData664
end InitECandidate.Proofs.FrontendStages.Declarations
