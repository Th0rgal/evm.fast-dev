import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify752
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body768_0 : Prog (BitVec 64) :=
Flapjack.Prog.call none "fp2_is_zero"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 192#64]]

def originalData768 : Decl (BitVec 64) :=
.function { name := "g2_is_inf", inline := false, exported := false, params := [("p", Flapjack.Shape.one)], body := body768_0, returnShape := (Flapjack.Shape.one) }
def simplifiedData768 : Decl (BitVec 64) :=
.function { name := "g2_is_inf", inline := false, exported := false, params := [("p", Flapjack.Shape.one)], body := body768_0, returnShape := (Flapjack.Shape.one) }
def original768 := Pancake.PanLang.declToHOL originalData768
def simplified768 := Pancake.PanLang.declToHOL simplifiedData768
end InitECandidate.Proofs.FrontendStages.Declarations
