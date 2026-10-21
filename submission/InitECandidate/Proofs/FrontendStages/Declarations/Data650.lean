import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify634
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body650_0 : Prog (BitVec 64) :=
Flapjack.Prog.call none "fq_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "x",
    Flapjack.Exp.rStruct
      [Flapjack.Exp.const 17522657719365597833#64, Flapjack.Exp.const 13107472804851548667#64,
        Flapjack.Exp.const 5164255478447964150#64, Flapjack.Exp.const 493319470278259999#64]]

def originalData650 : Decl (BitVec 64) :=
.function { name := "fq_to_mont", inline := false, exported := false, params := [("x", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body650_0, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData650 : Decl (BitVec 64) :=
.function { name := "fq_to_mont", inline := false, exported := false, params := [("x", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body650_0, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def original650 := Pancake.PanLang.declToHOL originalData650
def simplified650 := Pancake.PanLang.declToHOL simplifiedData650
end InitECandidate.Proofs.FrontendStages.Declarations
