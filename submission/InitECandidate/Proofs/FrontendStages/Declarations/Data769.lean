import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify753
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body769_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 288#64]

def body769_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body769_2 : Prog (BitVec 64) :=
.seq body769_0 body769_1

def originalData769 : Decl (BitVec 64) :=
.function { name := "g2_copy", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one)], body := body769_2, returnShape := (Flapjack.Shape.one) }
def simplifiedData769 : Decl (BitVec 64) :=
.function { name := "g2_copy", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one)], body := body769_2, returnShape := (Flapjack.Shape.one) }
def original769 := Pancake.PanLang.declToHOL originalData769
def simplified769 := Pancake.PanLang.declToHOL simplifiedData769
end InitECandidate.Proofs.FrontendStages.Declarations
