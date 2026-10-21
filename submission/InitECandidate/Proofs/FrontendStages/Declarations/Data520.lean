import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify504
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body520_0 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "slot") (Flapjack.Exp.var Flapjack.VarKind.local "log")

def body520_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body520_2 : Prog (BitVec 64) :=
.seq body520_0 body520_1

def body520_3 : Prog (BitVec 64) :=
.decCall ("slot") (Flapjack.Shape.one) ("lst_push") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 88#64]),
  Flapjack.Exp.const 8#64]) body520_2

def originalData520 : Decl (BitVec 64) :=
.function { name := "log_append", inline := false, exported := false, params := [("e", Flapjack.Shape.one), ("log", Flapjack.Shape.one)], body := body520_3, returnShape := (Flapjack.Shape.one) }
def simplifiedData520 : Decl (BitVec 64) :=
.function { name := "log_append", inline := false, exported := false, params := [("e", Flapjack.Shape.one), ("log", Flapjack.Shape.one)], body := body520_3, returnShape := (Flapjack.Shape.one) }
def original520 := Pancake.PanLang.declToHOL originalData520
def simplified520 := Pancake.PanLang.declToHOL simplifiedData520
end InitECandidate.Proofs.FrontendStages.Declarations
