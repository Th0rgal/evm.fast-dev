import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify296
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body312_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body312_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body312_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 0#64]))
  (Flapjack.Exp.const 0#64)) body312_0 body312_1

def body312_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body312_4 : Prog (BitVec 64) :=
.seq body312_2 body312_3

def originalData312 : Decl (BitVec 64) :=
.function { name := "tx_has_access_list", inline := false, exported := false, params := [("tx", Flapjack.Shape.one)], body := body312_4, returnShape := (Flapjack.Shape.one) }
def simplifiedData312 : Decl (BitVec 64) :=
.function { name := "tx_has_access_list", inline := false, exported := false, params := [("tx", Flapjack.Shape.one)], body := body312_4, returnShape := (Flapjack.Shape.one) }
def original312 := Pancake.PanLang.declToHOL originalData312
def simplified312 := Pancake.PanLang.declToHOL simplifiedData312
end InitECandidate.Proofs.FrontendStages.Declarations
