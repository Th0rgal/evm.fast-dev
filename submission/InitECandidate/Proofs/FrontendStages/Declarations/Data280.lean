import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify264
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body280_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body280_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body280_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "child") (Flapjack.Exp.const 0#64)) body280_0 body280_1

def body280_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 0#64]))
  (Flapjack.Exp.const 0#64)) body280_0 body280_1

def body280_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 8#64]))
  (Flapjack.Exp.const 0#64)) body280_0 body280_1

def body280_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body280_6 : Prog (BitVec 64) :=
.seq body280_4 body280_5

def body280_7 : Prog (BitVec 64) :=
.seq body280_3 body280_6

def body280_8 : Prog (BitVec 64) :=
.seq body280_2 body280_7

def body280_9 : Prog (BitVec 64) :=
.seq body280_2 body280_3

def body280_10 : Prog (BitVec 64) :=
.seq body280_9 body280_4

def body280_11 : Prog (BitVec 64) :=
.seq body280_10 body280_5

def originalData280 : Decl (BitVec 64) :=
.function { name := "_node_needs_rlp", inline := false, exported := false, params := [("child", Flapjack.Shape.one)], body := body280_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData280 : Decl (BitVec 64) :=
.function { name := "_node_needs_rlp", inline := false, exported := false, params := [("child", Flapjack.Shape.one)], body := body280_11, returnShape := (Flapjack.Shape.one) }
def original280 := Pancake.PanLang.declToHOL originalData280
def simplified280 := Pancake.PanLang.declToHOL simplifiedData280
end InitECandidate.Proofs.FrontendStages.Declarations
