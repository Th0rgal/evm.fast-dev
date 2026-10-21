import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify364
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body380_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body380_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body380_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 0#64]))
  (Flapjack.Exp.const 0#64)) body380_0 body380_1

def body380_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body380_0 body380_1

def body380_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "hs") (Flapjack.Exp.const 0#64)) body380_0 body380_1

def body380_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body380_6 : Prog (BitVec 64) :=
.seq body380_4 body380_5

def body380_7 : Prog (BitVec 64) :=
.decCall ("hs") (Flapjack.Shape.one) ("account_has_storage") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body380_6

def body380_8 : Prog (BitVec 64) :=
.seq body380_3 body380_7

def body380_9 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.var Flapjack.VarKind.global "empty_code_hash", Flapjack.Exp.const 32#64]) body380_8

def body380_10 : Prog (BitVec 64) :=
.seq body380_2 body380_9

def body380_11 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body380_10

def originalData380 : Decl (BitVec 64) :=
.function { name := "account_deployable", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body380_11, returnShape := (Flapjack.Shape.one) }
def simplifiedData380 : Decl (BitVec 64) :=
.function { name := "account_deployable", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body380_11, returnShape := (Flapjack.Shape.one) }
def original380 := Pancake.PanLang.declToHOL originalData380
def simplified380 := Pancake.PanLang.declToHOL simplifiedData380
end InitECandidate.Proofs.FrontendStages.Declarations
