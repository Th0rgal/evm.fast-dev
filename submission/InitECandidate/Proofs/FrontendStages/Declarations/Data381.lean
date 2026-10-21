import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify365
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body381_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body381_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body381_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 0#64]))
  (Flapjack.Exp.const 0#64)) body381_0 body381_1

def body381_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body381_0 body381_1

def body381_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "z")

def body381_5 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 8#64])]) body381_4

def body381_6 : Prog (BitVec 64) :=
.seq body381_3 body381_5

def body381_7 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.var Flapjack.VarKind.global "empty_code_hash", Flapjack.Exp.const 32#64]) body381_6

def body381_8 : Prog (BitVec 64) :=
.seq body381_2 body381_7

def originalData381 : Decl (BitVec 64) :=
.function { name := "acct_is_empty", inline := false, exported := false, params := [("a", Flapjack.Shape.one)], body := body381_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData381 : Decl (BitVec 64) :=
.function { name := "acct_is_empty", inline := false, exported := false, params := [("a", Flapjack.Shape.one)], body := body381_8, returnShape := (Flapjack.Shape.one) }
def original381 := Pancake.PanLang.declToHOL originalData381
def simplified381 := Pancake.PanLang.declToHOL simplifiedData381
end InitECandidate.Proofs.FrontendStages.Declarations
