import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify469
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body485_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 3#64]

def body485_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push_bool" [Flapjack.Exp.var Flapjack.VarKind.local "r"]

def body485_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body485_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body485_4 : Prog (BitVec 64) :=
.seq body485_2 body485_3

def body485_5 : Prog (BitVec 64) :=
.seq body485_1 body485_4

def body485_6 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.one) ("u256_slt") ([Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "y"]) body485_5

def body485_7 : Prog (BitVec 64) :=
.seq body485_0 body485_6

def body485_8 : Prog (BitVec 64) :=
.decCall ("y") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body485_7

def body485_9 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body485_8

def body485_10 : Prog (BitVec 64) :=
.seq body485_1 body485_2

def body485_11 : Prog (BitVec 64) :=
.seq body485_10 body485_3

def body485_12 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.one) ("u256_slt") ([Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "y"]) body485_11

def body485_13 : Prog (BitVec 64) :=
.seq body485_0 body485_12

def body485_14 : Prog (BitVec 64) :=
.decCall ("y") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body485_13

def body485_15 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body485_14

def originalData485 : Decl (BitVec 64) :=
.function { name := "op_slt", inline := false, exported := false, params := [], body := body485_9, returnShape := (Flapjack.Shape.one) }
def simplifiedData485 : Decl (BitVec 64) :=
.function { name := "op_slt", inline := false, exported := false, params := [], body := body485_15, returnShape := (Flapjack.Shape.one) }
def original485 := Pancake.PanLang.declToHOL originalData485
def simplified485 := Pancake.PanLang.declToHOL simplifiedData485
end InitECandidate.Proofs.FrontendStages.Declarations
