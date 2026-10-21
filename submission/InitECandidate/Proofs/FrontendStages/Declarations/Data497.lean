import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify481
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body497_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 5#64]

def body497_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push_word"
  [Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 256#64, Flapjack.Exp.var Flapjack.VarKind.local "bl"]]

def body497_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body497_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body497_4 : Prog (BitVec 64) :=
.seq body497_2 body497_3

def body497_5 : Prog (BitVec 64) :=
.seq body497_1 body497_4

def body497_6 : Prog (BitVec 64) :=
.decCall ("bl") (Flapjack.Shape.one) ("u256_bit_length") ([Flapjack.Exp.var Flapjack.VarKind.local "x"]) body497_5

def body497_7 : Prog (BitVec 64) :=
.seq body497_0 body497_6

def body497_8 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body497_7

def body497_9 : Prog (BitVec 64) :=
.seq body497_1 body497_2

def body497_10 : Prog (BitVec 64) :=
.seq body497_9 body497_3

def body497_11 : Prog (BitVec 64) :=
.decCall ("bl") (Flapjack.Shape.one) ("u256_bit_length") ([Flapjack.Exp.var Flapjack.VarKind.local "x"]) body497_10

def body497_12 : Prog (BitVec 64) :=
.seq body497_0 body497_11

def body497_13 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body497_12

def originalData497 : Decl (BitVec 64) :=
.function { name := "op_clz", inline := false, exported := false, params := [], body := body497_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData497 : Decl (BitVec 64) :=
.function { name := "op_clz", inline := false, exported := false, params := [], body := body497_13, returnShape := (Flapjack.Shape.one) }
def original497 := Pancake.PanLang.declToHOL originalData497
def simplified497 := Pancake.PanLang.declToHOL simplifiedData497
end InitECandidate.Proofs.FrontendStages.Declarations
