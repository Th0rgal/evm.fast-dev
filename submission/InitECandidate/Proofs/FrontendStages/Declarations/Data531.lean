import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify515
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body531_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def body531_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push" [Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body531_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body531_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body531_4 : Prog (BitVec 64) :=
.seq body531_2 body531_3

def body531_5 : Prog (BitVec 64) :=
.seq body531_1 body531_4

def body531_6 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("address_to_u256") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64]),
        Flapjack.Exp.const 16#64])]) body531_5

def body531_7 : Prog (BitVec 64) :=
.seq body531_0 body531_6

def body531_8 : Prog (BitVec 64) :=
.seq body531_1 body531_2

def body531_9 : Prog (BitVec 64) :=
.seq body531_8 body531_3

def body531_10 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("address_to_u256") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64]),
        Flapjack.Exp.const 16#64])]) body531_9

def body531_11 : Prog (BitVec 64) :=
.seq body531_0 body531_10

def originalData531 : Decl (BitVec 64) :=
.function { name := "op_caller", inline := false, exported := false, params := [], body := body531_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData531 : Decl (BitVec 64) :=
.function { name := "op_caller", inline := false, exported := false, params := [], body := body531_11, returnShape := (Flapjack.Shape.one) }
def original531 := Pancake.PanLang.declToHOL originalData531
def simplified531 := Pancake.PanLang.declToHOL simplifiedData531
end InitECandidate.Proofs.FrontendStages.Declarations
