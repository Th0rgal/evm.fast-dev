import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify474
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body490_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 3#64]

def body490_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push"
  [Flapjack.Exp.rStruct
      [Flapjack.Exp.op Flapjack.BinOp.or
          [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "x"),
            Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "y")],
        Flapjack.Exp.op Flapjack.BinOp.or
          [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "x"),
            Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "y")],
        Flapjack.Exp.op Flapjack.BinOp.or
          [Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "x"),
            Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "y")],
        Flapjack.Exp.op Flapjack.BinOp.or
          [Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "x"),
            Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "y")]]]

def body490_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body490_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body490_4 : Prog (BitVec 64) :=
.seq body490_2 body490_3

def body490_5 : Prog (BitVec 64) :=
.seq body490_1 body490_4

def body490_6 : Prog (BitVec 64) :=
.seq body490_0 body490_5

def body490_7 : Prog (BitVec 64) :=
.decCall ("y") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body490_6

def body490_8 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body490_7

def body490_9 : Prog (BitVec 64) :=
.seq body490_0 body490_1

def body490_10 : Prog (BitVec 64) :=
.seq body490_9 body490_2

def body490_11 : Prog (BitVec 64) :=
.seq body490_10 body490_3

def body490_12 : Prog (BitVec 64) :=
.decCall ("y") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body490_11

def body490_13 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body490_12

def originalData490 : Decl (BitVec 64) :=
.function { name := "op_or", inline := false, exported := false, params := [], body := body490_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData490 : Decl (BitVec 64) :=
.function { name := "op_or", inline := false, exported := false, params := [], body := body490_13, returnShape := (Flapjack.Shape.one) }
def original490 := Pancake.PanLang.declToHOL originalData490
def simplified490 := Pancake.PanLang.declToHOL simplifiedData490
end InitECandidate.Proofs.FrontendStages.Declarations
