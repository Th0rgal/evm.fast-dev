import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify530
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body546_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 5#64]

def body546_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push"
  [Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 8#64])]

def body546_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body546_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body546_4 : Prog (BitVec 64) :=
.seq body546_2 body546_3

def body546_5 : Prog (BitVec 64) :=
.seq body546_1 body546_4

def body546_6 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64]),
        Flapjack.Exp.const 32#64])]) body546_5

def body546_7 : Prog (BitVec 64) :=
.seq body546_0 body546_6

def body546_8 : Prog (BitVec 64) :=
.seq body546_1 body546_2

def body546_9 : Prog (BitVec 64) :=
.seq body546_8 body546_3

def body546_10 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64]),
        Flapjack.Exp.const 32#64])]) body546_9

def body546_11 : Prog (BitVec 64) :=
.seq body546_0 body546_10

def originalData546 : Decl (BitVec 64) :=
.function { name := "op_selfbalance", inline := false, exported := false, params := [], body := body546_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData546 : Decl (BitVec 64) :=
.function { name := "op_selfbalance", inline := false, exported := false, params := [], body := body546_11, returnShape := (Flapjack.Shape.one) }
def original546 := Pancake.PanLang.declToHOL originalData546
def simplified546 := Pancake.PanLang.declToHOL simplifiedData546
end InitECandidate.Proofs.FrontendStages.Declarations
