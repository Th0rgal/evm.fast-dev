import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify523
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body539_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def body539_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push"
  [Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 48#64])]

def body539_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body539_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body539_4 : Prog (BitVec 64) :=
.seq body539_2 body539_3

def body539_5 : Prog (BitVec 64) :=
.seq body539_1 body539_4

def body539_6 : Prog (BitVec 64) :=
.dec ("te") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 8#64])) body539_5

def body539_7 : Prog (BitVec 64) :=
.seq body539_0 body539_6

def body539_8 : Prog (BitVec 64) :=
.seq body539_1 body539_2

def body539_9 : Prog (BitVec 64) :=
.seq body539_8 body539_3

def body539_10 : Prog (BitVec 64) :=
.dec ("te") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 8#64])) body539_9

def body539_11 : Prog (BitVec 64) :=
.seq body539_0 body539_10

def originalData539 : Decl (BitVec 64) :=
.function { name := "op_gasprice", inline := false, exported := false, params := [], body := body539_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData539 : Decl (BitVec 64) :=
.function { name := "op_gasprice", inline := false, exported := false, params := [], body := body539_11, returnShape := (Flapjack.Shape.one) }
def original539 := Pancake.PanLang.declToHOL originalData539
def simplified539 := Pancake.PanLang.declToHOL simplifiedData539
end InitECandidate.Proofs.FrontendStages.Declarations
