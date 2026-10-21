import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify541
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body557_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 2#64]

def body557_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push" [Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body557_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body557_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body557_4 : Prog (BitVec 64) :=
.seq body557_2 body557_3

def body557_5 : Prog (BitVec 64) :=
.seq body557_1 body557_4

def body557_6 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 88#64]),
  Flapjack.Exp.const 32#64]) body557_5

def body557_7 : Prog (BitVec 64) :=
.decCall ("benv") (Flapjack.Shape.one) ("block_env") ([]) body557_6

def body557_8 : Prog (BitVec 64) :=
.seq body557_0 body557_7

def body557_9 : Prog (BitVec 64) :=
.seq body557_1 body557_2

def body557_10 : Prog (BitVec 64) :=
.seq body557_9 body557_3

def body557_11 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "benv", Flapjack.Exp.const 88#64]),
  Flapjack.Exp.const 32#64]) body557_10

def body557_12 : Prog (BitVec 64) :=
.decCall ("benv") (Flapjack.Shape.one) ("block_env") ([]) body557_11

def body557_13 : Prog (BitVec 64) :=
.seq body557_0 body557_12

def originalData557 : Decl (BitVec 64) :=
.function { name := "op_prevrandao", inline := false, exported := false, params := [], body := body557_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData557 : Decl (BitVec 64) :=
.function { name := "op_prevrandao", inline := false, exported := false, params := [], body := body557_13, returnShape := (Flapjack.Shape.one) }
def original557 := Pancake.PanLang.declToHOL originalData557
def simplified557 := Pancake.PanLang.declToHOL simplifiedData557
end InitECandidate.Proofs.FrontendStages.Declarations
