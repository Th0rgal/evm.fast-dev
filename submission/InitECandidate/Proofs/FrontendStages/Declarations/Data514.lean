import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify498
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body514_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 3#64]

def body514_1 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 2#64)

def body514_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body514_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "item")
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 16#64]))) body514_1 body514_2

def body514_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_swap_positions"
  [Flapjack.Exp.const 0#64, Flapjack.Exp.var Flapjack.VarKind.local "item"]

def body514_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body514_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body514_7 : Prog (BitVec 64) :=
.seq body514_5 body514_6

def body514_8 : Prog (BitVec 64) :=
.seq body514_4 body514_7

def body514_9 : Prog (BitVec 64) :=
.seq body514_3 body514_8

def body514_10 : Prog (BitVec 64) :=
.seq body514_0 body514_9

def body514_11 : Prog (BitVec 64) :=
.seq body514_0 body514_3

def body514_12 : Prog (BitVec 64) :=
.seq body514_11 body514_4

def body514_13 : Prog (BitVec 64) :=
.seq body514_12 body514_5

def body514_14 : Prog (BitVec 64) :=
.seq body514_13 body514_6

def originalData514 : Decl (BitVec 64) :=
.function { name := "op_swap", inline := false, exported := false, params := [("item", Flapjack.Shape.one)], body := body514_10, returnShape := (Flapjack.Shape.one) }
def simplifiedData514 : Decl (BitVec 64) :=
.function { name := "op_swap", inline := false, exported := false, params := [("item", Flapjack.Shape.one)], body := body514_14, returnShape := (Flapjack.Shape.one) }
def original514 := Pancake.PanLang.declToHOL originalData514
def simplified514 := Pancake.PanLang.declToHOL simplifiedData514
end InitECandidate.Proofs.FrontendStages.Declarations
