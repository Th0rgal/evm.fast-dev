import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify502
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body518_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 3#64]

def body518_1 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 2#64)

def body518_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body518_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 16#64]))
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 1#64])) body518_1 body518_2

def body518_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_swap_positions"
  [Flapjack.Exp.const 0#64, Flapjack.Exp.var Flapjack.VarKind.local "n"]

def body518_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 2#64]

def body518_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body518_7 : Prog (BitVec 64) :=
.seq body518_5 body518_6

def body518_8 : Prog (BitVec 64) :=
.seq body518_4 body518_7

def body518_9 : Prog (BitVec 64) :=
.seq body518_3 body518_8

def body518_10 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("decode_single") ([Flapjack.Exp.var Flapjack.VarKind.local "imm"]) body518_9

def body518_11 : Prog (BitVec 64) :=
.decCall ("imm") (Flapjack.Shape.one) ("code_imm") ([]) body518_10

def body518_12 : Prog (BitVec 64) :=
.seq body518_0 body518_11

def body518_13 : Prog (BitVec 64) :=
.seq body518_3 body518_4

def body518_14 : Prog (BitVec 64) :=
.seq body518_13 body518_5

def body518_15 : Prog (BitVec 64) :=
.seq body518_14 body518_6

def body518_16 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("decode_single") ([Flapjack.Exp.var Flapjack.VarKind.local "imm"]) body518_15

def body518_17 : Prog (BitVec 64) :=
.decCall ("imm") (Flapjack.Shape.one) ("code_imm") ([]) body518_16

def body518_18 : Prog (BitVec 64) :=
.seq body518_0 body518_17

def originalData518 : Decl (BitVec 64) :=
.function { name := "op_swapn", inline := false, exported := false, params := [], body := body518_12, returnShape := (Flapjack.Shape.one) }
def simplifiedData518 : Decl (BitVec 64) :=
.function { name := "op_swapn", inline := false, exported := false, params := [], body := body518_18, returnShape := (Flapjack.Shape.one) }
def original518 := Pancake.PanLang.declToHOL originalData518
def simplified518 := Pancake.PanLang.declToHOL simplifiedData518
end InitECandidate.Proofs.FrontendStages.Declarations
