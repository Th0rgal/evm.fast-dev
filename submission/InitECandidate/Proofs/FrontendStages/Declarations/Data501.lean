import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify485
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body501_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 10#64]

def body501_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body501_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body501_3 : Prog (BitVec 64) :=
.seq body501_1 body501_2

def body501_4 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body501_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64)) body501_3 body501_4

def body501_6 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 6#64)

def body501_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) body501_6 body501_4

def body501_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "dest"))

def body501_9 : Prog (BitVec 64) :=
.seq body501_8 body501_2

def body501_10 : Prog (BitVec 64) :=
.seq body501_7 body501_9

def body501_11 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("is_valid_jumpdest") ([Flapjack.Exp.var Flapjack.VarKind.local "dest"]) body501_10

def body501_12 : Prog (BitVec 64) :=
.seq body501_5 body501_11

def body501_13 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "cond"]) body501_12

def body501_14 : Prog (BitVec 64) :=
.seq body501_0 body501_13

def body501_15 : Prog (BitVec 64) :=
.decCall ("cond") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body501_14

def body501_16 : Prog (BitVec 64) :=
.decCall ("dest") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body501_15

def body501_17 : Prog (BitVec 64) :=
.seq body501_7 body501_8

def body501_18 : Prog (BitVec 64) :=
.seq body501_17 body501_2

def body501_19 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("is_valid_jumpdest") ([Flapjack.Exp.var Flapjack.VarKind.local "dest"]) body501_18

def body501_20 : Prog (BitVec 64) :=
.seq body501_5 body501_19

def body501_21 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "cond"]) body501_20

def body501_22 : Prog (BitVec 64) :=
.seq body501_0 body501_21

def body501_23 : Prog (BitVec 64) :=
.decCall ("cond") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body501_22

def body501_24 : Prog (BitVec 64) :=
.decCall ("dest") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body501_23

def originalData501 : Decl (BitVec 64) :=
.function { name := "op_jumpi", inline := false, exported := false, params := [], body := body501_16, returnShape := (Flapjack.Shape.one) }
def simplifiedData501 : Decl (BitVec 64) :=
.function { name := "op_jumpi", inline := false, exported := false, params := [], body := body501_24, returnShape := (Flapjack.Shape.one) }
def original501 := Pancake.PanLang.declToHOL originalData501
def simplified501 := Pancake.PanLang.declToHOL simplifiedData501
end InitECandidate.Proofs.FrontendStages.Declarations
