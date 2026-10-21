import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify525
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body541_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.const 100#64]]

def body541_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_after_charge"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "c"]

def body541_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push_word"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "code")]

def body541_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body541_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body541_5 : Prog (BitVec 64) :=
.seq body541_3 body541_4

def body541_6 : Prog (BitVec 64) :=
.seq body541_2 body541_5

def body541_7 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body541_6

def body541_8 : Prog (BitVec 64) :=
.seq body541_1 body541_7

def body541_9 : Prog (BitVec 64) :=
.seq body541_0 body541_8

def body541_10 : Prog (BitVec 64) :=
.decCall ("c") (Flapjack.Shape.one) ("access_gas_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body541_9

def body541_11 : Prog (BitVec 64) :=
.decCall ("addr") (Flapjack.Shape.one) ("to_address_masked") ([Flapjack.Exp.var Flapjack.VarKind.local "av"]) body541_10

def body541_12 : Prog (BitVec 64) :=
.decCall ("av") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body541_11

def body541_13 : Prog (BitVec 64) :=
.seq body541_0 body541_1

def body541_14 : Prog (BitVec 64) :=
.seq body541_2 body541_3

def body541_15 : Prog (BitVec 64) :=
.seq body541_14 body541_4

def body541_16 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body541_15

def body541_17 : Prog (BitVec 64) :=
.seq body541_13 body541_16

def body541_18 : Prog (BitVec 64) :=
.decCall ("c") (Flapjack.Shape.one) ("access_gas_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body541_17

def body541_19 : Prog (BitVec 64) :=
.decCall ("addr") (Flapjack.Shape.one) ("to_address_masked") ([Flapjack.Exp.var Flapjack.VarKind.local "av"]) body541_18

def body541_20 : Prog (BitVec 64) :=
.decCall ("av") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body541_19

def originalData541 : Decl (BitVec 64) :=
.function { name := "op_extcodesize", inline := false, exported := false, params := [], body := body541_12, returnShape := (Flapjack.Shape.one) }
def simplifiedData541 : Decl (BitVec 64) :=
.function { name := "op_extcodesize", inline := false, exported := false, params := [], body := body541_20, returnShape := (Flapjack.Shape.one) }
def original541 := Pancake.PanLang.declToHOL originalData541
def simplified541 := Pancake.PanLang.declToHOL simplifiedData541
end InitECandidate.Proofs.FrontendStages.Declarations
