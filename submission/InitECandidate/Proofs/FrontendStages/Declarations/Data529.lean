import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify513
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body529_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "c"]

def body529_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_after_charge"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "c"]

def body529_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "stack_push"
  [Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 8#64])]

def body529_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body529_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body529_5 : Prog (BitVec 64) :=
.seq body529_3 body529_4

def body529_6 : Prog (BitVec 64) :=
.seq body529_2 body529_5

def body529_7 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body529_6

def body529_8 : Prog (BitVec 64) :=
.seq body529_1 body529_7

def body529_9 : Prog (BitVec 64) :=
.seq body529_0 body529_8

def body529_10 : Prog (BitVec 64) :=
.decCall ("c") (Flapjack.Shape.one) ("access_gas_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body529_9

def body529_11 : Prog (BitVec 64) :=
.decCall ("addr") (Flapjack.Shape.one) ("to_address_masked") ([Flapjack.Exp.var Flapjack.VarKind.local "av"]) body529_10

def body529_12 : Prog (BitVec 64) :=
.decCall ("av") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body529_11

def body529_13 : Prog (BitVec 64) :=
.seq body529_0 body529_1

def body529_14 : Prog (BitVec 64) :=
.seq body529_2 body529_3

def body529_15 : Prog (BitVec 64) :=
.seq body529_14 body529_4

def body529_16 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body529_15

def body529_17 : Prog (BitVec 64) :=
.seq body529_13 body529_16

def body529_18 : Prog (BitVec 64) :=
.decCall ("c") (Flapjack.Shape.one) ("access_gas_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body529_17

def body529_19 : Prog (BitVec 64) :=
.decCall ("addr") (Flapjack.Shape.one) ("to_address_masked") ([Flapjack.Exp.var Flapjack.VarKind.local "av"]) body529_18

def body529_20 : Prog (BitVec 64) :=
.decCall ("av") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body529_19

def originalData529 : Decl (BitVec 64) :=
.function { name := "op_balance", inline := false, exported := false, params := [], body := body529_12, returnShape := (Flapjack.Shape.one) }
def simplifiedData529 : Decl (BitVec 64) :=
.function { name := "op_balance", inline := false, exported := false, params := [], body := body529_20, returnShape := (Flapjack.Shape.one) }
def original529 := Pancake.PanLang.declToHOL originalData529
def simplified529 := Pancake.PanLang.declToHOL simplifiedData529
end InitECandidate.Proofs.FrontendStages.Declarations
