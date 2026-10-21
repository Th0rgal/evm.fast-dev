import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify583
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body599_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "stipend" (Flapjack.Exp.const 2300#64)

def body599_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body599_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vz") (Flapjack.Exp.const 0#64)) body599_0 body599_1

def body599_3 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.var Flapjack.VarKind.local "s"])

def body599_4 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.var Flapjack.VarKind.local "gas", Flapjack.Exp.var Flapjack.VarKind.local "stipend"]) body599_3

def body599_5 : Prog (BitVec 64) :=
.decCall ("c") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.var Flapjack.VarKind.local "gas", Flapjack.Exp.var Flapjack.VarKind.local "extra_gas"]) body599_4

def body599_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "gas_left")
  (Flapjack.Exp.var Flapjack.VarKind.local "need")) body599_5 body599_1

def body599_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "g" (Flapjack.Exp.var Flapjack.VarKind.local "mx")

def body599_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "mx")
  (Flapjack.Exp.var Flapjack.VarKind.local "g")) body599_7 body599_1

def body599_9 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "g", Flapjack.Exp.var Flapjack.VarKind.local "extra_gas"],
      Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "g", Flapjack.Exp.var Flapjack.VarKind.local "stipend"]])

def body599_10 : Prog (BitVec 64) :=
.seq body599_8 body599_9

def body599_11 : Prog (BitVec 64) :=
.dec ("g") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "gas") body599_10

def body599_12 : Prog (BitVec 64) :=
.dec ("mx") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "avail",
    Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "avail") (Flapjack.Exp.const 6#64)]) body599_11

def body599_13 : Prog (BitVec 64) :=
.dec ("avail") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "gas_left", Flapjack.Exp.var Flapjack.VarKind.local "memory_cost"],
    Flapjack.Exp.var Flapjack.VarKind.local "extra_gas"]) body599_12

def body599_14 : Prog (BitVec 64) :=
.seq body599_6 body599_13

def body599_15 : Prog (BitVec 64) :=
.decCall ("need") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.var Flapjack.VarKind.local "extra_gas", Flapjack.Exp.var Flapjack.VarKind.local "memory_cost"]) body599_14

def body599_16 : Prog (BitVec 64) :=
.seq body599_2 body599_15

def body599_17 : Prog (BitVec 64) :=
.dec ("stipend") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body599_16

def body599_18 : Prog (BitVec 64) :=
.decCall ("vz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "value"]) body599_17

def originalData599 : Decl (BitVec 64) :=
.function { name := "calculate_message_call_gas", inline := false, exported := false, params := [("value", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("gas", Flapjack.Shape.one), ("gas_left", Flapjack.Shape.one), ("memory_cost", Flapjack.Shape.one),
  ("extra_gas", Flapjack.Shape.one)], body := body599_18, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData599 : Decl (BitVec 64) :=
.function { name := "calculate_message_call_gas", inline := false, exported := false, params := [("value", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("gas", Flapjack.Shape.one), ("gas_left", Flapjack.Shape.one), ("memory_cost", Flapjack.Shape.one),
  ("extra_gas", Flapjack.Shape.one)], body := body599_18, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def original599 := Pancake.PanLang.declToHOL originalData599
def simplified599 := Pancake.PanLang.declToHOL simplifiedData599
end InitECandidate.Proofs.FrontendStages.Declarations
