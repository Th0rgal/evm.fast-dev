import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data599
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate583
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody599_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "stipend" (Flapjack.Exp.const 2300#64)

def globalBody599_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody599_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vz") (Flapjack.Exp.const 0#64)) globalBody599_0 globalBody599_1

def globalBody599_3 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.var Flapjack.VarKind.local "s"])

def globalBody599_4 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.var Flapjack.VarKind.local "gas", Flapjack.Exp.var Flapjack.VarKind.local "stipend"]) globalBody599_3

def globalBody599_5 : Prog (BitVec 64) :=
.decCall ("c") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.var Flapjack.VarKind.local "gas", Flapjack.Exp.var Flapjack.VarKind.local "extra_gas"]) globalBody599_4

def globalBody599_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "gas_left")
  (Flapjack.Exp.var Flapjack.VarKind.local "need")) globalBody599_5 globalBody599_1

def globalBody599_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "g" (Flapjack.Exp.var Flapjack.VarKind.local "mx")

def globalBody599_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "mx")
  (Flapjack.Exp.var Flapjack.VarKind.local "g")) globalBody599_7 globalBody599_1

def globalBody599_9 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "g", Flapjack.Exp.var Flapjack.VarKind.local "extra_gas"],
      Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "g", Flapjack.Exp.var Flapjack.VarKind.local "stipend"]])

def globalBody599_10 : Prog (BitVec 64) :=
.seq globalBody599_8 globalBody599_9

def globalBody599_11 : Prog (BitVec 64) :=
.dec ("g") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "gas") globalBody599_10

def globalBody599_12 : Prog (BitVec 64) :=
.dec ("mx") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "avail",
    Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "avail") (Flapjack.Exp.const 6#64)]) globalBody599_11

def globalBody599_13 : Prog (BitVec 64) :=
.dec ("avail") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.sub
      [Flapjack.Exp.var Flapjack.VarKind.local "gas_left", Flapjack.Exp.var Flapjack.VarKind.local "memory_cost"],
    Flapjack.Exp.var Flapjack.VarKind.local "extra_gas"]) globalBody599_12

def globalBody599_14 : Prog (BitVec 64) :=
.seq globalBody599_6 globalBody599_13

def globalBody599_15 : Prog (BitVec 64) :=
.decCall ("need") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.var Flapjack.VarKind.local "extra_gas", Flapjack.Exp.var Flapjack.VarKind.local "memory_cost"]) globalBody599_14

def globalBody599_16 : Prog (BitVec 64) :=
.seq globalBody599_2 globalBody599_15

def globalBody599_17 : Prog (BitVec 64) :=
.dec ("stipend") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody599_16

def globalBody599_18 : Prog (BitVec 64) :=
.decCall ("vz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "value"]) globalBody599_17

def globalData599 : Decl (BitVec 64) :=
.function { name := "calculate_message_call_gas", inline := false, exported := false, params := [("value", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("gas", Flapjack.Shape.one), ("gas_left", Flapjack.Shape.one), ("memory_cost", Flapjack.Shape.one),
  ("extra_gas", Flapjack.Shape.one)], body := globalBody599_18, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput599 := Pancake.PanLang.declToHOL globalData599
end InitECandidate.Proofs.FrontendStages.Declarations
