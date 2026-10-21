import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data231
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate213
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody231_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody231_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody231_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "parent_blob_gas")
  (Flapjack.Exp.const 1835008#64)) globalBody231_0 globalBody231_1

def globalBody231_3 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "excess", Flapjack.Exp.var Flapjack.VarKind.local "q"])

def globalBody231_4 : Prog (BitVec 64) :=
.decCall ("q") (Flapjack.Shape.one) ("udiv") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "used",
      Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 21#64, Flapjack.Exp.const 14#64]],
  Flapjack.Exp.const 21#64]) globalBody231_3

def globalBody231_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "gt") (Flapjack.Exp.const 0#64)) globalBody231_4 globalBody231_1

def globalBody231_6 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "parent_blob_gas", Flapjack.Exp.const 1835008#64])

def globalBody231_7 : Prog (BitVec 64) :=
.seq globalBody231_5 globalBody231_6

def globalBody231_8 : Prog (BitVec 64) :=
.decCall ("gt") (Flapjack.Shape.one) ("u256_gt") ([Flapjack.Exp.var Flapjack.VarKind.local "base_blob_tx_price", Flapjack.Exp.var Flapjack.VarKind.local "target_price"]) globalBody231_7

def globalBody231_9 : Prog (BitVec 64) :=
.decCall ("base_blob_tx_price") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "base_cost", Flapjack.Exp.var Flapjack.VarKind.local "base_fee"]) globalBody231_8

def globalBody231_10 : Prog (BitVec 64) :=
.decCall ("base_cost") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.const 8192#64]) globalBody231_9

def globalBody231_11 : Prog (BitVec 64) :=
.decCall ("target_price") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "per_blob", Flapjack.Exp.var Flapjack.VarKind.local "price"]) globalBody231_10

def globalBody231_12 : Prog (BitVec 64) :=
.decCall ("per_blob") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.const 131072#64]) globalBody231_11

def globalBody231_13 : Prog (BitVec 64) :=
.decCall ("price") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_blob_gas_price") ([Flapjack.Exp.var Flapjack.VarKind.local "excess"]) globalBody231_12

def globalBody231_14 : Prog (BitVec 64) :=
.seq globalBody231_2 globalBody231_13

def globalBody231_15 : Prog (BitVec 64) :=
.dec ("parent_blob_gas") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "excess", Flapjack.Exp.var Flapjack.VarKind.local "used"]) globalBody231_14

def globalBody231_16 : Prog (BitVec 64) :=
.dec ("base_fee") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 160#64])) globalBody231_15

def globalBody231_17 : Prog (BitVec 64) :=
.dec ("used") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 200#64])) globalBody231_16

def globalBody231_18 : Prog (BitVec 64) :=
.dec ("excess") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 208#64])) globalBody231_17

def globalData231 : Decl (BitVec 64) :=
.function { name := "calculate_excess_blob_gas", inline := false, exported := false, params := [("parent", Flapjack.Shape.one)], body := globalBody231_18, returnShape := (Flapjack.Shape.one) }
def globalOutput231 := Pancake.PanLang.declToHOL globalData231
end InitECandidate.Proofs.FrontendStages.Declarations
