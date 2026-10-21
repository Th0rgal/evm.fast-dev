import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify215
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body231_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body231_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body231_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "parent_blob_gas")
  (Flapjack.Exp.const 1835008#64)) body231_0 body231_1

def body231_3 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "excess", Flapjack.Exp.var Flapjack.VarKind.local "q"])

def body231_4 : Prog (BitVec 64) :=
.decCall ("q") (Flapjack.Shape.one) ("udiv") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "used",
      Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 21#64, Flapjack.Exp.const 14#64]],
  Flapjack.Exp.const 21#64]) body231_3

def body231_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "gt") (Flapjack.Exp.const 0#64)) body231_4 body231_1

def body231_6 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "parent_blob_gas", Flapjack.Exp.const 1835008#64])

def body231_7 : Prog (BitVec 64) :=
.seq body231_5 body231_6

def body231_8 : Prog (BitVec 64) :=
.decCall ("gt") (Flapjack.Shape.one) ("u256_gt") ([Flapjack.Exp.var Flapjack.VarKind.local "base_blob_tx_price", Flapjack.Exp.var Flapjack.VarKind.local "target_price"]) body231_7

def body231_9 : Prog (BitVec 64) :=
.decCall ("base_blob_tx_price") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "base_cost", Flapjack.Exp.var Flapjack.VarKind.local "base_fee"]) body231_8

def body231_10 : Prog (BitVec 64) :=
.decCall ("base_cost") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.const 8192#64]) body231_9

def body231_11 : Prog (BitVec 64) :=
.decCall ("target_price") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "per_blob", Flapjack.Exp.var Flapjack.VarKind.local "price"]) body231_10

def body231_12 : Prog (BitVec 64) :=
.decCall ("per_blob") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.const 131072#64]) body231_11

def body231_13 : Prog (BitVec 64) :=
.decCall ("price") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("calculate_blob_gas_price") ([Flapjack.Exp.var Flapjack.VarKind.local "excess"]) body231_12

def body231_14 : Prog (BitVec 64) :=
.seq body231_2 body231_13

def body231_15 : Prog (BitVec 64) :=
.dec ("parent_blob_gas") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "excess", Flapjack.Exp.var Flapjack.VarKind.local "used"]) body231_14

def body231_16 : Prog (BitVec 64) :=
.dec ("base_fee") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 160#64])) body231_15

def body231_17 : Prog (BitVec 64) :=
.dec ("used") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 200#64])) body231_16

def body231_18 : Prog (BitVec 64) :=
.dec ("excess") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "parent", Flapjack.Exp.const 208#64])) body231_17

def originalData231 : Decl (BitVec 64) :=
.function { name := "calculate_excess_blob_gas", inline := false, exported := false, params := [("parent", Flapjack.Shape.one)], body := body231_18, returnShape := (Flapjack.Shape.one) }
def simplifiedData231 : Decl (BitVec 64) :=
.function { name := "calculate_excess_blob_gas", inline := false, exported := false, params := [("parent", Flapjack.Shape.one)], body := body231_18, returnShape := (Flapjack.Shape.one) }
def original231 := Pancake.PanLang.declToHOL originalData231
def simplified231 := Pancake.PanLang.declToHOL simplifiedData231
end InitECandidate.Proofs.FrontendStages.Declarations
