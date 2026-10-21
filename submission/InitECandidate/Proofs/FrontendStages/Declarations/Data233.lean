import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify217
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body233_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 10#64)

def body233_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body233_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) body233_0 body233_1

def body233_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "parent_base_fee")

def body233_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_used")
  (Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_target")) body233_3 body233_1

def body233_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "bfd"), none)) "u256_from_word" [Flapjack.Exp.const 1#64]

def body233_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64)) body233_5 body233_1

def body233_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "r")

def body233_8 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add") ([Flapjack.Exp.var Flapjack.VarKind.local "parent_base_fee", Flapjack.Exp.var Flapjack.VarKind.local "bfd"]) body233_7

def body233_9 : Prog (BitVec 64) :=
.seq body233_6 body233_8

def body233_10 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "bfd"]) body233_9

def body233_11 : Prog (BitVec 64) :=
.decCall ("bfd") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_div") ([Flapjack.Exp.var Flapjack.VarKind.local "tfd", Flapjack.Exp.var Flapjack.VarKind.local "eight"]) body233_10

def body233_12 : Prog (BitVec 64) :=
.decCall ("tfd") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_div") ([Flapjack.Exp.var Flapjack.VarKind.local "pfd", Flapjack.Exp.var Flapjack.VarKind.local "tgt"]) body233_11

def body233_13 : Prog (BitVec 64) :=
.decCall ("pfd") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "parent_base_fee", Flapjack.Exp.var Flapjack.VarKind.local "delta"]) body233_12

def body233_14 : Prog (BitVec 64) :=
.decCall ("delta") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_used",
      Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_target"]]) body233_13

def body233_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_target")
  (Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_used")) body233_14 body233_1

def body233_16 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "r2")

def body233_17 : Prog (BitVec 64) :=
.decCall ("r2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "parent_base_fee", Flapjack.Exp.var Flapjack.VarKind.local "bfd2"]) body233_16

def body233_18 : Prog (BitVec 64) :=
.decCall ("bfd2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_div") ([Flapjack.Exp.var Flapjack.VarKind.local "tfd2", Flapjack.Exp.var Flapjack.VarKind.local "eight"]) body233_17

def body233_19 : Prog (BitVec 64) :=
.decCall ("tfd2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_div") ([Flapjack.Exp.var Flapjack.VarKind.local "pfd2", Flapjack.Exp.var Flapjack.VarKind.local "tgt"]) body233_18

def body233_20 : Prog (BitVec 64) :=
.decCall ("pfd2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "parent_base_fee", Flapjack.Exp.var Flapjack.VarKind.local "delta2"]) body233_19

def body233_21 : Prog (BitVec 64) :=
.decCall ("delta2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_target",
      Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_used"]]) body233_20

def body233_22 : Prog (BitVec 64) :=
.seq body233_15 body233_21

def body233_23 : Prog (BitVec 64) :=
.decCall ("eight") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.const 8#64]) body233_22

def body233_24 : Prog (BitVec 64) :=
.decCall ("tgt") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_target"]) body233_23

def body233_25 : Prog (BitVec 64) :=
.seq body233_4 body233_24

def body233_26 : Prog (BitVec 64) :=
.seq body233_2 body233_25

def body233_27 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("check_gas_limit") ([Flapjack.Exp.var Flapjack.VarKind.local "block_gas_limit", Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_limit"]) body233_26

def body233_28 : Prog (BitVec 64) :=
.dec ("parent_gas_target") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_limit")
  (Flapjack.Exp.const 1#64)) body233_27

def body233_29 : Prog (BitVec 64) :=
.seq body233_2 body233_4

def body233_30 : Prog (BitVec 64) :=
.seq body233_29 body233_24

def body233_31 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("check_gas_limit") ([Flapjack.Exp.var Flapjack.VarKind.local "block_gas_limit", Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_limit"]) body233_30

def body233_32 : Prog (BitVec 64) :=
.dec ("parent_gas_target") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_limit")
  (Flapjack.Exp.const 1#64)) body233_31

def originalData233 : Decl (BitVec 64) :=
.function { name := "calculate_base_fee_per_gas", inline := false, exported := false, params := [("block_gas_limit", Flapjack.Shape.one), ("parent_gas_limit", Flapjack.Shape.one),
  ("parent_gas_used", Flapjack.Shape.one),
  ("parent_base_fee",
    Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body233_28, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData233 : Decl (BitVec 64) :=
.function { name := "calculate_base_fee_per_gas", inline := false, exported := false, params := [("block_gas_limit", Flapjack.Shape.one), ("parent_gas_limit", Flapjack.Shape.one),
  ("parent_gas_used", Flapjack.Shape.one),
  ("parent_base_fee",
    Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body233_32, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def original233 := Pancake.PanLang.declToHOL originalData233
def simplified233 := Pancake.PanLang.declToHOL simplifiedData233
end InitECandidate.Proofs.FrontendStages.Declarations
