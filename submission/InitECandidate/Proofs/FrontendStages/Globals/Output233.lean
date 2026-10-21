import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data233
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate215
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody233_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 10#64)

def globalBody233_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody233_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) globalBody233_0 globalBody233_1

def globalBody233_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "parent_base_fee")

def globalBody233_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_used")
  (Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_target")) globalBody233_3 globalBody233_1

def globalBody233_5 : Prog (BitVec 64) :=
.seq globalBody233_2 globalBody233_4

def globalBody233_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "bfd"), none)) "u256_from_word" [Flapjack.Exp.const 1#64]

def globalBody233_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64)) globalBody233_6 globalBody233_1

def globalBody233_8 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "r")

def globalBody233_9 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add") ([Flapjack.Exp.var Flapjack.VarKind.local "parent_base_fee", Flapjack.Exp.var Flapjack.VarKind.local "bfd"]) globalBody233_8

def globalBody233_10 : Prog (BitVec 64) :=
.seq globalBody233_7 globalBody233_9

def globalBody233_11 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "bfd"]) globalBody233_10

def globalBody233_12 : Prog (BitVec 64) :=
.decCall ("bfd") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_div") ([Flapjack.Exp.var Flapjack.VarKind.local "tfd", Flapjack.Exp.var Flapjack.VarKind.local "eight"]) globalBody233_11

def globalBody233_13 : Prog (BitVec 64) :=
.decCall ("tfd") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_div") ([Flapjack.Exp.var Flapjack.VarKind.local "pfd", Flapjack.Exp.var Flapjack.VarKind.local "tgt"]) globalBody233_12

def globalBody233_14 : Prog (BitVec 64) :=
.decCall ("pfd") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "parent_base_fee", Flapjack.Exp.var Flapjack.VarKind.local "delta"]) globalBody233_13

def globalBody233_15 : Prog (BitVec 64) :=
.decCall ("delta") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_used",
      Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_target"]]) globalBody233_14

def globalBody233_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_target")
  (Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_used")) globalBody233_15 globalBody233_1

def globalBody233_17 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "r2")

def globalBody233_18 : Prog (BitVec 64) :=
.decCall ("r2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "parent_base_fee", Flapjack.Exp.var Flapjack.VarKind.local "bfd2"]) globalBody233_17

def globalBody233_19 : Prog (BitVec 64) :=
.decCall ("bfd2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_div") ([Flapjack.Exp.var Flapjack.VarKind.local "tfd2", Flapjack.Exp.var Flapjack.VarKind.local "eight"]) globalBody233_18

def globalBody233_20 : Prog (BitVec 64) :=
.decCall ("tfd2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_div") ([Flapjack.Exp.var Flapjack.VarKind.local "pfd2", Flapjack.Exp.var Flapjack.VarKind.local "tgt"]) globalBody233_19

def globalBody233_21 : Prog (BitVec 64) :=
.decCall ("pfd2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "parent_base_fee", Flapjack.Exp.var Flapjack.VarKind.local "delta2"]) globalBody233_20

def globalBody233_22 : Prog (BitVec 64) :=
.decCall ("delta2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_target",
      Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_used"]]) globalBody233_21

def globalBody233_23 : Prog (BitVec 64) :=
.seq globalBody233_16 globalBody233_22

def globalBody233_24 : Prog (BitVec 64) :=
.decCall ("eight") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.const 8#64]) globalBody233_23

def globalBody233_25 : Prog (BitVec 64) :=
.decCall ("tgt") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_word") ([Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_target"]) globalBody233_24

def globalBody233_26 : Prog (BitVec 64) :=
.seq globalBody233_5 globalBody233_25

def globalBody233_27 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("check_gas_limit") ([Flapjack.Exp.var Flapjack.VarKind.local "block_gas_limit", Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_limit"]) globalBody233_26

def globalBody233_28 : Prog (BitVec 64) :=
.dec ("parent_gas_target") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "parent_gas_limit")
  (Flapjack.Exp.const 1#64)) globalBody233_27

def globalData233 : Decl (BitVec 64) :=
.function { name := "calculate_base_fee_per_gas", inline := false, exported := false, params := [("block_gas_limit", Flapjack.Shape.one), ("parent_gas_limit", Flapjack.Shape.one),
  ("parent_gas_used", Flapjack.Shape.one),
  ("parent_base_fee",
    Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := globalBody233_28, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput233 := Pancake.PanLang.declToHOL globalData233
end InitECandidate.Proofs.FrontendStages.Declarations
