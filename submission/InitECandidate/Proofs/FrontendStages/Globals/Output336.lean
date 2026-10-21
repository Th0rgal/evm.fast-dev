import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data336
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate320
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody336_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 40#64)

def globalBody336_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody336_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64)) globalBody336_0 globalBody336_1

def globalBody336_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "lt") (Flapjack.Exp.const 0#64)) globalBody336_0 globalBody336_1

def globalBody336_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "u256_is_zero"
  [Flapjack.Exp.var Flapjack.VarKind.local "s"]

def globalBody336_5 : Prog (BitVec 64) :=
.seq globalBody336_3 globalBody336_4

def globalBody336_6 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 41#64)

def globalBody336_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64)) globalBody336_6 globalBody336_1

def globalBody336_8 : Prog (BitVec 64) :=
.seq globalBody336_5 globalBody336_7

def globalBody336_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "gt") (Flapjack.Exp.const 0#64)) globalBody336_6 globalBody336_1

def globalBody336_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "signing_hash_pre155"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "out_hash"]

def globalBody336_11 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"), Flapjack.Exp.const 27#64])

def globalBody336_12 : Prog (BitVec 64) :=
.seq globalBody336_10 globalBody336_11

def globalBody336_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"))
        (Flapjack.Exp.const 27#64),
      Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"))
        (Flapjack.Exp.const 28#64)])) globalBody336_12 globalBody336_1

def globalBody336_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "fits") (Flapjack.Exp.const 0#64)) globalBody336_13 globalBody336_1

def globalBody336_15 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 42#64)

def globalBody336_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq35") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq36") (Flapjack.Exp.const 0#64))]) globalBody336_15 globalBody336_1

def globalBody336_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "signing_hash_155"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "chain_id",
    Flapjack.Exp.var Flapjack.VarKind.local "out_hash"]

def globalBody336_18 : Prog (BitVec 64) :=
.seq globalBody336_16 globalBody336_17

def globalBody336_19 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "eq36")

def globalBody336_20 : Prog (BitVec 64) :=
.seq globalBody336_18 globalBody336_19

def globalBody336_21 : Prog (BitVec 64) :=
.decCall ("eq36") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "v36"]) globalBody336_20

def globalBody336_22 : Prog (BitVec 64) :=
.decCall ("eq35") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "v35"]) globalBody336_21

def globalBody336_23 : Prog (BitVec 64) :=
.decCall ("v36") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add") ([Flapjack.Exp.var Flapjack.VarKind.local "x2",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 36#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]]) globalBody336_22

def globalBody336_24 : Prog (BitVec 64) :=
.decCall ("v35") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add") ([Flapjack.Exp.var Flapjack.VarKind.local "x2",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 35#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]]) globalBody336_23

def globalBody336_25 : Prog (BitVec 64) :=
.decCall ("x2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add") ([Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.var Flapjack.VarKind.local "c"]) globalBody336_24

def globalBody336_26 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.var Flapjack.VarKind.local "chain_id", Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
    Flapjack.Exp.const 0#64]) globalBody336_25

def globalBody336_27 : Prog (BitVec 64) :=
.seq globalBody336_14 globalBody336_26

def globalBody336_28 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 0#64)) globalBody336_27 globalBody336_1

def globalBody336_29 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 43#64)

def globalBody336_30 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "fits") (Flapjack.Exp.const 0#64)) globalBody336_29 globalBody336_1

def globalBody336_31 : Prog (BitVec 64) :=
.seq globalBody336_28 globalBody336_30

def globalBody336_32 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 1#64)
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"))) globalBody336_29 globalBody336_1

def globalBody336_33 : Prog (BitVec 64) :=
.seq globalBody336_31 globalBody336_32

def globalBody336_34 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "signing_hash_2930"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "out_hash"]

def globalBody336_35 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 1#64)) globalBody336_34 globalBody336_1

def globalBody336_36 : Prog (BitVec 64) :=
.seq globalBody336_33 globalBody336_35

def globalBody336_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "signing_hash_1559"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "out_hash"]

def globalBody336_38 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 2#64)) globalBody336_37 globalBody336_1

def globalBody336_39 : Prog (BitVec 64) :=
.seq globalBody336_36 globalBody336_38

def globalBody336_40 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "signing_hash_4844"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "out_hash"]

def globalBody336_41 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 3#64)) globalBody336_40 globalBody336_1

def globalBody336_42 : Prog (BitVec 64) :=
.seq globalBody336_39 globalBody336_41

def globalBody336_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "signing_hash_7702"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "out_hash"]

def globalBody336_44 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 4#64)) globalBody336_43 globalBody336_1

def globalBody336_45 : Prog (BitVec 64) :=
.seq globalBody336_42 globalBody336_44

def globalBody336_46 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"))

def globalBody336_47 : Prog (BitVec 64) :=
.seq globalBody336_45 globalBody336_46

def globalBody336_48 : Prog (BitVec 64) :=
.decCall ("fits") (Flapjack.Shape.one) ("u256_fits_word") ([Flapjack.Exp.var Flapjack.VarKind.local "v"]) globalBody336_47

def globalBody336_49 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 288#64])) globalBody336_48

def globalBody336_50 : Prog (BitVec 64) :=
.dec ("t") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 0#64])) globalBody336_49

def globalBody336_51 : Prog (BitVec 64) :=
.seq globalBody336_9 globalBody336_50

def globalBody336_52 : Prog (BitVec 64) :=
.decCall ("gt") (Flapjack.Shape.one) ("u256_gt") ([Flapjack.Exp.var Flapjack.VarKind.local "s",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 16134479119472337056#64, Flapjack.Exp.const 6725966010171805725#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 9223372036854775807#64]]) globalBody336_51

def globalBody336_53 : Prog (BitVec 64) :=
.seq globalBody336_8 globalBody336_52

def globalBody336_54 : Prog (BitVec 64) :=
.decCall ("lt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "r",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 13822214165235122497#64, Flapjack.Exp.const 13451932020343611451#64,
      Flapjack.Exp.const 18446744073709551614#64, Flapjack.Exp.const 18446744073709551615#64]]) globalBody336_53

def globalBody336_55 : Prog (BitVec 64) :=
.seq globalBody336_2 globalBody336_54

def globalBody336_56 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "r"]) globalBody336_55

def globalBody336_57 : Prog (BitVec 64) :=
.dec ("s") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 352#64])) globalBody336_56

def globalBody336_58 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 320#64])) globalBody336_57

def globalData336 : Decl (BitVec 64) :=
.function { name := "signature_recovery_parameters", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("chain_id", Flapjack.Shape.one), ("out_hash", Flapjack.Shape.one)], body := globalBody336_58, returnShape := (Flapjack.Shape.one) }
def globalOutput336 := Pancake.PanLang.declToHOL globalData336
end InitECandidate.Proofs.FrontendStages.Declarations
