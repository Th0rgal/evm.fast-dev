import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify320
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body336_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 40#64)

def body336_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body336_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64)) body336_0 body336_1

def body336_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "lt") (Flapjack.Exp.const 0#64)) body336_0 body336_1

def body336_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "u256_is_zero"
  [Flapjack.Exp.var Flapjack.VarKind.local "s"]

def body336_5 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 41#64)

def body336_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64)) body336_5 body336_1

def body336_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "gt") (Flapjack.Exp.const 0#64)) body336_5 body336_1

def body336_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "signing_hash_pre155"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "out_hash"]

def body336_9 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"), Flapjack.Exp.const 27#64])

def body336_10 : Prog (BitVec 64) :=
.seq body336_8 body336_9

def body336_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"))
        (Flapjack.Exp.const 27#64),
      Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"))
        (Flapjack.Exp.const 28#64)])) body336_10 body336_1

def body336_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "fits") (Flapjack.Exp.const 0#64)) body336_11 body336_1

def body336_13 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 42#64)

def body336_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq35") (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq36") (Flapjack.Exp.const 0#64))]) body336_13 body336_1

def body336_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "signing_hash_155"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "chain_id",
    Flapjack.Exp.var Flapjack.VarKind.local "out_hash"]

def body336_16 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "eq36")

def body336_17 : Prog (BitVec 64) :=
.seq body336_15 body336_16

def body336_18 : Prog (BitVec 64) :=
.seq body336_14 body336_17

def body336_19 : Prog (BitVec 64) :=
.decCall ("eq36") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "v36"]) body336_18

def body336_20 : Prog (BitVec 64) :=
.decCall ("eq35") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "v35"]) body336_19

def body336_21 : Prog (BitVec 64) :=
.decCall ("v36") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add") ([Flapjack.Exp.var Flapjack.VarKind.local "x2",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 36#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]]) body336_20

def body336_22 : Prog (BitVec 64) :=
.decCall ("v35") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add") ([Flapjack.Exp.var Flapjack.VarKind.local "x2",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 35#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]]) body336_21

def body336_23 : Prog (BitVec 64) :=
.decCall ("x2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add") ([Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.var Flapjack.VarKind.local "c"]) body336_22

def body336_24 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.var Flapjack.VarKind.local "chain_id", Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
    Flapjack.Exp.const 0#64]) body336_23

def body336_25 : Prog (BitVec 64) :=
.seq body336_12 body336_24

def body336_26 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 0#64)) body336_25 body336_1

def body336_27 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 43#64)

def body336_28 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "fits") (Flapjack.Exp.const 0#64)) body336_27 body336_1

def body336_29 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 1#64)
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"))) body336_27 body336_1

def body336_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "signing_hash_2930"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "out_hash"]

def body336_31 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 1#64)) body336_30 body336_1

def body336_32 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "signing_hash_1559"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "out_hash"]

def body336_33 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 2#64)) body336_32 body336_1

def body336_34 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "signing_hash_4844"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "out_hash"]

def body336_35 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 3#64)) body336_34 body336_1

def body336_36 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "signing_hash_7702"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.var Flapjack.VarKind.local "out_hash"]

def body336_37 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 4#64)) body336_36 body336_1

def body336_38 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"))

def body336_39 : Prog (BitVec 64) :=
.seq body336_37 body336_38

def body336_40 : Prog (BitVec 64) :=
.seq body336_35 body336_39

def body336_41 : Prog (BitVec 64) :=
.seq body336_33 body336_40

def body336_42 : Prog (BitVec 64) :=
.seq body336_31 body336_41

def body336_43 : Prog (BitVec 64) :=
.seq body336_29 body336_42

def body336_44 : Prog (BitVec 64) :=
.seq body336_28 body336_43

def body336_45 : Prog (BitVec 64) :=
.seq body336_26 body336_44

def body336_46 : Prog (BitVec 64) :=
.decCall ("fits") (Flapjack.Shape.one) ("u256_fits_word") ([Flapjack.Exp.var Flapjack.VarKind.local "v"]) body336_45

def body336_47 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 288#64])) body336_46

def body336_48 : Prog (BitVec 64) :=
.dec ("t") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 0#64])) body336_47

def body336_49 : Prog (BitVec 64) :=
.seq body336_7 body336_48

def body336_50 : Prog (BitVec 64) :=
.decCall ("gt") (Flapjack.Shape.one) ("u256_gt") ([Flapjack.Exp.var Flapjack.VarKind.local "s",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 16134479119472337056#64, Flapjack.Exp.const 6725966010171805725#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 9223372036854775807#64]]) body336_49

def body336_51 : Prog (BitVec 64) :=
.seq body336_6 body336_50

def body336_52 : Prog (BitVec 64) :=
.seq body336_4 body336_51

def body336_53 : Prog (BitVec 64) :=
.seq body336_3 body336_52

def body336_54 : Prog (BitVec 64) :=
.decCall ("lt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "r",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 13822214165235122497#64, Flapjack.Exp.const 13451932020343611451#64,
      Flapjack.Exp.const 18446744073709551614#64, Flapjack.Exp.const 18446744073709551615#64]]) body336_53

def body336_55 : Prog (BitVec 64) :=
.seq body336_2 body336_54

def body336_56 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "r"]) body336_55

def body336_57 : Prog (BitVec 64) :=
.dec ("s") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 352#64])) body336_56

def body336_58 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 320#64])) body336_57

def body336_59 : Prog (BitVec 64) :=
.seq body336_3 body336_4

def body336_60 : Prog (BitVec 64) :=
.seq body336_59 body336_6

def body336_61 : Prog (BitVec 64) :=
.seq body336_14 body336_15

def body336_62 : Prog (BitVec 64) :=
.seq body336_61 body336_16

def body336_63 : Prog (BitVec 64) :=
.decCall ("eq36") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "v36"]) body336_62

def body336_64 : Prog (BitVec 64) :=
.decCall ("eq35") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "v35"]) body336_63

def body336_65 : Prog (BitVec 64) :=
.decCall ("v36") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add") ([Flapjack.Exp.var Flapjack.VarKind.local "x2",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 36#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]]) body336_64

def body336_66 : Prog (BitVec 64) :=
.decCall ("v35") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add") ([Flapjack.Exp.var Flapjack.VarKind.local "x2",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 35#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]]) body336_65

def body336_67 : Prog (BitVec 64) :=
.decCall ("x2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add") ([Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.var Flapjack.VarKind.local "c"]) body336_66

def body336_68 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.var Flapjack.VarKind.local "chain_id", Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
    Flapjack.Exp.const 0#64]) body336_67

def body336_69 : Prog (BitVec 64) :=
.seq body336_12 body336_68

def body336_70 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 0#64)) body336_69 body336_1

def body336_71 : Prog (BitVec 64) :=
.seq body336_70 body336_28

def body336_72 : Prog (BitVec 64) :=
.seq body336_71 body336_29

def body336_73 : Prog (BitVec 64) :=
.seq body336_72 body336_31

def body336_74 : Prog (BitVec 64) :=
.seq body336_73 body336_33

def body336_75 : Prog (BitVec 64) :=
.seq body336_74 body336_35

def body336_76 : Prog (BitVec 64) :=
.seq body336_75 body336_37

def body336_77 : Prog (BitVec 64) :=
.seq body336_76 body336_38

def body336_78 : Prog (BitVec 64) :=
.decCall ("fits") (Flapjack.Shape.one) ("u256_fits_word") ([Flapjack.Exp.var Flapjack.VarKind.local "v"]) body336_77

def body336_79 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 288#64])) body336_78

def body336_80 : Prog (BitVec 64) :=
.dec ("t") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 0#64])) body336_79

def body336_81 : Prog (BitVec 64) :=
.seq body336_7 body336_80

def body336_82 : Prog (BitVec 64) :=
.decCall ("gt") (Flapjack.Shape.one) ("u256_gt") ([Flapjack.Exp.var Flapjack.VarKind.local "s",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 16134479119472337056#64, Flapjack.Exp.const 6725966010171805725#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 9223372036854775807#64]]) body336_81

def body336_83 : Prog (BitVec 64) :=
.seq body336_60 body336_82

def body336_84 : Prog (BitVec 64) :=
.decCall ("lt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "r",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 13822214165235122497#64, Flapjack.Exp.const 13451932020343611451#64,
      Flapjack.Exp.const 18446744073709551614#64, Flapjack.Exp.const 18446744073709551615#64]]) body336_83

def body336_85 : Prog (BitVec 64) :=
.seq body336_2 body336_84

def body336_86 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "r"]) body336_85

def body336_87 : Prog (BitVec 64) :=
.dec ("s") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 352#64])) body336_86

def body336_88 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 320#64])) body336_87

def originalData336 : Decl (BitVec 64) :=
.function { name := "signature_recovery_parameters", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("chain_id", Flapjack.Shape.one), ("out_hash", Flapjack.Shape.one)], body := body336_58, returnShape := (Flapjack.Shape.one) }
def simplifiedData336 : Decl (BitVec 64) :=
.function { name := "signature_recovery_parameters", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("chain_id", Flapjack.Shape.one), ("out_hash", Flapjack.Shape.one)], body := body336_88, returnShape := (Flapjack.Shape.one) }
def original336 := Pancake.PanLang.declToHOL originalData336
def simplified336 := Pancake.PanLang.declToHOL simplifiedData336
end InitECandidate.Proofs.FrontendStages.Declarations
