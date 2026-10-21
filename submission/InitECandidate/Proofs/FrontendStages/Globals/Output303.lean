import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data303
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate286
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody303_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 1#64)

def globalBody303_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody303_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "len") (Flapjack.Exp.const 0#64)) globalBody303_0 globalBody303_1

def globalBody303_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 400#64]

def globalBody303_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 384#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "p")

def globalBody303_5 : Prog (BitVec 64) :=
.seq globalBody303_3 globalBody303_4

def globalBody303_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 392#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "len")

def globalBody303_7 : Prog (BitVec 64) :=
.seq globalBody303_5 globalBody303_6

def globalBody303_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "top"), none)) "rlp_decode_fully"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 1#64],
    Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "len", Flapjack.Exp.const 1#64]]

def globalBody303_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "t" (Flapjack.Exp.var Flapjack.VarKind.local "b0")

def globalBody303_10 : Prog (BitVec 64) :=
.seq globalBody303_8 globalBody303_9

def globalBody303_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "nfields" (Flapjack.Exp.const 11#64)

def globalBody303_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 1#64)) globalBody303_11 globalBody303_1

def globalBody303_13 : Prog (BitVec 64) :=
.seq globalBody303_10 globalBody303_12

def globalBody303_14 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "nfields" (Flapjack.Exp.const 12#64)

def globalBody303_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 2#64)) globalBody303_14 globalBody303_1

def globalBody303_16 : Prog (BitVec 64) :=
.seq globalBody303_13 globalBody303_15

def globalBody303_17 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "nfields" (Flapjack.Exp.const 14#64)

def globalBody303_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 3#64)) globalBody303_17 globalBody303_1

def globalBody303_19 : Prog (BitVec 64) :=
.seq globalBody303_16 globalBody303_18

def globalBody303_20 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "nfields" (Flapjack.Exp.const 13#64)

def globalBody303_21 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 4#64)) globalBody303_20 globalBody303_1

def globalBody303_22 : Prog (BitVec 64) :=
.seq globalBody303_19 globalBody303_21

def globalBody303_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "top"), none)) "rlp_decode_fully"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "len"]

def globalBody303_24 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 2#64)

def globalBody303_25 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "b0")
        (Flapjack.Exp.const 192#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 254#64)
        (Flapjack.Exp.var Flapjack.VarKind.local "b0"))]) globalBody303_23 globalBody303_24

def globalBody303_26 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "b0") (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 4#64) (Flapjack.Exp.var Flapjack.VarKind.local "b0"))]) globalBody303_22 globalBody303_25

def globalBody303_27 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def globalBody303_28 : Prog (BitVec 64) :=
.seq globalBody303_26 globalBody303_27

def globalBody303_29 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 3#64)

def globalBody303_30 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "top"))
  (Flapjack.Exp.const 1#64)) globalBody303_29 globalBody303_1

def globalBody303_31 : Prog (BitVec 64) :=
.seq globalBody303_28 globalBody303_30

def globalBody303_32 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 4#64)

def globalBody303_33 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "lst"))
  (Flapjack.Exp.var Flapjack.VarKind.local "nfields")) globalBody303_32 globalBody303_1

def globalBody303_34 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_scalar_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 0#64, Flapjack.Exp.const 8#64,
    Flapjack.Exp.const 12#64]

def globalBody303_35 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def globalBody303_36 : Prog (BitVec 64) :=
.seq globalBody303_34 globalBody303_35

def globalBody303_37 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "k" (Flapjack.Exp.const 1#64)

def globalBody303_38 : Prog (BitVec 64) :=
.seq globalBody303_36 globalBody303_37

def globalBody303_39 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 0#64)) globalBody303_38 globalBody303_1

def globalBody303_40 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_scalar_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 8#64,
    Flapjack.Exp.const 12#64]

def globalBody303_41 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "v"
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 0#64])

def globalBody303_42 : Prog (BitVec 64) :=
.seq globalBody303_40 globalBody303_41

def globalBody303_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "v"), none)) "tx_scalar_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 32#64]

def globalBody303_44 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 4#64)) globalBody303_42 globalBody303_43

def globalBody303_45 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def globalBody303_46 : Prog (BitVec 64) :=
.seq globalBody303_44 globalBody303_45

def globalBody303_47 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "k"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64])

def globalBody303_48 : Prog (BitVec 64) :=
.seq globalBody303_46 globalBody303_47

def globalBody303_49 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "v"), none)) "tx_scalar_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 0#64]

def globalBody303_50 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def globalBody303_51 : Prog (BitVec 64) :=
.seq globalBody303_49 globalBody303_50

def globalBody303_52 : Prog (BitVec 64) :=
.seq globalBody303_51 globalBody303_47

def globalBody303_53 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def globalBody303_54 : Prog (BitVec 64) :=
.seq globalBody303_49 globalBody303_53

def globalBody303_55 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "v"), none)) "tx_scalar_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64],
    Flapjack.Exp.const 0#64]

def globalBody303_56 : Prog (BitVec 64) :=
.seq globalBody303_54 globalBody303_55

def globalBody303_57 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def globalBody303_58 : Prog (BitVec 64) :=
.seq globalBody303_56 globalBody303_57

def globalBody303_59 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "k"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 2#64])

def globalBody303_60 : Prog (BitVec 64) :=
.seq globalBody303_58 globalBody303_59

def globalBody303_61 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 1#64) (Flapjack.Exp.var Flapjack.VarKind.local "t")) globalBody303_52 globalBody303_60

def globalBody303_62 : Prog (BitVec 64) :=
.seq globalBody303_48 globalBody303_61

def globalBody303_63 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_scalar_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 0#64,
    Flapjack.Exp.const 14#64]

def globalBody303_64 : Prog (BitVec 64) :=
.seq globalBody303_62 globalBody303_63

def globalBody303_65 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 144#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def globalBody303_66 : Prog (BitVec 64) :=
.seq globalBody303_64 globalBody303_65

def globalBody303_67 : Prog (BitVec 64) :=
.seq globalBody303_66 globalBody303_47

def globalBody303_68 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_fixed_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 20#64]

def globalBody303_69 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_to_item"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k"]

def globalBody303_70 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 3#64)) globalBody303_68 globalBody303_69

def globalBody303_71 : Prog (BitVec 64) :=
.seq globalBody303_67 globalBody303_70

def globalBody303_72 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 152#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def globalBody303_73 : Prog (BitVec 64) :=
.seq globalBody303_71 globalBody303_72

def globalBody303_74 : Prog (BitVec 64) :=
.seq globalBody303_73 globalBody303_47

def globalBody303_75 : Prog (BitVec 64) :=
.seq globalBody303_74 globalBody303_43

def globalBody303_76 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def globalBody303_77 : Prog (BitVec 64) :=
.seq globalBody303_75 globalBody303_76

def globalBody303_78 : Prog (BitVec 64) :=
.seq globalBody303_77 globalBody303_47

def globalBody303_79 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 192#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "data"))

def globalBody303_80 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 200#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "data"))

def globalBody303_81 : Prog (BitVec 64) :=
.seq globalBody303_79 globalBody303_80

def globalBody303_82 : Prog (BitVec 64) :=
.seq globalBody303_81 globalBody303_47

def globalBody303_83 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 208#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "acc"))

def globalBody303_84 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 216#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "acc"))

def globalBody303_85 : Prog (BitVec 64) :=
.seq globalBody303_83 globalBody303_84

def globalBody303_86 : Prog (BitVec 64) :=
.seq globalBody303_85 globalBody303_47

def globalBody303_87 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_access_list") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "al"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "al")]) globalBody303_86

def globalBody303_88 : Prog (BitVec 64) :=
.decCall ("al") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_list_item") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k"]) globalBody303_87

def globalBody303_89 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 0#64)) globalBody303_88 globalBody303_1

def globalBody303_90 : Prog (BitVec 64) :=
.seq globalBody303_82 globalBody303_89

def globalBody303_91 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 224#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def globalBody303_92 : Prog (BitVec 64) :=
.seq globalBody303_43 globalBody303_91

def globalBody303_93 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 256#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "bh"))

def globalBody303_94 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 264#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "bh"))

def globalBody303_95 : Prog (BitVec 64) :=
.seq globalBody303_93 globalBody303_94

def globalBody303_96 : Prog (BitVec 64) :=
.seq globalBody303_95 globalBody303_59

def globalBody303_97 : Prog (BitVec 64) :=
.decCall ("bh") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_blob_hashes") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "bl"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "bl")]) globalBody303_96

def globalBody303_98 : Prog (BitVec 64) :=
.decCall ("bl") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_list_item") ([Flapjack.Exp.var Flapjack.VarKind.local "arr",
  Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64]]) globalBody303_97

def globalBody303_99 : Prog (BitVec 64) :=
.seq globalBody303_92 globalBody303_98

def globalBody303_100 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 3#64)) globalBody303_99 globalBody303_1

def globalBody303_101 : Prog (BitVec 64) :=
.seq globalBody303_90 globalBody303_100

def globalBody303_102 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 272#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "au"))

def globalBody303_103 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 280#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "au"))

def globalBody303_104 : Prog (BitVec 64) :=
.seq globalBody303_102 globalBody303_103

def globalBody303_105 : Prog (BitVec 64) :=
.seq globalBody303_104 globalBody303_47

def globalBody303_106 : Prog (BitVec 64) :=
.decCall ("au") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_authorizations") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "aul"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "aul")]) globalBody303_105

def globalBody303_107 : Prog (BitVec 64) :=
.decCall ("aul") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_list_item") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k"]) globalBody303_106

def globalBody303_108 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 4#64)) globalBody303_107 globalBody303_1

def globalBody303_109 : Prog (BitVec 64) :=
.seq globalBody303_101 globalBody303_108

def globalBody303_110 : Prog (BitVec 64) :=
.seq globalBody303_109 globalBody303_43

def globalBody303_111 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 288#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def globalBody303_112 : Prog (BitVec 64) :=
.seq globalBody303_110 globalBody303_111

def globalBody303_113 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "v"), none)) "tx_scalar_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64],
    Flapjack.Exp.const 32#64]

def globalBody303_114 : Prog (BitVec 64) :=
.seq globalBody303_112 globalBody303_113

def globalBody303_115 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 320#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def globalBody303_116 : Prog (BitVec 64) :=
.seq globalBody303_114 globalBody303_115

def globalBody303_117 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "v"), none)) "tx_scalar_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 2#64],
    Flapjack.Exp.const 32#64]

def globalBody303_118 : Prog (BitVec 64) :=
.seq globalBody303_116 globalBody303_117

def globalBody303_119 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 352#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def globalBody303_120 : Prog (BitVec 64) :=
.seq globalBody303_118 globalBody303_119

def globalBody303_121 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "tx")

def globalBody303_122 : Prog (BitVec 64) :=
.seq globalBody303_120 globalBody303_121

def globalBody303_123 : Prog (BitVec 64) :=
.decCall ("data") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_bytes_item") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k"]) globalBody303_122

def globalBody303_124 : Prog (BitVec 64) :=
.seq globalBody303_78 globalBody303_123

def globalBody303_125 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) globalBody303_124

def globalBody303_126 : Prog (BitVec 64) :=
.seq globalBody303_39 globalBody303_125

def globalBody303_127 : Prog (BitVec 64) :=
.dec ("w") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody303_126

def globalBody303_128 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody303_127

def globalBody303_129 : Prog (BitVec 64) :=
.seq globalBody303_33 globalBody303_128

def globalBody303_130 : Prog (BitVec 64) :=
.dec ("arr") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "lst")) globalBody303_129

def globalBody303_131 : Prog (BitVec 64) :=
.decCall ("lst") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_list_to_slices") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "top"),
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "top")]) globalBody303_130

def globalBody303_132 : Prog (BitVec 64) :=
.seq globalBody303_31 globalBody303_131

def globalBody303_133 : Prog (BitVec 64) :=
.dec ("nfields") (Flapjack.Shape.one) (Flapjack.Exp.const 9#64) globalBody303_132

def globalBody303_134 : Prog (BitVec 64) :=
.dec ("t") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody303_133

def globalBody303_135 : Prog (BitVec 64) :=
.dec ("top") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) globalBody303_134

def globalBody303_136 : Prog (BitVec 64) :=
.seq globalBody303_7 globalBody303_135

def globalBody303_137 : Prog (BitVec 64) :=
.decCall ("tx") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 400#64]) globalBody303_136

def globalBody303_138 : Prog (BitVec 64) :=
.dec ("b0") (Flapjack.Shape.one) (Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "p")) globalBody303_137

def globalBody303_139 : Prog (BitVec 64) :=
.seq globalBody303_2 globalBody303_138

def globalData303 : Decl (BitVec 64) :=
.function { name := "decode_transaction_rlp", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := globalBody303_139, returnShape := (Flapjack.Shape.one) }
def globalOutput303 := Pancake.PanLang.declToHOL globalData303
end InitECandidate.Proofs.FrontendStages.Declarations
