import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify287
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body303_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 1#64)

def body303_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body303_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "len") (Flapjack.Exp.const 0#64)) body303_0 body303_1

def body303_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 400#64]

def body303_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 384#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "p")

def body303_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 392#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "len")

def body303_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "top"), none)) "rlp_decode_fully"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 1#64],
    Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "len", Flapjack.Exp.const 1#64]]

def body303_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "t" (Flapjack.Exp.var Flapjack.VarKind.local "b0")

def body303_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "nfields" (Flapjack.Exp.const 11#64)

def body303_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 1#64)) body303_8 body303_1

def body303_10 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "nfields" (Flapjack.Exp.const 12#64)

def body303_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 2#64)) body303_10 body303_1

def body303_12 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "nfields" (Flapjack.Exp.const 14#64)

def body303_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 3#64)) body303_12 body303_1

def body303_14 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "nfields" (Flapjack.Exp.const 13#64)

def body303_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 4#64)) body303_14 body303_1

def body303_16 : Prog (BitVec 64) :=
.seq body303_13 body303_15

def body303_17 : Prog (BitVec 64) :=
.seq body303_11 body303_16

def body303_18 : Prog (BitVec 64) :=
.seq body303_9 body303_17

def body303_19 : Prog (BitVec 64) :=
.seq body303_7 body303_18

def body303_20 : Prog (BitVec 64) :=
.seq body303_6 body303_19

def body303_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "top"), none)) "rlp_decode_fully"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "len"]

def body303_22 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 2#64)

def body303_23 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "b0")
        (Flapjack.Exp.const 192#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 254#64)
        (Flapjack.Exp.var Flapjack.VarKind.local "b0"))]) body303_21 body303_22

def body303_24 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "b0") (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 4#64) (Flapjack.Exp.var Flapjack.VarKind.local "b0"))]) body303_20 body303_23

def body303_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body303_26 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 3#64)

def body303_27 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "top"))
  (Flapjack.Exp.const 1#64)) body303_26 body303_1

def body303_28 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 4#64)

def body303_29 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "lst"))
  (Flapjack.Exp.var Flapjack.VarKind.local "nfields")) body303_28 body303_1

def body303_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_scalar_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 0#64, Flapjack.Exp.const 8#64,
    Flapjack.Exp.const 12#64]

def body303_31 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def body303_32 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "k" (Flapjack.Exp.const 1#64)

def body303_33 : Prog (BitVec 64) :=
.seq body303_31 body303_32

def body303_34 : Prog (BitVec 64) :=
.seq body303_30 body303_33

def body303_35 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 0#64)) body303_34 body303_1

def body303_36 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_scalar_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 8#64,
    Flapjack.Exp.const 12#64]

def body303_37 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "v"
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 0#64])

def body303_38 : Prog (BitVec 64) :=
.seq body303_36 body303_37

def body303_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "v"), none)) "tx_scalar_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 32#64]

def body303_40 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 4#64)) body303_38 body303_39

def body303_41 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def body303_42 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "k"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64])

def body303_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "v"), none)) "tx_scalar_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 0#64]

def body303_44 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def body303_45 : Prog (BitVec 64) :=
.seq body303_44 body303_42

def body303_46 : Prog (BitVec 64) :=
.seq body303_43 body303_45

def body303_47 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def body303_48 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "v"), none)) "tx_scalar_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64],
    Flapjack.Exp.const 0#64]

def body303_49 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def body303_50 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "k"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 2#64])

def body303_51 : Prog (BitVec 64) :=
.seq body303_49 body303_50

def body303_52 : Prog (BitVec 64) :=
.seq body303_48 body303_51

def body303_53 : Prog (BitVec 64) :=
.seq body303_47 body303_52

def body303_54 : Prog (BitVec 64) :=
.seq body303_43 body303_53

def body303_55 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 1#64) (Flapjack.Exp.var Flapjack.VarKind.local "t")) body303_46 body303_54

def body303_56 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_scalar_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 0#64,
    Flapjack.Exp.const 14#64]

def body303_57 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 144#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def body303_58 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_fixed_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 20#64]

def body303_59 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_to_item"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k"]

def body303_60 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 3#64)) body303_58 body303_59

def body303_61 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 152#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def body303_62 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def body303_63 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 192#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "data"))

def body303_64 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 200#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "data"))

def body303_65 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 208#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "acc"))

def body303_66 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 216#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "acc"))

def body303_67 : Prog (BitVec 64) :=
.seq body303_66 body303_42

def body303_68 : Prog (BitVec 64) :=
.seq body303_65 body303_67

def body303_69 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_access_list") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "al"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "al")]) body303_68

def body303_70 : Prog (BitVec 64) :=
.decCall ("al") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_list_item") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k"]) body303_69

def body303_71 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 0#64)) body303_70 body303_1

def body303_72 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 224#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def body303_73 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 256#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "bh"))

def body303_74 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 264#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "bh"))

def body303_75 : Prog (BitVec 64) :=
.seq body303_74 body303_50

def body303_76 : Prog (BitVec 64) :=
.seq body303_73 body303_75

def body303_77 : Prog (BitVec 64) :=
.decCall ("bh") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_blob_hashes") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "bl"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "bl")]) body303_76

def body303_78 : Prog (BitVec 64) :=
.decCall ("bl") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_list_item") ([Flapjack.Exp.var Flapjack.VarKind.local "arr",
  Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64]]) body303_77

def body303_79 : Prog (BitVec 64) :=
.seq body303_72 body303_78

def body303_80 : Prog (BitVec 64) :=
.seq body303_39 body303_79

def body303_81 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 3#64)) body303_80 body303_1

def body303_82 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 272#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "au"))

def body303_83 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 280#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "au"))

def body303_84 : Prog (BitVec 64) :=
.seq body303_83 body303_42

def body303_85 : Prog (BitVec 64) :=
.seq body303_82 body303_84

def body303_86 : Prog (BitVec 64) :=
.decCall ("au") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_authorizations") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "aul"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "aul")]) body303_85

def body303_87 : Prog (BitVec 64) :=
.decCall ("aul") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_list_item") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k"]) body303_86

def body303_88 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 4#64)) body303_87 body303_1

def body303_89 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 288#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def body303_90 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "v"), none)) "tx_scalar_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64],
    Flapjack.Exp.const 32#64]

def body303_91 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 320#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def body303_92 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "v"), none)) "tx_scalar_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 2#64],
    Flapjack.Exp.const 32#64]

def body303_93 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 352#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "v")

def body303_94 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "tx")

def body303_95 : Prog (BitVec 64) :=
.seq body303_93 body303_94

def body303_96 : Prog (BitVec 64) :=
.seq body303_92 body303_95

def body303_97 : Prog (BitVec 64) :=
.seq body303_91 body303_96

def body303_98 : Prog (BitVec 64) :=
.seq body303_90 body303_97

def body303_99 : Prog (BitVec 64) :=
.seq body303_89 body303_98

def body303_100 : Prog (BitVec 64) :=
.seq body303_39 body303_99

def body303_101 : Prog (BitVec 64) :=
.seq body303_88 body303_100

def body303_102 : Prog (BitVec 64) :=
.seq body303_81 body303_101

def body303_103 : Prog (BitVec 64) :=
.seq body303_71 body303_102

def body303_104 : Prog (BitVec 64) :=
.seq body303_42 body303_103

def body303_105 : Prog (BitVec 64) :=
.seq body303_64 body303_104

def body303_106 : Prog (BitVec 64) :=
.seq body303_63 body303_105

def body303_107 : Prog (BitVec 64) :=
.decCall ("data") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_bytes_item") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k"]) body303_106

def body303_108 : Prog (BitVec 64) :=
.seq body303_42 body303_107

def body303_109 : Prog (BitVec 64) :=
.seq body303_62 body303_108

def body303_110 : Prog (BitVec 64) :=
.seq body303_39 body303_109

def body303_111 : Prog (BitVec 64) :=
.seq body303_42 body303_110

def body303_112 : Prog (BitVec 64) :=
.seq body303_61 body303_111

def body303_113 : Prog (BitVec 64) :=
.seq body303_60 body303_112

def body303_114 : Prog (BitVec 64) :=
.seq body303_42 body303_113

def body303_115 : Prog (BitVec 64) :=
.seq body303_57 body303_114

def body303_116 : Prog (BitVec 64) :=
.seq body303_56 body303_115

def body303_117 : Prog (BitVec 64) :=
.seq body303_55 body303_116

def body303_118 : Prog (BitVec 64) :=
.seq body303_42 body303_117

def body303_119 : Prog (BitVec 64) :=
.seq body303_41 body303_118

def body303_120 : Prog (BitVec 64) :=
.seq body303_40 body303_119

def body303_121 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body303_120

def body303_122 : Prog (BitVec 64) :=
.seq body303_35 body303_121

def body303_123 : Prog (BitVec 64) :=
.dec ("w") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body303_122

def body303_124 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body303_123

def body303_125 : Prog (BitVec 64) :=
.seq body303_29 body303_124

def body303_126 : Prog (BitVec 64) :=
.dec ("arr") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "lst")) body303_125

def body303_127 : Prog (BitVec 64) :=
.decCall ("lst") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_list_to_slices") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "top"),
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "top")]) body303_126

def body303_128 : Prog (BitVec 64) :=
.seq body303_27 body303_127

def body303_129 : Prog (BitVec 64) :=
.seq body303_25 body303_128

def body303_130 : Prog (BitVec 64) :=
.seq body303_24 body303_129

def body303_131 : Prog (BitVec 64) :=
.dec ("nfields") (Flapjack.Shape.one) (Flapjack.Exp.const 9#64) body303_130

def body303_132 : Prog (BitVec 64) :=
.dec ("t") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body303_131

def body303_133 : Prog (BitVec 64) :=
.dec ("top") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body303_132

def body303_134 : Prog (BitVec 64) :=
.seq body303_5 body303_133

def body303_135 : Prog (BitVec 64) :=
.seq body303_4 body303_134

def body303_136 : Prog (BitVec 64) :=
.seq body303_3 body303_135

def body303_137 : Prog (BitVec 64) :=
.decCall ("tx") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 400#64]) body303_136

def body303_138 : Prog (BitVec 64) :=
.dec ("b0") (Flapjack.Shape.one) (Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "p")) body303_137

def body303_139 : Prog (BitVec 64) :=
.seq body303_2 body303_138

def body303_140 : Prog (BitVec 64) :=
.seq body303_3 body303_4

def body303_141 : Prog (BitVec 64) :=
.seq body303_140 body303_5

def body303_142 : Prog (BitVec 64) :=
.seq body303_6 body303_7

def body303_143 : Prog (BitVec 64) :=
.seq body303_142 body303_9

def body303_144 : Prog (BitVec 64) :=
.seq body303_143 body303_11

def body303_145 : Prog (BitVec 64) :=
.seq body303_144 body303_13

def body303_146 : Prog (BitVec 64) :=
.seq body303_145 body303_15

def body303_147 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "b0") (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 4#64) (Flapjack.Exp.var Flapjack.VarKind.local "b0"))]) body303_146 body303_23

def body303_148 : Prog (BitVec 64) :=
.seq body303_147 body303_25

def body303_149 : Prog (BitVec 64) :=
.seq body303_148 body303_27

def body303_150 : Prog (BitVec 64) :=
.seq body303_30 body303_31

def body303_151 : Prog (BitVec 64) :=
.seq body303_150 body303_32

def body303_152 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 0#64)) body303_151 body303_1

def body303_153 : Prog (BitVec 64) :=
.seq body303_40 body303_41

def body303_154 : Prog (BitVec 64) :=
.seq body303_153 body303_42

def body303_155 : Prog (BitVec 64) :=
.seq body303_43 body303_44

def body303_156 : Prog (BitVec 64) :=
.seq body303_155 body303_42

def body303_157 : Prog (BitVec 64) :=
.seq body303_43 body303_47

def body303_158 : Prog (BitVec 64) :=
.seq body303_157 body303_48

def body303_159 : Prog (BitVec 64) :=
.seq body303_158 body303_49

def body303_160 : Prog (BitVec 64) :=
.seq body303_159 body303_50

def body303_161 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 1#64) (Flapjack.Exp.var Flapjack.VarKind.local "t")) body303_156 body303_160

def body303_162 : Prog (BitVec 64) :=
.seq body303_154 body303_161

def body303_163 : Prog (BitVec 64) :=
.seq body303_162 body303_56

def body303_164 : Prog (BitVec 64) :=
.seq body303_163 body303_57

def body303_165 : Prog (BitVec 64) :=
.seq body303_164 body303_42

def body303_166 : Prog (BitVec 64) :=
.seq body303_165 body303_60

def body303_167 : Prog (BitVec 64) :=
.seq body303_166 body303_61

def body303_168 : Prog (BitVec 64) :=
.seq body303_167 body303_42

def body303_169 : Prog (BitVec 64) :=
.seq body303_168 body303_39

def body303_170 : Prog (BitVec 64) :=
.seq body303_169 body303_62

def body303_171 : Prog (BitVec 64) :=
.seq body303_170 body303_42

def body303_172 : Prog (BitVec 64) :=
.seq body303_63 body303_64

def body303_173 : Prog (BitVec 64) :=
.seq body303_172 body303_42

def body303_174 : Prog (BitVec 64) :=
.seq body303_65 body303_66

def body303_175 : Prog (BitVec 64) :=
.seq body303_174 body303_42

def body303_176 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_access_list") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "al"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "al")]) body303_175

def body303_177 : Prog (BitVec 64) :=
.decCall ("al") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_list_item") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k"]) body303_176

def body303_178 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 0#64)) body303_177 body303_1

def body303_179 : Prog (BitVec 64) :=
.seq body303_173 body303_178

def body303_180 : Prog (BitVec 64) :=
.seq body303_39 body303_72

def body303_181 : Prog (BitVec 64) :=
.seq body303_73 body303_74

def body303_182 : Prog (BitVec 64) :=
.seq body303_181 body303_50

def body303_183 : Prog (BitVec 64) :=
.decCall ("bh") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_blob_hashes") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "bl"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "bl")]) body303_182

def body303_184 : Prog (BitVec 64) :=
.decCall ("bl") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_list_item") ([Flapjack.Exp.var Flapjack.VarKind.local "arr",
  Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 1#64]]) body303_183

def body303_185 : Prog (BitVec 64) :=
.seq body303_180 body303_184

def body303_186 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 3#64)) body303_185 body303_1

def body303_187 : Prog (BitVec 64) :=
.seq body303_179 body303_186

def body303_188 : Prog (BitVec 64) :=
.seq body303_82 body303_83

def body303_189 : Prog (BitVec 64) :=
.seq body303_188 body303_42

def body303_190 : Prog (BitVec 64) :=
.decCall ("au") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_authorizations") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "aul"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "aul")]) body303_189

def body303_191 : Prog (BitVec 64) :=
.decCall ("aul") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_list_item") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k"]) body303_190

def body303_192 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 4#64)) body303_191 body303_1

def body303_193 : Prog (BitVec 64) :=
.seq body303_187 body303_192

def body303_194 : Prog (BitVec 64) :=
.seq body303_193 body303_39

def body303_195 : Prog (BitVec 64) :=
.seq body303_194 body303_89

def body303_196 : Prog (BitVec 64) :=
.seq body303_195 body303_90

def body303_197 : Prog (BitVec 64) :=
.seq body303_196 body303_91

def body303_198 : Prog (BitVec 64) :=
.seq body303_197 body303_92

def body303_199 : Prog (BitVec 64) :=
.seq body303_198 body303_93

def body303_200 : Prog (BitVec 64) :=
.seq body303_199 body303_94

def body303_201 : Prog (BitVec 64) :=
.decCall ("data") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("tx_bytes_item") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "k"]) body303_200

def body303_202 : Prog (BitVec 64) :=
.seq body303_171 body303_201

def body303_203 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body303_202

def body303_204 : Prog (BitVec 64) :=
.seq body303_152 body303_203

def body303_205 : Prog (BitVec 64) :=
.dec ("w") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body303_204

def body303_206 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body303_205

def body303_207 : Prog (BitVec 64) :=
.seq body303_29 body303_206

def body303_208 : Prog (BitVec 64) :=
.dec ("arr") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "lst")) body303_207

def body303_209 : Prog (BitVec 64) :=
.decCall ("lst") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_list_to_slices") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "top"),
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "top")]) body303_208

def body303_210 : Prog (BitVec 64) :=
.seq body303_149 body303_209

def body303_211 : Prog (BitVec 64) :=
.dec ("nfields") (Flapjack.Shape.one) (Flapjack.Exp.const 9#64) body303_210

def body303_212 : Prog (BitVec 64) :=
.dec ("t") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body303_211

def body303_213 : Prog (BitVec 64) :=
.dec ("top") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body303_212

def body303_214 : Prog (BitVec 64) :=
.seq body303_141 body303_213

def body303_215 : Prog (BitVec 64) :=
.decCall ("tx") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 400#64]) body303_214

def body303_216 : Prog (BitVec 64) :=
.dec ("b0") (Flapjack.Shape.one) (Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "p")) body303_215

def body303_217 : Prog (BitVec 64) :=
.seq body303_2 body303_216

def originalData303 : Decl (BitVec 64) :=
.function { name := "decode_transaction_rlp", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := body303_139, returnShape := (Flapjack.Shape.one) }
def simplifiedData303 : Decl (BitVec 64) :=
.function { name := "decode_transaction_rlp", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := body303_217, returnShape := (Flapjack.Shape.one) }
def original303 := Pancake.PanLang.declToHOL originalData303
def simplified303 := Pancake.PanLang.declToHOL simplifiedData303
end InitECandidate.Proofs.FrontendStages.Declarations
