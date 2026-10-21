import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify309
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body325_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 8#64])]

def body325_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def body325_2 : Prog (BitVec 64) :=
.seq body325_0 body325_1

def body325_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body325_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 0#64)) body325_2 body325_3

def body325_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 16#64])]

def body325_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 48#64])]

def body325_7 : Prog (BitVec 64) :=
.seq body325_6 body325_1

def body325_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 80#64])]

def body325_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 112#64])]

def body325_10 : Prog (BitVec 64) :=
.seq body325_9 body325_1

def body325_11 : Prog (BitVec 64) :=
.seq body325_1 body325_10

def body325_12 : Prog (BitVec 64) :=
.seq body325_8 body325_11

def body325_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 1#64) (Flapjack.Exp.var Flapjack.VarKind.local "t")) body325_7 body325_12

def body325_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 144#64])]

def body325_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_put_to"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 152#64])]

def body325_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 160#64])]

def body325_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 192#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 200#64])]

def body325_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_put_access_list"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 208#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 216#64])]

def body325_19 : Prog (BitVec 64) :=
.seq body325_18 body325_1

def body325_20 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 0#64)) body325_19 body325_3

def body325_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 224#64])]

def body325_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_put_blob_hashes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 256#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 264#64])]

def body325_23 : Prog (BitVec 64) :=
.seq body325_22 body325_1

def body325_24 : Prog (BitVec 64) :=
.seq body325_1 body325_23

def body325_25 : Prog (BitVec 64) :=
.seq body325_21 body325_24

def body325_26 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 3#64)) body325_25 body325_3

def body325_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_put_authorizations"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 272#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 280#64])]

def body325_28 : Prog (BitVec 64) :=
.seq body325_27 body325_1

def body325_29 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 4#64)) body325_28 body325_3

def body325_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 288#64])]

def body325_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 320#64])]

def body325_32 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "tx_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 352#64])]

def body325_33 : Prog (BitVec 64) :=
.seq body325_32 body325_1

def body325_34 : Prog (BitVec 64) :=
.seq body325_1 body325_33

def body325_35 : Prog (BitVec 64) :=
.seq body325_31 body325_34

def body325_36 : Prog (BitVec 64) :=
.seq body325_1 body325_35

def body325_37 : Prog (BitVec 64) :=
.seq body325_30 body325_36

def body325_38 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "mode") (Flapjack.Exp.const 0#64)) body325_37 body325_3

def body325_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "chain_id"]

def body325_40 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "p") (Flapjack.Exp.const 128#64)

def body325_41 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 128#64)

def body325_42 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 2#64])

def body325_43 : Prog (BitVec 64) :=
.seq body325_41 body325_42

def body325_44 : Prog (BitVec 64) :=
.seq body325_40 body325_43

def body325_45 : Prog (BitVec 64) :=
.seq body325_1 body325_44

def body325_46 : Prog (BitVec 64) :=
.seq body325_39 body325_45

def body325_47 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "mode") (Flapjack.Exp.const 2#64)) body325_46 body325_3

def body325_48 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.var Flapjack.VarKind.local "payload_len"]

def body325_49 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "start"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.const 1#64])

def body325_50 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "start") (Flapjack.Exp.var Flapjack.VarKind.local "t")

def body325_51 : Prog (BitVec 64) :=
.seq body325_49 body325_50

def body325_52 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 0#64)) body325_51 body325_3

def body325_53 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.var Flapjack.VarKind.local "start",
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "start"]])

def body325_54 : Prog (BitVec 64) :=
.seq body325_52 body325_53

def body325_55 : Prog (BitVec 64) :=
.seq body325_48 body325_54

def body325_56 : Prog (BitVec 64) :=
.dec ("start") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "body", Flapjack.Exp.var Flapjack.VarKind.local "hl"]) body325_55

def body325_57 : Prog (BitVec 64) :=
.decCall ("hl") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.var Flapjack.VarKind.local "payload_len"]) body325_56

def body325_58 : Prog (BitVec 64) :=
.dec ("payload_len") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "body"]) body325_57

def body325_59 : Prog (BitVec 64) :=
.seq body325_47 body325_58

def body325_60 : Prog (BitVec 64) :=
.seq body325_38 body325_59

def body325_61 : Prog (BitVec 64) :=
.seq body325_29 body325_60

def body325_62 : Prog (BitVec 64) :=
.seq body325_26 body325_61

def body325_63 : Prog (BitVec 64) :=
.seq body325_20 body325_62

def body325_64 : Prog (BitVec 64) :=
.seq body325_1 body325_63

def body325_65 : Prog (BitVec 64) :=
.seq body325_17 body325_64

def body325_66 : Prog (BitVec 64) :=
.seq body325_1 body325_65

def body325_67 : Prog (BitVec 64) :=
.seq body325_16 body325_66

def body325_68 : Prog (BitVec 64) :=
.seq body325_1 body325_67

def body325_69 : Prog (BitVec 64) :=
.seq body325_15 body325_68

def body325_70 : Prog (BitVec 64) :=
.seq body325_1 body325_69

def body325_71 : Prog (BitVec 64) :=
.seq body325_14 body325_70

def body325_72 : Prog (BitVec 64) :=
.seq body325_13 body325_71

def body325_73 : Prog (BitVec 64) :=
.seq body325_1 body325_72

def body325_74 : Prog (BitVec 64) :=
.seq body325_5 body325_73

def body325_75 : Prog (BitVec 64) :=
.seq body325_4 body325_74

def body325_76 : Prog (BitVec 64) :=
.dec ("w") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body325_75

def body325_77 : Prog (BitVec 64) :=
.dec ("t") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 0#64])) body325_76

def body325_78 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "body") body325_77

def body325_79 : Prog (BitVec 64) :=
.dec ("body") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 10#64]) body325_78

def body325_80 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "bound"]) body325_79

def body325_81 : Prog (BitVec 64) :=
.decCall ("bound") (Flapjack.Shape.one) ("tx_encode_bound") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body325_80

def body325_82 : Prog (BitVec 64) :=
.seq body325_4 body325_5

def body325_83 : Prog (BitVec 64) :=
.seq body325_82 body325_1

def body325_84 : Prog (BitVec 64) :=
.seq body325_8 body325_1

def body325_85 : Prog (BitVec 64) :=
.seq body325_84 body325_9

def body325_86 : Prog (BitVec 64) :=
.seq body325_85 body325_1

def body325_87 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.const 1#64) (Flapjack.Exp.var Flapjack.VarKind.local "t")) body325_7 body325_86

def body325_88 : Prog (BitVec 64) :=
.seq body325_83 body325_87

def body325_89 : Prog (BitVec 64) :=
.seq body325_88 body325_14

def body325_90 : Prog (BitVec 64) :=
.seq body325_89 body325_1

def body325_91 : Prog (BitVec 64) :=
.seq body325_90 body325_15

def body325_92 : Prog (BitVec 64) :=
.seq body325_91 body325_1

def body325_93 : Prog (BitVec 64) :=
.seq body325_92 body325_16

def body325_94 : Prog (BitVec 64) :=
.seq body325_93 body325_1

def body325_95 : Prog (BitVec 64) :=
.seq body325_94 body325_17

def body325_96 : Prog (BitVec 64) :=
.seq body325_95 body325_1

def body325_97 : Prog (BitVec 64) :=
.seq body325_96 body325_20

def body325_98 : Prog (BitVec 64) :=
.seq body325_21 body325_1

def body325_99 : Prog (BitVec 64) :=
.seq body325_98 body325_22

def body325_100 : Prog (BitVec 64) :=
.seq body325_99 body325_1

def body325_101 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "t") (Flapjack.Exp.const 3#64)) body325_100 body325_3

def body325_102 : Prog (BitVec 64) :=
.seq body325_97 body325_101

def body325_103 : Prog (BitVec 64) :=
.seq body325_102 body325_29

def body325_104 : Prog (BitVec 64) :=
.seq body325_30 body325_1

def body325_105 : Prog (BitVec 64) :=
.seq body325_104 body325_31

def body325_106 : Prog (BitVec 64) :=
.seq body325_105 body325_1

def body325_107 : Prog (BitVec 64) :=
.seq body325_106 body325_32

def body325_108 : Prog (BitVec 64) :=
.seq body325_107 body325_1

def body325_109 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "mode") (Flapjack.Exp.const 0#64)) body325_108 body325_3

def body325_110 : Prog (BitVec 64) :=
.seq body325_103 body325_109

def body325_111 : Prog (BitVec 64) :=
.seq body325_39 body325_1

def body325_112 : Prog (BitVec 64) :=
.seq body325_111 body325_40

def body325_113 : Prog (BitVec 64) :=
.seq body325_112 body325_41

def body325_114 : Prog (BitVec 64) :=
.seq body325_113 body325_42

def body325_115 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "mode") (Flapjack.Exp.const 2#64)) body325_114 body325_3

def body325_116 : Prog (BitVec 64) :=
.seq body325_110 body325_115

def body325_117 : Prog (BitVec 64) :=
.seq body325_48 body325_52

def body325_118 : Prog (BitVec 64) :=
.seq body325_117 body325_53

def body325_119 : Prog (BitVec 64) :=
.dec ("start") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "body", Flapjack.Exp.var Flapjack.VarKind.local "hl"]) body325_118

def body325_120 : Prog (BitVec 64) :=
.decCall ("hl") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.var Flapjack.VarKind.local "payload_len"]) body325_119

def body325_121 : Prog (BitVec 64) :=
.dec ("payload_len") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "body"]) body325_120

def body325_122 : Prog (BitVec 64) :=
.seq body325_116 body325_121

def body325_123 : Prog (BitVec 64) :=
.dec ("w") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body325_122

def body325_124 : Prog (BitVec 64) :=
.dec ("t") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 0#64])) body325_123

def body325_125 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "body") body325_124

def body325_126 : Prog (BitVec 64) :=
.dec ("body") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 10#64]) body325_125

def body325_127 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "bound"]) body325_126

def body325_128 : Prog (BitVec 64) :=
.decCall ("bound") (Flapjack.Shape.one) ("tx_encode_bound") ([Flapjack.Exp.var Flapjack.VarKind.local "tx"]) body325_127

def originalData325 : Decl (BitVec 64) :=
.function { name := "tx_encode_generic", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("mode", Flapjack.Shape.one), ("chain_id", Flapjack.Shape.one)], body := body325_81, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData325 : Decl (BitVec 64) :=
.function { name := "tx_encode_generic", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("mode", Flapjack.Shape.one), ("chain_id", Flapjack.Shape.one)], body := body325_128, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def original325 := Pancake.PanLang.declToHOL originalData325
def simplified325 := Pancake.PanLang.declToHOL simplifiedData325
end InitECandidate.Proofs.FrontendStages.Declarations
