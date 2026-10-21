import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify210
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body226_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "w"])

def body226_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 16#64]),
    Flapjack.Exp.const 32#64]

def body226_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 24#64]),
    Flapjack.Exp.const 20#64]

def body226_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.const 32#64]

def body226_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.const 32#64]

def body226_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 48#64]),
    Flapjack.Exp.const 32#64]

def body226_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 56#64]),
    Flapjack.Exp.const 256#64]

def body226_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 64#64])]

def body226_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 96#64])]

def body226_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 104#64])]

def body226_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 112#64])]

def body226_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 120#64])]

def body226_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 128#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 136#64])]

def body226_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 144#64]),
    Flapjack.Exp.const 32#64]

def body226_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 152#64]),
    Flapjack.Exp.const 8#64]

def body226_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_put_u256"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load
      (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 160#64])]

def body226_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 192#64]),
    Flapjack.Exp.const 32#64]

def body226_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 200#64])]

def body226_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 208#64])]

def body226_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 216#64]),
    Flapjack.Exp.const 32#64]

def body226_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 224#64]),
    Flapjack.Exp.const 32#64]

def body226_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 232#64]),
    Flapjack.Exp.const 32#64]

def body226_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "rlp_encode_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 240#64])]

def body226_23 : Prog (BitVec 64) :=
.seq body226_22 body226_0

def body226_24 : Prog (BitVec 64) :=
.seq body226_0 body226_23

def body226_25 : Prog (BitVec 64) :=
.seq body226_21 body226_24

def body226_26 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body226_27 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 0#64]))
  (Flapjack.Exp.const 0#64)) body226_25 body226_26

def body226_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "start", Flapjack.Exp.var Flapjack.VarKind.local "payload_len"]

def body226_29 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.var Flapjack.VarKind.local "start",
      Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "payload_len", Flapjack.Exp.var Flapjack.VarKind.local "hl"]])

def body226_30 : Prog (BitVec 64) :=
.seq body226_28 body226_29

def body226_31 : Prog (BitVec 64) :=
.dec ("start") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 9#64],
    Flapjack.Exp.var Flapjack.VarKind.local "hl"]) body226_30

def body226_32 : Prog (BitVec 64) :=
.decCall ("hl") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.var Flapjack.VarKind.local "payload_len"]) body226_31

def body226_33 : Prog (BitVec 64) :=
.dec ("payload_len") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 9#64]]) body226_32

def body226_34 : Prog (BitVec 64) :=
.seq body226_27 body226_33

def body226_35 : Prog (BitVec 64) :=
.seq body226_0 body226_34

def body226_36 : Prog (BitVec 64) :=
.seq body226_20 body226_35

def body226_37 : Prog (BitVec 64) :=
.seq body226_0 body226_36

def body226_38 : Prog (BitVec 64) :=
.seq body226_19 body226_37

def body226_39 : Prog (BitVec 64) :=
.seq body226_0 body226_38

def body226_40 : Prog (BitVec 64) :=
.seq body226_18 body226_39

def body226_41 : Prog (BitVec 64) :=
.seq body226_0 body226_40

def body226_42 : Prog (BitVec 64) :=
.seq body226_17 body226_41

def body226_43 : Prog (BitVec 64) :=
.seq body226_0 body226_42

def body226_44 : Prog (BitVec 64) :=
.seq body226_16 body226_43

def body226_45 : Prog (BitVec 64) :=
.seq body226_0 body226_44

def body226_46 : Prog (BitVec 64) :=
.seq body226_15 body226_45

def body226_47 : Prog (BitVec 64) :=
.seq body226_0 body226_46

def body226_48 : Prog (BitVec 64) :=
.seq body226_14 body226_47

def body226_49 : Prog (BitVec 64) :=
.seq body226_0 body226_48

def body226_50 : Prog (BitVec 64) :=
.seq body226_13 body226_49

def body226_51 : Prog (BitVec 64) :=
.seq body226_0 body226_50

def body226_52 : Prog (BitVec 64) :=
.seq body226_12 body226_51

def body226_53 : Prog (BitVec 64) :=
.seq body226_0 body226_52

def body226_54 : Prog (BitVec 64) :=
.seq body226_11 body226_53

def body226_55 : Prog (BitVec 64) :=
.seq body226_0 body226_54

def body226_56 : Prog (BitVec 64) :=
.seq body226_10 body226_55

def body226_57 : Prog (BitVec 64) :=
.seq body226_0 body226_56

def body226_58 : Prog (BitVec 64) :=
.seq body226_9 body226_57

def body226_59 : Prog (BitVec 64) :=
.seq body226_0 body226_58

def body226_60 : Prog (BitVec 64) :=
.seq body226_8 body226_59

def body226_61 : Prog (BitVec 64) :=
.seq body226_0 body226_60

def body226_62 : Prog (BitVec 64) :=
.seq body226_7 body226_61

def body226_63 : Prog (BitVec 64) :=
.seq body226_0 body226_62

def body226_64 : Prog (BitVec 64) :=
.seq body226_6 body226_63

def body226_65 : Prog (BitVec 64) :=
.seq body226_0 body226_64

def body226_66 : Prog (BitVec 64) :=
.seq body226_5 body226_65

def body226_67 : Prog (BitVec 64) :=
.seq body226_0 body226_66

def body226_68 : Prog (BitVec 64) :=
.seq body226_4 body226_67

def body226_69 : Prog (BitVec 64) :=
.seq body226_0 body226_68

def body226_70 : Prog (BitVec 64) :=
.seq body226_3 body226_69

def body226_71 : Prog (BitVec 64) :=
.seq body226_0 body226_70

def body226_72 : Prog (BitVec 64) :=
.seq body226_2 body226_71

def body226_73 : Prog (BitVec 64) :=
.seq body226_0 body226_72

def body226_74 : Prog (BitVec 64) :=
.seq body226_1 body226_73

def body226_75 : Prog (BitVec 64) :=
.seq body226_0 body226_74

def body226_76 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.var Flapjack.VarKind.local "p",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.const 32#64]) body226_75

def body226_77 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 9#64]) body226_76

def body226_78 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1024#64]) body226_77

def body226_79 : Prog (BitVec 64) :=
.seq body226_0 body226_1

def body226_80 : Prog (BitVec 64) :=
.seq body226_79 body226_0

def body226_81 : Prog (BitVec 64) :=
.seq body226_80 body226_2

def body226_82 : Prog (BitVec 64) :=
.seq body226_81 body226_0

def body226_83 : Prog (BitVec 64) :=
.seq body226_82 body226_3

def body226_84 : Prog (BitVec 64) :=
.seq body226_83 body226_0

def body226_85 : Prog (BitVec 64) :=
.seq body226_84 body226_4

def body226_86 : Prog (BitVec 64) :=
.seq body226_85 body226_0

def body226_87 : Prog (BitVec 64) :=
.seq body226_86 body226_5

def body226_88 : Prog (BitVec 64) :=
.seq body226_87 body226_0

def body226_89 : Prog (BitVec 64) :=
.seq body226_88 body226_6

def body226_90 : Prog (BitVec 64) :=
.seq body226_89 body226_0

def body226_91 : Prog (BitVec 64) :=
.seq body226_90 body226_7

def body226_92 : Prog (BitVec 64) :=
.seq body226_91 body226_0

def body226_93 : Prog (BitVec 64) :=
.seq body226_92 body226_8

def body226_94 : Prog (BitVec 64) :=
.seq body226_93 body226_0

def body226_95 : Prog (BitVec 64) :=
.seq body226_94 body226_9

def body226_96 : Prog (BitVec 64) :=
.seq body226_95 body226_0

def body226_97 : Prog (BitVec 64) :=
.seq body226_96 body226_10

def body226_98 : Prog (BitVec 64) :=
.seq body226_97 body226_0

def body226_99 : Prog (BitVec 64) :=
.seq body226_98 body226_11

def body226_100 : Prog (BitVec 64) :=
.seq body226_99 body226_0

def body226_101 : Prog (BitVec 64) :=
.seq body226_100 body226_12

def body226_102 : Prog (BitVec 64) :=
.seq body226_101 body226_0

def body226_103 : Prog (BitVec 64) :=
.seq body226_102 body226_13

def body226_104 : Prog (BitVec 64) :=
.seq body226_103 body226_0

def body226_105 : Prog (BitVec 64) :=
.seq body226_104 body226_14

def body226_106 : Prog (BitVec 64) :=
.seq body226_105 body226_0

def body226_107 : Prog (BitVec 64) :=
.seq body226_106 body226_15

def body226_108 : Prog (BitVec 64) :=
.seq body226_107 body226_0

def body226_109 : Prog (BitVec 64) :=
.seq body226_108 body226_16

def body226_110 : Prog (BitVec 64) :=
.seq body226_109 body226_0

def body226_111 : Prog (BitVec 64) :=
.seq body226_110 body226_17

def body226_112 : Prog (BitVec 64) :=
.seq body226_111 body226_0

def body226_113 : Prog (BitVec 64) :=
.seq body226_112 body226_18

def body226_114 : Prog (BitVec 64) :=
.seq body226_113 body226_0

def body226_115 : Prog (BitVec 64) :=
.seq body226_114 body226_19

def body226_116 : Prog (BitVec 64) :=
.seq body226_115 body226_0

def body226_117 : Prog (BitVec 64) :=
.seq body226_116 body226_20

def body226_118 : Prog (BitVec 64) :=
.seq body226_117 body226_0

def body226_119 : Prog (BitVec 64) :=
.seq body226_21 body226_0

def body226_120 : Prog (BitVec 64) :=
.seq body226_119 body226_22

def body226_121 : Prog (BitVec 64) :=
.seq body226_120 body226_0

def body226_122 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 0#64]))
  (Flapjack.Exp.const 0#64)) body226_121 body226_26

def body226_123 : Prog (BitVec 64) :=
.seq body226_118 body226_122

def body226_124 : Prog (BitVec 64) :=
.seq body226_123 body226_33

def body226_125 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("rlp_encode_bytes") ([Flapjack.Exp.var Flapjack.VarKind.local "p",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 8#64]),
  Flapjack.Exp.const 32#64]) body226_124

def body226_126 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "buf", Flapjack.Exp.const 9#64]) body226_125

def body226_127 : Prog (BitVec 64) :=
.decCall ("buf") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 1024#64]) body226_126

def originalData226 : Decl (BitVec 64) :=
.function { name := "encode_header", inline := false, exported := false, params := [("h", Flapjack.Shape.one)], body := body226_78, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData226 : Decl (BitVec 64) :=
.function { name := "encode_header", inline := false, exported := false, params := [("h", Flapjack.Shape.one)], body := body226_127, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def original226 := Pancake.PanLang.declToHOL originalData226
def simplified226 := Pancake.PanLang.declToHOL simplifiedData226
end InitECandidate.Proofs.FrontendStages.Declarations
