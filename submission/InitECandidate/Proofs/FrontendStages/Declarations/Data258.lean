import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify242
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body258_0 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (some (Flapjack.VarKind.local, "it"),
      some ("RlpErr", "e", Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 3#64])))
  "rlp_decode_fully" [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "n"]

def body258_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def body258_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body258_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "it"))
  (Flapjack.Exp.const 0#64)) body258_1 body258_2

def body258_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 4#64]

def body258_5 : Prog (BitVec 64) :=
.seq body258_3 body258_4

def body258_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "it"))
  (Flapjack.Exp.const 0#64)) body258_5 body258_2

def body258_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 5#64]

def body258_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "pi"))
  (Flapjack.Exp.const 0#64)) body258_7 body258_2

def body258_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 6#64]

def body258_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "vi"))
  (Flapjack.Exp.const 0#64)) body258_9 body258_2

def body258_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "lf", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "p")

def body258_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "lf", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n")

def body258_13 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.var Flapjack.VarKind.local "lf"])

def body258_14 : Prog (BitVec 64) :=
.seq body258_12 body258_13

def body258_15 : Prog (BitVec 64) :=
.seq body258_11 body258_14

def body258_16 : Prog (BitVec 64) :=
.decCall ("lf") (Flapjack.Shape.one) ("node_new_leaf") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "cn"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "cn"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "vi"),
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "vi")]) body258_15

def body258_17 : Prog (BitVec 64) :=
.seq body258_10 body258_16

def body258_18 : Prog (BitVec 64) :=
.decCall ("vi") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_item") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "arr",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 1#64, Flapjack.Exp.const 16#64]]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "arr",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 1#64, Flapjack.Exp.const 16#64],
        Flapjack.Exp.const 8#64])]) body258_17

def body258_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "cn"))
  (Flapjack.Exp.const 0#64)) body258_18 body258_2

def body258_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 7#64]

def body258_21 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "cn"))
  (Flapjack.Exp.const 0#64)) body258_20 body258_2

def body258_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 1#64)

def body258_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "arr")

def body258_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "p")

def body258_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n")

def body258_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "cn"))

def body258_27 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "cn"))

def body258_28 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rStruct [Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "rec"])

def body258_29 : Prog (BitVec 64) :=
.seq body258_27 body258_28

def body258_30 : Prog (BitVec 64) :=
.seq body258_26 body258_29

def body258_31 : Prog (BitVec 64) :=
.seq body258_25 body258_30

def body258_32 : Prog (BitVec 64) :=
.seq body258_24 body258_31

def body258_33 : Prog (BitVec 64) :=
.seq body258_23 body258_32

def body258_34 : Prog (BitVec 64) :=
.seq body258_22 body258_33

def body258_35 : Prog (BitVec 64) :=
.decCall ("rec") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 88#64]) body258_34

def body258_36 : Prog (BitVec 64) :=
.seq body258_21 body258_35

def body258_37 : Prog (BitVec 64) :=
.seq body258_19 body258_36

def body258_38 : Prog (BitVec 64) :=
.decCall ("cn") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("compact_to_nibbles") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "pi"),
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "pi")]) body258_37

def body258_39 : Prog (BitVec 64) :=
.seq body258_8 body258_38

def body258_40 : Prog (BitVec 64) :=
.decCall ("pi") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_item") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "arr",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 0#64, Flapjack.Exp.const 16#64]]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "arr",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 0#64, Flapjack.Exp.const 16#64],
        Flapjack.Exp.const 8#64])]) body258_39

def body258_41 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "sl"))
  (Flapjack.Exp.const 2#64)) body258_40 body258_2

def body258_42 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "sl"))
  (Flapjack.Exp.const 17#64)) body258_4 body258_2

def body258_43 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec2", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 2#64)

def body258_44 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec2", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "br")

def body258_45 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec2", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "arr")

def body258_46 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec2", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 0#64)

def body258_47 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec2", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.const 0#64)

def body258_48 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec2", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "p")

def body258_49 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec2", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "n")

def body258_50 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rStruct [Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "rec2"])

def body258_51 : Prog (BitVec 64) :=
.seq body258_49 body258_50

def body258_52 : Prog (BitVec 64) :=
.seq body258_48 body258_51

def body258_53 : Prog (BitVec 64) :=
.seq body258_47 body258_52

def body258_54 : Prog (BitVec 64) :=
.seq body258_46 body258_53

def body258_55 : Prog (BitVec 64) :=
.seq body258_45 body258_54

def body258_56 : Prog (BitVec 64) :=
.seq body258_44 body258_55

def body258_57 : Prog (BitVec 64) :=
.seq body258_43 body258_56

def body258_58 : Prog (BitVec 64) :=
.decCall ("rec2") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 88#64]) body258_57

def body258_59 : Prog (BitVec 64) :=
.decCall ("br") (Flapjack.Shape.one) ("node_new_branch") ([]) body258_58

def body258_60 : Prog (BitVec 64) :=
.seq body258_42 body258_59

def body258_61 : Prog (BitVec 64) :=
.seq body258_41 body258_60

def body258_62 : Prog (BitVec 64) :=
.dec ("arr") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "sl")) body258_61

def body258_63 : Prog (BitVec 64) :=
.decCall ("sl") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_list_to_slices") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "it"),
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "it")]) body258_62

def body258_64 : Prog (BitVec 64) :=
.seq body258_6 body258_63

def body258_65 : Prog (BitVec 64) :=
.seq body258_0 body258_64

def body258_66 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body258_65

def body258_67 : Prog (BitVec 64) :=
.dec ("it") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body258_66

def body258_68 : Prog (BitVec 64) :=
.seq body258_0 body258_6

def body258_69 : Prog (BitVec 64) :=
.seq body258_11 body258_12

def body258_70 : Prog (BitVec 64) :=
.seq body258_69 body258_13

def body258_71 : Prog (BitVec 64) :=
.decCall ("lf") (Flapjack.Shape.one) ("node_new_leaf") ([Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "cn"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "cn"),
  Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "vi"),
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "vi")]) body258_70

def body258_72 : Prog (BitVec 64) :=
.seq body258_10 body258_71

def body258_73 : Prog (BitVec 64) :=
.decCall ("vi") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_item") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "arr",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 1#64, Flapjack.Exp.const 16#64]]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "arr",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 1#64, Flapjack.Exp.const 16#64],
        Flapjack.Exp.const 8#64])]) body258_72

def body258_74 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "cn"))
  (Flapjack.Exp.const 0#64)) body258_73 body258_2

def body258_75 : Prog (BitVec 64) :=
.seq body258_74 body258_21

def body258_76 : Prog (BitVec 64) :=
.seq body258_22 body258_23

def body258_77 : Prog (BitVec 64) :=
.seq body258_76 body258_24

def body258_78 : Prog (BitVec 64) :=
.seq body258_77 body258_25

def body258_79 : Prog (BitVec 64) :=
.seq body258_78 body258_26

def body258_80 : Prog (BitVec 64) :=
.seq body258_79 body258_27

def body258_81 : Prog (BitVec 64) :=
.seq body258_80 body258_28

def body258_82 : Prog (BitVec 64) :=
.decCall ("rec") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 88#64]) body258_81

def body258_83 : Prog (BitVec 64) :=
.seq body258_75 body258_82

def body258_84 : Prog (BitVec 64) :=
.decCall ("cn") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("compact_to_nibbles") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "pi"),
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "pi")]) body258_83

def body258_85 : Prog (BitVec 64) :=
.seq body258_8 body258_84

def body258_86 : Prog (BitVec 64) :=
.decCall ("pi") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_item") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "arr",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 0#64, Flapjack.Exp.const 16#64]]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "arr",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 0#64, Flapjack.Exp.const 16#64],
        Flapjack.Exp.const 8#64])]) body258_85

def body258_87 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "sl"))
  (Flapjack.Exp.const 2#64)) body258_86 body258_2

def body258_88 : Prog (BitVec 64) :=
.seq body258_87 body258_42

def body258_89 : Prog (BitVec 64) :=
.seq body258_43 body258_44

def body258_90 : Prog (BitVec 64) :=
.seq body258_89 body258_45

def body258_91 : Prog (BitVec 64) :=
.seq body258_90 body258_46

def body258_92 : Prog (BitVec 64) :=
.seq body258_91 body258_47

def body258_93 : Prog (BitVec 64) :=
.seq body258_92 body258_48

def body258_94 : Prog (BitVec 64) :=
.seq body258_93 body258_49

def body258_95 : Prog (BitVec 64) :=
.seq body258_94 body258_50

def body258_96 : Prog (BitVec 64) :=
.decCall ("rec2") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 88#64]) body258_95

def body258_97 : Prog (BitVec 64) :=
.decCall ("br") (Flapjack.Shape.one) ("node_new_branch") ([]) body258_96

def body258_98 : Prog (BitVec 64) :=
.seq body258_88 body258_97

def body258_99 : Prog (BitVec 64) :=
.dec ("arr") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "sl")) body258_98

def body258_100 : Prog (BitVec 64) :=
.decCall ("sl") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_list_to_slices") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "it"),
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "it")]) body258_99

def body258_101 : Prog (BitVec 64) :=
.seq body258_68 body258_100

def body258_102 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body258_101

def body258_103 : Prog (BitVec 64) :=
.dec ("it") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body258_102

def originalData258 : Decl (BitVec 64) :=
.function { name := "_decode_step", inline := false, exported := false, params := [("db", Flapjack.Shape.one), ("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body258_67, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData258 : Decl (BitVec 64) :=
.function { name := "_decode_step", inline := false, exported := false, params := [("db", Flapjack.Shape.one), ("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body258_103, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def original258 := Pancake.PanLang.declToHOL originalData258
def simplified258 := Pancake.PanLang.declToHOL simplifiedData258
end InitECandidate.Proofs.FrontendStages.Declarations
