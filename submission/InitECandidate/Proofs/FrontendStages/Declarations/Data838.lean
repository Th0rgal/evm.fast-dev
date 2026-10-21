import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify822
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body838_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 60#64)

def body838_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body838_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 576#64)) body838_0 body838_1

def body838_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 24#64]

def body838_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "ok" (Flapjack.Exp.const 0#64)

def body838_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0")
        (Flapjack.Exp.const 160#64)])) body838_4 body838_1

def body838_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64],
    Flapjack.Exp.const 24#64]

def body838_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 56#64]]

def body838_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0")
        (Flapjack.Exp.const 256#64)])) body838_4 body838_1

def body838_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 64#64],
    Flapjack.Exp.const 24#64]

def body838_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 88#64]]

def body838_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0")
        (Flapjack.Exp.const 320#64)])) body838_4 body838_1

def body838_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 96#64],
    Flapjack.Exp.const 24#64]

def body838_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 120#64]]

def body838_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0")
        (Flapjack.Exp.const 384#64)])) body838_4 body838_1

def body838_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 128#64],
    Flapjack.Exp.const 24#64]

def body838_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 152#64]]

def body838_17 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0")
        (Flapjack.Exp.const 512#64)])) body838_4 body838_1

def body838_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 160#64],
    Flapjack.Exp.const 24#64]

def body838_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 184#64]]

def body838_20 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0") (Flapjack.Exp.const 48#64)])) body838_4 body838_1

def body838_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 256#64],
    Flapjack.Exp.const 24#64]

def body838_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 280#64]]

def body838_23 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0") (Flapjack.Exp.const 32#64)])) body838_4 body838_1

def body838_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 320#64],
    Flapjack.Exp.const 24#64]

def body838_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 344#64]]

def body838_26 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0") (Flapjack.Exp.const 8#64)])) body838_4 body838_1

def body838_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 384#64],
    Flapjack.Exp.const 24#64]

def body838_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 408#64]]

def body838_29 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w0") (Flapjack.Exp.const 96#64)])) body838_4 body838_1

def body838_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z"), none)) "is_zero_bytes"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 512#64],
    Flapjack.Exp.const 24#64]

def body838_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w0"), none)) "ld_be64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 536#64]]

def body838_32 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body838_33 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 61#64)

def body838_34 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) body838_33 body838_1

def body838_35 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 192#64],
    Flapjack.Exp.const 48#64]

def body838_36 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 48#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 288#64],
    Flapjack.Exp.const 32#64]

def body838_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 80#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 352#64],
    Flapjack.Exp.const 8#64]

def body838_38 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 88#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 416#64],
    Flapjack.Exp.const 96#64]

def body838_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 184#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 544#64],
    Flapjack.Exp.const 8#64]

def body838_40 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body838_41 : Prog (BitVec 64) :=
.seq body838_39 body838_40

def body838_42 : Prog (BitVec 64) :=
.seq body838_38 body838_41

def body838_43 : Prog (BitVec 64) :=
.seq body838_37 body838_42

def body838_44 : Prog (BitVec 64) :=
.seq body838_36 body838_43

def body838_45 : Prog (BitVec 64) :=
.seq body838_35 body838_44

def body838_46 : Prog (BitVec 64) :=
.seq body838_34 body838_45

def body838_47 : Prog (BitVec 64) :=
.seq body838_32 body838_46

def body838_48 : Prog (BitVec 64) :=
.seq body838_26 body838_47

def body838_49 : Prog (BitVec 64) :=
.seq body838_31 body838_48

def body838_50 : Prog (BitVec 64) :=
.seq body838_30 body838_49

def body838_51 : Prog (BitVec 64) :=
.seq body838_29 body838_50

def body838_52 : Prog (BitVec 64) :=
.seq body838_28 body838_51

def body838_53 : Prog (BitVec 64) :=
.seq body838_27 body838_52

def body838_54 : Prog (BitVec 64) :=
.seq body838_26 body838_53

def body838_55 : Prog (BitVec 64) :=
.seq body838_25 body838_54

def body838_56 : Prog (BitVec 64) :=
.seq body838_24 body838_55

def body838_57 : Prog (BitVec 64) :=
.seq body838_23 body838_56

def body838_58 : Prog (BitVec 64) :=
.seq body838_22 body838_57

def body838_59 : Prog (BitVec 64) :=
.seq body838_21 body838_58

def body838_60 : Prog (BitVec 64) :=
.seq body838_20 body838_59

def body838_61 : Prog (BitVec 64) :=
.seq body838_19 body838_60

def body838_62 : Prog (BitVec 64) :=
.seq body838_18 body838_61

def body838_63 : Prog (BitVec 64) :=
.seq body838_17 body838_62

def body838_64 : Prog (BitVec 64) :=
.seq body838_16 body838_63

def body838_65 : Prog (BitVec 64) :=
.seq body838_15 body838_64

def body838_66 : Prog (BitVec 64) :=
.seq body838_14 body838_65

def body838_67 : Prog (BitVec 64) :=
.seq body838_13 body838_66

def body838_68 : Prog (BitVec 64) :=
.seq body838_12 body838_67

def body838_69 : Prog (BitVec 64) :=
.seq body838_11 body838_68

def body838_70 : Prog (BitVec 64) :=
.seq body838_10 body838_69

def body838_71 : Prog (BitVec 64) :=
.seq body838_9 body838_70

def body838_72 : Prog (BitVec 64) :=
.seq body838_8 body838_71

def body838_73 : Prog (BitVec 64) :=
.seq body838_7 body838_72

def body838_74 : Prog (BitVec 64) :=
.seq body838_6 body838_73

def body838_75 : Prog (BitVec 64) :=
.seq body838_5 body838_74

def body838_76 : Prog (BitVec 64) :=
.seq body838_3 body838_75

def body838_77 : Prog (BitVec 64) :=
.decCall ("w0") (Flapjack.Shape.one) ("ld_be64") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 24#64]]) body838_76

def body838_78 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body838_77

def body838_79 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("is_zero_bytes") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 24#64]) body838_78

def body838_80 : Prog (BitVec 64) :=
.dec ("ok") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body838_79

def body838_81 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body838_80

def body838_82 : Prog (BitVec 64) :=
.seq body838_2 body838_81

def body838_83 : Prog (BitVec 64) :=
.seq body838_3 body838_5

def body838_84 : Prog (BitVec 64) :=
.seq body838_83 body838_6

def body838_85 : Prog (BitVec 64) :=
.seq body838_84 body838_7

def body838_86 : Prog (BitVec 64) :=
.seq body838_85 body838_8

def body838_87 : Prog (BitVec 64) :=
.seq body838_86 body838_9

def body838_88 : Prog (BitVec 64) :=
.seq body838_87 body838_10

def body838_89 : Prog (BitVec 64) :=
.seq body838_88 body838_11

def body838_90 : Prog (BitVec 64) :=
.seq body838_89 body838_12

def body838_91 : Prog (BitVec 64) :=
.seq body838_90 body838_13

def body838_92 : Prog (BitVec 64) :=
.seq body838_91 body838_14

def body838_93 : Prog (BitVec 64) :=
.seq body838_92 body838_15

def body838_94 : Prog (BitVec 64) :=
.seq body838_93 body838_16

def body838_95 : Prog (BitVec 64) :=
.seq body838_94 body838_17

def body838_96 : Prog (BitVec 64) :=
.seq body838_95 body838_18

def body838_97 : Prog (BitVec 64) :=
.seq body838_96 body838_19

def body838_98 : Prog (BitVec 64) :=
.seq body838_97 body838_20

def body838_99 : Prog (BitVec 64) :=
.seq body838_98 body838_21

def body838_100 : Prog (BitVec 64) :=
.seq body838_99 body838_22

def body838_101 : Prog (BitVec 64) :=
.seq body838_100 body838_23

def body838_102 : Prog (BitVec 64) :=
.seq body838_101 body838_24

def body838_103 : Prog (BitVec 64) :=
.seq body838_102 body838_25

def body838_104 : Prog (BitVec 64) :=
.seq body838_103 body838_26

def body838_105 : Prog (BitVec 64) :=
.seq body838_104 body838_27

def body838_106 : Prog (BitVec 64) :=
.seq body838_105 body838_28

def body838_107 : Prog (BitVec 64) :=
.seq body838_106 body838_29

def body838_108 : Prog (BitVec 64) :=
.seq body838_107 body838_30

def body838_109 : Prog (BitVec 64) :=
.seq body838_108 body838_31

def body838_110 : Prog (BitVec 64) :=
.seq body838_109 body838_26

def body838_111 : Prog (BitVec 64) :=
.seq body838_110 body838_32

def body838_112 : Prog (BitVec 64) :=
.seq body838_111 body838_34

def body838_113 : Prog (BitVec 64) :=
.seq body838_112 body838_35

def body838_114 : Prog (BitVec 64) :=
.seq body838_113 body838_36

def body838_115 : Prog (BitVec 64) :=
.seq body838_114 body838_37

def body838_116 : Prog (BitVec 64) :=
.seq body838_115 body838_38

def body838_117 : Prog (BitVec 64) :=
.seq body838_116 body838_39

def body838_118 : Prog (BitVec 64) :=
.seq body838_117 body838_40

def body838_119 : Prog (BitVec 64) :=
.decCall ("w0") (Flapjack.Shape.one) ("ld_be64") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 24#64]]) body838_118

def body838_120 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body838_119

def body838_121 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("is_zero_bytes") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 24#64]) body838_120

def body838_122 : Prog (BitVec 64) :=
.dec ("ok") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body838_121

def body838_123 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body838_122

def body838_124 : Prog (BitVec 64) :=
.seq body838_2 body838_123

def originalData838 : Decl (BitVec 64) :=
.function { name := "extract_deposit_data", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body838_82, returnShape := (Flapjack.Shape.one) }
def simplifiedData838 : Decl (BitVec 64) :=
.function { name := "extract_deposit_data", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body838_124, returnShape := (Flapjack.Shape.one) }
def original838 := Pancake.PanLang.declToHOL originalData838
def simplified838 := Pancake.PanLang.declToHOL simplifiedData838
end InitECandidate.Proofs.FrontendStages.Declarations
