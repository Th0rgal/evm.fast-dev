import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify208
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body224_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "HdrErr" (Flapjack.Exp.const 10#64)

def body224_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body224_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "top"))
  (Flapjack.Exp.const 1#64)) body224_0 body224_1

def body224_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "is_current" (Flapjack.Exp.const 1#64)

def body224_4 : Prog (BitVec 64) :=
Flapjack.Prog.raise "HdrErr" (Flapjack.Exp.const 11#64)

def body224_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 21#64)) body224_4 body224_1

def body224_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 23#64)) body224_3 body224_5

def body224_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "is_current")

def body224_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def body224_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 1#64, Flapjack.Exp.const 32#64]

def body224_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def body224_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 2#64, Flapjack.Exp.const 20#64]

def body224_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def body224_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 3#64, Flapjack.Exp.const 32#64]

def body224_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def body224_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 4#64, Flapjack.Exp.const 32#64]

def body224_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def body224_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 5#64, Flapjack.Exp.const 32#64]

def body224_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def body224_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 6#64, Flapjack.Exp.const 256#64]

def body224_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def body224_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "d")

def body224_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def body224_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "hdr_word_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 9#64]

def body224_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def body224_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "hdr_word_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 10#64]

def body224_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def body224_27 : Prog (BitVec 64) :=
Flapjack.Prog.raise "HdrErr" (Flapjack.Exp.const 12#64)

def body224_28 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 8#64)
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "tsf"))) body224_27 body224_1

def body224_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "hdr_word_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 11#64]

def body224_30 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def body224_31 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "ex"))

def body224_32 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 136#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "ex"))

def body224_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 13#64, Flapjack.Exp.const 32#64]

def body224_34 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 144#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def body224_35 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 14#64, Flapjack.Exp.const 8#64]

def body224_36 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 152#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def body224_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "d"), none)) "hdr_u256_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 15#64, Flapjack.Exp.const 0#64]

def body224_38 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "d")

def body224_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 16#64, Flapjack.Exp.const 32#64]

def body224_40 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 192#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def body224_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "hdr_word_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 17#64]

def body224_42 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 200#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def body224_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "bg"), none)) "hdr_uint_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 18#64, Flapjack.Exp.const 8#64]

def body224_44 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "hdr_word_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 18#64]

def body224_45 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 208#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def body224_46 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 19#64, Flapjack.Exp.const 32#64]

def body224_47 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 216#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def body224_48 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 20#64, Flapjack.Exp.const 32#64]

def body224_49 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 224#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def body224_50 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 21#64, Flapjack.Exp.const 32#64]

def body224_51 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 232#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def body224_52 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "bg"), none)) "hdr_uint_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 22#64, Flapjack.Exp.const 8#64]

def body224_53 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "hdr_word_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 22#64]

def body224_54 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 240#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def body224_55 : Prog (BitVec 64) :=
.seq body224_53 body224_54

def body224_56 : Prog (BitVec 64) :=
.seq body224_52 body224_55

def body224_57 : Prog (BitVec 64) :=
.seq body224_51 body224_56

def body224_58 : Prog (BitVec 64) :=
.seq body224_50 body224_57

def body224_59 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 232#64])
  (Flapjack.Exp.const 0#64)

def body224_60 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 240#64])
  (Flapjack.Exp.const 0#64)

def body224_61 : Prog (BitVec 64) :=
.seq body224_59 body224_60

def body224_62 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "is_current") (Flapjack.Exp.const 0#64)) body224_58 body224_61

def body224_63 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "h")

def body224_64 : Prog (BitVec 64) :=
.seq body224_62 body224_63

def body224_65 : Prog (BitVec 64) :=
.seq body224_49 body224_64

def body224_66 : Prog (BitVec 64) :=
.seq body224_48 body224_65

def body224_67 : Prog (BitVec 64) :=
.seq body224_47 body224_66

def body224_68 : Prog (BitVec 64) :=
.seq body224_46 body224_67

def body224_69 : Prog (BitVec 64) :=
.seq body224_45 body224_68

def body224_70 : Prog (BitVec 64) :=
.seq body224_44 body224_69

def body224_71 : Prog (BitVec 64) :=
.seq body224_43 body224_70

def body224_72 : Prog (BitVec 64) :=
.seq body224_42 body224_71

def body224_73 : Prog (BitVec 64) :=
.seq body224_41 body224_72

def body224_74 : Prog (BitVec 64) :=
.decCall ("bg") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("hdr_uint_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 17#64, Flapjack.Exp.const 8#64]) body224_73

def body224_75 : Prog (BitVec 64) :=
.seq body224_40 body224_74

def body224_76 : Prog (BitVec 64) :=
.seq body224_39 body224_75

def body224_77 : Prog (BitVec 64) :=
.seq body224_38 body224_76

def body224_78 : Prog (BitVec 64) :=
.seq body224_37 body224_77

def body224_79 : Prog (BitVec 64) :=
.seq body224_36 body224_78

def body224_80 : Prog (BitVec 64) :=
.seq body224_35 body224_79

def body224_81 : Prog (BitVec 64) :=
.seq body224_34 body224_80

def body224_82 : Prog (BitVec 64) :=
.seq body224_33 body224_81

def body224_83 : Prog (BitVec 64) :=
.seq body224_32 body224_82

def body224_84 : Prog (BitVec 64) :=
.seq body224_31 body224_83

def body224_85 : Prog (BitVec 64) :=
.decCall ("ex") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("hdr_raw_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 12#64]) body224_84

def body224_86 : Prog (BitVec 64) :=
.seq body224_30 body224_85

def body224_87 : Prog (BitVec 64) :=
.seq body224_29 body224_86

def body224_88 : Prog (BitVec 64) :=
.seq body224_28 body224_87

def body224_89 : Prog (BitVec 64) :=
.decCall ("tsf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("hdr_uint_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 11#64, Flapjack.Exp.const 32#64]) body224_88

def body224_90 : Prog (BitVec 64) :=
.seq body224_26 body224_89

def body224_91 : Prog (BitVec 64) :=
.seq body224_25 body224_90

def body224_92 : Prog (BitVec 64) :=
.seq body224_24 body224_91

def body224_93 : Prog (BitVec 64) :=
.seq body224_23 body224_92

def body224_94 : Prog (BitVec 64) :=
.seq body224_22 body224_93

def body224_95 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("hdr_word_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 8#64]) body224_94

def body224_96 : Prog (BitVec 64) :=
.seq body224_21 body224_95

def body224_97 : Prog (BitVec 64) :=
.decCall ("d") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("hdr_u256_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 7#64, Flapjack.Exp.const 0#64]) body224_96

def body224_98 : Prog (BitVec 64) :=
.seq body224_20 body224_97

def body224_99 : Prog (BitVec 64) :=
.seq body224_19 body224_98

def body224_100 : Prog (BitVec 64) :=
.seq body224_18 body224_99

def body224_101 : Prog (BitVec 64) :=
.seq body224_17 body224_100

def body224_102 : Prog (BitVec 64) :=
.seq body224_16 body224_101

def body224_103 : Prog (BitVec 64) :=
.seq body224_15 body224_102

def body224_104 : Prog (BitVec 64) :=
.seq body224_14 body224_103

def body224_105 : Prog (BitVec 64) :=
.seq body224_13 body224_104

def body224_106 : Prog (BitVec 64) :=
.seq body224_12 body224_105

def body224_107 : Prog (BitVec 64) :=
.seq body224_11 body224_106

def body224_108 : Prog (BitVec 64) :=
.seq body224_10 body224_107

def body224_109 : Prog (BitVec 64) :=
.seq body224_9 body224_108

def body224_110 : Prog (BitVec 64) :=
.seq body224_8 body224_109

def body224_111 : Prog (BitVec 64) :=
.decCall ("f") (Flapjack.Shape.one) ("hdr_bytes_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 0#64, Flapjack.Exp.const 32#64]) body224_110

def body224_112 : Prog (BitVec 64) :=
.seq body224_7 body224_111

def body224_113 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 248#64]) body224_112

def body224_114 : Prog (BitVec 64) :=
.seq body224_6 body224_113

def body224_115 : Prog (BitVec 64) :=
.dec ("is_current") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body224_114

def body224_116 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "lst")) body224_115

def body224_117 : Prog (BitVec 64) :=
.dec ("arr") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "lst")) body224_116

def body224_118 : Prog (BitVec 64) :=
.decCall ("lst") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_list_to_slices") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "top"),
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "top")]) body224_117

def body224_119 : Prog (BitVec 64) :=
.seq body224_2 body224_118

def body224_120 : Prog (BitVec 64) :=
.decCall ("top") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_decode_fully") ([Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "len"]) body224_119

def body224_121 : Prog (BitVec 64) :=
.seq body224_8 body224_9

def body224_122 : Prog (BitVec 64) :=
.seq body224_121 body224_10

def body224_123 : Prog (BitVec 64) :=
.seq body224_122 body224_11

def body224_124 : Prog (BitVec 64) :=
.seq body224_123 body224_12

def body224_125 : Prog (BitVec 64) :=
.seq body224_124 body224_13

def body224_126 : Prog (BitVec 64) :=
.seq body224_125 body224_14

def body224_127 : Prog (BitVec 64) :=
.seq body224_126 body224_15

def body224_128 : Prog (BitVec 64) :=
.seq body224_127 body224_16

def body224_129 : Prog (BitVec 64) :=
.seq body224_128 body224_17

def body224_130 : Prog (BitVec 64) :=
.seq body224_129 body224_18

def body224_131 : Prog (BitVec 64) :=
.seq body224_130 body224_19

def body224_132 : Prog (BitVec 64) :=
.seq body224_131 body224_20

def body224_133 : Prog (BitVec 64) :=
.seq body224_22 body224_23

def body224_134 : Prog (BitVec 64) :=
.seq body224_133 body224_24

def body224_135 : Prog (BitVec 64) :=
.seq body224_134 body224_25

def body224_136 : Prog (BitVec 64) :=
.seq body224_135 body224_26

def body224_137 : Prog (BitVec 64) :=
.seq body224_28 body224_29

def body224_138 : Prog (BitVec 64) :=
.seq body224_137 body224_30

def body224_139 : Prog (BitVec 64) :=
.seq body224_31 body224_32

def body224_140 : Prog (BitVec 64) :=
.seq body224_139 body224_33

def body224_141 : Prog (BitVec 64) :=
.seq body224_140 body224_34

def body224_142 : Prog (BitVec 64) :=
.seq body224_141 body224_35

def body224_143 : Prog (BitVec 64) :=
.seq body224_142 body224_36

def body224_144 : Prog (BitVec 64) :=
.seq body224_143 body224_37

def body224_145 : Prog (BitVec 64) :=
.seq body224_144 body224_38

def body224_146 : Prog (BitVec 64) :=
.seq body224_145 body224_39

def body224_147 : Prog (BitVec 64) :=
.seq body224_146 body224_40

def body224_148 : Prog (BitVec 64) :=
.seq body224_41 body224_42

def body224_149 : Prog (BitVec 64) :=
.seq body224_148 body224_43

def body224_150 : Prog (BitVec 64) :=
.seq body224_149 body224_44

def body224_151 : Prog (BitVec 64) :=
.seq body224_150 body224_45

def body224_152 : Prog (BitVec 64) :=
.seq body224_151 body224_46

def body224_153 : Prog (BitVec 64) :=
.seq body224_152 body224_47

def body224_154 : Prog (BitVec 64) :=
.seq body224_153 body224_48

def body224_155 : Prog (BitVec 64) :=
.seq body224_154 body224_49

def body224_156 : Prog (BitVec 64) :=
.seq body224_50 body224_51

def body224_157 : Prog (BitVec 64) :=
.seq body224_156 body224_52

def body224_158 : Prog (BitVec 64) :=
.seq body224_157 body224_53

def body224_159 : Prog (BitVec 64) :=
.seq body224_158 body224_54

def body224_160 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "is_current") (Flapjack.Exp.const 0#64)) body224_159 body224_61

def body224_161 : Prog (BitVec 64) :=
.seq body224_155 body224_160

def body224_162 : Prog (BitVec 64) :=
.seq body224_161 body224_63

def body224_163 : Prog (BitVec 64) :=
.decCall ("bg") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("hdr_uint_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 17#64, Flapjack.Exp.const 8#64]) body224_162

def body224_164 : Prog (BitVec 64) :=
.seq body224_147 body224_163

def body224_165 : Prog (BitVec 64) :=
.decCall ("ex") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("hdr_raw_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 12#64]) body224_164

def body224_166 : Prog (BitVec 64) :=
.seq body224_138 body224_165

def body224_167 : Prog (BitVec 64) :=
.decCall ("tsf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("hdr_uint_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 11#64, Flapjack.Exp.const 32#64]) body224_166

def body224_168 : Prog (BitVec 64) :=
.seq body224_136 body224_167

def body224_169 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("hdr_word_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 8#64]) body224_168

def body224_170 : Prog (BitVec 64) :=
.seq body224_21 body224_169

def body224_171 : Prog (BitVec 64) :=
.decCall ("d") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("hdr_u256_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 7#64, Flapjack.Exp.const 0#64]) body224_170

def body224_172 : Prog (BitVec 64) :=
.seq body224_132 body224_171

def body224_173 : Prog (BitVec 64) :=
.decCall ("f") (Flapjack.Shape.one) ("hdr_bytes_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 0#64, Flapjack.Exp.const 32#64]) body224_172

def body224_174 : Prog (BitVec 64) :=
.seq body224_7 body224_173

def body224_175 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 248#64]) body224_174

def body224_176 : Prog (BitVec 64) :=
.seq body224_6 body224_175

def body224_177 : Prog (BitVec 64) :=
.dec ("is_current") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body224_176

def body224_178 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "lst")) body224_177

def body224_179 : Prog (BitVec 64) :=
.dec ("arr") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "lst")) body224_178

def body224_180 : Prog (BitVec 64) :=
.decCall ("lst") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_list_to_slices") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "top"),
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "top")]) body224_179

def body224_181 : Prog (BitVec 64) :=
.seq body224_2 body224_180

def body224_182 : Prog (BitVec 64) :=
.decCall ("top") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_decode_fully") ([Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "len"]) body224_181

def originalData224 : Decl (BitVec 64) :=
.function { name := "decode_header", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := body224_120, returnShape := (Flapjack.Shape.one) }
def simplifiedData224 : Decl (BitVec 64) :=
.function { name := "decode_header", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := body224_182, returnShape := (Flapjack.Shape.one) }
def original224 := Pancake.PanLang.declToHOL originalData224
def simplified224 := Pancake.PanLang.declToHOL simplifiedData224
end InitECandidate.Proofs.FrontendStages.Declarations
