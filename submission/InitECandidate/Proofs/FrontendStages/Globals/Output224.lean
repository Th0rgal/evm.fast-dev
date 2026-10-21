import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data224
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate206
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody224_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "HdrErr" (Flapjack.Exp.const 10#64)

def globalBody224_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody224_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "top"))
  (Flapjack.Exp.const 1#64)) globalBody224_0 globalBody224_1

def globalBody224_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "is_current" (Flapjack.Exp.const 1#64)

def globalBody224_4 : Prog (BitVec 64) :=
Flapjack.Prog.raise "HdrErr" (Flapjack.Exp.const 11#64)

def globalBody224_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 21#64)) globalBody224_4 globalBody224_1

def globalBody224_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 23#64)) globalBody224_3 globalBody224_5

def globalBody224_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "is_current")

def globalBody224_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def globalBody224_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 1#64, Flapjack.Exp.const 32#64]

def globalBody224_10 : Prog (BitVec 64) :=
.seq globalBody224_8 globalBody224_9

def globalBody224_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def globalBody224_12 : Prog (BitVec 64) :=
.seq globalBody224_10 globalBody224_11

def globalBody224_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 2#64, Flapjack.Exp.const 20#64]

def globalBody224_14 : Prog (BitVec 64) :=
.seq globalBody224_12 globalBody224_13

def globalBody224_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def globalBody224_16 : Prog (BitVec 64) :=
.seq globalBody224_14 globalBody224_15

def globalBody224_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 3#64, Flapjack.Exp.const 32#64]

def globalBody224_18 : Prog (BitVec 64) :=
.seq globalBody224_16 globalBody224_17

def globalBody224_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def globalBody224_20 : Prog (BitVec 64) :=
.seq globalBody224_18 globalBody224_19

def globalBody224_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 4#64, Flapjack.Exp.const 32#64]

def globalBody224_22 : Prog (BitVec 64) :=
.seq globalBody224_20 globalBody224_21

def globalBody224_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def globalBody224_24 : Prog (BitVec 64) :=
.seq globalBody224_22 globalBody224_23

def globalBody224_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 5#64, Flapjack.Exp.const 32#64]

def globalBody224_26 : Prog (BitVec 64) :=
.seq globalBody224_24 globalBody224_25

def globalBody224_27 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def globalBody224_28 : Prog (BitVec 64) :=
.seq globalBody224_26 globalBody224_27

def globalBody224_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 6#64, Flapjack.Exp.const 256#64]

def globalBody224_30 : Prog (BitVec 64) :=
.seq globalBody224_28 globalBody224_29

def globalBody224_31 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def globalBody224_32 : Prog (BitVec 64) :=
.seq globalBody224_30 globalBody224_31

def globalBody224_33 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "d")

def globalBody224_34 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def globalBody224_35 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "hdr_word_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 9#64]

def globalBody224_36 : Prog (BitVec 64) :=
.seq globalBody224_34 globalBody224_35

def globalBody224_37 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def globalBody224_38 : Prog (BitVec 64) :=
.seq globalBody224_36 globalBody224_37

def globalBody224_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "hdr_word_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 10#64]

def globalBody224_40 : Prog (BitVec 64) :=
.seq globalBody224_38 globalBody224_39

def globalBody224_41 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def globalBody224_42 : Prog (BitVec 64) :=
.seq globalBody224_40 globalBody224_41

def globalBody224_43 : Prog (BitVec 64) :=
Flapjack.Prog.raise "HdrErr" (Flapjack.Exp.const 12#64)

def globalBody224_44 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 8#64)
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "tsf"))) globalBody224_43 globalBody224_1

def globalBody224_45 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "hdr_word_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 11#64]

def globalBody224_46 : Prog (BitVec 64) :=
.seq globalBody224_44 globalBody224_45

def globalBody224_47 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def globalBody224_48 : Prog (BitVec 64) :=
.seq globalBody224_46 globalBody224_47

def globalBody224_49 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "ex"))

def globalBody224_50 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 136#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "ex"))

def globalBody224_51 : Prog (BitVec 64) :=
.seq globalBody224_49 globalBody224_50

def globalBody224_52 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 13#64, Flapjack.Exp.const 32#64]

def globalBody224_53 : Prog (BitVec 64) :=
.seq globalBody224_51 globalBody224_52

def globalBody224_54 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 144#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def globalBody224_55 : Prog (BitVec 64) :=
.seq globalBody224_53 globalBody224_54

def globalBody224_56 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 14#64, Flapjack.Exp.const 8#64]

def globalBody224_57 : Prog (BitVec 64) :=
.seq globalBody224_55 globalBody224_56

def globalBody224_58 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 152#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def globalBody224_59 : Prog (BitVec 64) :=
.seq globalBody224_57 globalBody224_58

def globalBody224_60 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "d"), none)) "hdr_u256_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 15#64, Flapjack.Exp.const 0#64]

def globalBody224_61 : Prog (BitVec 64) :=
.seq globalBody224_59 globalBody224_60

def globalBody224_62 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "d")

def globalBody224_63 : Prog (BitVec 64) :=
.seq globalBody224_61 globalBody224_62

def globalBody224_64 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 16#64, Flapjack.Exp.const 32#64]

def globalBody224_65 : Prog (BitVec 64) :=
.seq globalBody224_63 globalBody224_64

def globalBody224_66 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 192#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def globalBody224_67 : Prog (BitVec 64) :=
.seq globalBody224_65 globalBody224_66

def globalBody224_68 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "hdr_word_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 17#64]

def globalBody224_69 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 200#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def globalBody224_70 : Prog (BitVec 64) :=
.seq globalBody224_68 globalBody224_69

def globalBody224_71 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "bg"), none)) "hdr_uint_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 18#64, Flapjack.Exp.const 8#64]

def globalBody224_72 : Prog (BitVec 64) :=
.seq globalBody224_70 globalBody224_71

def globalBody224_73 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "hdr_word_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 18#64]

def globalBody224_74 : Prog (BitVec 64) :=
.seq globalBody224_72 globalBody224_73

def globalBody224_75 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 208#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def globalBody224_76 : Prog (BitVec 64) :=
.seq globalBody224_74 globalBody224_75

def globalBody224_77 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 19#64, Flapjack.Exp.const 32#64]

def globalBody224_78 : Prog (BitVec 64) :=
.seq globalBody224_76 globalBody224_77

def globalBody224_79 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 216#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def globalBody224_80 : Prog (BitVec 64) :=
.seq globalBody224_78 globalBody224_79

def globalBody224_81 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 20#64, Flapjack.Exp.const 32#64]

def globalBody224_82 : Prog (BitVec 64) :=
.seq globalBody224_80 globalBody224_81

def globalBody224_83 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 224#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def globalBody224_84 : Prog (BitVec 64) :=
.seq globalBody224_82 globalBody224_83

def globalBody224_85 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "f"), none)) "hdr_bytes_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 21#64, Flapjack.Exp.const 32#64]

def globalBody224_86 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 232#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "f")

def globalBody224_87 : Prog (BitVec 64) :=
.seq globalBody224_85 globalBody224_86

def globalBody224_88 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "bg"), none)) "hdr_uint_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 22#64, Flapjack.Exp.const 8#64]

def globalBody224_89 : Prog (BitVec 64) :=
.seq globalBody224_87 globalBody224_88

def globalBody224_90 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "hdr_word_field"
  [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 22#64]

def globalBody224_91 : Prog (BitVec 64) :=
.seq globalBody224_89 globalBody224_90

def globalBody224_92 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 240#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "w")

def globalBody224_93 : Prog (BitVec 64) :=
.seq globalBody224_91 globalBody224_92

def globalBody224_94 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 232#64])
  (Flapjack.Exp.const 0#64)

def globalBody224_95 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 240#64])
  (Flapjack.Exp.const 0#64)

def globalBody224_96 : Prog (BitVec 64) :=
.seq globalBody224_94 globalBody224_95

def globalBody224_97 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "is_current") (Flapjack.Exp.const 0#64)) globalBody224_93 globalBody224_96

def globalBody224_98 : Prog (BitVec 64) :=
.seq globalBody224_84 globalBody224_97

def globalBody224_99 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "h")

def globalBody224_100 : Prog (BitVec 64) :=
.seq globalBody224_98 globalBody224_99

def globalBody224_101 : Prog (BitVec 64) :=
.decCall ("bg") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("hdr_uint_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 17#64, Flapjack.Exp.const 8#64]) globalBody224_100

def globalBody224_102 : Prog (BitVec 64) :=
.seq globalBody224_67 globalBody224_101

def globalBody224_103 : Prog (BitVec 64) :=
.decCall ("ex") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("hdr_raw_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 12#64]) globalBody224_102

def globalBody224_104 : Prog (BitVec 64) :=
.seq globalBody224_48 globalBody224_103

def globalBody224_105 : Prog (BitVec 64) :=
.decCall ("tsf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("hdr_uint_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 11#64, Flapjack.Exp.const 32#64]) globalBody224_104

def globalBody224_106 : Prog (BitVec 64) :=
.seq globalBody224_42 globalBody224_105

def globalBody224_107 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("hdr_word_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 8#64]) globalBody224_106

def globalBody224_108 : Prog (BitVec 64) :=
.seq globalBody224_33 globalBody224_107

def globalBody224_109 : Prog (BitVec 64) :=
.decCall ("d") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("hdr_u256_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 7#64, Flapjack.Exp.const 0#64]) globalBody224_108

def globalBody224_110 : Prog (BitVec 64) :=
.seq globalBody224_32 globalBody224_109

def globalBody224_111 : Prog (BitVec 64) :=
.decCall ("f") (Flapjack.Shape.one) ("hdr_bytes_field") ([Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.const 0#64, Flapjack.Exp.const 32#64]) globalBody224_110

def globalBody224_112 : Prog (BitVec 64) :=
.seq globalBody224_7 globalBody224_111

def globalBody224_113 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 248#64]) globalBody224_112

def globalBody224_114 : Prog (BitVec 64) :=
.seq globalBody224_6 globalBody224_113

def globalBody224_115 : Prog (BitVec 64) :=
.dec ("is_current") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody224_114

def globalBody224_116 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "lst")) globalBody224_115

def globalBody224_117 : Prog (BitVec 64) :=
.dec ("arr") (Flapjack.Shape.one) (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "lst")) globalBody224_116

def globalBody224_118 : Prog (BitVec 64) :=
.decCall ("lst") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_list_to_slices") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "top"),
  Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "top")]) globalBody224_117

def globalBody224_119 : Prog (BitVec 64) :=
.seq globalBody224_2 globalBody224_118

def globalBody224_120 : Prog (BitVec 64) :=
.decCall ("top") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("rlp_decode_fully") ([Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "len"]) globalBody224_119

def globalData224 : Decl (BitVec 64) :=
.function { name := "decode_header", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := globalBody224_120, returnShape := (Flapjack.Shape.one) }
def globalOutput224 := Pancake.PanLang.declToHOL globalData224
end InitECandidate.Proofs.FrontendStages.Declarations
