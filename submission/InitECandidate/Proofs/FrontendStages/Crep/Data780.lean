import InitECandidate.Proofs.FrontendStages.Crep.Translate764
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody780_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 3)

def crepBody780_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody780_2 : CrepProg (BitVec 64) :=
.seq crepBody780_0 crepBody780_1

def crepBody780_3 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 60#64) crepBody780_2

def crepBody780_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 4#64

def crepBody780_5 : CrepProg (BitVec 64) :=
.seq crepBody780_3 crepBody780_4

def crepBody780_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 576#64)) crepBody780_5 crepBody780_1

def crepBody780_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "heap_mark" []

def crepBody780_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "is_zero_bytes" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 24#64]

def crepBody780_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "ld_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 24#64]]

def crepBody780_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.const 0#64)

def crepBody780_11 : CrepProg (BitVec 64) :=
.seq crepBody780_10 crepBody780_1

def crepBody780_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 160#64)])) crepBody780_11 crepBody780_1

def crepBody780_13 : CrepProg (BitVec 64) :=
.seq crepBody780_8 crepBody780_12

def crepBody780_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "is_zero_bytes"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64],
    Flapjack.CrepExp.const 24#64]

def crepBody780_15 : CrepProg (BitVec 64) :=
.seq crepBody780_13 crepBody780_14

def crepBody780_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "ld_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 56#64]]

def crepBody780_17 : CrepProg (BitVec 64) :=
.seq crepBody780_15 crepBody780_16

def crepBody780_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 256#64)])) crepBody780_11 crepBody780_1

def crepBody780_19 : CrepProg (BitVec 64) :=
.seq crepBody780_17 crepBody780_18

def crepBody780_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "is_zero_bytes"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 64#64],
    Flapjack.CrepExp.const 24#64]

def crepBody780_21 : CrepProg (BitVec 64) :=
.seq crepBody780_19 crepBody780_20

def crepBody780_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "ld_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 88#64]]

def crepBody780_23 : CrepProg (BitVec 64) :=
.seq crepBody780_21 crepBody780_22

def crepBody780_24 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 320#64)])) crepBody780_11 crepBody780_1

def crepBody780_25 : CrepProg (BitVec 64) :=
.seq crepBody780_23 crepBody780_24

def crepBody780_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "is_zero_bytes"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.const 24#64]

def crepBody780_27 : CrepProg (BitVec 64) :=
.seq crepBody780_25 crepBody780_26

def crepBody780_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "ld_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 120#64]]

def crepBody780_29 : CrepProg (BitVec 64) :=
.seq crepBody780_27 crepBody780_28

def crepBody780_30 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 384#64)])) crepBody780_11 crepBody780_1

def crepBody780_31 : CrepProg (BitVec 64) :=
.seq crepBody780_29 crepBody780_30

def crepBody780_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "is_zero_bytes"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 128#64],
    Flapjack.CrepExp.const 24#64]

def crepBody780_33 : CrepProg (BitVec 64) :=
.seq crepBody780_31 crepBody780_32

def crepBody780_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "ld_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 152#64]]

def crepBody780_35 : CrepProg (BitVec 64) :=
.seq crepBody780_33 crepBody780_34

def crepBody780_36 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 512#64)])) crepBody780_11 crepBody780_1

def crepBody780_37 : CrepProg (BitVec 64) :=
.seq crepBody780_35 crepBody780_36

def crepBody780_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "is_zero_bytes"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64],
    Flapjack.CrepExp.const 24#64]

def crepBody780_39 : CrepProg (BitVec 64) :=
.seq crepBody780_37 crepBody780_38

def crepBody780_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "ld_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 184#64]]

def crepBody780_41 : CrepProg (BitVec 64) :=
.seq crepBody780_39 crepBody780_40

def crepBody780_42 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 48#64)])) crepBody780_11 crepBody780_1

def crepBody780_43 : CrepProg (BitVec 64) :=
.seq crepBody780_41 crepBody780_42

def crepBody780_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "is_zero_bytes"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 256#64],
    Flapjack.CrepExp.const 24#64]

def crepBody780_45 : CrepProg (BitVec 64) :=
.seq crepBody780_43 crepBody780_44

def crepBody780_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "ld_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 280#64]]

def crepBody780_47 : CrepProg (BitVec 64) :=
.seq crepBody780_45 crepBody780_46

def crepBody780_48 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 32#64)])) crepBody780_11 crepBody780_1

def crepBody780_49 : CrepProg (BitVec 64) :=
.seq crepBody780_47 crepBody780_48

def crepBody780_50 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "is_zero_bytes"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 320#64],
    Flapjack.CrepExp.const 24#64]

def crepBody780_51 : CrepProg (BitVec 64) :=
.seq crepBody780_49 crepBody780_50

def crepBody780_52 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "ld_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 344#64]]

def crepBody780_53 : CrepProg (BitVec 64) :=
.seq crepBody780_51 crepBody780_52

def crepBody780_54 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 8#64)])) crepBody780_11 crepBody780_1

def crepBody780_55 : CrepProg (BitVec 64) :=
.seq crepBody780_53 crepBody780_54

def crepBody780_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "is_zero_bytes"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 384#64],
    Flapjack.CrepExp.const 24#64]

def crepBody780_57 : CrepProg (BitVec 64) :=
.seq crepBody780_55 crepBody780_56

def crepBody780_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "ld_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 408#64]]

def crepBody780_59 : CrepProg (BitVec 64) :=
.seq crepBody780_57 crepBody780_58

def crepBody780_60 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 96#64)])) crepBody780_11 crepBody780_1

def crepBody780_61 : CrepProg (BitVec 64) :=
.seq crepBody780_59 crepBody780_60

def crepBody780_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "is_zero_bytes"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 512#64],
    Flapjack.CrepExp.const 24#64]

def crepBody780_63 : CrepProg (BitVec 64) :=
.seq crepBody780_61 crepBody780_62

def crepBody780_64 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "ld_be64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 536#64]]

def crepBody780_65 : CrepProg (BitVec 64) :=
.seq crepBody780_63 crepBody780_64

def crepBody780_66 : CrepProg (BitVec 64) :=
.seq crepBody780_65 crepBody780_54

def crepBody780_67 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody780_68 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody780_67

def crepBody780_69 : CrepProg (BitVec 64) :=
.seq crepBody780_66 crepBody780_68

def crepBody780_70 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 8)

def crepBody780_71 : CrepProg (BitVec 64) :=
.seq crepBody780_70 crepBody780_1

def crepBody780_72 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 61#64) crepBody780_71

def crepBody780_73 : CrepProg (BitVec 64) :=
.seq crepBody780_72 crepBody780_4

def crepBody780_74 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody780_73 crepBody780_1

def crepBody780_75 : CrepProg (BitVec 64) :=
.seq crepBody780_69 crepBody780_74

def crepBody780_76 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "memcpy"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.const 48#64]

def crepBody780_77 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody780_76

def crepBody780_78 : CrepProg (BitVec 64) :=
.seq crepBody780_75 crepBody780_77

def crepBody780_79 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 48#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64],
    Flapjack.CrepExp.const 32#64]

def crepBody780_80 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody780_79

def crepBody780_81 : CrepProg (BitVec 64) :=
.seq crepBody780_78 crepBody780_80

def crepBody780_82 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 80#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 352#64],
    Flapjack.CrepExp.const 8#64]

def crepBody780_83 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody780_82

def crepBody780_84 : CrepProg (BitVec 64) :=
.seq crepBody780_81 crepBody780_83

def crepBody780_85 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 88#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 416#64],
    Flapjack.CrepExp.const 96#64]

def crepBody780_86 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody780_85

def crepBody780_87 : CrepProg (BitVec 64) :=
.seq crepBody780_84 crepBody780_86

def crepBody780_88 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 184#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 544#64],
    Flapjack.CrepExp.const 8#64]

def crepBody780_89 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody780_88

def crepBody780_90 : CrepProg (BitVec 64) :=
.seq crepBody780_87 crepBody780_89

def crepBody780_91 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody780_92 : CrepProg (BitVec 64) :=
.seq crepBody780_90 crepBody780_91

def crepBody780_93 : CrepProg (BitVec 64) :=
.seq crepBody780_9 crepBody780_92

def crepBody780_94 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody780_93

def crepBody780_95 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody780_94

def crepBody780_96 : CrepProg (BitVec 64) :=
.seq crepBody780_8 crepBody780_95

def crepBody780_97 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody780_96

def crepBody780_98 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 1#64) crepBody780_97

def crepBody780_99 : CrepProg (BitVec 64) :=
.seq crepBody780_7 crepBody780_98

def crepBody780_100 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody780_99

def crepBody780_101 : CrepProg (BitVec 64) :=
.seq crepBody780_6 crepBody780_100

def data780 : CrepProg (BitVec 64) := crepBody780_101
def output780 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [101#8, 120#8, 116#8, 114#8, 97#8, 99#8, 116#8, 95#8, 100#8, 101#8, 112#8, 111#8, 115#8, 105#8, 116#8, 95#8, 100#8,
    97#8, 116#8, 97#8], [0, 1, 2], crepProgToHOL data780)
end InitECandidate.Proofs.FrontendStages.Crep
