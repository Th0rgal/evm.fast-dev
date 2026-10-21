import InitECandidate.Proofs.FrontendStages.Crep.Translate778
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody794_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "min" [Flapjack.CrepExp.const 16777216#64, Flapjack.CrepExp.var 6]

def crepBody794_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 8)

def crepBody794_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody794_3 : CrepProg (BitVec 64) :=
.seq crepBody794_1 crepBody794_2

def crepBody794_4 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 80#64) crepBody794_3

def crepBody794_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 4#64

def crepBody794_6 : CrepProg (BitVec 64) :=
.seq crepBody794_4 crepBody794_5

def crepBody794_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 7)) crepBody794_6 crepBody794_2

def crepBody794_8 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 81#64) crepBody794_3

def crepBody794_9 : CrepProg (BitVec 64) :=
.seq crepBody794_8 crepBody794_5

def crepBody794_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 6)) crepBody794_9 crepBody794_2

def crepBody794_11 : CrepProg (BitVec 64) :=
.seq crepBody794_7 crepBody794_10

def crepBody794_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "calculate_total_blob_gas" [Flapjack.CrepExp.var 0]

def crepBody794_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 9)

def crepBody794_14 : CrepProg (BitVec 64) :=
.seq crepBody794_13 crepBody794_2

def crepBody794_15 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 82#64) crepBody794_14

def crepBody794_16 : CrepProg (BitVec 64) :=
.seq crepBody794_15 crepBody794_5

def crepBody794_17 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 8)) crepBody794_16 crepBody794_2

def crepBody794_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "get_account" [Flapjack.CrepExp.var 1]

def crepBody794_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "u256_lt"
  [Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26,
    Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody794_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 28)

def crepBody794_21 : CrepProg (BitVec 64) :=
.seq crepBody794_20 crepBody794_2

def crepBody794_22 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.const 83#64) crepBody794_21

def crepBody794_23 : CrepProg (BitVec 64) :=
.seq crepBody794_22 crepBody794_5

def crepBody794_24 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 27) (Flapjack.CrepExp.const 0#64)) crepBody794_23 crepBody794_2

def crepBody794_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 14 (Flapjack.CrepExp.var 23)

def crepBody794_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 15 (Flapjack.CrepExp.var 24)

def crepBody794_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 16 (Flapjack.CrepExp.var 25)

def crepBody794_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 17 (Flapjack.CrepExp.var 26)

def crepBody794_29 : CrepProg (BitVec 64) :=
.seq crepBody794_28 crepBody794_2

def crepBody794_30 : CrepProg (BitVec 64) :=
.seq crepBody794_27 crepBody794_29

def crepBody794_31 : CrepProg (BitVec 64) :=
.seq crepBody794_26 crepBody794_30

def crepBody794_32 : CrepProg (BitVec 64) :=
.seq crepBody794_25 crepBody794_31

def crepBody794_33 : CrepProg (BitVec 64) :=
.seq crepBody794_24 crepBody794_32

def crepBody794_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 18 (Flapjack.CrepExp.var 23)

def crepBody794_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 19 (Flapjack.CrepExp.var 24)

def crepBody794_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 20 (Flapjack.CrepExp.var 25)

def crepBody794_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 21 (Flapjack.CrepExp.var 26)

def crepBody794_38 : CrepProg (BitVec 64) :=
.seq crepBody794_37 crepBody794_2

def crepBody794_39 : CrepProg (BitVec 64) :=
.seq crepBody794_36 crepBody794_38

def crepBody794_40 : CrepProg (BitVec 64) :=
.seq crepBody794_35 crepBody794_39

def crepBody794_41 : CrepProg (BitVec 64) :=
.seq crepBody794_34 crepBody794_40

def crepBody794_42 : CrepProg (BitVec 64) :=
.seq crepBody794_33 crepBody794_41

def crepBody794_43 : CrepProg (BitVec 64) :=
.seq crepBody794_19 crepBody794_42

def crepBody794_44 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody794_43

def crepBody794_45 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 24#64])) crepBody794_44

def crepBody794_46 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 16#64])) crepBody794_45

def crepBody794_47 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 8#64])) crepBody794_46

def crepBody794_48 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64])) crepBody794_47

def crepBody794_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([31], none)) "u256_lt"
  [Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26,
    Flapjack.CrepExp.var 27, Flapjack.CrepExp.var 28, Flapjack.CrepExp.var 29, Flapjack.CrepExp.var 30]

def crepBody794_50 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 32)

def crepBody794_51 : CrepProg (BitVec 64) :=
.seq crepBody794_50 crepBody794_2

def crepBody794_52 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 84#64) crepBody794_51

def crepBody794_53 : CrepProg (BitVec 64) :=
.seq crepBody794_52 crepBody794_5

def crepBody794_54 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 31) (Flapjack.CrepExp.const 0#64)) crepBody794_53 crepBody794_2

def crepBody794_55 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([32], none)) "u256_lt"
  [Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26,
    Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody794_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 33)

def crepBody794_57 : CrepProg (BitVec 64) :=
.seq crepBody794_56 crepBody794_2

def crepBody794_58 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.const 85#64) crepBody794_57

def crepBody794_59 : CrepProg (BitVec 64) :=
.seq crepBody794_58 crepBody794_5

def crepBody794_60 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 32) (Flapjack.CrepExp.const 0#64)) crepBody794_59 crepBody794_2

def crepBody794_61 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([33, 34, 35, 36], none)) "u256_sub"
  [Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26,
    Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody794_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([37], none)) "u256_lt"
  [Flapjack.CrepExp.var 27, Flapjack.CrepExp.var 28, Flapjack.CrepExp.var 29, Flapjack.CrepExp.var 30,
    Flapjack.CrepExp.var 33, Flapjack.CrepExp.var 34, Flapjack.CrepExp.var 35, Flapjack.CrepExp.var 36]

def crepBody794_63 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 38 (Flapjack.CrepExp.var 27)

def crepBody794_64 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 39 (Flapjack.CrepExp.var 28)

def crepBody794_65 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 40 (Flapjack.CrepExp.var 29)

def crepBody794_66 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 41 (Flapjack.CrepExp.var 30)

def crepBody794_67 : CrepProg (BitVec 64) :=
.seq crepBody794_66 crepBody794_2

def crepBody794_68 : CrepProg (BitVec 64) :=
.seq crepBody794_65 crepBody794_67

def crepBody794_69 : CrepProg (BitVec 64) :=
.seq crepBody794_64 crepBody794_68

def crepBody794_70 : CrepProg (BitVec 64) :=
.seq crepBody794_63 crepBody794_69

def crepBody794_71 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 37) (Flapjack.CrepExp.const 0#64)) crepBody794_70 crepBody794_2

def crepBody794_72 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14, 15, 16, 17], none)) "u256_add"
  [Flapjack.CrepExp.var 38, Flapjack.CrepExp.var 39, Flapjack.CrepExp.var 40, Flapjack.CrepExp.var 41,
    Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody794_73 : CrepProg (BitVec 64) :=
.seq crepBody794_71 crepBody794_72

def crepBody794_74 : CrepProg (BitVec 64) :=
.seq crepBody794_73 crepBody794_41

def crepBody794_75 : CrepProg (BitVec 64) :=
.dec 41 (Flapjack.CrepExp.var 36) crepBody794_74

def crepBody794_76 : CrepProg (BitVec 64) :=
.dec 40 (Flapjack.CrepExp.var 35) crepBody794_75

def crepBody794_77 : CrepProg (BitVec 64) :=
.dec 39 (Flapjack.CrepExp.var 34) crepBody794_76

def crepBody794_78 : CrepProg (BitVec 64) :=
.dec 38 (Flapjack.CrepExp.var 33) crepBody794_77

def crepBody794_79 : CrepProg (BitVec 64) :=
.seq crepBody794_62 crepBody794_78

def crepBody794_80 : CrepProg (BitVec 64) :=
.dec 37 (Flapjack.CrepExp.const 0#64) crepBody794_79

def crepBody794_81 : CrepProg (BitVec 64) :=
.seq crepBody794_61 crepBody794_80

def crepBody794_82 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.const 0#64) crepBody794_81

def crepBody794_83 : CrepProg (BitVec 64) :=
.dec 35 (Flapjack.CrepExp.const 0#64) crepBody794_82

def crepBody794_84 : CrepProg (BitVec 64) :=
.dec 34 (Flapjack.CrepExp.const 0#64) crepBody794_83

def crepBody794_85 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.const 0#64) crepBody794_84

def crepBody794_86 : CrepProg (BitVec 64) :=
.seq crepBody794_60 crepBody794_85

def crepBody794_87 : CrepProg (BitVec 64) :=
.seq crepBody794_55 crepBody794_86

def crepBody794_88 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody794_87

def crepBody794_89 : CrepProg (BitVec 64) :=
.seq crepBody794_54 crepBody794_88

def crepBody794_90 : CrepProg (BitVec 64) :=
.seq crepBody794_49 crepBody794_89

def crepBody794_91 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.const 0#64) crepBody794_90

def crepBody794_92 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 80#64],
      Flapjack.CrepExp.const 24#64])) crepBody794_91

def crepBody794_93 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 80#64],
      Flapjack.CrepExp.const 16#64])) crepBody794_92

def crepBody794_94 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 80#64],
      Flapjack.CrepExp.const 8#64])) crepBody794_93

def crepBody794_95 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 80#64])) crepBody794_94

def crepBody794_96 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 112#64],
      Flapjack.CrepExp.const 24#64])) crepBody794_95

def crepBody794_97 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 112#64],
      Flapjack.CrepExp.const 16#64])) crepBody794_96

def crepBody794_98 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 112#64],
      Flapjack.CrepExp.const 8#64])) crepBody794_97

def crepBody794_99 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 112#64])) crepBody794_98

def crepBody794_100 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 22) (Flapjack.CrepExp.const 0#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 22) (Flapjack.CrepExp.const 1#64)])) crepBody794_48 crepBody794_99

def crepBody794_101 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23, 24, 25, 26, 27], none)) "fee_mul"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20,
    Flapjack.CrepExp.var 21]

def crepBody794_102 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 34)

def crepBody794_103 : CrepProg (BitVec 64) :=
.seq crepBody794_102 crepBody794_2

def crepBody794_104 : CrepProg (BitVec 64) :=
.dec 34 (Flapjack.CrepExp.const 86#64) crepBody794_103

def crepBody794_105 : CrepProg (BitVec 64) :=
.seq crepBody794_104 crepBody794_5

def crepBody794_106 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 33) (Flapjack.CrepExp.const 0#64)) crepBody794_105 crepBody794_2

def crepBody794_107 : CrepProg (BitVec 64) :=
.dec 34 (Flapjack.CrepExp.const 87#64) crepBody794_103

def crepBody794_108 : CrepProg (BitVec 64) :=
.seq crepBody794_107 crepBody794_5

def crepBody794_109 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 6#64) (Flapjack.CrepExp.var 33)) crepBody794_108 crepBody794_2

def crepBody794_110 : CrepProg (BitVec 64) :=
.seq crepBody794_106 crepBody794_109

def crepBody794_111 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 35)

def crepBody794_112 : CrepProg (BitVec 64) :=
.seq crepBody794_111 crepBody794_2

def crepBody794_113 : CrepProg (BitVec 64) :=
.dec 35 (Flapjack.CrepExp.const 88#64) crepBody794_112

def crepBody794_114 : CrepProg (BitVec 64) :=
.seq crepBody794_113 crepBody794_5

def crepBody794_115 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.loadByte
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 256#64]),
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 34, Flapjack.CrepExp.const 32#64]]))
  (Flapjack.CrepExp.const 1#64)) crepBody794_114 crepBody794_2

def crepBody794_116 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 34 (Flapjack.CrepExp.var 35)

def crepBody794_117 : CrepProg (BitVec 64) :=
.seq crepBody794_116 crepBody794_2

def crepBody794_118 : CrepProg (BitVec 64) :=
.dec 35 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 34, Flapjack.CrepExp.const 1#64]) crepBody794_117

def crepBody794_119 : CrepProg (BitVec 64) :=
.seq crepBody794_115 crepBody794_118

def crepBody794_120 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 34) (Flapjack.CrepExp.var 33)) crepBody794_119

def crepBody794_121 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([35, 36, 37, 38], none)) "calculate_blob_gas_price"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
          Flapjack.CrepExp.const 96#64])]

def crepBody794_122 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([43], none)) "u256_lt"
  [Flapjack.CrepExp.var 39, Flapjack.CrepExp.var 40, Flapjack.CrepExp.var 41, Flapjack.CrepExp.var 42,
    Flapjack.CrepExp.var 35, Flapjack.CrepExp.var 36, Flapjack.CrepExp.var 37, Flapjack.CrepExp.var 38]

def crepBody794_123 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 44)

def crepBody794_124 : CrepProg (BitVec 64) :=
.seq crepBody794_123 crepBody794_2

def crepBody794_125 : CrepProg (BitVec 64) :=
.dec 44 (Flapjack.CrepExp.const 89#64) crepBody794_124

def crepBody794_126 : CrepProg (BitVec 64) :=
.seq crepBody794_125 crepBody794_5

def crepBody794_127 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 43) (Flapjack.CrepExp.const 0#64)) crepBody794_126 crepBody794_2

def crepBody794_128 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([44, 45, 46, 47, 48], none)) "fee_mul"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 39, Flapjack.CrepExp.var 40, Flapjack.CrepExp.var 41,
    Flapjack.CrepExp.var 42]

def crepBody794_129 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 28 (Flapjack.CrepExp.const 1#64)

def crepBody794_130 : CrepProg (BitVec 64) :=
.seq crepBody794_129 crepBody794_2

def crepBody794_131 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 44) (Flapjack.CrepExp.const 0#64)) crepBody794_130 crepBody794_2

def crepBody794_132 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([49, 50, 51, 52, 53], none)) "u256_add_carry"
  [Flapjack.CrepExp.var 29, Flapjack.CrepExp.var 30, Flapjack.CrepExp.var 31, Flapjack.CrepExp.var 32,
    Flapjack.CrepExp.var 45, Flapjack.CrepExp.var 46, Flapjack.CrepExp.var 47, Flapjack.CrepExp.var 48]

def crepBody794_133 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 53) (Flapjack.CrepExp.const 0#64)) crepBody794_130 crepBody794_2

def crepBody794_134 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 29 (Flapjack.CrepExp.var 49)

def crepBody794_135 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 30 (Flapjack.CrepExp.var 50)

def crepBody794_136 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 31 (Flapjack.CrepExp.var 51)

def crepBody794_137 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 32 (Flapjack.CrepExp.var 52)

def crepBody794_138 : CrepProg (BitVec 64) :=
.seq crepBody794_137 crepBody794_2

def crepBody794_139 : CrepProg (BitVec 64) :=
.seq crepBody794_136 crepBody794_138

def crepBody794_140 : CrepProg (BitVec 64) :=
.seq crepBody794_135 crepBody794_139

def crepBody794_141 : CrepProg (BitVec 64) :=
.seq crepBody794_134 crepBody794_140

def crepBody794_142 : CrepProg (BitVec 64) :=
.seq crepBody794_133 crepBody794_141

def crepBody794_143 : CrepProg (BitVec 64) :=
.seq crepBody794_132 crepBody794_142

def crepBody794_144 : CrepProg (BitVec 64) :=
.dec 53 (Flapjack.CrepExp.const 0#64) crepBody794_143

def crepBody794_145 : CrepProg (BitVec 64) :=
.dec 52 (Flapjack.CrepExp.const 0#64) crepBody794_144

def crepBody794_146 : CrepProg (BitVec 64) :=
.dec 51 (Flapjack.CrepExp.const 0#64) crepBody794_145

def crepBody794_147 : CrepProg (BitVec 64) :=
.dec 50 (Flapjack.CrepExp.const 0#64) crepBody794_146

def crepBody794_148 : CrepProg (BitVec 64) :=
.dec 49 (Flapjack.CrepExp.const 0#64) crepBody794_147

def crepBody794_149 : CrepProg (BitVec 64) :=
.seq crepBody794_131 crepBody794_148

def crepBody794_150 : CrepProg (BitVec 64) :=
.seq crepBody794_128 crepBody794_149

def crepBody794_151 : CrepProg (BitVec 64) :=
.dec 48 (Flapjack.CrepExp.const 0#64) crepBody794_150

def crepBody794_152 : CrepProg (BitVec 64) :=
.dec 47 (Flapjack.CrepExp.const 0#64) crepBody794_151

def crepBody794_153 : CrepProg (BitVec 64) :=
.dec 46 (Flapjack.CrepExp.const 0#64) crepBody794_152

def crepBody794_154 : CrepProg (BitVec 64) :=
.dec 45 (Flapjack.CrepExp.const 0#64) crepBody794_153

def crepBody794_155 : CrepProg (BitVec 64) :=
.dec 44 (Flapjack.CrepExp.const 0#64) crepBody794_154

def crepBody794_156 : CrepProg (BitVec 64) :=
.seq crepBody794_127 crepBody794_155

def crepBody794_157 : CrepProg (BitVec 64) :=
.seq crepBody794_122 crepBody794_156

def crepBody794_158 : CrepProg (BitVec 64) :=
.dec 43 (Flapjack.CrepExp.const 0#64) crepBody794_157

def crepBody794_159 : CrepProg (BitVec 64) :=
.dec 42 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 224#64],
      Flapjack.CrepExp.const 24#64])) crepBody794_158

def crepBody794_160 : CrepProg (BitVec 64) :=
.dec 41 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 224#64],
      Flapjack.CrepExp.const 16#64])) crepBody794_159

def crepBody794_161 : CrepProg (BitVec 64) :=
.dec 40 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 224#64],
      Flapjack.CrepExp.const 8#64])) crepBody794_160

def crepBody794_162 : CrepProg (BitVec 64) :=
.dec 39 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 224#64])) crepBody794_161

def crepBody794_163 : CrepProg (BitVec 64) :=
.seq crepBody794_121 crepBody794_162

def crepBody794_164 : CrepProg (BitVec 64) :=
.dec 38 (Flapjack.CrepExp.const 0#64) crepBody794_163

def crepBody794_165 : CrepProg (BitVec 64) :=
.dec 37 (Flapjack.CrepExp.const 0#64) crepBody794_164

def crepBody794_166 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.const 0#64) crepBody794_165

def crepBody794_167 : CrepProg (BitVec 64) :=
.dec 35 (Flapjack.CrepExp.const 0#64) crepBody794_166

def crepBody794_168 : CrepProg (BitVec 64) :=
.seq crepBody794_120 crepBody794_167

def crepBody794_169 : CrepProg (BitVec 64) :=
.dec 34 (Flapjack.CrepExp.const 0#64) crepBody794_168

def crepBody794_170 : CrepProg (BitVec 64) :=
.seq crepBody794_110 crepBody794_169

def crepBody794_171 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 264#64])) crepBody794_170

def crepBody794_172 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 22) (Flapjack.CrepExp.const 3#64)) crepBody794_171 crepBody794_2

def crepBody794_173 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.const 90#64) crepBody794_57

def crepBody794_174 : CrepProg (BitVec 64) :=
.seq crepBody794_173 crepBody794_5

def crepBody794_175 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 280#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody794_174 crepBody794_2

def crepBody794_176 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 22) (Flapjack.CrepExp.const 4#64)) crepBody794_175 crepBody794_2

def crepBody794_177 : CrepProg (BitVec 64) :=
.seq crepBody794_172 crepBody794_176

def crepBody794_178 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([37], none)) "u256_fits_word"
  [Flapjack.CrepExp.var 33, Flapjack.CrepExp.var 34, Flapjack.CrepExp.var 35, Flapjack.CrepExp.var 36]

def crepBody794_179 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 39)

def crepBody794_180 : CrepProg (BitVec 64) :=
.seq crepBody794_179 crepBody794_2

def crepBody794_181 : CrepProg (BitVec 64) :=
.dec 39 (Flapjack.CrepExp.const 92#64) crepBody794_180

def crepBody794_182 : CrepProg (BitVec 64) :=
.seq crepBody794_181 crepBody794_5

def crepBody794_183 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 37) (Flapjack.CrepExp.const 0#64)) crepBody794_182 crepBody794_2

def crepBody794_184 : CrepProg (BitVec 64) :=
.dec 39 (Flapjack.CrepExp.const 91#64) crepBody794_180

def crepBody794_185 : CrepProg (BitVec 64) :=
.seq crepBody794_184 crepBody794_5

def crepBody794_186 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 33) (Flapjack.CrepExp.var 38)) crepBody794_185 crepBody794_2

def crepBody794_187 : CrepProg (BitVec 64) :=
.seq crepBody794_183 crepBody794_186

def crepBody794_188 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 38) (Flapjack.CrepExp.var 33)) crepBody794_182 crepBody794_2

def crepBody794_189 : CrepProg (BitVec 64) :=
.seq crepBody794_187 crepBody794_188

def crepBody794_190 : CrepProg (BitVec 64) :=
.dec 39 (Flapjack.CrepExp.const 93#64) crepBody794_180

def crepBody794_191 : CrepProg (BitVec 64) :=
.seq crepBody794_190 crepBody794_5

def crepBody794_192 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 28) (Flapjack.CrepExp.const 0#64)) crepBody794_191 crepBody794_2

def crepBody794_193 : CrepProg (BitVec 64) :=
.seq crepBody794_189 crepBody794_192

def crepBody794_194 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([39, 40, 41, 42, 43], none)) "u256_add_carry"
  [Flapjack.CrepExp.var 29, Flapjack.CrepExp.var 30, Flapjack.CrepExp.var 31, Flapjack.CrepExp.var 32,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody794_195 : CrepProg (BitVec 64) :=
.dec 44 (Flapjack.CrepExp.const 93#64) crepBody794_124

def crepBody794_196 : CrepProg (BitVec 64) :=
.seq crepBody794_195 crepBody794_5

def crepBody794_197 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 43) (Flapjack.CrepExp.const 0#64)) crepBody794_196 crepBody794_2

def crepBody794_198 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([44], none)) "u256_lt"
  [Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.var 39, Flapjack.CrepExp.var 40, Flapjack.CrepExp.var 41, Flapjack.CrepExp.var 42]

def crepBody794_199 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 45)

def crepBody794_200 : CrepProg (BitVec 64) :=
.seq crepBody794_199 crepBody794_2

def crepBody794_201 : CrepProg (BitVec 64) :=
.dec 45 (Flapjack.CrepExp.const 93#64) crepBody794_200

def crepBody794_202 : CrepProg (BitVec 64) :=
.seq crepBody794_201 crepBody794_5

def crepBody794_203 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 44) (Flapjack.CrepExp.const 0#64)) crepBody794_202 crepBody794_2

def crepBody794_204 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([45, 46], none)) "get_code"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.var 1]

def crepBody794_205 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([47], none)) "memeq"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 136#64]),
    Flapjack.CrepExp.const 32#64]

def crepBody794_206 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([48], none)) "is_valid_delegation" [Flapjack.CrepExp.var 45, Flapjack.CrepExp.var 46]

def crepBody794_207 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 49)

def crepBody794_208 : CrepProg (BitVec 64) :=
.seq crepBody794_207 crepBody794_2

def crepBody794_209 : CrepProg (BitVec 64) :=
.dec 49 (Flapjack.CrepExp.const 94#64) crepBody794_208

def crepBody794_210 : CrepProg (BitVec 64) :=
.seq crepBody794_209 crepBody794_5

def crepBody794_211 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 48) (Flapjack.CrepExp.const 0#64)) crepBody794_210 crepBody794_2

def crepBody794_212 : CrepProg (BitVec 64) :=
.seq crepBody794_206 crepBody794_211

def crepBody794_213 : CrepProg (BitVec 64) :=
.dec 48 (Flapjack.CrepExp.const 0#64) crepBody794_212

def crepBody794_214 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 47) (Flapjack.CrepExp.const 0#64)) crepBody794_213 crepBody794_2

def crepBody794_215 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17]

def crepBody794_216 : CrepProg (BitVec 64) :=
.seq crepBody794_214 crepBody794_215

def crepBody794_217 : CrepProg (BitVec 64) :=
.seq crepBody794_205 crepBody794_216

def crepBody794_218 : CrepProg (BitVec 64) :=
.dec 47 (Flapjack.CrepExp.const 0#64) crepBody794_217

def crepBody794_219 : CrepProg (BitVec 64) :=
.seq crepBody794_204 crepBody794_218

def crepBody794_220 : CrepProg (BitVec 64) :=
.dec 46 (Flapjack.CrepExp.const 0#64) crepBody794_219

def crepBody794_221 : CrepProg (BitVec 64) :=
.dec 45 (Flapjack.CrepExp.const 0#64) crepBody794_220

def crepBody794_222 : CrepProg (BitVec 64) :=
.seq crepBody794_203 crepBody794_221

def crepBody794_223 : CrepProg (BitVec 64) :=
.seq crepBody794_198 crepBody794_222

def crepBody794_224 : CrepProg (BitVec 64) :=
.dec 44 (Flapjack.CrepExp.const 0#64) crepBody794_223

def crepBody794_225 : CrepProg (BitVec 64) :=
.seq crepBody794_197 crepBody794_224

def crepBody794_226 : CrepProg (BitVec 64) :=
.seq crepBody794_194 crepBody794_225

def crepBody794_227 : CrepProg (BitVec 64) :=
.dec 43 (Flapjack.CrepExp.const 0#64) crepBody794_226

def crepBody794_228 : CrepProg (BitVec 64) :=
.dec 42 (Flapjack.CrepExp.const 0#64) crepBody794_227

def crepBody794_229 : CrepProg (BitVec 64) :=
.dec 41 (Flapjack.CrepExp.const 0#64) crepBody794_228

def crepBody794_230 : CrepProg (BitVec 64) :=
.dec 40 (Flapjack.CrepExp.const 0#64) crepBody794_229

def crepBody794_231 : CrepProg (BitVec 64) :=
.dec 39 (Flapjack.CrepExp.const 0#64) crepBody794_230

def crepBody794_232 : CrepProg (BitVec 64) :=
.seq crepBody794_193 crepBody794_231

def crepBody794_233 : CrepProg (BitVec 64) :=
.dec 38 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 0#64])) crepBody794_232

def crepBody794_234 : CrepProg (BitVec 64) :=
.seq crepBody794_178 crepBody794_233

def crepBody794_235 : CrepProg (BitVec 64) :=
.dec 37 (Flapjack.CrepExp.const 0#64) crepBody794_234

def crepBody794_236 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64],
      Flapjack.CrepExp.const 24#64])) crepBody794_235

def crepBody794_237 : CrepProg (BitVec 64) :=
.dec 35 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64],
      Flapjack.CrepExp.const 16#64])) crepBody794_236

def crepBody794_238 : CrepProg (BitVec 64) :=
.dec 34 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64],
      Flapjack.CrepExp.const 8#64])) crepBody794_237

def crepBody794_239 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64])) crepBody794_238

def crepBody794_240 : CrepProg (BitVec 64) :=
.seq crepBody794_177 crepBody794_239

def crepBody794_241 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.var 27) crepBody794_240

def crepBody794_242 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.var 26) crepBody794_241

def crepBody794_243 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.var 25) crepBody794_242

def crepBody794_244 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.var 24) crepBody794_243

def crepBody794_245 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.var 23) crepBody794_244

def crepBody794_246 : CrepProg (BitVec 64) :=
.seq crepBody794_101 crepBody794_245

def crepBody794_247 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody794_246

def crepBody794_248 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody794_247

def crepBody794_249 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody794_248

def crepBody794_250 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody794_249

def crepBody794_251 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody794_250

def crepBody794_252 : CrepProg (BitVec 64) :=
.seq crepBody794_100 crepBody794_251

def crepBody794_253 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64])) crepBody794_252

def crepBody794_254 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody794_253

def crepBody794_255 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody794_254

def crepBody794_256 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody794_255

def crepBody794_257 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody794_256

def crepBody794_258 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody794_257

def crepBody794_259 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody794_258

def crepBody794_260 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody794_259

def crepBody794_261 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody794_260

def crepBody794_262 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
          Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 24#64])) crepBody794_261

def crepBody794_263 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
          Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 16#64])) crepBody794_262

def crepBody794_264 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
          Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 8#64])) crepBody794_263

def crepBody794_265 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
      Flapjack.CrepExp.const 48#64])) crepBody794_264

def crepBody794_266 : CrepProg (BitVec 64) :=
.seq crepBody794_18 crepBody794_265

def crepBody794_267 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody794_266

def crepBody794_268 : CrepProg (BitVec 64) :=
.seq crepBody794_17 crepBody794_267

def crepBody794_269 : CrepProg (BitVec 64) :=
.seq crepBody794_12 crepBody794_268

def crepBody794_270 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody794_269

def crepBody794_271 : CrepProg (BitVec 64) :=
.seq crepBody794_11 crepBody794_270

def crepBody794_272 : CrepProg (BitVec 64) :=
.seq crepBody794_0 crepBody794_271

def crepBody794_273 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody794_272

def crepBody794_274 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 144#64])) crepBody794_273

def crepBody794_275 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.const 2752512#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 416#64]),
          Flapjack.CrepExp.const 48#64])]) crepBody794_274

def crepBody794_276 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 416#64]),
          Flapjack.CrepExp.const 8#64])]) crepBody794_275

def crepBody794_277 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 416#64]),
          Flapjack.CrepExp.const 0#64])]) crepBody794_276

def crepBody794_278 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 408#64]),
      Flapjack.CrepExp.const 8#64])) crepBody794_277

def data794 : CrepProg (BitVec 64) := crepBody794_278
def output794 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [99#8, 104#8, 101#8, 99#8, 107#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 97#8, 99#8, 116#8, 105#8, 111#8, 110#8], [0, 1], crepProgToHOL data794)
end InitECandidate.Proofs.FrontendStages.Crep
