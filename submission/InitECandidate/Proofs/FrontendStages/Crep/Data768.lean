import InitECandidate.Proofs.FrontendStages.Crep.Translate752
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody768_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "buffer_read"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 96#64,
    Flapjack.CrepExp.var 4]

def crepBody768_1 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody768_0

def crepBody768_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "u256_from_be" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 32#64]

def crepBody768_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "sat_word"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody768_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 10)

def crepBody768_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody768_6 : CrepProg (BitVec 64) :=
.seq crepBody768_4 crepBody768_5

def crepBody768_7 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 4#64) crepBody768_6

def crepBody768_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody768_9 : CrepProg (BitVec 64) :=
.seq crepBody768_7 crepBody768_8

def crepBody768_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 1024#64) (Flapjack.CrepExp.var 9)) crepBody768_9 crepBody768_5

def crepBody768_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10, 11, 12, 13], none)) "u256_from_be"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 32#64],
    Flapjack.CrepExp.const 32#64]

def crepBody768_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "sat_word"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody768_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 15)

def crepBody768_14 : CrepProg (BitVec 64) :=
.seq crepBody768_13 crepBody768_5

def crepBody768_15 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 4#64) crepBody768_14

def crepBody768_16 : CrepProg (BitVec 64) :=
.seq crepBody768_15 crepBody768_8

def crepBody768_17 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 1024#64) (Flapjack.CrepExp.var 14)) crepBody768_16 crepBody768_5

def crepBody768_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16, 17, 18], none)) "u256_from_be"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 64#64],
    Flapjack.CrepExp.const 32#64]

def crepBody768_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "sat_word"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18]

def crepBody768_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 20)

def crepBody768_21 : CrepProg (BitVec 64) :=
.seq crepBody768_20 crepBody768_5

def crepBody768_22 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 4#64) crepBody768_21

def crepBody768_23 : CrepProg (BitVec 64) :=
.seq crepBody768_22 crepBody768_8

def crepBody768_24 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 1024#64) (Flapjack.CrepExp.var 19)) crepBody768_23 crepBody768_5

def crepBody768_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "min" [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.var 14]

def crepBody768_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "buffer_read"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21,
    Flapjack.CrepExp.var 4]

def crepBody768_27 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody768_26

def crepBody768_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22, 23, 24, 25], none)) "u256_from_be" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 21]

def crepBody768_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([26], none)) "modexp_gas"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 22,
    Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25]

def crepBody768_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "charge_gas" [Flapjack.CrepExp.var 26]

def crepBody768_31 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody768_30

def crepBody768_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "alloc" [Flapjack.CrepExp.const 8#64]

def crepBody768_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 28) (Flapjack.CrepExp.var 29)

def crepBody768_34 : CrepProg (BitVec 64) :=
.seq crepBody768_33 crepBody768_5

def crepBody768_35 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.var 27) crepBody768_34

def crepBody768_36 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody768_35

def crepBody768_37 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.const 0#64) crepBody768_34

def crepBody768_38 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody768_37

def crepBody768_39 : CrepProg (BitVec 64) :=
.seq crepBody768_36 crepBody768_38

def crepBody768_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody768_41 : CrepProg (BitVec 64) :=
.seq crepBody768_39 crepBody768_40

def crepBody768_42 : CrepProg (BitVec 64) :=
.seq crepBody768_32 crepBody768_41

def crepBody768_43 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody768_42

def crepBody768_44 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 0#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.const 0#64))]) crepBody768_43 crepBody768_5

def crepBody768_45 : CrepProg (BitVec 64) :=
.seq crepBody768_31 crepBody768_44

def crepBody768_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 8#64]]

def crepBody768_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([28], none)) "heap_mark" []

def crepBody768_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([29], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64]]

def crepBody768_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([30], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 8#64]]

def crepBody768_50 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([31], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 8#64]]

def crepBody768_51 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([32], none)) "buffer_read"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 96#64, Flapjack.CrepExp.var 9,
    Flapjack.CrepExp.var 29]

def crepBody768_52 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody768_51

def crepBody768_53 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([32], none)) "buffer_read"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 14,
    Flapjack.CrepExp.var 30]

def crepBody768_54 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody768_53

def crepBody768_55 : CrepProg (BitVec 64) :=
.seq crepBody768_52 crepBody768_54

def crepBody768_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([32], none)) "buffer_read"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 14], Flapjack.CrepExp.var 19,
    Flapjack.CrepExp.var 31]

def crepBody768_57 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody768_56

def crepBody768_58 : CrepProg (BitVec 64) :=
.seq crepBody768_55 crepBody768_57

def crepBody768_59 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([32], none)) "modexp"
  [Flapjack.CrepExp.var 29, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 30, Flapjack.CrepExp.var 14,
    Flapjack.CrepExp.var 31, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 27]

def crepBody768_60 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody768_59

def crepBody768_61 : CrepProg (BitVec 64) :=
.seq crepBody768_58 crepBody768_60

def crepBody768_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([32], none)) "heap_release" [Flapjack.CrepExp.var 28]

def crepBody768_63 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody768_62

def crepBody768_64 : CrepProg (BitVec 64) :=
.seq crepBody768_61 crepBody768_63

def crepBody768_65 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 32) (Flapjack.CrepExp.var 33)

def crepBody768_66 : CrepProg (BitVec 64) :=
.seq crepBody768_65 crepBody768_5

def crepBody768_67 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.var 27) crepBody768_66

def crepBody768_68 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody768_67

def crepBody768_69 : CrepProg (BitVec 64) :=
.seq crepBody768_64 crepBody768_68

def crepBody768_70 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.var 19) crepBody768_66

def crepBody768_71 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody768_70

def crepBody768_72 : CrepProg (BitVec 64) :=
.seq crepBody768_69 crepBody768_71

def crepBody768_73 : CrepProg (BitVec 64) :=
.seq crepBody768_72 crepBody768_40

def crepBody768_74 : CrepProg (BitVec 64) :=
.seq crepBody768_50 crepBody768_73

def crepBody768_75 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.const 0#64) crepBody768_74

def crepBody768_76 : CrepProg (BitVec 64) :=
.seq crepBody768_49 crepBody768_75

def crepBody768_77 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.const 0#64) crepBody768_76

def crepBody768_78 : CrepProg (BitVec 64) :=
.seq crepBody768_48 crepBody768_77

def crepBody768_79 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.const 0#64) crepBody768_78

def crepBody768_80 : CrepProg (BitVec 64) :=
.seq crepBody768_47 crepBody768_79

def crepBody768_81 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.const 0#64) crepBody768_80

def crepBody768_82 : CrepProg (BitVec 64) :=
.seq crepBody768_46 crepBody768_81

def crepBody768_83 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody768_82

def crepBody768_84 : CrepProg (BitVec 64) :=
.seq crepBody768_45 crepBody768_83

def crepBody768_85 : CrepProg (BitVec 64) :=
.seq crepBody768_29 crepBody768_84

def crepBody768_86 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody768_85

def crepBody768_87 : CrepProg (BitVec 64) :=
.seq crepBody768_28 crepBody768_86

def crepBody768_88 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody768_87

def crepBody768_89 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody768_88

def crepBody768_90 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody768_89

def crepBody768_91 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody768_90

def crepBody768_92 : CrepProg (BitVec 64) :=
.seq crepBody768_27 crepBody768_91

def crepBody768_93 : CrepProg (BitVec 64) :=
.seq crepBody768_25 crepBody768_92

def crepBody768_94 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody768_93

def crepBody768_95 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.const 96#64, Flapjack.CrepExp.var 9]) crepBody768_94

def crepBody768_96 : CrepProg (BitVec 64) :=
.seq crepBody768_24 crepBody768_95

def crepBody768_97 : CrepProg (BitVec 64) :=
.seq crepBody768_19 crepBody768_96

def crepBody768_98 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody768_97

def crepBody768_99 : CrepProg (BitVec 64) :=
.seq crepBody768_18 crepBody768_98

def crepBody768_100 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody768_99

def crepBody768_101 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody768_100

def crepBody768_102 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody768_101

def crepBody768_103 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody768_102

def crepBody768_104 : CrepProg (BitVec 64) :=
.seq crepBody768_17 crepBody768_103

def crepBody768_105 : CrepProg (BitVec 64) :=
.seq crepBody768_12 crepBody768_104

def crepBody768_106 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody768_105

def crepBody768_107 : CrepProg (BitVec 64) :=
.seq crepBody768_11 crepBody768_106

def crepBody768_108 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody768_107

def crepBody768_109 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody768_108

def crepBody768_110 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody768_109

def crepBody768_111 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody768_110

def crepBody768_112 : CrepProg (BitVec 64) :=
.seq crepBody768_10 crepBody768_111

def crepBody768_113 : CrepProg (BitVec 64) :=
.seq crepBody768_3 crepBody768_112

def crepBody768_114 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody768_113

def crepBody768_115 : CrepProg (BitVec 64) :=
.seq crepBody768_2 crepBody768_114

def crepBody768_116 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody768_115

def crepBody768_117 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody768_116

def crepBody768_118 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody768_117

def crepBody768_119 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody768_118

def crepBody768_120 : CrepProg (BitVec 64) :=
.seq crepBody768_1 crepBody768_119

def crepBody768_121 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 272#64])) crepBody768_120

def crepBody768_122 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64])) crepBody768_121

def crepBody768_123 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 88#64])) crepBody768_122

def crepBody768_124 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody768_123

def data768 : CrepProg (BitVec 64) := crepBody768_124
def output768 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 95#8, 109#8, 111#8, 100#8, 101#8, 120#8, 112#8], [], crepProgToHOL data768)
end InitECandidate.Proofs.FrontendStages.Crep
