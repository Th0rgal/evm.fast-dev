import InitECandidate.Proofs.FrontendStages.Crep.Translate261
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody277_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 2)

def crepBody277_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody277_2 : CrepProg (BitVec 64) :=
.seq crepBody277_0 crepBody277_1

def crepBody277_3 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 1#64) crepBody277_2

def crepBody277_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 6#64

def crepBody277_5 : CrepProg (BitVec 64) :=
.seq crepBody277_3 crepBody277_4

def crepBody277_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody277_5 crepBody277_1

def crepBody277_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 400#64]

def crepBody277_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "memzero" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 400#64]

def crepBody277_9 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody277_8

def crepBody277_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 5)

def crepBody277_11 : CrepProg (BitVec 64) :=
.seq crepBody277_10 crepBody277_1

def crepBody277_12 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 0) crepBody277_11

def crepBody277_13 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 384#64]) crepBody277_12

def crepBody277_14 : CrepProg (BitVec 64) :=
.seq crepBody277_9 crepBody277_13

def crepBody277_15 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 1) crepBody277_11

def crepBody277_16 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 392#64]) crepBody277_15

def crepBody277_17 : CrepProg (BitVec 64) :=
.seq crepBody277_14 crepBody277_16

def crepBody277_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4, 5, 6, 7], none)) "rlp_decode_fully"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 1#64]]

def crepBody277_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 2)

def crepBody277_20 : CrepProg (BitVec 64) :=
.seq crepBody277_19 crepBody277_1

def crepBody277_21 : CrepProg (BitVec 64) :=
.seq crepBody277_18 crepBody277_20

def crepBody277_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.const 11#64)

def crepBody277_23 : CrepProg (BitVec 64) :=
.seq crepBody277_22 crepBody277_1

def crepBody277_24 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 1#64)) crepBody277_23 crepBody277_1

def crepBody277_25 : CrepProg (BitVec 64) :=
.seq crepBody277_21 crepBody277_24

def crepBody277_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.const 12#64)

def crepBody277_27 : CrepProg (BitVec 64) :=
.seq crepBody277_26 crepBody277_1

def crepBody277_28 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 2#64)) crepBody277_27 crepBody277_1

def crepBody277_29 : CrepProg (BitVec 64) :=
.seq crepBody277_25 crepBody277_28

def crepBody277_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.const 14#64)

def crepBody277_31 : CrepProg (BitVec 64) :=
.seq crepBody277_30 crepBody277_1

def crepBody277_32 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 3#64)) crepBody277_31 crepBody277_1

def crepBody277_33 : CrepProg (BitVec 64) :=
.seq crepBody277_29 crepBody277_32

def crepBody277_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.const 13#64)

def crepBody277_35 : CrepProg (BitVec 64) :=
.seq crepBody277_34 crepBody277_1

def crepBody277_36 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 4#64)) crepBody277_35 crepBody277_1

def crepBody277_37 : CrepProg (BitVec 64) :=
.seq crepBody277_33 crepBody277_36

def crepBody277_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4, 5, 6, 7], none)) "rlp_decode_fully" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody277_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 10)

def crepBody277_40 : CrepProg (BitVec 64) :=
.seq crepBody277_39 crepBody277_1

def crepBody277_41 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 2#64) crepBody277_40

def crepBody277_42 : CrepProg (BitVec 64) :=
.seq crepBody277_41 crepBody277_4

def crepBody277_43 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 192#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.const 254#64) (Flapjack.CrepExp.var 2))]) crepBody277_38 crepBody277_42

def crepBody277_44 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 1#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.const 4#64) (Flapjack.CrepExp.var 2))]) crepBody277_37 crepBody277_43

def crepBody277_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.var 11)

def crepBody277_46 : CrepProg (BitVec 64) :=
.seq crepBody277_45 crepBody277_1

def crepBody277_47 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 8) crepBody277_46

def crepBody277_48 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 0#64]) crepBody277_47

def crepBody277_49 : CrepProg (BitVec 64) :=
.seq crepBody277_44 crepBody277_48

def crepBody277_50 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 3#64) crepBody277_40

def crepBody277_51 : CrepProg (BitVec 64) :=
.seq crepBody277_50 crepBody277_4

def crepBody277_52 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 1#64)) crepBody277_51 crepBody277_1

def crepBody277_53 : CrepProg (BitVec 64) :=
.seq crepBody277_49 crepBody277_52

def crepBody277_54 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10, 11], none)) "rlp_list_to_slices" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody277_55 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 13)

def crepBody277_56 : CrepProg (BitVec 64) :=
.seq crepBody277_55 crepBody277_1

def crepBody277_57 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 4#64) crepBody277_56

def crepBody277_58 : CrepProg (BitVec 64) :=
.seq crepBody277_57 crepBody277_4

def crepBody277_59 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.var 9)) crepBody277_58 crepBody277_1

def crepBody277_60 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "tx_scalar_word"
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 12#64]

def crepBody277_61 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 15) (Flapjack.CrepExp.var 16)

def crepBody277_62 : CrepProg (BitVec 64) :=
.seq crepBody277_61 crepBody277_1

def crepBody277_63 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.var 14) crepBody277_62

def crepBody277_64 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 8#64]) crepBody277_63

def crepBody277_65 : CrepProg (BitVec 64) :=
.seq crepBody277_60 crepBody277_64

def crepBody277_66 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 13 (Flapjack.CrepExp.const 1#64)

def crepBody277_67 : CrepProg (BitVec 64) :=
.seq crepBody277_66 crepBody277_1

def crepBody277_68 : CrepProg (BitVec 64) :=
.seq crepBody277_65 crepBody277_67

def crepBody277_69 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 0#64)) crepBody277_68 crepBody277_1

def crepBody277_70 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "tx_scalar_word"
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 12#64]

def crepBody277_71 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 15 (Flapjack.CrepExp.var 14)

def crepBody277_72 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 16 (Flapjack.CrepExp.const 0#64)

def crepBody277_73 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 17 (Flapjack.CrepExp.const 0#64)

def crepBody277_74 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 18 (Flapjack.CrepExp.const 0#64)

def crepBody277_75 : CrepProg (BitVec 64) :=
.seq crepBody277_74 crepBody277_1

def crepBody277_76 : CrepProg (BitVec 64) :=
.seq crepBody277_73 crepBody277_75

def crepBody277_77 : CrepProg (BitVec 64) :=
.seq crepBody277_72 crepBody277_76

def crepBody277_78 : CrepProg (BitVec 64) :=
.seq crepBody277_71 crepBody277_77

def crepBody277_79 : CrepProg (BitVec 64) :=
.seq crepBody277_70 crepBody277_78

def crepBody277_80 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16, 17, 18], none)) "tx_scalar_u256"
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 32#64]

def crepBody277_81 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 4#64)) crepBody277_79 crepBody277_80

def crepBody277_82 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.var 20)

def crepBody277_83 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 21)

def crepBody277_84 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 22)

def crepBody277_85 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 23)

def crepBody277_86 : CrepProg (BitVec 64) :=
.seq crepBody277_85 crepBody277_1

def crepBody277_87 : CrepProg (BitVec 64) :=
.seq crepBody277_84 crepBody277_86

def crepBody277_88 : CrepProg (BitVec 64) :=
.seq crepBody277_83 crepBody277_87

def crepBody277_89 : CrepProg (BitVec 64) :=
.seq crepBody277_82 crepBody277_88

def crepBody277_90 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.var 18) crepBody277_89

def crepBody277_91 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 17) crepBody277_90

def crepBody277_92 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.var 16) crepBody277_91

def crepBody277_93 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 15) crepBody277_92

def crepBody277_94 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 16#64]) crepBody277_93

def crepBody277_95 : CrepProg (BitVec 64) :=
.seq crepBody277_81 crepBody277_94

def crepBody277_96 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 13 (Flapjack.CrepExp.var 19)

def crepBody277_97 : CrepProg (BitVec 64) :=
.seq crepBody277_96 crepBody277_1

def crepBody277_98 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 1#64]) crepBody277_97

def crepBody277_99 : CrepProg (BitVec 64) :=
.seq crepBody277_95 crepBody277_98

def crepBody277_100 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16, 17, 18], none)) "tx_scalar_u256"
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 0#64]

def crepBody277_101 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 48#64]) crepBody277_93

def crepBody277_102 : CrepProg (BitVec 64) :=
.seq crepBody277_100 crepBody277_101

def crepBody277_103 : CrepProg (BitVec 64) :=
.seq crepBody277_102 crepBody277_98

def crepBody277_104 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 80#64]) crepBody277_93

def crepBody277_105 : CrepProg (BitVec 64) :=
.seq crepBody277_100 crepBody277_104

def crepBody277_106 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16, 17, 18], none)) "tx_scalar_u256"
  [Flapjack.CrepExp.var 12,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.const 0#64]

def crepBody277_107 : CrepProg (BitVec 64) :=
.seq crepBody277_105 crepBody277_106

def crepBody277_108 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 112#64]) crepBody277_93

def crepBody277_109 : CrepProg (BitVec 64) :=
.seq crepBody277_107 crepBody277_108

def crepBody277_110 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 2#64]) crepBody277_97

def crepBody277_111 : CrepProg (BitVec 64) :=
.seq crepBody277_109 crepBody277_110

def crepBody277_112 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.const 1#64) (Flapjack.CrepExp.var 8)) crepBody277_103 crepBody277_111

def crepBody277_113 : CrepProg (BitVec 64) :=
.seq crepBody277_99 crepBody277_112

def crepBody277_114 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "tx_scalar_word"
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 14#64]

def crepBody277_115 : CrepProg (BitVec 64) :=
.seq crepBody277_113 crepBody277_114

def crepBody277_116 : CrepProg (BitVec 64) :=
.seq crepBody277_82 crepBody277_1

def crepBody277_117 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 14) crepBody277_116

def crepBody277_118 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 144#64]) crepBody277_117

def crepBody277_119 : CrepProg (BitVec 64) :=
.seq crepBody277_115 crepBody277_118

def crepBody277_120 : CrepProg (BitVec 64) :=
.seq crepBody277_119 crepBody277_98

def crepBody277_121 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "tx_fixed_bytes"
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 20#64]

def crepBody277_122 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "tx_to_item" [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody277_123 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 3#64)) crepBody277_121 crepBody277_122

def crepBody277_124 : CrepProg (BitVec 64) :=
.seq crepBody277_120 crepBody277_123

def crepBody277_125 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 152#64]) crepBody277_117

def crepBody277_126 : CrepProg (BitVec 64) :=
.seq crepBody277_124 crepBody277_125

def crepBody277_127 : CrepProg (BitVec 64) :=
.seq crepBody277_126 crepBody277_98

def crepBody277_128 : CrepProg (BitVec 64) :=
.seq crepBody277_127 crepBody277_80

def crepBody277_129 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 160#64]) crepBody277_93

def crepBody277_130 : CrepProg (BitVec 64) :=
.seq crepBody277_128 crepBody277_129

def crepBody277_131 : CrepProg (BitVec 64) :=
.seq crepBody277_130 crepBody277_98

def crepBody277_132 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19, 20], none)) "tx_bytes_item" [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody277_133 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 21) (Flapjack.CrepExp.var 22)

def crepBody277_134 : CrepProg (BitVec 64) :=
.seq crepBody277_133 crepBody277_1

def crepBody277_135 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 19) crepBody277_134

def crepBody277_136 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 192#64]) crepBody277_135

def crepBody277_137 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 20) crepBody277_134

def crepBody277_138 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 200#64]) crepBody277_137

def crepBody277_139 : CrepProg (BitVec 64) :=
.seq crepBody277_136 crepBody277_138

def crepBody277_140 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 13 (Flapjack.CrepExp.var 21)

def crepBody277_141 : CrepProg (BitVec 64) :=
.seq crepBody277_140 crepBody277_1

def crepBody277_142 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 1#64]) crepBody277_141

def crepBody277_143 : CrepProg (BitVec 64) :=
.seq crepBody277_139 crepBody277_142

def crepBody277_144 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21, 22], none)) "tx_list_item" [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody277_145 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23, 24], none)) "decode_access_list" [Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22]

def crepBody277_146 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 25) (Flapjack.CrepExp.var 26)

def crepBody277_147 : CrepProg (BitVec 64) :=
.seq crepBody277_146 crepBody277_1

def crepBody277_148 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.var 23) crepBody277_147

def crepBody277_149 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 208#64]) crepBody277_148

def crepBody277_150 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.var 24) crepBody277_147

def crepBody277_151 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 216#64]) crepBody277_150

def crepBody277_152 : CrepProg (BitVec 64) :=
.seq crepBody277_149 crepBody277_151

def crepBody277_153 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 13 (Flapjack.CrepExp.var 25)

def crepBody277_154 : CrepProg (BitVec 64) :=
.seq crepBody277_153 crepBody277_1

def crepBody277_155 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 1#64]) crepBody277_154

def crepBody277_156 : CrepProg (BitVec 64) :=
.seq crepBody277_152 crepBody277_155

def crepBody277_157 : CrepProg (BitVec 64) :=
.seq crepBody277_145 crepBody277_156

def crepBody277_158 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody277_157

def crepBody277_159 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody277_158

def crepBody277_160 : CrepProg (BitVec 64) :=
.seq crepBody277_144 crepBody277_159

def crepBody277_161 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody277_160

def crepBody277_162 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody277_161

def crepBody277_163 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 0#64)) crepBody277_162 crepBody277_1

def crepBody277_164 : CrepProg (BitVec 64) :=
.seq crepBody277_143 crepBody277_163

def crepBody277_165 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 21, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 23)

def crepBody277_166 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 21, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 24)

def crepBody277_167 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 21, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 25)

def crepBody277_168 : CrepProg (BitVec 64) :=
.seq crepBody277_167 crepBody277_1

def crepBody277_169 : CrepProg (BitVec 64) :=
.seq crepBody277_166 crepBody277_168

def crepBody277_170 : CrepProg (BitVec 64) :=
.seq crepBody277_165 crepBody277_169

def crepBody277_171 : CrepProg (BitVec 64) :=
.seq crepBody277_133 crepBody277_170

def crepBody277_172 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.var 18) crepBody277_171

def crepBody277_173 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.var 17) crepBody277_172

def crepBody277_174 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.var 16) crepBody277_173

def crepBody277_175 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 15) crepBody277_174

def crepBody277_176 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 224#64]) crepBody277_175

def crepBody277_177 : CrepProg (BitVec 64) :=
.seq crepBody277_80 crepBody277_176

def crepBody277_178 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21, 22], none)) "tx_list_item"
  [Flapjack.CrepExp.var 12,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 1#64]]

def crepBody277_179 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23, 24], none)) "decode_blob_hashes" [Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22]

def crepBody277_180 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 256#64]) crepBody277_148

def crepBody277_181 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 264#64]) crepBody277_150

def crepBody277_182 : CrepProg (BitVec 64) :=
.seq crepBody277_180 crepBody277_181

def crepBody277_183 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 2#64]) crepBody277_154

def crepBody277_184 : CrepProg (BitVec 64) :=
.seq crepBody277_182 crepBody277_183

def crepBody277_185 : CrepProg (BitVec 64) :=
.seq crepBody277_179 crepBody277_184

def crepBody277_186 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody277_185

def crepBody277_187 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody277_186

def crepBody277_188 : CrepProg (BitVec 64) :=
.seq crepBody277_178 crepBody277_187

def crepBody277_189 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody277_188

def crepBody277_190 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody277_189

def crepBody277_191 : CrepProg (BitVec 64) :=
.seq crepBody277_177 crepBody277_190

def crepBody277_192 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 3#64)) crepBody277_191 crepBody277_1

def crepBody277_193 : CrepProg (BitVec 64) :=
.seq crepBody277_164 crepBody277_192

def crepBody277_194 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23, 24], none)) "decode_authorizations"
  [Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22]

def crepBody277_195 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 272#64]) crepBody277_148

def crepBody277_196 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 280#64]) crepBody277_150

def crepBody277_197 : CrepProg (BitVec 64) :=
.seq crepBody277_195 crepBody277_196

def crepBody277_198 : CrepProg (BitVec 64) :=
.seq crepBody277_197 crepBody277_155

def crepBody277_199 : CrepProg (BitVec 64) :=
.seq crepBody277_194 crepBody277_198

def crepBody277_200 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody277_199

def crepBody277_201 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody277_200

def crepBody277_202 : CrepProg (BitVec 64) :=
.seq crepBody277_144 crepBody277_201

def crepBody277_203 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody277_202

def crepBody277_204 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody277_203

def crepBody277_205 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 4#64)) crepBody277_204 crepBody277_1

def crepBody277_206 : CrepProg (BitVec 64) :=
.seq crepBody277_193 crepBody277_205

def crepBody277_207 : CrepProg (BitVec 64) :=
.seq crepBody277_206 crepBody277_80

def crepBody277_208 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 288#64]) crepBody277_175

def crepBody277_209 : CrepProg (BitVec 64) :=
.seq crepBody277_207 crepBody277_208

def crepBody277_210 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16, 17, 18], none)) "tx_scalar_u256"
  [Flapjack.CrepExp.var 12,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.const 32#64]

def crepBody277_211 : CrepProg (BitVec 64) :=
.seq crepBody277_209 crepBody277_210

def crepBody277_212 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 320#64]) crepBody277_175

def crepBody277_213 : CrepProg (BitVec 64) :=
.seq crepBody277_211 crepBody277_212

def crepBody277_214 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16, 17, 18], none)) "tx_scalar_u256"
  [Flapjack.CrepExp.var 12,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 2#64],
    Flapjack.CrepExp.const 32#64]

def crepBody277_215 : CrepProg (BitVec 64) :=
.seq crepBody277_213 crepBody277_214

def crepBody277_216 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 352#64]) crepBody277_175

def crepBody277_217 : CrepProg (BitVec 64) :=
.seq crepBody277_215 crepBody277_216

def crepBody277_218 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody277_219 : CrepProg (BitVec 64) :=
.seq crepBody277_217 crepBody277_218

def crepBody277_220 : CrepProg (BitVec 64) :=
.seq crepBody277_132 crepBody277_219

def crepBody277_221 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody277_220

def crepBody277_222 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody277_221

def crepBody277_223 : CrepProg (BitVec 64) :=
.seq crepBody277_131 crepBody277_222

def crepBody277_224 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody277_223

def crepBody277_225 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody277_224

def crepBody277_226 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody277_225

def crepBody277_227 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody277_226

def crepBody277_228 : CrepProg (BitVec 64) :=
.seq crepBody277_69 crepBody277_227

def crepBody277_229 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody277_228

def crepBody277_230 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody277_229

def crepBody277_231 : CrepProg (BitVec 64) :=
.seq crepBody277_59 crepBody277_230

def crepBody277_232 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 10) crepBody277_231

def crepBody277_233 : CrepProg (BitVec 64) :=
.seq crepBody277_54 crepBody277_232

def crepBody277_234 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody277_233

def crepBody277_235 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody277_234

def crepBody277_236 : CrepProg (BitVec 64) :=
.seq crepBody277_53 crepBody277_235

def crepBody277_237 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 9#64) crepBody277_236

def crepBody277_238 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody277_237

def crepBody277_239 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody277_238

def crepBody277_240 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody277_239

def crepBody277_241 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody277_240

def crepBody277_242 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody277_241

def crepBody277_243 : CrepProg (BitVec 64) :=
.seq crepBody277_17 crepBody277_242

def crepBody277_244 : CrepProg (BitVec 64) :=
.seq crepBody277_7 crepBody277_243

def crepBody277_245 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody277_244

def crepBody277_246 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.loadByte (Flapjack.CrepExp.var 0)) crepBody277_245

def crepBody277_247 : CrepProg (BitVec 64) :=
.seq crepBody277_6 crepBody277_246

def data277 : CrepProg (BitVec 64) := crepBody277_247
def output277 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 97#8, 99#8, 116#8, 105#8, 111#8,
    110#8, 95#8, 114#8, 108#8, 112#8], [0, 1], crepProgToHOL data277)
end InitECandidate.Proofs.FrontendStages.Crep
