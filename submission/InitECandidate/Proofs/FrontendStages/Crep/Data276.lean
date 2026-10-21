import InitECandidate.Proofs.FrontendStages.Crep.Translate260
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody276_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3], none)) "rlp_list_to_slices" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody276_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 120#64]]

def crepBody276_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6, 7, 8, 9], none)) "rlp_item"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 16#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64])]

def crepBody276_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 10)

def crepBody276_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody276_5 : CrepProg (BitVec 64) :=
.seq crepBody276_3 crepBody276_4

def crepBody276_6 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 20#64) crepBody276_5

def crepBody276_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 6#64

def crepBody276_8 : CrepProg (BitVec 64) :=
.seq crepBody276_6 crepBody276_7

def crepBody276_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 1#64)) crepBody276_8 crepBody276_4

def crepBody276_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10, 11], none)) "rlp_list_to_slices" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody276_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 12)

def crepBody276_12 : CrepProg (BitVec 64) :=
.seq crepBody276_11 crepBody276_4

def crepBody276_13 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 20#64) crepBody276_12

def crepBody276_14 : CrepProg (BitVec 64) :=
.seq crepBody276_13 crepBody276_7

def crepBody276_15 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 6#64)) crepBody276_14 crepBody276_4

def crepBody276_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13, 14, 15, 16], none)) "tx_scalar_u256"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 32#64]

def crepBody276_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 17) (Flapjack.CrepExp.var 18)

def crepBody276_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 19)

def crepBody276_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 20)

def crepBody276_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 21)

def crepBody276_21 : CrepProg (BitVec 64) :=
.seq crepBody276_20 crepBody276_4

def crepBody276_22 : CrepProg (BitVec 64) :=
.seq crepBody276_19 crepBody276_21

def crepBody276_23 : CrepProg (BitVec 64) :=
.seq crepBody276_18 crepBody276_22

def crepBody276_24 : CrepProg (BitVec 64) :=
.seq crepBody276_17 crepBody276_23

def crepBody276_25 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.var 16) crepBody276_24

def crepBody276_26 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 15) crepBody276_25

def crepBody276_27 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.var 14) crepBody276_26

def crepBody276_28 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.var 13) crepBody276_27

def crepBody276_29 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 0#64]) crepBody276_28

def crepBody276_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "tx_fixed_bytes"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.const 20#64]

def crepBody276_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 18) (Flapjack.CrepExp.var 19)

def crepBody276_32 : CrepProg (BitVec 64) :=
.seq crepBody276_31 crepBody276_4

def crepBody276_33 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.var 17) crepBody276_32

def crepBody276_34 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 32#64]) crepBody276_33

def crepBody276_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "tx_scalar_word"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 12#64]

def crepBody276_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.var 20)

def crepBody276_37 : CrepProg (BitVec 64) :=
.seq crepBody276_36 crepBody276_4

def crepBody276_38 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 18) crepBody276_37

def crepBody276_39 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 40#64]) crepBody276_38

def crepBody276_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "tx_scalar_word"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.const 12#64]

def crepBody276_41 : CrepProg (BitVec 64) :=
.seq crepBody276_39 crepBody276_40

def crepBody276_42 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 48#64]) crepBody276_38

def crepBody276_43 : CrepProg (BitVec 64) :=
.seq crepBody276_41 crepBody276_42

def crepBody276_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19, 20, 21, 22], none)) "tx_scalar_u256"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 32#64]

def crepBody276_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 23) (Flapjack.CrepExp.var 24)

def crepBody276_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 23, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 25)

def crepBody276_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 23, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 26)

def crepBody276_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 23, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 27)

def crepBody276_49 : CrepProg (BitVec 64) :=
.seq crepBody276_48 crepBody276_4

def crepBody276_50 : CrepProg (BitVec 64) :=
.seq crepBody276_47 crepBody276_49

def crepBody276_51 : CrepProg (BitVec 64) :=
.seq crepBody276_46 crepBody276_50

def crepBody276_52 : CrepProg (BitVec 64) :=
.seq crepBody276_45 crepBody276_51

def crepBody276_53 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.var 22) crepBody276_52

def crepBody276_54 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.var 21) crepBody276_53

def crepBody276_55 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.var 20) crepBody276_54

def crepBody276_56 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.var 19) crepBody276_55

def crepBody276_57 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 56#64]) crepBody276_56

def crepBody276_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23, 24, 25, 26], none)) "tx_scalar_u256"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 5#64, Flapjack.CrepExp.const 32#64]

def crepBody276_59 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 27) (Flapjack.CrepExp.var 28)

def crepBody276_60 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 27, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 29)

def crepBody276_61 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 27, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 30)

def crepBody276_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 27, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 31)

def crepBody276_63 : CrepProg (BitVec 64) :=
.seq crepBody276_62 crepBody276_4

def crepBody276_64 : CrepProg (BitVec 64) :=
.seq crepBody276_61 crepBody276_63

def crepBody276_65 : CrepProg (BitVec 64) :=
.seq crepBody276_60 crepBody276_64

def crepBody276_66 : CrepProg (BitVec 64) :=
.seq crepBody276_59 crepBody276_65

def crepBody276_67 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.var 26) crepBody276_66

def crepBody276_68 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.var 25) crepBody276_67

def crepBody276_69 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.var 24) crepBody276_68

def crepBody276_70 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.var 23) crepBody276_69

def crepBody276_71 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 88#64]) crepBody276_70

def crepBody276_72 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 27)

def crepBody276_73 : CrepProg (BitVec 64) :=
.seq crepBody276_72 crepBody276_4

def crepBody276_74 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64]) crepBody276_73

def crepBody276_75 : CrepProg (BitVec 64) :=
.seq crepBody276_71 crepBody276_74

def crepBody276_76 : CrepProg (BitVec 64) :=
.seq crepBody276_58 crepBody276_75

def crepBody276_77 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody276_76

def crepBody276_78 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody276_77

def crepBody276_79 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody276_78

def crepBody276_80 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody276_79

def crepBody276_81 : CrepProg (BitVec 64) :=
.seq crepBody276_57 crepBody276_80

def crepBody276_82 : CrepProg (BitVec 64) :=
.seq crepBody276_44 crepBody276_81

def crepBody276_83 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody276_82

def crepBody276_84 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody276_83

def crepBody276_85 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody276_84

def crepBody276_86 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody276_85

def crepBody276_87 : CrepProg (BitVec 64) :=
.seq crepBody276_43 crepBody276_86

def crepBody276_88 : CrepProg (BitVec 64) :=
.seq crepBody276_35 crepBody276_87

def crepBody276_89 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody276_88

def crepBody276_90 : CrepProg (BitVec 64) :=
.seq crepBody276_34 crepBody276_89

def crepBody276_91 : CrepProg (BitVec 64) :=
.seq crepBody276_30 crepBody276_90

def crepBody276_92 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody276_91

def crepBody276_93 : CrepProg (BitVec 64) :=
.seq crepBody276_29 crepBody276_92

def crepBody276_94 : CrepProg (BitVec 64) :=
.seq crepBody276_16 crepBody276_93

def crepBody276_95 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody276_94

def crepBody276_96 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody276_95

def crepBody276_97 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody276_96

def crepBody276_98 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody276_97

def crepBody276_99 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 120#64]]) crepBody276_98

def crepBody276_100 : CrepProg (BitVec 64) :=
.seq crepBody276_15 crepBody276_99

def crepBody276_101 : CrepProg (BitVec 64) :=
.seq crepBody276_10 crepBody276_100

def crepBody276_102 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody276_101

def crepBody276_103 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody276_102

def crepBody276_104 : CrepProg (BitVec 64) :=
.seq crepBody276_9 crepBody276_103

def crepBody276_105 : CrepProg (BitVec 64) :=
.seq crepBody276_2 crepBody276_104

def crepBody276_106 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody276_105

def crepBody276_107 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody276_106

def crepBody276_108 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody276_107

def crepBody276_109 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody276_108

def crepBody276_110 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 3)) crepBody276_109

def crepBody276_111 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 3]

def crepBody276_112 : CrepProg (BitVec 64) :=
.seq crepBody276_110 crepBody276_111

def crepBody276_113 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody276_112

def crepBody276_114 : CrepProg (BitVec 64) :=
.seq crepBody276_1 crepBody276_113

def crepBody276_115 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody276_114

def crepBody276_116 : CrepProg (BitVec 64) :=
.seq crepBody276_0 crepBody276_115

def crepBody276_117 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody276_116

def crepBody276_118 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody276_117

def data276 : CrepProg (BitVec 64) := crepBody276_118
def output276 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 97#8, 117#8, 116#8, 104#8, 111#8, 114#8, 105#8, 122#8, 97#8, 116#8,
    105#8, 111#8, 110#8, 115#8], [0, 1], crepProgToHOL data276)
end InitECandidate.Proofs.FrontendStages.Crep
