import InitECandidate.Proofs.FrontendStages.Crep.Translate706
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody722_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody722_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 96#64, Flapjack.CrepExp.const 9#64]]

def crepBody722_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sqr" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 13]

def crepBody722_3 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_2

def crepBody722_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sqr" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 14]

def crepBody722_5 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_4

def crepBody722_6 : CrepProg (BitVec 64) :=
.seq crepBody722_3 crepBody722_5

def crepBody722_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sqr" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5]

def crepBody722_8 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_7

def crepBody722_9 : CrepProg (BitVec 64) :=
.seq crepBody722_6 crepBody722_8

def crepBody722_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_add"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 13]

def crepBody722_11 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_10

def crepBody722_12 : CrepProg (BitVec 64) :=
.seq crepBody722_9 crepBody722_11

def crepBody722_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sqr" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 7]

def crepBody722_14 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_13

def crepBody722_15 : CrepProg (BitVec 64) :=
.seq crepBody722_12 crepBody722_14

def crepBody722_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sub"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 4]

def crepBody722_17 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_16

def crepBody722_18 : CrepProg (BitVec 64) :=
.seq crepBody722_15 crepBody722_17

def crepBody722_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sub"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 6]

def crepBody722_20 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_19

def crepBody722_21 : CrepProg (BitVec 64) :=
.seq crepBody722_18 crepBody722_20

def crepBody722_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_add"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 7]

def crepBody722_23 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_22

def crepBody722_24 : CrepProg (BitVec 64) :=
.seq crepBody722_21 crepBody722_23

def crepBody722_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_add"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 4]

def crepBody722_26 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_25

def crepBody722_27 : CrepProg (BitVec 64) :=
.seq crepBody722_24 crepBody722_26

def crepBody722_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_add"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 4]

def crepBody722_29 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_28

def crepBody722_30 : CrepProg (BitVec 64) :=
.seq crepBody722_27 crepBody722_29

def crepBody722_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_add"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 8]

def crepBody722_32 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_31

def crepBody722_33 : CrepProg (BitVec 64) :=
.seq crepBody722_30 crepBody722_32

def crepBody722_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sqr" [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 8]

def crepBody722_35 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_34

def crepBody722_36 : CrepProg (BitVec 64) :=
.seq crepBody722_33 crepBody722_35

def crepBody722_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sqr" [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 15]

def crepBody722_38 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_37

def crepBody722_39 : CrepProg (BitVec 64) :=
.seq crepBody722_36 crepBody722_38

def crepBody722_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sub"
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 7]

def crepBody722_41 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_40

def crepBody722_42 : CrepProg (BitVec 64) :=
.seq crepBody722_39 crepBody722_41

def crepBody722_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sub"
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 7]

def crepBody722_44 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_43

def crepBody722_45 : CrepProg (BitVec 64) :=
.seq crepBody722_42 crepBody722_44

def crepBody722_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_add"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 14]

def crepBody722_47 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_46

def crepBody722_48 : CrepProg (BitVec 64) :=
.seq crepBody722_45 crepBody722_47

def crepBody722_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sqr" [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 15]

def crepBody722_50 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_49

def crepBody722_51 : CrepProg (BitVec 64) :=
.seq crepBody722_48 crepBody722_50

def crepBody722_52 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sub"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 5]

def crepBody722_53 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_52

def crepBody722_54 : CrepProg (BitVec 64) :=
.seq crepBody722_51 crepBody722_53

def crepBody722_55 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sub"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 11]

def crepBody722_56 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_55

def crepBody722_57 : CrepProg (BitVec 64) :=
.seq crepBody722_54 crepBody722_56

def crepBody722_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sub"
  [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 12]

def crepBody722_59 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_58

def crepBody722_60 : CrepProg (BitVec 64) :=
.seq crepBody722_57 crepBody722_59

def crepBody722_61 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_mul"
  [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 8]

def crepBody722_62 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_61

def crepBody722_63 : CrepProg (BitVec 64) :=
.seq crepBody722_60 crepBody722_62

def crepBody722_64 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_add"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 6]

def crepBody722_65 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_64

def crepBody722_66 : CrepProg (BitVec 64) :=
.seq crepBody722_63 crepBody722_65

def crepBody722_67 : CrepProg (BitVec 64) :=
.seq crepBody722_66 crepBody722_65

def crepBody722_68 : CrepProg (BitVec 64) :=
.seq crepBody722_67 crepBody722_65

def crepBody722_69 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sub"
  [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 6]

def crepBody722_70 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_69

def crepBody722_71 : CrepProg (BitVec 64) :=
.seq crepBody722_68 crepBody722_70

def crepBody722_72 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_copy" [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 12]

def crepBody722_73 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_72

def crepBody722_74 : CrepProg (BitVec 64) :=
.seq crepBody722_71 crepBody722_73

def crepBody722_75 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_mul"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 11]

def crepBody722_76 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_75

def crepBody722_77 : CrepProg (BitVec 64) :=
.seq crepBody722_74 crepBody722_76

def crepBody722_78 : CrepProg (BitVec 64) :=
.seq crepBody722_77 crepBody722_23

def crepBody722_79 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_neg"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.var 7]

def crepBody722_80 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_79

def crepBody722_81 : CrepProg (BitVec 64) :=
.seq crepBody722_78 crepBody722_80

def crepBody722_82 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sqr" [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 10]

def crepBody722_83 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_82

def crepBody722_84 : CrepProg (BitVec 64) :=
.seq crepBody722_81 crepBody722_83

def crepBody722_85 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sub"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 4]

def crepBody722_86 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_85

def crepBody722_87 : CrepProg (BitVec 64) :=
.seq crepBody722_84 crepBody722_86

def crepBody722_88 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sub"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 9]

def crepBody722_89 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_88

def crepBody722_90 : CrepProg (BitVec 64) :=
.seq crepBody722_87 crepBody722_89

def crepBody722_91 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_add"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5]

def crepBody722_92 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_91

def crepBody722_93 : CrepProg (BitVec 64) :=
.seq crepBody722_90 crepBody722_92

def crepBody722_94 : CrepProg (BitVec 64) :=
.seq crepBody722_93 crepBody722_92

def crepBody722_95 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_sub"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 5]

def crepBody722_96 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_95

def crepBody722_97 : CrepProg (BitVec 64) :=
.seq crepBody722_94 crepBody722_96

def crepBody722_98 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_mul"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 11]

def crepBody722_99 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_98

def crepBody722_100 : CrepProg (BitVec 64) :=
.seq crepBody722_97 crepBody722_99

def crepBody722_101 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "fp2_add"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 4]

def crepBody722_102 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_101

def crepBody722_103 : CrepProg (BitVec 64) :=
.seq crepBody722_100 crepBody722_102

def crepBody722_104 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody722_105 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody722_104

def crepBody722_106 : CrepProg (BitVec 64) :=
.seq crepBody722_103 crepBody722_105

def crepBody722_107 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody722_108 : CrepProg (BitVec 64) :=
.seq crepBody722_106 crepBody722_107

def crepBody722_109 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64]) crepBody722_108

def crepBody722_110 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64]) crepBody722_109

def crepBody722_111 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 0) crepBody722_110

def crepBody722_112 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 768#64]) crepBody722_111

def crepBody722_113 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 672#64]) crepBody722_112

def crepBody722_114 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 576#64]) crepBody722_113

def crepBody722_115 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 480#64]) crepBody722_114

def crepBody722_116 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 384#64]) crepBody722_115

def crepBody722_117 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 288#64]) crepBody722_116

def crepBody722_118 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 192#64]) crepBody722_117

def crepBody722_119 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 96#64]) crepBody722_118

def crepBody722_120 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.var 3) crepBody722_119

def crepBody722_121 : CrepProg (BitVec 64) :=
.seq crepBody722_1 crepBody722_120

def crepBody722_122 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody722_121

def crepBody722_123 : CrepProg (BitVec 64) :=
.seq crepBody722_0 crepBody722_122

def crepBody722_124 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody722_123

def data722 : CrepProg (BitVec 64) := crepBody722_124
def output722 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 97#8, 105#8, 114#8, 95#8, 100#8, 111#8, 117#8, 98#8, 108#8, 105#8, 110#8, 103#8, 95#8, 115#8, 116#8, 101#8,
    112#8], [0, 1], crepProgToHOL data722)
end InitECandidate.Proofs.FrontendStages.Crep
