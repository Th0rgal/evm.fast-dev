import InitECandidate.Proofs.FrontendStages.Crep.Translate699
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody715_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "g2_is_inf" [Flapjack.CrepExp.var 1]

def crepBody715_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "g2_copy" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 2]

def crepBody715_2 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody715_1

def crepBody715_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody715_4 : CrepProg (BitVec 64) :=
.seq crepBody715_2 crepBody715_3

def crepBody715_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody715_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 1#64)) crepBody715_4 crepBody715_5

def crepBody715_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "g2_is_inf" [Flapjack.CrepExp.var 2]

def crepBody715_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "g2_copy" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody715_9 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody715_8

def crepBody715_10 : CrepProg (BitVec 64) :=
.seq crepBody715_9 crepBody715_3

def crepBody715_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 1#64)) crepBody715_10 crepBody715_5

def crepBody715_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "heap_mark" []

def crepBody715_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 96#64, Flapjack.CrepExp.const 12#64]]

def crepBody715_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "fp2_mul"
  [Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64]]

def crepBody715_15 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody715_14

def crepBody715_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "fp2_mul"
  [Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 192#64]]

def crepBody715_17 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody715_16

def crepBody715_18 : CrepProg (BitVec 64) :=
.seq crepBody715_15 crepBody715_17

def crepBody715_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "fp2_mul"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64]]

def crepBody715_20 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody715_19

def crepBody715_21 : CrepProg (BitVec 64) :=
.seq crepBody715_18 crepBody715_20

def crepBody715_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "fp2_mul"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 192#64]]

def crepBody715_23 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody715_22

def crepBody715_24 : CrepProg (BitVec 64) :=
.seq crepBody715_21 crepBody715_23

def crepBody715_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "fp2_eq" [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10]

def crepBody715_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_eq" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody715_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "heap_release" [Flapjack.CrepExp.var 5]

def crepBody715_28 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody715_27

def crepBody715_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "g2_double" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody715_30 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody715_29

def crepBody715_31 : CrepProg (BitVec 64) :=
.seq crepBody715_30 crepBody715_3

def crepBody715_32 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 20) (Flapjack.CrepExp.const 1#64)) crepBody715_31 crepBody715_5

def crepBody715_33 : CrepProg (BitVec 64) :=
.seq crepBody715_28 crepBody715_32

def crepBody715_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "g2_set_inf" [Flapjack.CrepExp.var 0]

def crepBody715_35 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody715_34

def crepBody715_36 : CrepProg (BitVec 64) :=
.seq crepBody715_33 crepBody715_35

def crepBody715_37 : CrepProg (BitVec 64) :=
.seq crepBody715_36 crepBody715_3

def crepBody715_38 : CrepProg (BitVec 64) :=
.seq crepBody715_26 crepBody715_37

def crepBody715_39 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_38

def crepBody715_40 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.const 1#64)) crepBody715_39 crepBody715_5

def crepBody715_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_sub"
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody715_42 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_41

def crepBody715_43 : CrepProg (BitVec 64) :=
.seq crepBody715_40 crepBody715_42

def crepBody715_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_sub"
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10]

def crepBody715_45 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_44

def crepBody715_46 : CrepProg (BitVec 64) :=
.seq crepBody715_43 crepBody715_45

def crepBody715_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_sqr" [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 12]

def crepBody715_48 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_47

def crepBody715_49 : CrepProg (BitVec 64) :=
.seq crepBody715_46 crepBody715_48

def crepBody715_50 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_mul"
  [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 10]

def crepBody715_51 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_50

def crepBody715_52 : CrepProg (BitVec 64) :=
.seq crepBody715_49 crepBody715_51

def crepBody715_53 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_mul"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody715_54 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_53

def crepBody715_55 : CrepProg (BitVec 64) :=
.seq crepBody715_52 crepBody715_54

def crepBody715_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_mul"
  [Flapjack.CrepExp.var 16,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 192#64]]

def crepBody715_57 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_56

def crepBody715_58 : CrepProg (BitVec 64) :=
.seq crepBody715_55 crepBody715_57

def crepBody715_59 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_sqr" [Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 11]

def crepBody715_60 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_59

def crepBody715_61 : CrepProg (BitVec 64) :=
.seq crepBody715_58 crepBody715_60

def crepBody715_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_mul"
  [Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 16]

def crepBody715_63 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_62

def crepBody715_64 : CrepProg (BitVec 64) :=
.seq crepBody715_61 crepBody715_63

def crepBody715_65 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_sub"
  [Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 15]

def crepBody715_66 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_65

def crepBody715_67 : CrepProg (BitVec 64) :=
.seq crepBody715_64 crepBody715_66

def crepBody715_68 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_add"
  [Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 14]

def crepBody715_69 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_68

def crepBody715_70 : CrepProg (BitVec 64) :=
.seq crepBody715_67 crepBody715_69

def crepBody715_71 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_sub"
  [Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18]

def crepBody715_72 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_71

def crepBody715_73 : CrepProg (BitVec 64) :=
.seq crepBody715_70 crepBody715_72

def crepBody715_74 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_mul"
  [Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 17]

def crepBody715_75 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_74

def crepBody715_76 : CrepProg (BitVec 64) :=
.seq crepBody715_73 crepBody715_75

def crepBody715_77 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_sub"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 17]

def crepBody715_78 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_77

def crepBody715_79 : CrepProg (BitVec 64) :=
.seq crepBody715_76 crepBody715_78

def crepBody715_80 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_mul"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 7]

def crepBody715_81 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_80

def crepBody715_82 : CrepProg (BitVec 64) :=
.seq crepBody715_79 crepBody715_81

def crepBody715_83 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_mul"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 8]

def crepBody715_84 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_83

def crepBody715_85 : CrepProg (BitVec 64) :=
.seq crepBody715_82 crepBody715_84

def crepBody715_86 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_sub"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody715_87 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_86

def crepBody715_88 : CrepProg (BitVec 64) :=
.seq crepBody715_85 crepBody715_87

def crepBody715_89 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_mul"
  [Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16]

def crepBody715_90 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_89

def crepBody715_91 : CrepProg (BitVec 64) :=
.seq crepBody715_88 crepBody715_90

def crepBody715_92 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_copy" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 18]

def crepBody715_93 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_92

def crepBody715_94 : CrepProg (BitVec 64) :=
.seq crepBody715_91 crepBody715_93

def crepBody715_95 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_copy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.var 7]

def crepBody715_96 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_95

def crepBody715_97 : CrepProg (BitVec 64) :=
.seq crepBody715_94 crepBody715_96

def crepBody715_98 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "fp2_copy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.var 16]

def crepBody715_99 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_98

def crepBody715_100 : CrepProg (BitVec 64) :=
.seq crepBody715_97 crepBody715_99

def crepBody715_101 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "heap_release" [Flapjack.CrepExp.var 5]

def crepBody715_102 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody715_101

def crepBody715_103 : CrepProg (BitVec 64) :=
.seq crepBody715_100 crepBody715_102

def crepBody715_104 : CrepProg (BitVec 64) :=
.seq crepBody715_103 crepBody715_3

def crepBody715_105 : CrepProg (BitVec 64) :=
.seq crepBody715_25 crepBody715_104

def crepBody715_106 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody715_105

def crepBody715_107 : CrepProg (BitVec 64) :=
.seq crepBody715_24 crepBody715_106

def crepBody715_108 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 1056#64]) crepBody715_107

def crepBody715_109 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 960#64]) crepBody715_108

def crepBody715_110 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 864#64]) crepBody715_109

def crepBody715_111 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 768#64]) crepBody715_110

def crepBody715_112 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 672#64]) crepBody715_111

def crepBody715_113 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 576#64]) crepBody715_112

def crepBody715_114 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 480#64]) crepBody715_113

def crepBody715_115 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 384#64]) crepBody715_114

def crepBody715_116 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 288#64]) crepBody715_115

def crepBody715_117 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 192#64]) crepBody715_116

def crepBody715_118 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 96#64]) crepBody715_117

def crepBody715_119 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 6) crepBody715_118

def crepBody715_120 : CrepProg (BitVec 64) :=
.seq crepBody715_13 crepBody715_119

def crepBody715_121 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody715_120

def crepBody715_122 : CrepProg (BitVec 64) :=
.seq crepBody715_12 crepBody715_121

def crepBody715_123 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody715_122

def crepBody715_124 : CrepProg (BitVec 64) :=
.seq crepBody715_11 crepBody715_123

def crepBody715_125 : CrepProg (BitVec 64) :=
.seq crepBody715_7 crepBody715_124

def crepBody715_126 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody715_125

def crepBody715_127 : CrepProg (BitVec 64) :=
.seq crepBody715_6 crepBody715_126

def crepBody715_128 : CrepProg (BitVec 64) :=
.seq crepBody715_0 crepBody715_127

def crepBody715_129 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody715_128

def data715 : CrepProg (BitVec 64) := crepBody715_129
def output715 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 97#8, 100#8, 100#8], [0, 1, 2], crepProgToHOL data715)
end InitECandidate.Proofs.FrontendStages.Crep
