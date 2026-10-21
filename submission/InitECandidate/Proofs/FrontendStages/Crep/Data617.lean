import InitECandidate.Proofs.FrontendStages.Crep.Translate601
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody617_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "heap_mark" []

def crepBody617_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "alloc" [Flapjack.CrepExp.var 6]

def crepBody617_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "alloc" [Flapjack.CrepExp.var 6]

def crepBody617_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "alloc" [Flapjack.CrepExp.var 6]

def crepBody617_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "alloc" [Flapjack.CrepExp.var 6]

def crepBody617_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "fe_set_zero" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 17]

def crepBody617_6 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody617_5

def crepBody617_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "fe_set_zero" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 18]

def crepBody617_8 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody617_7

def crepBody617_9 : CrepProg (BitVec 64) :=
.seq crepBody617_6 crepBody617_8

def crepBody617_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 10]

def crepBody617_11 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody617_10

def crepBody617_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 13]

def crepBody617_13 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody617_12

def crepBody617_14 : CrepProg (BitVec 64) :=
.seq crepBody617_11 crepBody617_13

def crepBody617_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "fe_sub"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 19]

def crepBody617_16 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody617_15

def crepBody617_17 : CrepProg (BitVec 64) :=
.seq crepBody617_14 crepBody617_16

def crepBody617_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 10]

def crepBody617_19 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody617_18

def crepBody617_20 : CrepProg (BitVec 64) :=
.seq crepBody617_17 crepBody617_19

def crepBody617_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 13]

def crepBody617_22 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody617_21

def crepBody617_23 : CrepProg (BitVec 64) :=
.seq crepBody617_20 crepBody617_22

def crepBody617_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "fe_sub"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19]

def crepBody617_25 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody617_24

def crepBody617_26 : CrepProg (BitVec 64) :=
.seq crepBody617_23 crepBody617_25

def crepBody617_27 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 4)) crepBody617_9 crepBody617_26

def crepBody617_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "fe_is_zero" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 18]

def crepBody617_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "fe_is_zero" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 17]

def crepBody617_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "fe_sqr"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 8]

def crepBody617_31 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody617_30

def crepBody617_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "fe_mul_small"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 3#64]

def crepBody617_33 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody617_32

def crepBody617_34 : CrepProg (BitVec 64) :=
.seq crepBody617_31 crepBody617_33

def crepBody617_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10]

def crepBody617_36 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody617_35

def crepBody617_37 : CrepProg (BitVec 64) :=
.seq crepBody617_34 crepBody617_36

def crepBody617_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "fe_mul_small"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 2#64]

def crepBody617_39 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody617_38

def crepBody617_40 : CrepProg (BitVec 64) :=
.seq crepBody617_37 crepBody617_39

def crepBody617_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 10]

def crepBody617_42 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody617_41

def crepBody617_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 16]

def crepBody617_44 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody617_43

def crepBody617_45 : CrepProg (BitVec 64) :=
.seq crepBody617_42 crepBody617_44

def crepBody617_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "fe_sub"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 19]

def crepBody617_47 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody617_46

def crepBody617_48 : CrepProg (BitVec 64) :=
.seq crepBody617_45 crepBody617_47

def crepBody617_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 16]

def crepBody617_50 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody617_49

def crepBody617_51 : CrepProg (BitVec 64) :=
.seq crepBody617_48 crepBody617_50

def crepBody617_52 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "heap_release" [Flapjack.CrepExp.var 7]

def crepBody617_53 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody617_52

def crepBody617_54 : CrepProg (BitVec 64) :=
.seq crepBody617_51 crepBody617_53

def crepBody617_55 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody617_56 : CrepProg (BitVec 64) :=
.seq crepBody617_54 crepBody617_55

def crepBody617_57 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 22) (Flapjack.CrepExp.const 1#64)) crepBody617_40 crepBody617_56

def crepBody617_58 : CrepProg (BitVec 64) :=
.seq crepBody617_29 crepBody617_57

def crepBody617_59 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody617_58

def crepBody617_60 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody617_61 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 21) (Flapjack.CrepExp.const 1#64)) crepBody617_59 crepBody617_60

def crepBody617_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 10]

def crepBody617_63 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody617_62

def crepBody617_64 : CrepProg (BitVec 64) :=
.seq crepBody617_61 crepBody617_63

def crepBody617_65 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 16]

def crepBody617_66 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody617_65

def crepBody617_67 : CrepProg (BitVec 64) :=
.seq crepBody617_64 crepBody617_66

def crepBody617_68 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "fe_sub"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20]

def crepBody617_69 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody617_68

def crepBody617_70 : CrepProg (BitVec 64) :=
.seq crepBody617_67 crepBody617_69

def crepBody617_71 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 19]

def crepBody617_72 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody617_71

def crepBody617_73 : CrepProg (BitVec 64) :=
.seq crepBody617_70 crepBody617_72

def crepBody617_74 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 10]

def crepBody617_75 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody617_74

def crepBody617_76 : CrepProg (BitVec 64) :=
.seq crepBody617_73 crepBody617_75

def crepBody617_77 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 16]

def crepBody617_78 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody617_77

def crepBody617_79 : CrepProg (BitVec 64) :=
.seq crepBody617_76 crepBody617_78

def crepBody617_80 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "fe_sub"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 1]

def crepBody617_81 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody617_80

def crepBody617_82 : CrepProg (BitVec 64) :=
.seq crepBody617_79 crepBody617_81

def crepBody617_83 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 20]

def crepBody617_84 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody617_83

def crepBody617_85 : CrepProg (BitVec 64) :=
.seq crepBody617_82 crepBody617_84

def crepBody617_86 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "fe_sub"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20]

def crepBody617_87 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody617_86

def crepBody617_88 : CrepProg (BitVec 64) :=
.seq crepBody617_85 crepBody617_87

def crepBody617_89 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 16]

def crepBody617_90 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody617_89

def crepBody617_91 : CrepProg (BitVec 64) :=
.seq crepBody617_88 crepBody617_90

def crepBody617_92 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 10]

def crepBody617_93 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody617_92

def crepBody617_94 : CrepProg (BitVec 64) :=
.seq crepBody617_91 crepBody617_93

def crepBody617_95 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "heap_release" [Flapjack.CrepExp.var 7]

def crepBody617_96 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody617_95

def crepBody617_97 : CrepProg (BitVec 64) :=
.seq crepBody617_94 crepBody617_96

def crepBody617_98 : CrepProg (BitVec 64) :=
.seq crepBody617_97 crepBody617_55

def crepBody617_99 : CrepProg (BitVec 64) :=
.seq crepBody617_28 crepBody617_98

def crepBody617_100 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody617_99

def crepBody617_101 : CrepProg (BitVec 64) :=
.seq crepBody617_27 crepBody617_100

def crepBody617_102 : CrepProg (BitVec 64) :=
.seq crepBody617_4 crepBody617_101

def crepBody617_103 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody617_102

def crepBody617_104 : CrepProg (BitVec 64) :=
.seq crepBody617_3 crepBody617_103

def crepBody617_105 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody617_104

def crepBody617_106 : CrepProg (BitVec 64) :=
.seq crepBody617_2 crepBody617_105

def crepBody617_107 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody617_106

def crepBody617_108 : CrepProg (BitVec 64) :=
.seq crepBody617_1 crepBody617_107

def crepBody617_109 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody617_108

def crepBody617_110 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 6]]) crepBody617_109

def crepBody617_111 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]) crepBody617_110

def crepBody617_112 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 5) crepBody617_111

def crepBody617_113 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 6]]) crepBody617_112

def crepBody617_114 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 6]) crepBody617_113

def crepBody617_115 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 4) crepBody617_114

def crepBody617_116 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 6]]) crepBody617_115

def crepBody617_117 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 6]) crepBody617_116

def crepBody617_118 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 3) crepBody617_117

def crepBody617_119 : CrepProg (BitVec 64) :=
.seq crepBody617_0 crepBody617_118

def crepBody617_120 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody617_119

def crepBody617_121 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64]) crepBody617_120

def data617 : CrepProg (BitVec 64) := crepBody617_121
def output617 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [101#8, 99#8, 112#8, 95#8, 108#8, 105#8, 110#8, 101#8, 102#8, 117#8, 110#8, 99#8], [0, 1, 2, 3, 4, 5], crepProgToHOL data617)
end InitECandidate.Proofs.FrontendStages.Crep
