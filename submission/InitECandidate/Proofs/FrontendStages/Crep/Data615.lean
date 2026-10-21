import InitECandidate.Proofs.FrontendStages.Crep.Translate599
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody615_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "fe_is_zero"
  [Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 2,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 4]]]

def crepBody615_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "memcpy"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.var 4]]

def crepBody615_2 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody615_1

def crepBody615_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody615_4 : CrepProg (BitVec 64) :=
.seq crepBody615_2 crepBody615_3

def crepBody615_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody615_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 1#64)) crepBody615_4 crepBody615_5

def crepBody615_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "fe_is_zero"
  [Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 3,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 4]]]

def crepBody615_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "memcpy"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.var 4]]

def crepBody615_9 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody615_8

def crepBody615_10 : CrepProg (BitVec 64) :=
.seq crepBody615_9 crepBody615_3

def crepBody615_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 1#64)) crepBody615_10 crepBody615_5

def crepBody615_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "heap_mark" []

def crepBody615_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "alloc" [Flapjack.CrepExp.var 4]

def crepBody615_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "alloc" [Flapjack.CrepExp.var 4]

def crepBody615_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "alloc" [Flapjack.CrepExp.var 4]

def crepBody615_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "alloc" [Flapjack.CrepExp.var 4]

def crepBody615_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 10]

def crepBody615_18 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody615_17

def crepBody615_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 13]

def crepBody615_20 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody615_19

def crepBody615_21 : CrepProg (BitVec 64) :=
.seq crepBody615_18 crepBody615_20

def crepBody615_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 10]

def crepBody615_23 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody615_22

def crepBody615_24 : CrepProg (BitVec 64) :=
.seq crepBody615_21 crepBody615_23

def crepBody615_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 13]

def crepBody615_26 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody615_25

def crepBody615_27 : CrepProg (BitVec 64) :=
.seq crepBody615_24 crepBody615_26

def crepBody615_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "fe_eq"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17]

def crepBody615_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "fe_eq"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15]

def crepBody615_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "heap_release" [Flapjack.CrepExp.var 7]

def crepBody615_31 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody615_30

def crepBody615_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "ecp_double"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]

def crepBody615_33 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody615_32

def crepBody615_34 : CrepProg (BitVec 64) :=
.seq crepBody615_33 crepBody615_3

def crepBody615_35 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.const 1#64)) crepBody615_34 crepBody615_5

def crepBody615_36 : CrepProg (BitVec 64) :=
.seq crepBody615_31 crepBody615_35

def crepBody615_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "ecp_set_inf" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody615_38 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody615_37

def crepBody615_39 : CrepProg (BitVec 64) :=
.seq crepBody615_36 crepBody615_38

def crepBody615_40 : CrepProg (BitVec 64) :=
.seq crepBody615_39 crepBody615_3

def crepBody615_41 : CrepProg (BitVec 64) :=
.seq crepBody615_29 crepBody615_40

def crepBody615_42 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody615_41

def crepBody615_43 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 18) (Flapjack.CrepExp.const 1#64)) crepBody615_42 crepBody615_5

def crepBody615_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "alloc" [Flapjack.CrepExp.var 4]

def crepBody615_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "alloc" [Flapjack.CrepExp.var 4]

def crepBody615_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "alloc" [Flapjack.CrepExp.var 4]

def crepBody615_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "alloc" [Flapjack.CrepExp.var 4]

def crepBody615_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23], none)) "alloc" [Flapjack.CrepExp.var 4]

def crepBody615_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "alloc" [Flapjack.CrepExp.var 4]

def crepBody615_50 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([25], none)) "alloc" [Flapjack.CrepExp.var 4]

def crepBody615_51 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([26], none)) "alloc" [Flapjack.CrepExp.var 4]

def crepBody615_52 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fe_sub"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15]

def crepBody615_53 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_52

def crepBody615_54 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fe_sub"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17]

def crepBody615_55 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_54

def crepBody615_56 : CrepProg (BitVec 64) :=
.seq crepBody615_53 crepBody615_55

def crepBody615_57 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fe_sqr"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 20]

def crepBody615_58 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_57

def crepBody615_59 : CrepProg (BitVec 64) :=
.seq crepBody615_56 crepBody615_58

def crepBody615_60 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 22, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 17]

def crepBody615_61 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_60

def crepBody615_62 : CrepProg (BitVec 64) :=
.seq crepBody615_59 crepBody615_61

def crepBody615_63 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21]

def crepBody615_64 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_63

def crepBody615_65 : CrepProg (BitVec 64) :=
.seq crepBody615_62 crepBody615_64

def crepBody615_66 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 13]

def crepBody615_67 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_66

def crepBody615_68 : CrepProg (BitVec 64) :=
.seq crepBody615_65 crepBody615_67

def crepBody615_69 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fe_sqr"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 19]

def crepBody615_70 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_69

def crepBody615_71 : CrepProg (BitVec 64) :=
.seq crepBody615_68 crepBody615_70

def crepBody615_72 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 24]

def crepBody615_73 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_72

def crepBody615_74 : CrepProg (BitVec 64) :=
.seq crepBody615_71 crepBody615_73

def crepBody615_75 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fe_sub"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 23]

def crepBody615_76 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_75

def crepBody615_77 : CrepProg (BitVec 64) :=
.seq crepBody615_74 crepBody615_76

def crepBody615_78 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fe_mul_small"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 26, Flapjack.CrepExp.var 22, Flapjack.CrepExp.const 2#64]

def crepBody615_79 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_78

def crepBody615_80 : CrepProg (BitVec 64) :=
.seq crepBody615_77 crepBody615_79

def crepBody615_81 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fe_sub"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26]

def crepBody615_82 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_81

def crepBody615_83 : CrepProg (BitVec 64) :=
.seq crepBody615_80 crepBody615_82

def crepBody615_84 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 26, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 25]

def crepBody615_85 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_84

def crepBody615_86 : CrepProg (BitVec 64) :=
.seq crepBody615_83 crepBody615_85

def crepBody615_87 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fe_sub"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 22, Flapjack.CrepExp.var 25]

def crepBody615_88 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_87

def crepBody615_89 : CrepProg (BitVec 64) :=
.seq crepBody615_86 crepBody615_88

def crepBody615_90 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20]

def crepBody615_91 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_90

def crepBody615_92 : CrepProg (BitVec 64) :=
.seq crepBody615_89 crepBody615_91

def crepBody615_93 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 15]

def crepBody615_94 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_93

def crepBody615_95 : CrepProg (BitVec 64) :=
.seq crepBody615_92 crepBody615_94

def crepBody615_96 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fe_sub"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 14]

def crepBody615_97 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_96

def crepBody615_98 : CrepProg (BitVec 64) :=
.seq crepBody615_95 crepBody615_97

def crepBody615_99 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24]

def crepBody615_100 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_99

def crepBody615_101 : CrepProg (BitVec 64) :=
.seq crepBody615_98 crepBody615_100

def crepBody615_102 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "memcpy"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 26, Flapjack.CrepExp.var 4]

def crepBody615_103 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_102

def crepBody615_104 : CrepProg (BitVec 64) :=
.seq crepBody615_101 crepBody615_103

def crepBody615_105 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 4], Flapjack.CrepExp.var 20,
    Flapjack.CrepExp.var 4]

def crepBody615_106 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_105

def crepBody615_107 : CrepProg (BitVec 64) :=
.seq crepBody615_104 crepBody615_106

def crepBody615_108 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 1,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 4]],
    Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 4]

def crepBody615_109 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_108

def crepBody615_110 : CrepProg (BitVec 64) :=
.seq crepBody615_107 crepBody615_109

def crepBody615_111 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "heap_release" [Flapjack.CrepExp.var 7]

def crepBody615_112 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody615_111

def crepBody615_113 : CrepProg (BitVec 64) :=
.seq crepBody615_110 crepBody615_112

def crepBody615_114 : CrepProg (BitVec 64) :=
.seq crepBody615_113 crepBody615_3

def crepBody615_115 : CrepProg (BitVec 64) :=
.seq crepBody615_51 crepBody615_114

def crepBody615_116 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody615_115

def crepBody615_117 : CrepProg (BitVec 64) :=
.seq crepBody615_50 crepBody615_116

def crepBody615_118 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody615_117

def crepBody615_119 : CrepProg (BitVec 64) :=
.seq crepBody615_49 crepBody615_118

def crepBody615_120 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody615_119

def crepBody615_121 : CrepProg (BitVec 64) :=
.seq crepBody615_48 crepBody615_120

def crepBody615_122 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody615_121

def crepBody615_123 : CrepProg (BitVec 64) :=
.seq crepBody615_47 crepBody615_122

def crepBody615_124 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody615_123

def crepBody615_125 : CrepProg (BitVec 64) :=
.seq crepBody615_46 crepBody615_124

def crepBody615_126 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody615_125

def crepBody615_127 : CrepProg (BitVec 64) :=
.seq crepBody615_45 crepBody615_126

def crepBody615_128 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody615_127

def crepBody615_129 : CrepProg (BitVec 64) :=
.seq crepBody615_44 crepBody615_128

def crepBody615_130 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody615_129

def crepBody615_131 : CrepProg (BitVec 64) :=
.seq crepBody615_43 crepBody615_130

def crepBody615_132 : CrepProg (BitVec 64) :=
.seq crepBody615_28 crepBody615_131

def crepBody615_133 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody615_132

def crepBody615_134 : CrepProg (BitVec 64) :=
.seq crepBody615_27 crepBody615_133

def crepBody615_135 : CrepProg (BitVec 64) :=
.seq crepBody615_16 crepBody615_134

def crepBody615_136 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody615_135

def crepBody615_137 : CrepProg (BitVec 64) :=
.seq crepBody615_15 crepBody615_136

def crepBody615_138 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody615_137

def crepBody615_139 : CrepProg (BitVec 64) :=
.seq crepBody615_14 crepBody615_138

def crepBody615_140 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody615_139

def crepBody615_141 : CrepProg (BitVec 64) :=
.seq crepBody615_13 crepBody615_140

def crepBody615_142 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody615_141

def crepBody615_143 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 4]]) crepBody615_142

def crepBody615_144 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]) crepBody615_143

def crepBody615_145 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 3) crepBody615_144

def crepBody615_146 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 4]]) crepBody615_145

def crepBody615_147 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 4]) crepBody615_146

def crepBody615_148 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 2) crepBody615_147

def crepBody615_149 : CrepProg (BitVec 64) :=
.seq crepBody615_12 crepBody615_148

def crepBody615_150 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody615_149

def crepBody615_151 : CrepProg (BitVec 64) :=
.seq crepBody615_11 crepBody615_150

def crepBody615_152 : CrepProg (BitVec 64) :=
.seq crepBody615_7 crepBody615_151

def crepBody615_153 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody615_152

def crepBody615_154 : CrepProg (BitVec 64) :=
.seq crepBody615_6 crepBody615_153

def crepBody615_155 : CrepProg (BitVec 64) :=
.seq crepBody615_0 crepBody615_154

def crepBody615_156 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody615_155

def crepBody615_157 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64]) crepBody615_156

def data615 : CrepProg (BitVec 64) := crepBody615_157
def output615 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [101#8, 99#8, 112#8, 95#8, 97#8, 100#8, 100#8], [0, 1, 2, 3], crepProgToHOL data615)
end InitECandidate.Proofs.FrontendStages.Crep
