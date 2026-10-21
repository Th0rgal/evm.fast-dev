import InitECandidate.Proofs.FrontendStages.Crep.Translate598
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody614_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_mark" []

def crepBody614_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "alloc" [Flapjack.CrepExp.var 3]

def crepBody614_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "alloc" [Flapjack.CrepExp.var 3]

def crepBody614_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "alloc" [Flapjack.CrepExp.var 3]

def crepBody614_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "alloc" [Flapjack.CrepExp.var 3]

def crepBody614_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "alloc" [Flapjack.CrepExp.var 3]

def crepBody614_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "alloc" [Flapjack.CrepExp.var 3]

def crepBody614_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "alloc" [Flapjack.CrepExp.var 3]

def crepBody614_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_sqr"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 5]

def crepBody614_9 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_8

def crepBody614_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_mul_small"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 3#64]

def crepBody614_11 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_10

def crepBody614_12 : CrepProg (BitVec 64) :=
.seq crepBody614_9 crepBody614_11

def crepBody614_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody614_14 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_13

def crepBody614_15 : CrepProg (BitVec 64) :=
.seq crepBody614_12 crepBody614_14

def crepBody614_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody614_17 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_16

def crepBody614_18 : CrepProg (BitVec 64) :=
.seq crepBody614_15 crepBody614_17

def crepBody614_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 9]

def crepBody614_20 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_19

def crepBody614_21 : CrepProg (BitVec 64) :=
.seq crepBody614_18 crepBody614_20

def crepBody614_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_sqr"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 8]

def crepBody614_23 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_22

def crepBody614_24 : CrepProg (BitVec 64) :=
.seq crepBody614_21 crepBody614_23

def crepBody614_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_mul_small"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64]

def crepBody614_26 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_25

def crepBody614_27 : CrepProg (BitVec 64) :=
.seq crepBody614_24 crepBody614_26

def crepBody614_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_sub"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14]

def crepBody614_29 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_28

def crepBody614_30 : CrepProg (BitVec 64) :=
.seq crepBody614_27 crepBody614_29

def crepBody614_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_sqr"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 9]

def crepBody614_32 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_31

def crepBody614_33 : CrepProg (BitVec 64) :=
.seq crepBody614_30 crepBody614_32

def crepBody614_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 9]

def crepBody614_35 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_34

def crepBody614_36 : CrepProg (BitVec 64) :=
.seq crepBody614_33 crepBody614_35

def crepBody614_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_mul_small"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 2#64]

def crepBody614_38 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_37

def crepBody614_39 : CrepProg (BitVec 64) :=
.seq crepBody614_36 crepBody614_38

def crepBody614_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_mul_small"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 4#64]

def crepBody614_41 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_40

def crepBody614_42 : CrepProg (BitVec 64) :=
.seq crepBody614_39 crepBody614_41

def crepBody614_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_sub"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 11]

def crepBody614_44 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_43

def crepBody614_45 : CrepProg (BitVec 64) :=
.seq crepBody614_42 crepBody614_44

def crepBody614_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 14]

def crepBody614_47 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_46

def crepBody614_48 : CrepProg (BitVec 64) :=
.seq crepBody614_45 crepBody614_47

def crepBody614_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_sqr"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 6]

def crepBody614_50 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_49

def crepBody614_51 : CrepProg (BitVec 64) :=
.seq crepBody614_48 crepBody614_50

def crepBody614_52 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 12]

def crepBody614_53 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_52

def crepBody614_54 : CrepProg (BitVec 64) :=
.seq crepBody614_51 crepBody614_53

def crepBody614_55 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_mul_small"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]

def crepBody614_56 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_55

def crepBody614_57 : CrepProg (BitVec 64) :=
.seq crepBody614_54 crepBody614_56

def crepBody614_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_sub"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 8]

def crepBody614_59 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_58

def crepBody614_60 : CrepProg (BitVec 64) :=
.seq crepBody614_57 crepBody614_59

def crepBody614_61 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 12]

def crepBody614_62 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_61

def crepBody614_63 : CrepProg (BitVec 64) :=
.seq crepBody614_60 crepBody614_62

def crepBody614_64 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fe_mul_small"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64]

def crepBody614_65 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_64

def crepBody614_66 : CrepProg (BitVec 64) :=
.seq crepBody614_63 crepBody614_65

def crepBody614_67 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "memcpy"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 3]

def crepBody614_68 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_67

def crepBody614_69 : CrepProg (BitVec 64) :=
.seq crepBody614_66 crepBody614_68

def crepBody614_70 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3], Flapjack.CrepExp.var 14,
    Flapjack.CrepExp.var 3]

def crepBody614_71 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_70

def crepBody614_72 : CrepProg (BitVec 64) :=
.seq crepBody614_69 crepBody614_71

def crepBody614_73 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 1,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 3]],
    Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 3]

def crepBody614_74 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_73

def crepBody614_75 : CrepProg (BitVec 64) :=
.seq crepBody614_72 crepBody614_74

def crepBody614_76 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "heap_release" [Flapjack.CrepExp.var 4]

def crepBody614_77 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody614_76

def crepBody614_78 : CrepProg (BitVec 64) :=
.seq crepBody614_75 crepBody614_77

def crepBody614_79 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody614_80 : CrepProg (BitVec 64) :=
.seq crepBody614_78 crepBody614_79

def crepBody614_81 : CrepProg (BitVec 64) :=
.seq crepBody614_7 crepBody614_80

def crepBody614_82 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody614_81

def crepBody614_83 : CrepProg (BitVec 64) :=
.seq crepBody614_6 crepBody614_82

def crepBody614_84 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody614_83

def crepBody614_85 : CrepProg (BitVec 64) :=
.seq crepBody614_5 crepBody614_84

def crepBody614_86 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody614_85

def crepBody614_87 : CrepProg (BitVec 64) :=
.seq crepBody614_4 crepBody614_86

def crepBody614_88 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody614_87

def crepBody614_89 : CrepProg (BitVec 64) :=
.seq crepBody614_3 crepBody614_88

def crepBody614_90 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody614_89

def crepBody614_91 : CrepProg (BitVec 64) :=
.seq crepBody614_2 crepBody614_90

def crepBody614_92 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody614_91

def crepBody614_93 : CrepProg (BitVec 64) :=
.seq crepBody614_1 crepBody614_92

def crepBody614_94 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody614_93

def crepBody614_95 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 3]]) crepBody614_94

def crepBody614_96 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]) crepBody614_95

def crepBody614_97 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 2) crepBody614_96

def crepBody614_98 : CrepProg (BitVec 64) :=
.seq crepBody614_0 crepBody614_97

def crepBody614_99 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody614_98

def crepBody614_100 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64]) crepBody614_99

def data614 : CrepProg (BitVec 64) := crepBody614_100
def output614 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [101#8, 99#8, 112#8, 95#8, 100#8, 111#8, 117#8, 98#8, 108#8, 101#8], [0, 1, 2], crepProgToHOL data614)
end InitECandidate.Proofs.FrontendStages.Crep
