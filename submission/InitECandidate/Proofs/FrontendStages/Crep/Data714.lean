import InitECandidate.Proofs.FrontendStages.Crep.Translate698
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody714_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody714_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 96#64, Flapjack.CrepExp.const 8#64]]

def crepBody714_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_sqr" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 12]

def crepBody714_3 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_2

def crepBody714_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_add"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 4]

def crepBody714_5 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_4

def crepBody714_6 : CrepProg (BitVec 64) :=
.seq crepBody714_3 crepBody714_5

def crepBody714_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_add"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 4]

def crepBody714_8 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_7

def crepBody714_9 : CrepProg (BitVec 64) :=
.seq crepBody714_6 crepBody714_8

def crepBody714_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_mul"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14]

def crepBody714_11 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_10

def crepBody714_12 : CrepProg (BitVec 64) :=
.seq crepBody714_9 crepBody714_11

def crepBody714_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_mul"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody714_14 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_13

def crepBody714_15 : CrepProg (BitVec 64) :=
.seq crepBody714_12 crepBody714_14

def crepBody714_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_mul"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5]

def crepBody714_17 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_16

def crepBody714_18 : CrepProg (BitVec 64) :=
.seq crepBody714_15 crepBody714_17

def crepBody714_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_add"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 6]

def crepBody714_20 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_19

def crepBody714_21 : CrepProg (BitVec 64) :=
.seq crepBody714_18 crepBody714_20

def crepBody714_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_add"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 9]

def crepBody714_23 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_22

def crepBody714_24 : CrepProg (BitVec 64) :=
.seq crepBody714_21 crepBody714_23

def crepBody714_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_add"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 9]

def crepBody714_26 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_25

def crepBody714_27 : CrepProg (BitVec 64) :=
.seq crepBody714_24 crepBody714_26

def crepBody714_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_sqr" [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 4]

def crepBody714_29 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_28

def crepBody714_30 : CrepProg (BitVec 64) :=
.seq crepBody714_27 crepBody714_29

def crepBody714_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_sub"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 7]

def crepBody714_32 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_31

def crepBody714_33 : CrepProg (BitVec 64) :=
.seq crepBody714_30 crepBody714_32

def crepBody714_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_sqr" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 5]

def crepBody714_35 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_34

def crepBody714_36 : CrepProg (BitVec 64) :=
.seq crepBody714_33 crepBody714_35

def crepBody714_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_mul"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 5]

def crepBody714_38 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_37

def crepBody714_39 : CrepProg (BitVec 64) :=
.seq crepBody714_36 crepBody714_38

def crepBody714_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_add"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 10]

def crepBody714_41 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_40

def crepBody714_42 : CrepProg (BitVec 64) :=
.seq crepBody714_39 crepBody714_41

def crepBody714_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_sub"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 7]

def crepBody714_44 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_43

def crepBody714_45 : CrepProg (BitVec 64) :=
.seq crepBody714_42 crepBody714_44

def crepBody714_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_mul"
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 9]

def crepBody714_47 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_46

def crepBody714_48 : CrepProg (BitVec 64) :=
.seq crepBody714_45 crepBody714_47

def crepBody714_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_sqr" [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 13]

def crepBody714_50 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_49

def crepBody714_51 : CrepProg (BitVec 64) :=
.seq crepBody714_48 crepBody714_50

def crepBody714_52 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_mul"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 8]

def crepBody714_53 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_52

def crepBody714_54 : CrepProg (BitVec 64) :=
.seq crepBody714_51 crepBody714_53

def crepBody714_55 : CrepProg (BitVec 64) :=
.seq crepBody714_54 crepBody714_23

def crepBody714_56 : CrepProg (BitVec 64) :=
.seq crepBody714_55 crepBody714_23

def crepBody714_57 : CrepProg (BitVec 64) :=
.seq crepBody714_56 crepBody714_23

def crepBody714_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_sub"
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 9]

def crepBody714_59 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_58

def crepBody714_60 : CrepProg (BitVec 64) :=
.seq crepBody714_57 crepBody714_59

def crepBody714_61 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_mul"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 8]

def crepBody714_62 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_61

def crepBody714_63 : CrepProg (BitVec 64) :=
.seq crepBody714_60 crepBody714_62

def crepBody714_64 : CrepProg (BitVec 64) :=
.seq crepBody714_63 crepBody714_23

def crepBody714_65 : CrepProg (BitVec 64) :=
.seq crepBody714_64 crepBody714_23

def crepBody714_66 : CrepProg (BitVec 64) :=
.seq crepBody714_65 crepBody714_23

def crepBody714_67 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_copy" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 10]

def crepBody714_68 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_67

def crepBody714_69 : CrepProg (BitVec 64) :=
.seq crepBody714_66 crepBody714_68

def crepBody714_70 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_copy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.var 11]

def crepBody714_71 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_70

def crepBody714_72 : CrepProg (BitVec 64) :=
.seq crepBody714_69 crepBody714_71

def crepBody714_73 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "fp2_copy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.var 9]

def crepBody714_74 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_73

def crepBody714_75 : CrepProg (BitVec 64) :=
.seq crepBody714_72 crepBody714_74

def crepBody714_76 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody714_77 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody714_76

def crepBody714_78 : CrepProg (BitVec 64) :=
.seq crepBody714_75 crepBody714_77

def crepBody714_79 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody714_80 : CrepProg (BitVec 64) :=
.seq crepBody714_78 crepBody714_79

def crepBody714_81 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64]) crepBody714_80

def crepBody714_82 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]) crepBody714_81

def crepBody714_83 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 1) crepBody714_82

def crepBody714_84 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 672#64]) crepBody714_83

def crepBody714_85 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 576#64]) crepBody714_84

def crepBody714_86 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 480#64]) crepBody714_85

def crepBody714_87 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 384#64]) crepBody714_86

def crepBody714_88 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 288#64]) crepBody714_87

def crepBody714_89 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 192#64]) crepBody714_88

def crepBody714_90 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 96#64]) crepBody714_89

def crepBody714_91 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.var 3) crepBody714_90

def crepBody714_92 : CrepProg (BitVec 64) :=
.seq crepBody714_1 crepBody714_91

def crepBody714_93 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody714_92

def crepBody714_94 : CrepProg (BitVec 64) :=
.seq crepBody714_0 crepBody714_93

def crepBody714_95 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody714_94

def data714 : CrepProg (BitVec 64) := crepBody714_95
def output714 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 100#8, 111#8, 117#8, 98#8, 108#8, 101#8], [0, 1], crepProgToHOL data714)
end InitECandidate.Proofs.FrontendStages.Crep
