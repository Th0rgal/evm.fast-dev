import InitECandidate.Proofs.FrontendStages.Crep.Translate724
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody740_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_mark" []

def crepBody740_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody740_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc" [Flapjack.CrepExp.const 144#64]

def crepBody740_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "alloc" [Flapjack.CrepExp.const 288#64]

def crepBody740_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "alloc" [Flapjack.CrepExp.const 288#64]

def crepBody740_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "alloc" [Flapjack.CrepExp.const 144#64]

def crepBody740_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "alloc" [Flapjack.CrepExp.const 288#64]

def crepBody740_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "alloc" [Flapjack.CrepExp.const 576#64]

def crepBody740_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fp2_copy"
  [Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 480#64]]

def crepBody740_9 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_8

def crepBody740_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fp2_copy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 576#64]]

def crepBody740_11 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_10

def crepBody740_12 : CrepProg (BitVec 64) :=
.seq crepBody740_9 crepBody740_11

def crepBody740_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fp2_set_one"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 192#64]]

def crepBody740_14 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_13

def crepBody740_15 : CrepProg (BitVec 64) :=
.seq crepBody740_12 crepBody740_14

def crepBody740_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "kzg_neg_scalar" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 5]

def crepBody740_17 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_16

def crepBody740_18 : CrepProg (BitVec 64) :=
.seq crepBody740_15 crepBody740_17

def crepBody740_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "g2_mul"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 4#64]

def crepBody740_20 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_19

def crepBody740_21 : CrepProg (BitVec 64) :=
.seq crepBody740_18 crepBody740_20

def crepBody740_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fp2_copy"
  [Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 672#64]]

def crepBody740_23 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_22

def crepBody740_24 : CrepProg (BitVec 64) :=
.seq crepBody740_21 crepBody740_23

def crepBody740_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fp2_copy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 768#64]]

def crepBody740_26 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_25

def crepBody740_27 : CrepProg (BitVec 64) :=
.seq crepBody740_24 crepBody740_26

def crepBody740_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fp2_set_one"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 192#64]]

def crepBody740_29 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_28

def crepBody740_30 : CrepProg (BitVec 64) :=
.seq crepBody740_27 crepBody740_29

def crepBody740_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "g2_add"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 10]

def crepBody740_32 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_31

def crepBody740_33 : CrepProg (BitVec 64) :=
.seq crepBody740_30 crepBody740_32

def crepBody740_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "memcpy"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 384#64],
    Flapjack.CrepExp.const 48#64]

def crepBody740_35 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_34

def crepBody740_36 : CrepProg (BitVec 64) :=
.seq crepBody740_33 crepBody740_35

def crepBody740_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 48#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 432#64],
    Flapjack.CrepExp.const 48#64]

def crepBody740_38 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_37

def crepBody740_39 : CrepProg (BitVec 64) :=
.seq crepBody740_36 crepBody740_38

def crepBody740_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.var 13)

def crepBody740_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 14)

def crepBody740_42 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 15)

def crepBody740_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 16)

def crepBody740_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 32#64])
  (Flapjack.CrepExp.var 17)

def crepBody740_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 40#64])
  (Flapjack.CrepExp.var 18)

def crepBody740_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody740_47 : CrepProg (BitVec 64) :=
.seq crepBody740_45 crepBody740_46

def crepBody740_48 : CrepProg (BitVec 64) :=
.seq crepBody740_44 crepBody740_47

def crepBody740_49 : CrepProg (BitVec 64) :=
.seq crepBody740_43 crepBody740_48

def crepBody740_50 : CrepProg (BitVec 64) :=
.seq crepBody740_42 crepBody740_49

def crepBody740_51 : CrepProg (BitVec 64) :=
.seq crepBody740_41 crepBody740_50

def crepBody740_52 : CrepProg (BitVec 64) :=
.seq crepBody740_40 crepBody740_51

def crepBody740_53 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 1582556514881692819#64) crepBody740_52

def crepBody740_54 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 6631298214892334189#64) crepBody740_53

def crepBody740_55 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 8632934651105793861#64) crepBody740_54

def crepBody740_56 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 6865905132761471162#64) crepBody740_55

def crepBody740_57 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 17002214543764226050#64) crepBody740_56

def crepBody740_58 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 8505329371266088957#64) crepBody740_57

def crepBody740_59 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 96#64]) crepBody740_58

def crepBody740_60 : CrepProg (BitVec 64) :=
.seq crepBody740_39 crepBody740_59

def crepBody740_61 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "kzg_neg_scalar" [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 5]

def crepBody740_62 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_61

def crepBody740_63 : CrepProg (BitVec 64) :=
.seq crepBody740_60 crepBody740_62

def crepBody740_64 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "g1_mul"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 4#64]

def crepBody740_65 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_64

def crepBody740_66 : CrepProg (BitVec 64) :=
.seq crepBody740_63 crepBody740_65

def crepBody740_67 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "g1_add"
  [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 9]

def crepBody740_68 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_67

def crepBody740_69 : CrepProg (BitVec 64) :=
.seq crepBody740_66 crepBody740_68

def crepBody740_70 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "g2_neg" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 7]

def crepBody740_71 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_70

def crepBody740_72 : CrepProg (BitVec 64) :=
.seq crepBody740_69 crepBody740_71

def crepBody740_73 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fp12_set_one" [Flapjack.CrepExp.var 11]

def crepBody740_74 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_73

def crepBody740_75 : CrepProg (BitVec 64) :=
.seq crepBody740_72 crepBody740_74

def crepBody740_76 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "pair_accumulate"
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 7]

def crepBody740_77 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_76

def crepBody740_78 : CrepProg (BitVec 64) :=
.seq crepBody740_75 crepBody740_77

def crepBody740_79 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "pair_accumulate"
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 10]

def crepBody740_80 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_79

def crepBody740_81 : CrepProg (BitVec 64) :=
.seq crepBody740_78 crepBody740_80

def crepBody740_82 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fp12_final_exp" [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 11]

def crepBody740_83 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_82

def crepBody740_84 : CrepProg (BitVec 64) :=
.seq crepBody740_81 crepBody740_83

def crepBody740_85 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fp12_is_one" [Flapjack.CrepExp.var 11]

def crepBody740_86 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "heap_release" [Flapjack.CrepExp.var 4]

def crepBody740_87 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody740_86

def crepBody740_88 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 12]

def crepBody740_89 : CrepProg (BitVec 64) :=
.seq crepBody740_87 crepBody740_88

def crepBody740_90 : CrepProg (BitVec 64) :=
.seq crepBody740_85 crepBody740_89

def crepBody740_91 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody740_90

def crepBody740_92 : CrepProg (BitVec 64) :=
.seq crepBody740_84 crepBody740_91

def crepBody740_93 : CrepProg (BitVec 64) :=
.seq crepBody740_7 crepBody740_92

def crepBody740_94 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody740_93

def crepBody740_95 : CrepProg (BitVec 64) :=
.seq crepBody740_6 crepBody740_94

def crepBody740_96 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody740_95

def crepBody740_97 : CrepProg (BitVec 64) :=
.seq crepBody740_5 crepBody740_96

def crepBody740_98 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody740_97

def crepBody740_99 : CrepProg (BitVec 64) :=
.seq crepBody740_4 crepBody740_98

def crepBody740_100 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody740_99

def crepBody740_101 : CrepProg (BitVec 64) :=
.seq crepBody740_3 crepBody740_100

def crepBody740_102 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody740_101

def crepBody740_103 : CrepProg (BitVec 64) :=
.seq crepBody740_2 crepBody740_102

def crepBody740_104 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody740_103

def crepBody740_105 : CrepProg (BitVec 64) :=
.seq crepBody740_1 crepBody740_104

def crepBody740_106 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody740_105

def crepBody740_107 : CrepProg (BitVec 64) :=
.seq crepBody740_0 crepBody740_106

def crepBody740_108 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody740_107

def data740 : CrepProg (BitVec 64) := crepBody740_108
def output740 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [107#8, 122#8, 103#8, 95#8, 118#8, 101#8, 114#8, 105#8, 102#8, 121#8], [0, 1, 2, 3], crepProgToHOL data740)
end InitECandidate.Proofs.FrontendStages.Crep
