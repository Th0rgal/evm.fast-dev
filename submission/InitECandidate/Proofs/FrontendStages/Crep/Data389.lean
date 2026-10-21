import InitECandidate.Proofs.FrontendStages.Crep.Translate373
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody389_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody389_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody389_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 2#64)) crepBody389_0 crepBody389_1

def crepBody389_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "heap_mark" []

def crepBody389_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]]

def crepBody389_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11 (Flapjack.CrepExp.var 1)

def crepBody389_6 : CrepProg (BitVec 64) :=
.seq crepBody389_5 crepBody389_1

def crepBody389_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 11)) crepBody389_6 crepBody389_1

def crepBody389_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 12 (Flapjack.CrepExp.var 1)

def crepBody389_9 : CrepProg (BitVec 64) :=
.seq crepBody389_8 crepBody389_1

def crepBody389_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 12)) crepBody389_9 crepBody389_1

def crepBody389_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "bal_sort_gt"
  [Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 3]

def crepBody389_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 8,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 2]],
    Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 2]

def crepBody389_13 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody389_12

def crepBody389_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 13 (Flapjack.CrepExp.var 19)

def crepBody389_15 : CrepProg (BitVec 64) :=
.seq crepBody389_14 crepBody389_1

def crepBody389_16 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 1#64]) crepBody389_15

def crepBody389_17 : CrepProg (BitVec 64) :=
.seq crepBody389_13 crepBody389_16

def crepBody389_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 8,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 2]],
    Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 2]

def crepBody389_19 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody389_18

def crepBody389_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 14 (Flapjack.CrepExp.var 19)

def crepBody389_21 : CrepProg (BitVec 64) :=
.seq crepBody389_20 crepBody389_1

def crepBody389_22 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 1#64]) crepBody389_21

def crepBody389_23 : CrepProg (BitVec 64) :=
.seq crepBody389_19 crepBody389_22

def crepBody389_24 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 18) (Flapjack.CrepExp.const 0#64)) crepBody389_17 crepBody389_23

def crepBody389_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 15 (Flapjack.CrepExp.var 19)

def crepBody389_26 : CrepProg (BitVec 64) :=
.seq crepBody389_25 crepBody389_1

def crepBody389_27 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 1#64]) crepBody389_26

def crepBody389_28 : CrepProg (BitVec 64) :=
.seq crepBody389_24 crepBody389_27

def crepBody389_29 : CrepProg (BitVec 64) :=
.seq crepBody389_11 crepBody389_28

def crepBody389_30 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody389_29

def crepBody389_31 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 2]]) crepBody389_30

def crepBody389_32 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 2]]) crepBody389_31

def crepBody389_33 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.var 11)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.var 12))]) crepBody389_32

def crepBody389_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 8,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 2]],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 7,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 2]],
    Flapjack.CrepExp.var 2]

def crepBody389_35 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody389_34

def crepBody389_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 13 (Flapjack.CrepExp.var 16)

def crepBody389_37 : CrepProg (BitVec 64) :=
.seq crepBody389_36 crepBody389_1

def crepBody389_38 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 1#64]) crepBody389_37

def crepBody389_39 : CrepProg (BitVec 64) :=
.seq crepBody389_35 crepBody389_38

def crepBody389_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 15 (Flapjack.CrepExp.var 16)

def crepBody389_41 : CrepProg (BitVec 64) :=
.seq crepBody389_40 crepBody389_1

def crepBody389_42 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 1#64]) crepBody389_41

def crepBody389_43 : CrepProg (BitVec 64) :=
.seq crepBody389_39 crepBody389_42

def crepBody389_44 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.var 11)) crepBody389_43

def crepBody389_45 : CrepProg (BitVec 64) :=
.seq crepBody389_33 crepBody389_44

def crepBody389_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 8,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 2]],
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 7,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 2]],
    Flapjack.CrepExp.var 2]

def crepBody389_47 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody389_46

def crepBody389_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 14 (Flapjack.CrepExp.var 16)

def crepBody389_49 : CrepProg (BitVec 64) :=
.seq crepBody389_48 crepBody389_1

def crepBody389_50 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 1#64]) crepBody389_49

def crepBody389_51 : CrepProg (BitVec 64) :=
.seq crepBody389_47 crepBody389_50

def crepBody389_52 : CrepProg (BitVec 64) :=
.seq crepBody389_51 crepBody389_42

def crepBody389_53 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.var 12)) crepBody389_52

def crepBody389_54 : CrepProg (BitVec 64) :=
.seq crepBody389_45 crepBody389_53

def crepBody389_55 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10 (Flapjack.CrepExp.var 12)

def crepBody389_56 : CrepProg (BitVec 64) :=
.seq crepBody389_55 crepBody389_1

def crepBody389_57 : CrepProg (BitVec 64) :=
.seq crepBody389_54 crepBody389_56

def crepBody389_58 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 10) crepBody389_57

def crepBody389_59 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 11) crepBody389_58

def crepBody389_60 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 10) crepBody389_59

def crepBody389_61 : CrepProg (BitVec 64) :=
.seq crepBody389_10 crepBody389_60

def crepBody389_62 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 9]) crepBody389_61

def crepBody389_63 : CrepProg (BitVec 64) :=
.seq crepBody389_7 crepBody389_62

def crepBody389_64 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 9]) crepBody389_63

def crepBody389_65 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.var 1)) crepBody389_64

def crepBody389_66 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 8)

def crepBody389_67 : CrepProg (BitVec 64) :=
.seq crepBody389_66 crepBody389_1

def crepBody389_68 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 11)

def crepBody389_69 : CrepProg (BitVec 64) :=
.seq crepBody389_68 crepBody389_1

def crepBody389_70 : CrepProg (BitVec 64) :=
.seq crepBody389_67 crepBody389_69

def crepBody389_71 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.var 12)

def crepBody389_72 : CrepProg (BitVec 64) :=
.seq crepBody389_71 crepBody389_1

def crepBody389_73 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 2#64]) crepBody389_72

def crepBody389_74 : CrepProg (BitVec 64) :=
.seq crepBody389_70 crepBody389_73

def crepBody389_75 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 7) crepBody389_74

def crepBody389_76 : CrepProg (BitVec 64) :=
.seq crepBody389_65 crepBody389_75

def crepBody389_77 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody389_76

def crepBody389_78 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 1)) crepBody389_77

def crepBody389_79 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "memcpy"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]]

def crepBody389_80 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody389_79

def crepBody389_81 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.var 0)) crepBody389_80 crepBody389_1

def crepBody389_82 : CrepProg (BitVec 64) :=
.seq crepBody389_78 crepBody389_81

def crepBody389_83 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "heap_release" [Flapjack.CrepExp.var 5]

def crepBody389_84 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody389_83

def crepBody389_85 : CrepProg (BitVec 64) :=
.seq crepBody389_82 crepBody389_84

def crepBody389_86 : CrepProg (BitVec 64) :=
.seq crepBody389_85 crepBody389_0

def crepBody389_87 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 1#64) crepBody389_86

def crepBody389_88 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 6) crepBody389_87

def crepBody389_89 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 0) crepBody389_88

def crepBody389_90 : CrepProg (BitVec 64) :=
.seq crepBody389_4 crepBody389_89

def crepBody389_91 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody389_90

def crepBody389_92 : CrepProg (BitVec 64) :=
.seq crepBody389_3 crepBody389_91

def crepBody389_93 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody389_92

def crepBody389_94 : CrepProg (BitVec 64) :=
.seq crepBody389_2 crepBody389_93

def data389 : CrepProg (BitVec 64) := crepBody389_94
def output389 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [115#8, 111#8, 114#8, 116#8, 95#8, 101#8, 108#8, 101#8, 109#8, 115#8], [0, 1, 2, 3, 4], crepProgToHOL data389)
end InitECandidate.Proofs.FrontendStages.Crep
