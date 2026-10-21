import InitECandidate.Proofs.FrontendStages.Crep.Translate607
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody623_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody623_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 416#64]

def crepBody623_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 416#64]

def crepBody623_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc" [Flapjack.CrepExp.const 416#64]

def crepBody623_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc" [Flapjack.CrepExp.const 416#64]

def crepBody623_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "alloc" [Flapjack.CrepExp.const 416#64]

def crepBody623_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "alloc" [Flapjack.CrepExp.const 416#64]

def crepBody623_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "memzero" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 416#64]

def crepBody623_8 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody623_7

def crepBody623_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 10)

def crepBody623_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 11)

def crepBody623_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 12)

def crepBody623_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 13)

def crepBody623_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody623_14 : CrepProg (BitVec 64) :=
.seq crepBody623_12 crepBody623_13

def crepBody623_15 : CrepProg (BitVec 64) :=
.seq crepBody623_11 crepBody623_14

def crepBody623_16 : CrepProg (BitVec 64) :=
.seq crepBody623_10 crepBody623_15

def crepBody623_17 : CrepProg (BitVec 64) :=
.seq crepBody623_9 crepBody623_16

def crepBody623_18 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 2762764518496934255#64) crepBody623_17

def crepBody623_19 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 4628036095437277618#64) crepBody623_18

def crepBody623_20 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 13698472384431417117#64) crepBody623_19

def crepBody623_21 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 5544790254283102953#64) crepBody623_20

def crepBody623_22 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 3) crepBody623_21

def crepBody623_23 : CrepProg (BitVec 64) :=
.seq crepBody623_8 crepBody623_22

def crepBody623_24 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 2710440286313254821#64) crepBody623_17

def crepBody623_25 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 2169086236411634456#64) crepBody623_24

def crepBody623_26 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 15026249742141879542#64) crepBody623_25

def crepBody623_27 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 10102850021236865696#64) crepBody623_26

def crepBody623_28 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 192#64]) crepBody623_27

def crepBody623_29 : CrepProg (BitVec 64) :=
.seq crepBody623_23 crepBody623_28

def crepBody623_30 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 1011752739694698287#64) crepBody623_17

def crepBody623_31 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 7381016538464732716#64) crepBody623_30

def crepBody623_32 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 754611498739239741#64) crepBody623_31

def crepBody623_33 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 15230403791020821917#64) crepBody623_32

def crepBody623_34 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 384#64]) crepBody623_33

def crepBody623_35 : CrepProg (BitVec 64) :=
.seq crepBody623_29 crepBody623_34

def crepBody623_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "memzero" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 416#64]

def crepBody623_37 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody623_36

def crepBody623_38 : CrepProg (BitVec 64) :=
.seq crepBody623_35 crepBody623_37

def crepBody623_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "memcpy"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 384#64]

def crepBody623_40 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody623_39

def crepBody623_41 : CrepProg (BitVec 64) :=
.seq crepBody623_38 crepBody623_40

def crepBody623_42 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "memzero" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 416#64]

def crepBody623_43 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody623_42

def crepBody623_44 : CrepProg (BitVec 64) :=
.seq crepBody623_41 crepBody623_43

def crepBody623_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "memzero" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 416#64]

def crepBody623_46 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody623_45

def crepBody623_47 : CrepProg (BitVec 64) :=
.seq crepBody623_44 crepBody623_46

def crepBody623_48 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 6) crepBody623_33

def crepBody623_49 : CrepProg (BitVec 64) :=
.seq crepBody623_47 crepBody623_48

def crepBody623_50 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fq_poly_deg" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 13#64]

def crepBody623_51 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.break 0

def crepBody623_52 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notLess (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 9)) crepBody623_51 crepBody623_13

def crepBody623_53 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fq_poly_deg" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 13#64]

def crepBody623_54 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "memzero" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 416#64]

def crepBody623_55 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody623_54

def crepBody623_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16, 17, 18], none)) "fq_inv"
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14]

def crepBody623_57 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23, 24, 25, 26], none)) "fq_mul"
  [Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22,
    Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18]

def crepBody623_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 27) (Flapjack.CrepExp.var 28)

def crepBody623_59 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 27, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 29)

def crepBody623_60 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 27, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 30)

def crepBody623_61 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 27, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 31)

def crepBody623_62 : CrepProg (BitVec 64) :=
.seq crepBody623_61 crepBody623_13

def crepBody623_63 : CrepProg (BitVec 64) :=
.seq crepBody623_60 crepBody623_62

def crepBody623_64 : CrepProg (BitVec 64) :=
.seq crepBody623_59 crepBody623_63

def crepBody623_65 : CrepProg (BitVec 64) :=
.seq crepBody623_58 crepBody623_64

def crepBody623_66 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.var 26) crepBody623_65

def crepBody623_67 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.var 25) crepBody623_66

def crepBody623_68 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.var 24) crepBody623_67

def crepBody623_69 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.var 23) crepBody623_68

def crepBody623_70 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 9],
        Flapjack.CrepExp.const 32#64]]) crepBody623_69

def crepBody623_71 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27], none)) "fq_poly_submul"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24,
    Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26,
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 9], Flapjack.CrepExp.var 9]

def crepBody623_72 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody623_71

def crepBody623_73 : CrepProg (BitVec 64) :=
.seq crepBody623_70 crepBody623_72

def crepBody623_74 : CrepProg (BitVec 64) :=
.seq crepBody623_73 crepBody623_53

def crepBody623_75 : CrepProg (BitVec 64) :=
.seq crepBody623_57 crepBody623_74

def crepBody623_76 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody623_75

def crepBody623_77 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody623_76

def crepBody623_78 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody623_77

def crepBody623_79 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody623_78

def crepBody623_80 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 3,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 24#64])) crepBody623_79

def crepBody623_81 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 3,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 16#64])) crepBody623_80

def crepBody623_82 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 3,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 8#64])) crepBody623_81

def crepBody623_83 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 3,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 32#64]])) crepBody623_82

def crepBody623_84 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.notLess (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.var 9)) crepBody623_83

def crepBody623_85 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "memcpy"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 416#64]

def crepBody623_86 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody623_85

def crepBody623_87 : CrepProg (BitVec 64) :=
.seq crepBody623_84 crepBody623_86

def crepBody623_88 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "u256_is_zero"
  [Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22, Flapjack.CrepExp.var 23]

def crepBody623_89 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([25], none)) "fq_poly_submul"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21,
    Flapjack.CrepExp.var 22, Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 19,
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.var 19]]

def crepBody623_90 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody623_89

def crepBody623_91 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 24) (Flapjack.CrepExp.const 0#64)) crepBody623_90 crepBody623_13

def crepBody623_92 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 19 (Flapjack.CrepExp.var 25)

def crepBody623_93 : CrepProg (BitVec 64) :=
.seq crepBody623_92 crepBody623_13

def crepBody623_94 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 1#64]) crepBody623_93

def crepBody623_95 : CrepProg (BitVec 64) :=
.seq crepBody623_91 crepBody623_94

def crepBody623_96 : CrepProg (BitVec 64) :=
.seq crepBody623_88 crepBody623_95

def crepBody623_97 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody623_96

def crepBody623_98 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 7,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 24#64])) crepBody623_97

def crepBody623_99 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 7,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 16#64])) crepBody623_98

def crepBody623_100 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 7,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 8#64])) crepBody623_99

def crepBody623_101 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 7,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 32#64]])) crepBody623_100

def crepBody623_102 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.const 13#64)) crepBody623_101

def crepBody623_103 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 4)

def crepBody623_104 : CrepProg (BitVec 64) :=
.seq crepBody623_103 crepBody623_13

def crepBody623_105 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 20)

def crepBody623_106 : CrepProg (BitVec 64) :=
.seq crepBody623_105 crepBody623_13

def crepBody623_107 : CrepProg (BitVec 64) :=
.seq crepBody623_104 crepBody623_106

def crepBody623_108 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 20 (Flapjack.CrepExp.var 5)

def crepBody623_109 : CrepProg (BitVec 64) :=
.seq crepBody623_108 crepBody623_13

def crepBody623_110 : CrepProg (BitVec 64) :=
.seq crepBody623_107 crepBody623_109

def crepBody623_111 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 6)

def crepBody623_112 : CrepProg (BitVec 64) :=
.seq crepBody623_111 crepBody623_13

def crepBody623_113 : CrepProg (BitVec 64) :=
.seq crepBody623_110 crepBody623_112

def crepBody623_114 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.var 8)

def crepBody623_115 : CrepProg (BitVec 64) :=
.seq crepBody623_114 crepBody623_13

def crepBody623_116 : CrepProg (BitVec 64) :=
.seq crepBody623_113 crepBody623_115

def crepBody623_117 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 20)

def crepBody623_118 : CrepProg (BitVec 64) :=
.seq crepBody623_117 crepBody623_13

def crepBody623_119 : CrepProg (BitVec 64) :=
.seq crepBody623_116 crepBody623_118

def crepBody623_120 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 3) crepBody623_119

def crepBody623_121 : CrepProg (BitVec 64) :=
.seq crepBody623_102 crepBody623_120

def crepBody623_122 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody623_121

def crepBody623_123 : CrepProg (BitVec 64) :=
.seq crepBody623_87 crepBody623_122

def crepBody623_124 : CrepProg (BitVec 64) :=
.seq crepBody623_56 crepBody623_123

def crepBody623_125 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody623_124

def crepBody623_126 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody623_125

def crepBody623_127 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody623_126

def crepBody623_128 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody623_127

def crepBody623_129 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 4,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 24#64])) crepBody623_128

def crepBody623_130 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 4,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 16#64])) crepBody623_129

def crepBody623_131 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 4,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 8#64])) crepBody623_130

def crepBody623_132 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 4,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 32#64]])) crepBody623_131

def crepBody623_133 : CrepProg (BitVec 64) :=
.seq crepBody623_55 crepBody623_132

def crepBody623_134 : CrepProg (BitVec 64) :=
.seq crepBody623_53 crepBody623_133

def crepBody623_135 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody623_134

def crepBody623_136 : CrepProg (BitVec 64) :=
.seq crepBody623_52 crepBody623_135

def crepBody623_137 : CrepProg (BitVec 64) :=
.seq crepBody623_50 crepBody623_136

def crepBody623_138 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody623_137

def crepBody623_139 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.const 1#64) crepBody623_138

def crepBody623_140 : CrepProg (BitVec 64) :=
.seq crepBody623_49 crepBody623_139

def crepBody623_141 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "memzero" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 384#64]

def crepBody623_142 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody623_141

def crepBody623_143 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody623_144 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody623_143

def crepBody623_145 : CrepProg (BitVec 64) :=
.seq crepBody623_142 crepBody623_144

def crepBody623_146 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody623_147 : CrepProg (BitVec 64) :=
.seq crepBody623_145 crepBody623_146

def crepBody623_148 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 0#64)) crepBody623_147 crepBody623_13

def crepBody623_149 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14, 15, 16, 17], none)) "fq_inv"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody623_150 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([23, 24, 25, 26], none)) "fq_mul"
  [Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22,
    Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17]

def crepBody623_151 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 32#64]]) crepBody623_69

def crepBody623_152 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 18 (Flapjack.CrepExp.var 27)

def crepBody623_153 : CrepProg (BitVec 64) :=
.seq crepBody623_152 crepBody623_13

def crepBody623_154 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 1#64]) crepBody623_153

def crepBody623_155 : CrepProg (BitVec 64) :=
.seq crepBody623_151 crepBody623_154

def crepBody623_156 : CrepProg (BitVec 64) :=
.seq crepBody623_150 crepBody623_155

def crepBody623_157 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody623_156

def crepBody623_158 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody623_157

def crepBody623_159 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody623_158

def crepBody623_160 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody623_159

def crepBody623_161 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 6,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 24#64])) crepBody623_160

def crepBody623_162 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 6,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 16#64])) crepBody623_161

def crepBody623_163 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 6,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 8#64])) crepBody623_162

def crepBody623_164 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 6,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 32#64]])) crepBody623_163

def crepBody623_165 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 18) (Flapjack.CrepExp.const 12#64)) crepBody623_164

def crepBody623_166 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody623_167 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody623_166

def crepBody623_168 : CrepProg (BitVec 64) :=
.seq crepBody623_165 crepBody623_167

def crepBody623_169 : CrepProg (BitVec 64) :=
.seq crepBody623_168 crepBody623_146

def crepBody623_170 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody623_169

def crepBody623_171 : CrepProg (BitVec 64) :=
.seq crepBody623_149 crepBody623_170

def crepBody623_172 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody623_171

def crepBody623_173 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody623_172

def crepBody623_174 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody623_173

def crepBody623_175 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody623_174

def crepBody623_176 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 24#64])) crepBody623_175

def crepBody623_177 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64])) crepBody623_176

def crepBody623_178 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64])) crepBody623_177

def crepBody623_179 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 4)) crepBody623_178

def crepBody623_180 : CrepProg (BitVec 64) :=
.seq crepBody623_148 crepBody623_179

def crepBody623_181 : CrepProg (BitVec 64) :=
.seq crepBody623_50 crepBody623_180

def crepBody623_182 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody623_181

def crepBody623_183 : CrepProg (BitVec 64) :=
.seq crepBody623_140 crepBody623_182

def crepBody623_184 : CrepProg (BitVec 64) :=
.seq crepBody623_6 crepBody623_183

def crepBody623_185 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody623_184

def crepBody623_186 : CrepProg (BitVec 64) :=
.seq crepBody623_5 crepBody623_185

def crepBody623_187 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody623_186

def crepBody623_188 : CrepProg (BitVec 64) :=
.seq crepBody623_4 crepBody623_187

def crepBody623_189 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody623_188

def crepBody623_190 : CrepProg (BitVec 64) :=
.seq crepBody623_3 crepBody623_189

def crepBody623_191 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody623_190

def crepBody623_192 : CrepProg (BitVec 64) :=
.seq crepBody623_2 crepBody623_191

def crepBody623_193 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody623_192

def crepBody623_194 : CrepProg (BitVec 64) :=
.seq crepBody623_1 crepBody623_193

def crepBody623_195 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody623_194

def crepBody623_196 : CrepProg (BitVec 64) :=
.seq crepBody623_0 crepBody623_195

def crepBody623_197 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody623_196

def data623 : CrepProg (BitVec 64) := crepBody623_197
def output623 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 113#8, 49#8, 50#8, 95#8, 105#8, 110#8, 118#8], [0, 1], crepProgToHOL data623)
end InitECandidate.Proofs.FrontendStages.Crep
