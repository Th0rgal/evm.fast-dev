import InitECandidate.Proofs.FrontendStages.Crep.Translate716
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody732_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "heap_mark" []

def crepBody732_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 96#64, Flapjack.CrepExp.const 6#64]]

def crepBody732_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "fp2_copy" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 2]

def crepBody732_3 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody732_2

def crepBody732_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fp2_mul"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 2]

def crepBody732_5 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody732_4

def crepBody732_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11 (Flapjack.CrepExp.var 12)

def crepBody732_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody732_8 : CrepProg (BitVec 64) :=
.seq crepBody732_6 crepBody732_7

def crepBody732_9 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 1#64]) crepBody732_8

def crepBody732_10 : CrepProg (BitVec 64) :=
.seq crepBody732_5 crepBody732_9

def crepBody732_11 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 6#64)) crepBody732_10

def crepBody732_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fp2_mul"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 5]

def crepBody732_13 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody732_12

def crepBody732_14 : CrepProg (BitVec 64) :=
.seq crepBody732_11 crepBody732_13

def crepBody732_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fp2_mul"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 2]

def crepBody732_16 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody732_15

def crepBody732_17 : CrepProg (BitVec 64) :=
.seq crepBody732_14 crepBody732_16

def crepBody732_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fp2_mul"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody732_19 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody732_18

def crepBody732_20 : CrepProg (BitVec 64) :=
.seq crepBody732_17 crepBody732_19

def crepBody732_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fp2_pow"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 1528#64],
    Flapjack.CrepExp.const 12#64]

def crepBody732_22 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody732_21

def crepBody732_23 : CrepProg (BitVec 64) :=
.seq crepBody732_20 crepBody732_22

def crepBody732_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "fp2_mul"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 6]

def crepBody732_25 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody732_24

def crepBody732_26 : CrepProg (BitVec 64) :=
.seq crepBody732_23 crepBody732_25

def crepBody732_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "fp2_copy" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 8]

def crepBody732_28 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody732_27

def crepBody732_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11 (Flapjack.CrepExp.const 0#64)

def crepBody732_30 : CrepProg (BitVec 64) :=
.seq crepBody732_29 crepBody732_7

def crepBody732_31 : CrepProg (BitVec 64) :=
.seq crepBody732_28 crepBody732_30

def crepBody732_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "fp2_mul"
  [Flapjack.CrepExp.var 9,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
        Flapjack.CrepExp.const 5216#64,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 96#64]],
    Flapjack.CrepExp.var 8]

def crepBody732_33 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody732_32

def crepBody732_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "fp2_sqr" [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 9]

def crepBody732_35 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody732_34

def crepBody732_36 : CrepProg (BitVec 64) :=
.seq crepBody732_33 crepBody732_35

def crepBody732_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "fp2_mul"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 2]

def crepBody732_38 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody732_37

def crepBody732_39 : CrepProg (BitVec 64) :=
.seq crepBody732_36 crepBody732_38

def crepBody732_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "fp2_sub"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 1]

def crepBody732_41 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody732_40

def crepBody732_42 : CrepProg (BitVec 64) :=
.seq crepBody732_39 crepBody732_41

def crepBody732_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "fp2_is_zero" [Flapjack.CrepExp.var 10]

def crepBody732_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 12 (Flapjack.CrepExp.const 1#64)

def crepBody732_45 : CrepProg (BitVec 64) :=
.seq crepBody732_44 crepBody732_7

def crepBody732_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "fp2_copy" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 9]

def crepBody732_47 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody732_46

def crepBody732_48 : CrepProg (BitVec 64) :=
.seq crepBody732_45 crepBody732_47

def crepBody732_49 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 1#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.const 0#64))]) crepBody732_48 crepBody732_7

def crepBody732_50 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11 (Flapjack.CrepExp.var 14)

def crepBody732_51 : CrepProg (BitVec 64) :=
.seq crepBody732_50 crepBody732_7

def crepBody732_52 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 1#64]) crepBody732_51

def crepBody732_53 : CrepProg (BitVec 64) :=
.seq crepBody732_49 crepBody732_52

def crepBody732_54 : CrepProg (BitVec 64) :=
.seq crepBody732_43 crepBody732_53

def crepBody732_55 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody732_54

def crepBody732_56 : CrepProg (BitVec 64) :=
.seq crepBody732_42 crepBody732_55

def crepBody732_57 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 4#64)) crepBody732_56

def crepBody732_58 : CrepProg (BitVec 64) :=
.seq crepBody732_31 crepBody732_57

def crepBody732_59 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody732_60 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody732_59

def crepBody732_61 : CrepProg (BitVec 64) :=
.seq crepBody732_58 crepBody732_60

def crepBody732_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 12]

def crepBody732_63 : CrepProg (BitVec 64) :=
.seq crepBody732_61 crepBody732_62

def crepBody732_64 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody732_63

def crepBody732_65 : CrepProg (BitVec 64) :=
.seq crepBody732_26 crepBody732_64

def crepBody732_66 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody732_65

def crepBody732_67 : CrepProg (BitVec 64) :=
.seq crepBody732_3 crepBody732_66

def crepBody732_68 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 480#64]) crepBody732_67

def crepBody732_69 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 384#64]) crepBody732_68

def crepBody732_70 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 288#64]) crepBody732_69

def crepBody732_71 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 192#64]) crepBody732_70

def crepBody732_72 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 96#64]) crepBody732_71

def crepBody732_73 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 4) crepBody732_72

def crepBody732_74 : CrepProg (BitVec 64) :=
.seq crepBody732_1 crepBody732_73

def crepBody732_75 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody732_74

def crepBody732_76 : CrepProg (BitVec 64) :=
.seq crepBody732_0 crepBody732_75

def crepBody732_77 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody732_76

def data732 : CrepProg (BitVec 64) := crepBody732_77
def output732 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [115#8, 119#8, 117#8, 95#8, 115#8, 113#8, 114#8, 116#8, 95#8, 100#8, 105#8, 118#8, 105#8, 115#8, 105#8, 111#8, 110#8,
    95#8, 102#8, 112#8, 50#8], [0, 1, 2], crepProgToHOL data732)
end InitECandidate.Proofs.FrontendStages.Crep
