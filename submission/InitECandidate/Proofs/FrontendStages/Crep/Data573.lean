import InitECandidate.Proofs.FrontendStages.Crep.Translate557
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody573_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "heap_mark" []

def crepBody573_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64],
        Flapjack.CrepExp.const 8#64]]

def crepBody573_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "bn_from_be"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 9]

def crepBody573_3 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody573_2

def crepBody573_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "digits_len" [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 8]

def crepBody573_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "memzero" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5]

def crepBody573_6 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody573_5

def crepBody573_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "heap_release" [Flapjack.CrepExp.var 7]

def crepBody573_8 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody573_7

def crepBody573_9 : CrepProg (BitVec 64) :=
.seq crepBody573_6 crepBody573_8

def crepBody573_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody573_11 : CrepProg (BitVec 64) :=
.seq crepBody573_9 crepBody573_10

def crepBody573_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody573_13 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 0#64)) crepBody573_11 crepBody573_12

def crepBody573_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "max"
  [Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 10]]

def crepBody573_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64],
        Flapjack.CrepExp.const 8#64]]

def crepBody573_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64]]

def crepBody573_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64]]

def crepBody573_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([16], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 10],
        Flapjack.CrepExp.const 8#64]]

def crepBody573_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64],
        Flapjack.CrepExp.const 8#64]]

def crepBody573_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64],
        Flapjack.CrepExp.const 16#64]]

def crepBody573_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64]]

def crepBody573_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "bn_from_be"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 13]

def crepBody573_23 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody573_22

def crepBody573_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "bn_mod"
  [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19]

def crepBody573_25 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody573_24

def crepBody573_26 : CrepProg (BitVec 64) :=
.seq crepBody573_23 crepBody573_25

def crepBody573_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "be_top_bit" [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody573_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "memzero"
  [Flapjack.CrepExp.var 15,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64]]

def crepBody573_29 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody573_28

def crepBody573_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 21) (Flapjack.CrepExp.var 22)

def crepBody573_31 : CrepProg (BitVec 64) :=
.seq crepBody573_30 crepBody573_12

def crepBody573_32 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 1#64) crepBody573_31

def crepBody573_33 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.var 15) crepBody573_32

def crepBody573_34 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 1#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.load (Flapjack.CrepExp.var 9))
        (Flapjack.CrepExp.const 1#64))]) crepBody573_12 crepBody573_33

def crepBody573_35 : CrepProg (BitVec 64) :=
.seq crepBody573_29 crepBody573_34

def crepBody573_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "memcpy"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 14,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64]]

def crepBody573_37 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody573_36

def crepBody573_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 20 (Flapjack.CrepExp.var 21)

def crepBody573_39 : CrepProg (BitVec 64) :=
.seq crepBody573_38 crepBody573_12

def crepBody573_40 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 20, Flapjack.CrepExp.const 1#64]) crepBody573_39

def crepBody573_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "bn_mul"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.var 16]

def crepBody573_42 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody573_41

def crepBody573_43 : CrepProg (BitVec 64) :=
.seq crepBody573_40 crepBody573_42

def crepBody573_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "bn_mod"
  [Flapjack.CrepExp.var 16,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 10],
    Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 17,
    Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19]

def crepBody573_45 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody573_44

def crepBody573_46 : CrepProg (BitVec 64) :=
.seq crepBody573_43 crepBody573_45

def crepBody573_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "bn_mul"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.var 16]

def crepBody573_48 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody573_47

def crepBody573_49 : CrepProg (BitVec 64) :=
.seq crepBody573_48 crepBody573_45

def crepBody573_50 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.op Flapjack.BinOp.and
    [Flapjack.CrepExp.shift Flapjack.Shift.lsr
        (Flapjack.CrepExp.loadByte
          (Flapjack.CrepExp.op Flapjack.BinOp.sub
            [Flapjack.CrepExp.op Flapjack.BinOp.sub
                [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3],
                  Flapjack.CrepExp.const 1#64],
              Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 20) (Flapjack.CrepExp.const 3#64)]))
        (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 20, Flapjack.CrepExp.const 7#64]),
      Flapjack.CrepExp.const 1#64])
  (Flapjack.CrepExp.const 1#64)) crepBody573_49 crepBody573_12

def crepBody573_51 : CrepProg (BitVec 64) :=
.seq crepBody573_46 crepBody573_50

def crepBody573_52 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 20)) crepBody573_51

def crepBody573_53 : CrepProg (BitVec 64) :=
.seq crepBody573_37 crepBody573_52

def crepBody573_54 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 20) (Flapjack.CrepExp.const 0#64)) crepBody573_35 crepBody573_53

def crepBody573_55 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "bn_to_be"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5]

def crepBody573_56 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody573_55

def crepBody573_57 : CrepProg (BitVec 64) :=
.seq crepBody573_54 crepBody573_56

def crepBody573_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "heap_release" [Flapjack.CrepExp.var 7]

def crepBody573_59 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody573_58

def crepBody573_60 : CrepProg (BitVec 64) :=
.seq crepBody573_57 crepBody573_59

def crepBody573_61 : CrepProg (BitVec 64) :=
.seq crepBody573_60 crepBody573_10

def crepBody573_62 : CrepProg (BitVec 64) :=
.seq crepBody573_27 crepBody573_61

def crepBody573_63 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody573_62

def crepBody573_64 : CrepProg (BitVec 64) :=
.seq crepBody573_26 crepBody573_63

def crepBody573_65 : CrepProg (BitVec 64) :=
.seq crepBody573_21 crepBody573_64

def crepBody573_66 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody573_65

def crepBody573_67 : CrepProg (BitVec 64) :=
.seq crepBody573_20 crepBody573_66

def crepBody573_68 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody573_67

def crepBody573_69 : CrepProg (BitVec 64) :=
.seq crepBody573_19 crepBody573_68

def crepBody573_70 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody573_69

def crepBody573_71 : CrepProg (BitVec 64) :=
.seq crepBody573_18 crepBody573_70

def crepBody573_72 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody573_71

def crepBody573_73 : CrepProg (BitVec 64) :=
.seq crepBody573_17 crepBody573_72

def crepBody573_74 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody573_73

def crepBody573_75 : CrepProg (BitVec 64) :=
.seq crepBody573_16 crepBody573_74

def crepBody573_76 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody573_75

def crepBody573_77 : CrepProg (BitVec 64) :=
.seq crepBody573_15 crepBody573_76

def crepBody573_78 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody573_77

def crepBody573_79 : CrepProg (BitVec 64) :=
.seq crepBody573_14 crepBody573_78

def crepBody573_80 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody573_79

def crepBody573_81 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.shift Flapjack.Shift.lsr
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 3#64])
  (Flapjack.CrepExp.const 2#64)) crepBody573_80

def crepBody573_82 : CrepProg (BitVec 64) :=
.seq crepBody573_13 crepBody573_81

def crepBody573_83 : CrepProg (BitVec 64) :=
.seq crepBody573_4 crepBody573_82

def crepBody573_84 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody573_83

def crepBody573_85 : CrepProg (BitVec 64) :=
.seq crepBody573_3 crepBody573_84

def crepBody573_86 : CrepProg (BitVec 64) :=
.seq crepBody573_1 crepBody573_85

def crepBody573_87 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody573_86

def crepBody573_88 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.shift Flapjack.Shift.lsr
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 3#64])
  (Flapjack.CrepExp.const 2#64)) crepBody573_87

def crepBody573_89 : CrepProg (BitVec 64) :=
.seq crepBody573_0 crepBody573_88

def crepBody573_90 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody573_89

def data573 : CrepProg (BitVec 64) := crepBody573_90
def output573 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [109#8, 111#8, 100#8, 101#8, 120#8, 112#8], [0, 1, 2, 3, 4, 5, 6], crepProgToHOL data573)
end InitECandidate.Proofs.FrontendStages.Crep
