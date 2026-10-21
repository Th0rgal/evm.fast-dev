import InitECandidate.Proofs.FrontendStages.Crep.Translate584
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody600_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "heap_mark" []

def crepBody600_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 23#64, Flapjack.CrepExp.const 32#64]]

def crepBody600_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10
  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 11#64])

def crepBody600_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody600_4 : CrepProg (BitVec 64) :=
.seq crepBody600_2 crepBody600_3

def crepBody600_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 11#64) (Flapjack.CrepExp.var 5)) crepBody600_4 crepBody600_3

def crepBody600_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11 (Flapjack.CrepExp.const 11#64)

def crepBody600_7 : CrepProg (BitVec 64) :=
.seq crepBody600_6 crepBody600_3

def crepBody600_8 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 11#64) (Flapjack.CrepExp.var 11)) crepBody600_7 crepBody600_3

def crepBody600_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20, 21, 22, 23], none)) "fq_mul"
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15,
    Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19]

def crepBody600_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6, 7, 8, 9], none)) "fq_add"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9,
    Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22, Flapjack.CrepExp.var 23]

def crepBody600_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10 (Flapjack.CrepExp.var 24)

def crepBody600_12 : CrepProg (BitVec 64) :=
.seq crepBody600_11 crepBody600_3

def crepBody600_13 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 1#64]) crepBody600_12

def crepBody600_14 : CrepProg (BitVec 64) :=
.seq crepBody600_10 crepBody600_13

def crepBody600_15 : CrepProg (BitVec 64) :=
.seq crepBody600_9 crepBody600_14

def crepBody600_16 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody600_15

def crepBody600_17 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody600_16

def crepBody600_18 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody600_17

def crepBody600_19 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody600_18

def crepBody600_20 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 10],
              Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 24#64])) crepBody600_19

def crepBody600_21 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 10],
              Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 16#64])) crepBody600_20

def crepBody600_22 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 10],
              Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 8#64])) crepBody600_21

def crepBody600_23 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 2,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
        [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 10],
          Flapjack.CrepExp.const 32#64]])) crepBody600_22

def crepBody600_24 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 24#64])) crepBody600_23

def crepBody600_25 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 16#64])) crepBody600_24

def crepBody600_26 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 8#64])) crepBody600_25

def crepBody600_27 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 1,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 32#64]])) crepBody600_26

def crepBody600_28 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.var 10)) crepBody600_27

def crepBody600_29 : CrepProg (BitVec 64) :=
.seq crepBody600_8 crepBody600_28

def crepBody600_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.var 13)

def crepBody600_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 14)

def crepBody600_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 15)

def crepBody600_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 16)

def crepBody600_34 : CrepProg (BitVec 64) :=
.seq crepBody600_33 crepBody600_3

def crepBody600_35 : CrepProg (BitVec 64) :=
.seq crepBody600_32 crepBody600_34

def crepBody600_36 : CrepProg (BitVec 64) :=
.seq crepBody600_31 crepBody600_35

def crepBody600_37 : CrepProg (BitVec 64) :=
.seq crepBody600_30 crepBody600_36

def crepBody600_38 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.var 9) crepBody600_37

def crepBody600_39 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 8) crepBody600_38

def crepBody600_40 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 7) crepBody600_39

def crepBody600_41 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 6) crepBody600_40

def crepBody600_42 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 32#64]]) crepBody600_41

def crepBody600_43 : CrepProg (BitVec 64) :=
.seq crepBody600_29 crepBody600_42

def crepBody600_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 12)

def crepBody600_45 : CrepProg (BitVec 64) :=
.seq crepBody600_44 crepBody600_3

def crepBody600_46 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64]) crepBody600_45

def crepBody600_47 : CrepProg (BitVec 64) :=
.seq crepBody600_43 crepBody600_46

def crepBody600_48 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 5) crepBody600_47

def crepBody600_49 : CrepProg (BitVec 64) :=
.seq crepBody600_5 crepBody600_48

def crepBody600_50 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody600_49

def crepBody600_51 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody600_50

def crepBody600_52 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody600_51

def crepBody600_53 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody600_52

def crepBody600_54 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody600_53

def crepBody600_55 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 23#64)) crepBody600_54

def crepBody600_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "fq12_reduce" [Flapjack.CrepExp.var 4]

def crepBody600_57 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody600_56

def crepBody600_58 : CrepProg (BitVec 64) :=
.seq crepBody600_55 crepBody600_57

def crepBody600_59 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "memcpy"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 384#64]

def crepBody600_60 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody600_59

def crepBody600_61 : CrepProg (BitVec 64) :=
.seq crepBody600_58 crepBody600_60

def crepBody600_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody600_63 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody600_62

def crepBody600_64 : CrepProg (BitVec 64) :=
.seq crepBody600_61 crepBody600_63

def crepBody600_65 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody600_66 : CrepProg (BitVec 64) :=
.seq crepBody600_64 crepBody600_65

def crepBody600_67 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody600_66

def crepBody600_68 : CrepProg (BitVec 64) :=
.seq crepBody600_1 crepBody600_67

def crepBody600_69 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody600_68

def crepBody600_70 : CrepProg (BitVec 64) :=
.seq crepBody600_0 crepBody600_69

def crepBody600_71 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody600_70

def data600 : CrepProg (BitVec 64) := crepBody600_71
def output600 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 113#8, 49#8, 50#8, 95#8, 109#8, 117#8, 108#8], [0, 1, 2], crepProgToHOL data600)
end InitECandidate.Proofs.FrontendStages.Crep
