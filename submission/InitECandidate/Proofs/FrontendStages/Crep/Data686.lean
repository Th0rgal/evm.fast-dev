import InitECandidate.Proofs.FrontendStages.Crep.Translate670
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody686_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody686_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 96#64, Flapjack.CrepExp.const 6#64]]

def crepBody686_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_sqr" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 1]

def crepBody686_3 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_2

def crepBody686_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_mul"
  [Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64]]

def crepBody686_5 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_4

def crepBody686_6 : CrepProg (BitVec 64) :=
.seq crepBody686_3 crepBody686_5

def crepBody686_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_mul_xi" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 7]

def crepBody686_8 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_7

def crepBody686_9 : CrepProg (BitVec 64) :=
.seq crepBody686_6 crepBody686_8

def crepBody686_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_sub"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 7]

def crepBody686_11 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_10

def crepBody686_12 : CrepProg (BitVec 64) :=
.seq crepBody686_9 crepBody686_11

def crepBody686_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_sqr"
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64]]

def crepBody686_14 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_13

def crepBody686_15 : CrepProg (BitVec 64) :=
.seq crepBody686_12 crepBody686_14

def crepBody686_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_mul_xi" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5]

def crepBody686_17 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_16

def crepBody686_18 : CrepProg (BitVec 64) :=
.seq crepBody686_15 crepBody686_17

def crepBody686_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_mul"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]]

def crepBody686_20 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_19

def crepBody686_21 : CrepProg (BitVec 64) :=
.seq crepBody686_18 crepBody686_20

def crepBody686_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_sub"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 7]

def crepBody686_23 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_22

def crepBody686_24 : CrepProg (BitVec 64) :=
.seq crepBody686_21 crepBody686_23

def crepBody686_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_sqr"
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]]

def crepBody686_26 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_25

def crepBody686_27 : CrepProg (BitVec 64) :=
.seq crepBody686_24 crepBody686_26

def crepBody686_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_mul"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64]]

def crepBody686_29 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_28

def crepBody686_30 : CrepProg (BitVec 64) :=
.seq crepBody686_27 crepBody686_29

def crepBody686_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_sub"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody686_32 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_31

def crepBody686_33 : CrepProg (BitVec 64) :=
.seq crepBody686_30 crepBody686_32

def crepBody686_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_mul"
  [Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.var 5]

def crepBody686_35 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_34

def crepBody686_36 : CrepProg (BitVec 64) :=
.seq crepBody686_33 crepBody686_35

def crepBody686_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_mul"
  [Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.var 6]

def crepBody686_38 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_37

def crepBody686_39 : CrepProg (BitVec 64) :=
.seq crepBody686_36 crepBody686_38

def crepBody686_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_add"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 7]

def crepBody686_41 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_40

def crepBody686_42 : CrepProg (BitVec 64) :=
.seq crepBody686_39 crepBody686_41

def crepBody686_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_mul_xi" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 8]

def crepBody686_44 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_43

def crepBody686_45 : CrepProg (BitVec 64) :=
.seq crepBody686_42 crepBody686_44

def crepBody686_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_mul"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 4]

def crepBody686_47 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_46

def crepBody686_48 : CrepProg (BitVec 64) :=
.seq crepBody686_45 crepBody686_47

def crepBody686_49 : CrepProg (BitVec 64) :=
.seq crepBody686_48 crepBody686_41

def crepBody686_50 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_inv" [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 8]

def crepBody686_51 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_50

def crepBody686_52 : CrepProg (BitVec 64) :=
.seq crepBody686_49 crepBody686_51

def crepBody686_53 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 9]

def crepBody686_54 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_53

def crepBody686_55 : CrepProg (BitVec 64) :=
.seq crepBody686_52 crepBody686_54

def crepBody686_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 9]

def crepBody686_57 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_56

def crepBody686_58 : CrepProg (BitVec 64) :=
.seq crepBody686_55 crepBody686_57

def crepBody686_59 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "fp2_mul"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 9]

def crepBody686_60 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_59

def crepBody686_61 : CrepProg (BitVec 64) :=
.seq crepBody686_58 crepBody686_60

def crepBody686_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody686_63 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody686_62

def crepBody686_64 : CrepProg (BitVec 64) :=
.seq crepBody686_61 crepBody686_63

def crepBody686_65 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody686_66 : CrepProg (BitVec 64) :=
.seq crepBody686_64 crepBody686_65

def crepBody686_67 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 480#64]) crepBody686_66

def crepBody686_68 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 384#64]) crepBody686_67

def crepBody686_69 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 288#64]) crepBody686_68

def crepBody686_70 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 192#64]) crepBody686_69

def crepBody686_71 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 96#64]) crepBody686_70

def crepBody686_72 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.var 3) crepBody686_71

def crepBody686_73 : CrepProg (BitVec 64) :=
.seq crepBody686_1 crepBody686_72

def crepBody686_74 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody686_73

def crepBody686_75 : CrepProg (BitVec 64) :=
.seq crepBody686_0 crepBody686_74

def crepBody686_76 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody686_75

def data686 : CrepProg (BitVec 64) := crepBody686_76
def output686 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 112#8, 54#8, 95#8, 105#8, 110#8, 118#8], [0, 1], crepProgToHOL data686)
end InitECandidate.Proofs.FrontendStages.Crep
