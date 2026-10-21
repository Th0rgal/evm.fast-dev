import InitECandidate.Proofs.FrontendStages.Crep.Translate681
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody697_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "heap_mark" []

def crepBody697_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 576#64, Flapjack.CrepExp.const 5#64]]

def crepBody697_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_inv" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 1]

def crepBody697_3 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_2

def crepBody697_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_conj" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 1]

def crepBody697_5 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_4

def crepBody697_6 : CrepProg (BitVec 64) :=
.seq crepBody697_3 crepBody697_5

def crepBody697_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_mul"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 8]

def crepBody697_8 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_7

def crepBody697_9 : CrepProg (BitVec 64) :=
.seq crepBody697_6 crepBody697_8

def crepBody697_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_frob" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 4]

def crepBody697_11 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_10

def crepBody697_12 : CrepProg (BitVec 64) :=
.seq crepBody697_9 crepBody697_11

def crepBody697_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_frob" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 8]

def crepBody697_14 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_13

def crepBody697_15 : CrepProg (BitVec 64) :=
.seq crepBody697_12 crepBody697_14

def crepBody697_16 : CrepProg (BitVec 64) :=
.seq crepBody697_15 crepBody697_8

def crepBody697_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_exp_x" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 4]

def crepBody697_18 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_17

def crepBody697_19 : CrepProg (BitVec 64) :=
.seq crepBody697_16 crepBody697_18

def crepBody697_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_conj" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 4]

def crepBody697_21 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_20

def crepBody697_22 : CrepProg (BitVec 64) :=
.seq crepBody697_19 crepBody697_21

def crepBody697_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_mul"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 8]

def crepBody697_24 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_23

def crepBody697_25 : CrepProg (BitVec 64) :=
.seq crepBody697_22 crepBody697_24

def crepBody697_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_exp_x" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 5]

def crepBody697_27 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_26

def crepBody697_28 : CrepProg (BitVec 64) :=
.seq crepBody697_25 crepBody697_27

def crepBody697_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_conj" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 5]

def crepBody697_30 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_29

def crepBody697_31 : CrepProg (BitVec 64) :=
.seq crepBody697_28 crepBody697_30

def crepBody697_32 : CrepProg (BitVec 64) :=
.seq crepBody697_31 crepBody697_24

def crepBody697_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_exp_x" [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 5]

def crepBody697_34 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_33

def crepBody697_35 : CrepProg (BitVec 64) :=
.seq crepBody697_32 crepBody697_34

def crepBody697_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_frob" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 5]

def crepBody697_37 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_36

def crepBody697_38 : CrepProg (BitVec 64) :=
.seq crepBody697_35 crepBody697_37

def crepBody697_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_mul"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 8]

def crepBody697_40 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_39

def crepBody697_41 : CrepProg (BitVec 64) :=
.seq crepBody697_38 crepBody697_40

def crepBody697_42 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_exp_x" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 6]

def crepBody697_43 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_42

def crepBody697_44 : CrepProg (BitVec 64) :=
.seq crepBody697_41 crepBody697_43

def crepBody697_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_exp_x" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 7]

def crepBody697_46 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_45

def crepBody697_47 : CrepProg (BitVec 64) :=
.seq crepBody697_44 crepBody697_46

def crepBody697_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_frob" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 6]

def crepBody697_49 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_48

def crepBody697_50 : CrepProg (BitVec 64) :=
.seq crepBody697_47 crepBody697_49

def crepBody697_51 : CrepProg (BitVec 64) :=
.seq crepBody697_50 crepBody697_14

def crepBody697_52 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_mul"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody697_53 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_52

def crepBody697_54 : CrepProg (BitVec 64) :=
.seq crepBody697_51 crepBody697_53

def crepBody697_55 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_conj" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 6]

def crepBody697_56 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_55

def crepBody697_57 : CrepProg (BitVec 64) :=
.seq crepBody697_54 crepBody697_56

def crepBody697_58 : CrepProg (BitVec 64) :=
.seq crepBody697_57 crepBody697_53

def crepBody697_59 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_mul"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 4]

def crepBody697_60 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_59

def crepBody697_61 : CrepProg (BitVec 64) :=
.seq crepBody697_58 crepBody697_60

def crepBody697_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_mul"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 4]

def crepBody697_63 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_62

def crepBody697_64 : CrepProg (BitVec 64) :=
.seq crepBody697_61 crepBody697_63

def crepBody697_65 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "fp12_mul"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody697_66 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_65

def crepBody697_67 : CrepProg (BitVec 64) :=
.seq crepBody697_64 crepBody697_66

def crepBody697_68 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "heap_release" [Flapjack.CrepExp.var 2]

def crepBody697_69 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody697_68

def crepBody697_70 : CrepProg (BitVec 64) :=
.seq crepBody697_67 crepBody697_69

def crepBody697_71 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody697_72 : CrepProg (BitVec 64) :=
.seq crepBody697_70 crepBody697_71

def crepBody697_73 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 2304#64]) crepBody697_72

def crepBody697_74 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1728#64]) crepBody697_73

def crepBody697_75 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1152#64]) crepBody697_74

def crepBody697_76 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 576#64]) crepBody697_75

def crepBody697_77 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.var 3) crepBody697_76

def crepBody697_78 : CrepProg (BitVec 64) :=
.seq crepBody697_1 crepBody697_77

def crepBody697_79 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody697_78

def crepBody697_80 : CrepProg (BitVec 64) :=
.seq crepBody697_0 crepBody697_79

def crepBody697_81 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody697_80

def data697 : CrepProg (BitVec 64) := crepBody697_81
def output697 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [102#8, 112#8, 49#8, 50#8, 95#8, 102#8, 105#8, 110#8, 97#8, 108#8, 95#8, 101#8, 120#8, 112#8], [0, 1], crepProgToHOL data697)
end InitECandidate.Proofs.FrontendStages.Crep
