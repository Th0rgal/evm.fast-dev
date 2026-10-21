import InitECandidate.Proofs.FrontendStages.Crep.Translate636
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody652_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "bls_fp_is_zero"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody652_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64,
    Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody652_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody652_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 1#64)) crepBody652_1 crepBody652_2

def crepBody652_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22,
    Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24]

def crepBody652_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 1#64)) crepBody652_4 crepBody652_2

def crepBody652_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11,
      Flapjack.CrepExp.var 12])
  (Flapjack.CrepExp.const 0#64)) crepBody652_5 crepBody652_2

def crepBody652_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26, Flapjack.CrepExp.var 27, Flapjack.CrepExp.var 28,
    Flapjack.CrepExp.var 29, Flapjack.CrepExp.var 30]

def crepBody652_8 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 1#64)) crepBody652_7 crepBody652_2

def crepBody652_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17,
      Flapjack.CrepExp.var 18])
  (Flapjack.CrepExp.const 0#64)) crepBody652_8 crepBody652_2

def crepBody652_10 : CrepProg (BitVec 64) :=
.seq crepBody652_6 crepBody652_9

def crepBody652_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7, 8, 9, 10, 11, 12], none)) "bls_fp_shr1"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12]

def crepBody652_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19, 20, 21, 22, 23, 24], none)) "bls_fp_half_can"
  [Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22,
    Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24]

def crepBody652_13 : CrepProg (BitVec 64) :=
.seq crepBody652_11 crepBody652_12

def crepBody652_14 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 1#64])
  (Flapjack.CrepExp.const 0#64)) crepBody652_13

def crepBody652_15 : CrepProg (BitVec 64) :=
.seq crepBody652_10 crepBody652_14

def crepBody652_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13, 14, 15, 16, 17, 18], none)) "bls_fp_shr1"
  [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16,
    Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18]

def crepBody652_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([25, 26, 27, 28, 29, 30], none)) "bls_fp_half_can"
  [Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26, Flapjack.CrepExp.var 27, Flapjack.CrepExp.var 28,
    Flapjack.CrepExp.var 29, Flapjack.CrepExp.var 30]

def crepBody652_18 : CrepProg (BitVec 64) :=
.seq crepBody652_16 crepBody652_17

def crepBody652_19 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 1#64])
  (Flapjack.CrepExp.const 0#64)) crepBody652_18

def crepBody652_20 : CrepProg (BitVec 64) :=
.seq crepBody652_15 crepBody652_19

def crepBody652_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([31], none)) "bls_fp_lt_raw"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14,
    Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18]

def crepBody652_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([32, 33, 34, 35, 36, 37, 38], none)) "bls_fp_sub_raw"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14,
    Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18]

def crepBody652_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 32)

def crepBody652_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 33)

def crepBody652_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.var 34)

def crepBody652_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10 (Flapjack.CrepExp.var 35)

def crepBody652_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11 (Flapjack.CrepExp.var 36)

def crepBody652_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 12 (Flapjack.CrepExp.var 37)

def crepBody652_29 : CrepProg (BitVec 64) :=
.seq crepBody652_28 crepBody652_2

def crepBody652_30 : CrepProg (BitVec 64) :=
.seq crepBody652_27 crepBody652_29

def crepBody652_31 : CrepProg (BitVec 64) :=
.seq crepBody652_26 crepBody652_30

def crepBody652_32 : CrepProg (BitVec 64) :=
.seq crepBody652_25 crepBody652_31

def crepBody652_33 : CrepProg (BitVec 64) :=
.seq crepBody652_24 crepBody652_32

def crepBody652_34 : CrepProg (BitVec 64) :=
.seq crepBody652_23 crepBody652_33

def crepBody652_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19, 20, 21, 22, 23, 24], none)) "bls_fp_sub"
  [Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22,
    Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26,
    Flapjack.CrepExp.var 27, Flapjack.CrepExp.var 28, Flapjack.CrepExp.var 29, Flapjack.CrepExp.var 30]

def crepBody652_36 : CrepProg (BitVec 64) :=
.seq crepBody652_34 crepBody652_35

def crepBody652_37 : CrepProg (BitVec 64) :=
.seq crepBody652_22 crepBody652_36

def crepBody652_38 : CrepProg (BitVec 64) :=
.dec 38 (Flapjack.CrepExp.const 0#64) crepBody652_37

def crepBody652_39 : CrepProg (BitVec 64) :=
.dec 37 (Flapjack.CrepExp.const 0#64) crepBody652_38

def crepBody652_40 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.const 0#64) crepBody652_39

def crepBody652_41 : CrepProg (BitVec 64) :=
.dec 35 (Flapjack.CrepExp.const 0#64) crepBody652_40

def crepBody652_42 : CrepProg (BitVec 64) :=
.dec 34 (Flapjack.CrepExp.const 0#64) crepBody652_41

def crepBody652_43 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.const 0#64) crepBody652_42

def crepBody652_44 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody652_43

def crepBody652_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([32, 33, 34, 35, 36, 37, 38], none)) "bls_fp_sub_raw"
  [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16,
    Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12]

def crepBody652_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 13 (Flapjack.CrepExp.var 32)

def crepBody652_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 14 (Flapjack.CrepExp.var 33)

def crepBody652_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 15 (Flapjack.CrepExp.var 34)

def crepBody652_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 16 (Flapjack.CrepExp.var 35)

def crepBody652_50 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 17 (Flapjack.CrepExp.var 36)

def crepBody652_51 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 18 (Flapjack.CrepExp.var 37)

def crepBody652_52 : CrepProg (BitVec 64) :=
.seq crepBody652_51 crepBody652_2

def crepBody652_53 : CrepProg (BitVec 64) :=
.seq crepBody652_50 crepBody652_52

def crepBody652_54 : CrepProg (BitVec 64) :=
.seq crepBody652_49 crepBody652_53

def crepBody652_55 : CrepProg (BitVec 64) :=
.seq crepBody652_48 crepBody652_54

def crepBody652_56 : CrepProg (BitVec 64) :=
.seq crepBody652_47 crepBody652_55

def crepBody652_57 : CrepProg (BitVec 64) :=
.seq crepBody652_46 crepBody652_56

def crepBody652_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([25, 26, 27, 28, 29, 30], none)) "bls_fp_sub"
  [Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26, Flapjack.CrepExp.var 27, Flapjack.CrepExp.var 28,
    Flapjack.CrepExp.var 29, Flapjack.CrepExp.var 30, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20,
    Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22, Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24]

def crepBody652_59 : CrepProg (BitVec 64) :=
.seq crepBody652_57 crepBody652_58

def crepBody652_60 : CrepProg (BitVec 64) :=
.seq crepBody652_45 crepBody652_59

def crepBody652_61 : CrepProg (BitVec 64) :=
.dec 38 (Flapjack.CrepExp.const 0#64) crepBody652_60

def crepBody652_62 : CrepProg (BitVec 64) :=
.dec 37 (Flapjack.CrepExp.const 0#64) crepBody652_61

def crepBody652_63 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.const 0#64) crepBody652_62

def crepBody652_64 : CrepProg (BitVec 64) :=
.dec 35 (Flapjack.CrepExp.const 0#64) crepBody652_63

def crepBody652_65 : CrepProg (BitVec 64) :=
.dec 34 (Flapjack.CrepExp.const 0#64) crepBody652_64

def crepBody652_66 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.const 0#64) crepBody652_65

def crepBody652_67 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody652_66

def crepBody652_68 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 31) (Flapjack.CrepExp.const 0#64)) crepBody652_44 crepBody652_67

def crepBody652_69 : CrepProg (BitVec 64) :=
.seq crepBody652_21 crepBody652_68

def crepBody652_70 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.const 0#64) crepBody652_69

def crepBody652_71 : CrepProg (BitVec 64) :=
.seq crepBody652_20 crepBody652_70

def crepBody652_72 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.const 1#64) crepBody652_71

def crepBody652_73 : CrepProg (BitVec 64) :=
.seq crepBody652_72 crepBody652_1

def crepBody652_74 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.const 0#64) crepBody652_73

def crepBody652_75 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.const 0#64) crepBody652_74

def crepBody652_76 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.const 0#64) crepBody652_75

def crepBody652_77 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody652_76

def crepBody652_78 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody652_77

def crepBody652_79 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody652_78

def crepBody652_80 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody652_79

def crepBody652_81 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody652_80

def crepBody652_82 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody652_81

def crepBody652_83 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody652_82

def crepBody652_84 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody652_83

def crepBody652_85 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 1#64) crepBody652_84

def crepBody652_86 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 1873798617647539866#64) crepBody652_85

def crepBody652_87 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 5412103778470702295#64) crepBody652_86

def crepBody652_88 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 7239337960414712511#64) crepBody652_87

def crepBody652_89 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 7435674573564081700#64) crepBody652_88

def crepBody652_90 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 2210141511517208575#64) crepBody652_89

def crepBody652_91 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 13402431016077863595#64) crepBody652_90

def crepBody652_92 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 5) crepBody652_91

def crepBody652_93 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 4) crepBody652_92

def crepBody652_94 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 3) crepBody652_93

def crepBody652_95 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 2) crepBody652_94

def crepBody652_96 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 1) crepBody652_95

def crepBody652_97 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 0) crepBody652_96

def crepBody652_98 : CrepProg (BitVec 64) :=
.seq crepBody652_3 crepBody652_97

def crepBody652_99 : CrepProg (BitVec 64) :=
.seq crepBody652_0 crepBody652_98

def crepBody652_100 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody652_99

def data652 : CrepProg (BitVec 64) := crepBody652_100
def output652 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 108#8, 115#8, 95#8, 102#8, 112#8, 95#8, 105#8, 110#8, 118#8, 95#8, 114#8, 97#8, 119#8], [0, 1, 2, 3, 4, 5], crepProgToHOL data652)
end InitECandidate.Proofs.FrontendStages.Crep
