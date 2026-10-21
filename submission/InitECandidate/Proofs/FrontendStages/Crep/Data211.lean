import InitECandidate.Proofs.FrontendStages.Crep.Translate195
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody211_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4, 5, 6], none)) "u256_from_word" [Flapjack.CrepExp.var 2]

def crepBody211_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7, 8, 9, 10], none)) "u256_from_word" [Flapjack.CrepExp.var 1]

def crepBody211_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11, 12, 13, 14], none)) "u256_from_word" [Flapjack.CrepExp.var 0]

def crepBody211_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11, 12, 13, 14], none)) "u256_mul"
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14,
    Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody211_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([24], none)) "u256_is_zero"
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14]

def crepBody211_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16, 17, 18], none)) "u256_add"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18,
    Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14]

def crepBody211_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([25, 26, 27, 28, 29, 30, 31, 32], none)) "u256_mul_full"
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14,
    Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10]

def crepBody211_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([33], none)) "trap_with" [Flapjack.CrepExp.const 3#64]

def crepBody211_8 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.const 0#64) crepBody211_7

def crepBody211_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody211_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.var 29, Flapjack.CrepExp.var 30, Flapjack.CrepExp.var 31, Flapjack.CrepExp.var 32])
  (Flapjack.CrepExp.const 0#64)) crepBody211_8 crepBody211_9

def crepBody211_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([37, 38, 39, 40], none)) "u256_from_word" [Flapjack.CrepExp.var 19]

def crepBody211_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([37, 38, 39, 40], none)) "u256_mul"
  [Flapjack.CrepExp.var 37, Flapjack.CrepExp.var 38, Flapjack.CrepExp.var 39, Flapjack.CrepExp.var 40,
    Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody211_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11, 12, 13, 14], none)) "u256_div"
  [Flapjack.CrepExp.var 33, Flapjack.CrepExp.var 34, Flapjack.CrepExp.var 35, Flapjack.CrepExp.var 36,
    Flapjack.CrepExp.var 37, Flapjack.CrepExp.var 38, Flapjack.CrepExp.var 39, Flapjack.CrepExp.var 40]

def crepBody211_14 : CrepProg (BitVec 64) :=
.seq crepBody211_12 crepBody211_13

def crepBody211_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 19 (Flapjack.CrepExp.var 41)

def crepBody211_16 : CrepProg (BitVec 64) :=
.seq crepBody211_15 crepBody211_9

def crepBody211_17 : CrepProg (BitVec 64) :=
.dec 41 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 19, Flapjack.CrepExp.const 1#64]) crepBody211_16

def crepBody211_18 : CrepProg (BitVec 64) :=
.seq crepBody211_14 crepBody211_17

def crepBody211_19 : CrepProg (BitVec 64) :=
.seq crepBody211_18 crepBody211_4

def crepBody211_20 : CrepProg (BitVec 64) :=
.seq crepBody211_11 crepBody211_19

def crepBody211_21 : CrepProg (BitVec 64) :=
.dec 40 (Flapjack.CrepExp.const 0#64) crepBody211_20

def crepBody211_22 : CrepProg (BitVec 64) :=
.dec 39 (Flapjack.CrepExp.const 0#64) crepBody211_21

def crepBody211_23 : CrepProg (BitVec 64) :=
.dec 38 (Flapjack.CrepExp.const 0#64) crepBody211_22

def crepBody211_24 : CrepProg (BitVec 64) :=
.dec 37 (Flapjack.CrepExp.const 0#64) crepBody211_23

def crepBody211_25 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.var 28) crepBody211_24

def crepBody211_26 : CrepProg (BitVec 64) :=
.dec 35 (Flapjack.CrepExp.var 27) crepBody211_25

def crepBody211_27 : CrepProg (BitVec 64) :=
.dec 34 (Flapjack.CrepExp.var 26) crepBody211_26

def crepBody211_28 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.var 25) crepBody211_27

def crepBody211_29 : CrepProg (BitVec 64) :=
.seq crepBody211_10 crepBody211_28

def crepBody211_30 : CrepProg (BitVec 64) :=
.seq crepBody211_6 crepBody211_29

def crepBody211_31 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody211_30

def crepBody211_32 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.const 0#64) crepBody211_31

def crepBody211_33 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.const 0#64) crepBody211_32

def crepBody211_34 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.const 0#64) crepBody211_33

def crepBody211_35 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.const 0#64) crepBody211_34

def crepBody211_36 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody211_35

def crepBody211_37 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody211_36

def crepBody211_38 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody211_37

def crepBody211_39 : CrepProg (BitVec 64) :=
.seq crepBody211_5 crepBody211_38

def crepBody211_40 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 24) (Flapjack.CrepExp.const 0#64)) crepBody211_39

def crepBody211_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16, 17, 18], none)) "u256_div"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18,
    Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody211_42 : CrepProg (BitVec 64) :=
.seq crepBody211_40 crepBody211_41

def crepBody211_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18]

def crepBody211_44 : CrepProg (BitVec 64) :=
.seq crepBody211_42 crepBody211_43

def crepBody211_45 : CrepProg (BitVec 64) :=
.seq crepBody211_4 crepBody211_44

def crepBody211_46 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody211_45

def crepBody211_47 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody211_46

def crepBody211_48 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody211_47

def crepBody211_49 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody211_48

def crepBody211_50 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody211_49

def crepBody211_51 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 1#64) crepBody211_50

def crepBody211_52 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody211_51

def crepBody211_53 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody211_52

def crepBody211_54 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody211_53

def crepBody211_55 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody211_54

def crepBody211_56 : CrepProg (BitVec 64) :=
.seq crepBody211_3 crepBody211_55

def crepBody211_57 : CrepProg (BitVec 64) :=
.seq crepBody211_2 crepBody211_56

def crepBody211_58 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody211_57

def crepBody211_59 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody211_58

def crepBody211_60 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody211_59

def crepBody211_61 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody211_60

def crepBody211_62 : CrepProg (BitVec 64) :=
.seq crepBody211_1 crepBody211_61

def crepBody211_63 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody211_62

def crepBody211_64 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody211_63

def crepBody211_65 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody211_64

def crepBody211_66 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody211_65

def crepBody211_67 : CrepProg (BitVec 64) :=
.seq crepBody211_0 crepBody211_66

def crepBody211_68 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody211_67

def crepBody211_69 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody211_68

def crepBody211_70 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody211_69

def crepBody211_71 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody211_70

def data211 : CrepProg (BitVec 64) := crepBody211_71
def output211 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [116#8, 97#8, 121#8, 108#8, 111#8, 114#8, 95#8, 101#8, 120#8, 112#8, 111#8, 110#8, 101#8, 110#8, 116#8, 105#8, 97#8,
    108#8], [0, 1, 2], crepProgToHOL data211)
end InitECandidate.Proofs.FrontendStages.Crep
