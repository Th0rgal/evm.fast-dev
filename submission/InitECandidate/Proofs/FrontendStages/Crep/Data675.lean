import InitECandidate.Proofs.FrontendStages.Crep.Translate659
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody675_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14, 15, 16, 17, 18, 19], none)) "bls_fp_sqr"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]

def crepBody675_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20, 21, 22, 23, 24, 25], none)) "bls_fp_sqr"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody675_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([26, 27, 28, 29, 30, 31], none)) "bls_fp_add"
  [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17,
    Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21,
    Flapjack.CrepExp.var 22, Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25]

def crepBody675_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([32, 33, 34, 35, 36, 37], none)) "bls_fp_inv"
  [Flapjack.CrepExp.var 26, Flapjack.CrepExp.var 27, Flapjack.CrepExp.var 28, Flapjack.CrepExp.var 29,
    Flapjack.CrepExp.var 30, Flapjack.CrepExp.var 31]

def crepBody675_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([38, 39, 40, 41, 42, 43], none)) "bls_fp_mul"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 32, Flapjack.CrepExp.var 33,
    Flapjack.CrepExp.var 34, Flapjack.CrepExp.var 35, Flapjack.CrepExp.var 36, Flapjack.CrepExp.var 37]

def crepBody675_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([44, 45, 46, 47, 48, 49], none)) "bls_fp_mul"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 32, Flapjack.CrepExp.var 33,
    Flapjack.CrepExp.var 34, Flapjack.CrepExp.var 35, Flapjack.CrepExp.var 36, Flapjack.CrepExp.var 37]

def crepBody675_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([44, 45, 46, 47, 48, 49], none)) "bls_fp_neg"
  [Flapjack.CrepExp.var 44, Flapjack.CrepExp.var 45, Flapjack.CrepExp.var 46, Flapjack.CrepExp.var 47,
    Flapjack.CrepExp.var 48, Flapjack.CrepExp.var 49]

def crepBody675_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 50) (Flapjack.CrepExp.var 51)

def crepBody675_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 50, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 52)

def crepBody675_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 50, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 53)

def crepBody675_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 50, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 54)

def crepBody675_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 50, Flapjack.CrepExp.const 32#64])
  (Flapjack.CrepExp.var 55)

def crepBody675_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 50, Flapjack.CrepExp.const 40#64])
  (Flapjack.CrepExp.var 56)

def crepBody675_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody675_14 : CrepProg (BitVec 64) :=
.seq crepBody675_12 crepBody675_13

def crepBody675_15 : CrepProg (BitVec 64) :=
.seq crepBody675_11 crepBody675_14

def crepBody675_16 : CrepProg (BitVec 64) :=
.seq crepBody675_10 crepBody675_15

def crepBody675_17 : CrepProg (BitVec 64) :=
.seq crepBody675_9 crepBody675_16

def crepBody675_18 : CrepProg (BitVec 64) :=
.seq crepBody675_8 crepBody675_17

def crepBody675_19 : CrepProg (BitVec 64) :=
.seq crepBody675_7 crepBody675_18

def crepBody675_20 : CrepProg (BitVec 64) :=
.dec 56 (Flapjack.CrepExp.var 43) crepBody675_19

def crepBody675_21 : CrepProg (BitVec 64) :=
.dec 55 (Flapjack.CrepExp.var 42) crepBody675_20

def crepBody675_22 : CrepProg (BitVec 64) :=
.dec 54 (Flapjack.CrepExp.var 41) crepBody675_21

def crepBody675_23 : CrepProg (BitVec 64) :=
.dec 53 (Flapjack.CrepExp.var 40) crepBody675_22

def crepBody675_24 : CrepProg (BitVec 64) :=
.dec 52 (Flapjack.CrepExp.var 39) crepBody675_23

def crepBody675_25 : CrepProg (BitVec 64) :=
.dec 51 (Flapjack.CrepExp.var 38) crepBody675_24

def crepBody675_26 : CrepProg (BitVec 64) :=
.dec 50 (Flapjack.CrepExp.var 0) crepBody675_25

def crepBody675_27 : CrepProg (BitVec 64) :=
.seq crepBody675_6 crepBody675_26

def crepBody675_28 : CrepProg (BitVec 64) :=
.dec 56 (Flapjack.CrepExp.var 49) crepBody675_19

def crepBody675_29 : CrepProg (BitVec 64) :=
.dec 55 (Flapjack.CrepExp.var 48) crepBody675_28

def crepBody675_30 : CrepProg (BitVec 64) :=
.dec 54 (Flapjack.CrepExp.var 47) crepBody675_29

def crepBody675_31 : CrepProg (BitVec 64) :=
.dec 53 (Flapjack.CrepExp.var 46) crepBody675_30

def crepBody675_32 : CrepProg (BitVec 64) :=
.dec 52 (Flapjack.CrepExp.var 45) crepBody675_31

def crepBody675_33 : CrepProg (BitVec 64) :=
.dec 51 (Flapjack.CrepExp.var 44) crepBody675_32

def crepBody675_34 : CrepProg (BitVec 64) :=
.dec 50 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64]) crepBody675_33

def crepBody675_35 : CrepProg (BitVec 64) :=
.seq crepBody675_27 crepBody675_34

def crepBody675_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody675_37 : CrepProg (BitVec 64) :=
.seq crepBody675_35 crepBody675_36

def crepBody675_38 : CrepProg (BitVec 64) :=
.seq crepBody675_5 crepBody675_37

def crepBody675_39 : CrepProg (BitVec 64) :=
.dec 49 (Flapjack.CrepExp.const 0#64) crepBody675_38

def crepBody675_40 : CrepProg (BitVec 64) :=
.dec 48 (Flapjack.CrepExp.const 0#64) crepBody675_39

def crepBody675_41 : CrepProg (BitVec 64) :=
.dec 47 (Flapjack.CrepExp.const 0#64) crepBody675_40

def crepBody675_42 : CrepProg (BitVec 64) :=
.dec 46 (Flapjack.CrepExp.const 0#64) crepBody675_41

def crepBody675_43 : CrepProg (BitVec 64) :=
.dec 45 (Flapjack.CrepExp.const 0#64) crepBody675_42

def crepBody675_44 : CrepProg (BitVec 64) :=
.dec 44 (Flapjack.CrepExp.const 0#64) crepBody675_43

def crepBody675_45 : CrepProg (BitVec 64) :=
.seq crepBody675_4 crepBody675_44

def crepBody675_46 : CrepProg (BitVec 64) :=
.dec 43 (Flapjack.CrepExp.const 0#64) crepBody675_45

def crepBody675_47 : CrepProg (BitVec 64) :=
.dec 42 (Flapjack.CrepExp.const 0#64) crepBody675_46

def crepBody675_48 : CrepProg (BitVec 64) :=
.dec 41 (Flapjack.CrepExp.const 0#64) crepBody675_47

def crepBody675_49 : CrepProg (BitVec 64) :=
.dec 40 (Flapjack.CrepExp.const 0#64) crepBody675_48

def crepBody675_50 : CrepProg (BitVec 64) :=
.dec 39 (Flapjack.CrepExp.const 0#64) crepBody675_49

def crepBody675_51 : CrepProg (BitVec 64) :=
.dec 38 (Flapjack.CrepExp.const 0#64) crepBody675_50

def crepBody675_52 : CrepProg (BitVec 64) :=
.seq crepBody675_3 crepBody675_51

def crepBody675_53 : CrepProg (BitVec 64) :=
.dec 37 (Flapjack.CrepExp.const 0#64) crepBody675_52

def crepBody675_54 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.const 0#64) crepBody675_53

def crepBody675_55 : CrepProg (BitVec 64) :=
.dec 35 (Flapjack.CrepExp.const 0#64) crepBody675_54

def crepBody675_56 : CrepProg (BitVec 64) :=
.dec 34 (Flapjack.CrepExp.const 0#64) crepBody675_55

def crepBody675_57 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.const 0#64) crepBody675_56

def crepBody675_58 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody675_57

def crepBody675_59 : CrepProg (BitVec 64) :=
.seq crepBody675_2 crepBody675_58

def crepBody675_60 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.const 0#64) crepBody675_59

def crepBody675_61 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.const 0#64) crepBody675_60

def crepBody675_62 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.const 0#64) crepBody675_61

def crepBody675_63 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.const 0#64) crepBody675_62

def crepBody675_64 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody675_63

def crepBody675_65 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.const 0#64) crepBody675_64

def crepBody675_66 : CrepProg (BitVec 64) :=
.seq crepBody675_1 crepBody675_65

def crepBody675_67 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody675_66

def crepBody675_68 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody675_67

def crepBody675_69 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody675_68

def crepBody675_70 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody675_69

def crepBody675_71 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody675_70

def crepBody675_72 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody675_71

def crepBody675_73 : CrepProg (BitVec 64) :=
.seq crepBody675_0 crepBody675_72

def crepBody675_74 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody675_73

def crepBody675_75 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody675_74

def crepBody675_76 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody675_75

def crepBody675_77 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody675_76

def crepBody675_78 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody675_77

def crepBody675_79 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody675_78

def crepBody675_80 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 40#64])) crepBody675_79

def crepBody675_81 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 32#64])) crepBody675_80

def crepBody675_82 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 24#64])) crepBody675_81

def crepBody675_83 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 16#64])) crepBody675_82

def crepBody675_84 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64],
      Flapjack.CrepExp.const 8#64])) crepBody675_83

def crepBody675_85 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64])) crepBody675_84

def crepBody675_86 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 40#64])) crepBody675_85

def crepBody675_87 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64])) crepBody675_86

def crepBody675_88 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 24#64])) crepBody675_87

def crepBody675_89 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64])) crepBody675_88

def crepBody675_90 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64])) crepBody675_89

def crepBody675_91 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 1)) crepBody675_90

def data675 : CrepProg (BitVec 64) := crepBody675_91
def output675 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 105#8, 110#8, 118#8], [0, 1], crepProgToHOL data675)
end InitECandidate.Proofs.FrontendStages.Crep
