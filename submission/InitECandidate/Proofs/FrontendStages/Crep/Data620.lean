import InitECandidate.Proofs.FrontendStages.Crep.Translate604
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody620_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11, 12, 13, 14], none)) "fq_mul_small"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.const 9#64]

def crepBody620_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16, 17, 18], none)) "fq_add"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14]

def crepBody620_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19, 20, 21, 22], none)) "fq_neg"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10]

def crepBody620_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([31, 32, 33, 34], none)) "fq_mul"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18,
    Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26]

def crepBody620_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([35, 36, 37, 38], none)) "fq_mul"
  [Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22,
    Flapjack.CrepExp.var 27, Flapjack.CrepExp.var 28, Flapjack.CrepExp.var 29, Flapjack.CrepExp.var 30]

def crepBody620_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([39, 40, 41, 42], none)) "fq_mul"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18,
    Flapjack.CrepExp.var 27, Flapjack.CrepExp.var 28, Flapjack.CrepExp.var 29, Flapjack.CrepExp.var 30]

def crepBody620_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([43, 44, 45, 46], none)) "fq_mul"
  [Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21, Flapjack.CrepExp.var 22,
    Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25, Flapjack.CrepExp.var 26]

def crepBody620_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([47, 48, 49, 50], none)) "fq_sub"
  [Flapjack.CrepExp.var 31, Flapjack.CrepExp.var 32, Flapjack.CrepExp.var 33, Flapjack.CrepExp.var 34,
    Flapjack.CrepExp.var 35, Flapjack.CrepExp.var 36, Flapjack.CrepExp.var 37, Flapjack.CrepExp.var 38]

def crepBody620_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([51, 52, 53, 54], none)) "fq_add"
  [Flapjack.CrepExp.var 39, Flapjack.CrepExp.var 40, Flapjack.CrepExp.var 41, Flapjack.CrepExp.var 42,
    Flapjack.CrepExp.var 43, Flapjack.CrepExp.var 44, Flapjack.CrepExp.var 45, Flapjack.CrepExp.var 46]

def crepBody620_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([55, 56, 57, 58], none)) "fq_mul_small"
  [Flapjack.CrepExp.var 51, Flapjack.CrepExp.var 52, Flapjack.CrepExp.var 53, Flapjack.CrepExp.var 54,
    Flapjack.CrepExp.const 9#64]

def crepBody620_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([59, 60, 61, 62], none)) "fq_sub"
  [Flapjack.CrepExp.var 47, Flapjack.CrepExp.var 48, Flapjack.CrepExp.var 49, Flapjack.CrepExp.var 50,
    Flapjack.CrepExp.var 55, Flapjack.CrepExp.var 56, Flapjack.CrepExp.var 57, Flapjack.CrepExp.var 58]

def crepBody620_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 63) (Flapjack.CrepExp.var 64)

def crepBody620_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 63, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 65)

def crepBody620_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 63, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 66)

def crepBody620_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 63, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 67)

def crepBody620_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody620_16 : CrepProg (BitVec 64) :=
.seq crepBody620_14 crepBody620_15

def crepBody620_17 : CrepProg (BitVec 64) :=
.seq crepBody620_13 crepBody620_16

def crepBody620_18 : CrepProg (BitVec 64) :=
.seq crepBody620_12 crepBody620_17

def crepBody620_19 : CrepProg (BitVec 64) :=
.seq crepBody620_11 crepBody620_18

def crepBody620_20 : CrepProg (BitVec 64) :=
.dec 67 (Flapjack.CrepExp.var 62) crepBody620_19

def crepBody620_21 : CrepProg (BitVec 64) :=
.dec 66 (Flapjack.CrepExp.var 61) crepBody620_20

def crepBody620_22 : CrepProg (BitVec 64) :=
.dec 65 (Flapjack.CrepExp.var 60) crepBody620_21

def crepBody620_23 : CrepProg (BitVec 64) :=
.dec 64 (Flapjack.CrepExp.var 59) crepBody620_22

def crepBody620_24 : CrepProg (BitVec 64) :=
.dec 63 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 32#64]]) crepBody620_23

def crepBody620_25 : CrepProg (BitVec 64) :=
.dec 67 (Flapjack.CrepExp.var 54) crepBody620_19

def crepBody620_26 : CrepProg (BitVec 64) :=
.dec 66 (Flapjack.CrepExp.var 53) crepBody620_25

def crepBody620_27 : CrepProg (BitVec 64) :=
.dec 65 (Flapjack.CrepExp.var 52) crepBody620_26

def crepBody620_28 : CrepProg (BitVec 64) :=
.dec 64 (Flapjack.CrepExp.var 51) crepBody620_27

def crepBody620_29 : CrepProg (BitVec 64) :=
.dec 63 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 6#64],
        Flapjack.CrepExp.const 32#64]]) crepBody620_28

def crepBody620_30 : CrepProg (BitVec 64) :=
.seq crepBody620_24 crepBody620_29

def crepBody620_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 2 (Flapjack.CrepExp.var 63)

def crepBody620_32 : CrepProg (BitVec 64) :=
.seq crepBody620_31 crepBody620_15

def crepBody620_33 : CrepProg (BitVec 64) :=
.dec 63 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 1#64]) crepBody620_32

def crepBody620_34 : CrepProg (BitVec 64) :=
.seq crepBody620_30 crepBody620_33

def crepBody620_35 : CrepProg (BitVec 64) :=
.seq crepBody620_10 crepBody620_34

def crepBody620_36 : CrepProg (BitVec 64) :=
.dec 62 (Flapjack.CrepExp.const 0#64) crepBody620_35

def crepBody620_37 : CrepProg (BitVec 64) :=
.dec 61 (Flapjack.CrepExp.const 0#64) crepBody620_36

def crepBody620_38 : CrepProg (BitVec 64) :=
.dec 60 (Flapjack.CrepExp.const 0#64) crepBody620_37

def crepBody620_39 : CrepProg (BitVec 64) :=
.dec 59 (Flapjack.CrepExp.const 0#64) crepBody620_38

def crepBody620_40 : CrepProg (BitVec 64) :=
.seq crepBody620_9 crepBody620_39

def crepBody620_41 : CrepProg (BitVec 64) :=
.dec 58 (Flapjack.CrepExp.const 0#64) crepBody620_40

def crepBody620_42 : CrepProg (BitVec 64) :=
.dec 57 (Flapjack.CrepExp.const 0#64) crepBody620_41

def crepBody620_43 : CrepProg (BitVec 64) :=
.dec 56 (Flapjack.CrepExp.const 0#64) crepBody620_42

def crepBody620_44 : CrepProg (BitVec 64) :=
.dec 55 (Flapjack.CrepExp.const 0#64) crepBody620_43

def crepBody620_45 : CrepProg (BitVec 64) :=
.seq crepBody620_8 crepBody620_44

def crepBody620_46 : CrepProg (BitVec 64) :=
.dec 54 (Flapjack.CrepExp.const 0#64) crepBody620_45

def crepBody620_47 : CrepProg (BitVec 64) :=
.dec 53 (Flapjack.CrepExp.const 0#64) crepBody620_46

def crepBody620_48 : CrepProg (BitVec 64) :=
.dec 52 (Flapjack.CrepExp.const 0#64) crepBody620_47

def crepBody620_49 : CrepProg (BitVec 64) :=
.dec 51 (Flapjack.CrepExp.const 0#64) crepBody620_48

def crepBody620_50 : CrepProg (BitVec 64) :=
.seq crepBody620_7 crepBody620_49

def crepBody620_51 : CrepProg (BitVec 64) :=
.dec 50 (Flapjack.CrepExp.const 0#64) crepBody620_50

def crepBody620_52 : CrepProg (BitVec 64) :=
.dec 49 (Flapjack.CrepExp.const 0#64) crepBody620_51

def crepBody620_53 : CrepProg (BitVec 64) :=
.dec 48 (Flapjack.CrepExp.const 0#64) crepBody620_52

def crepBody620_54 : CrepProg (BitVec 64) :=
.dec 47 (Flapjack.CrepExp.const 0#64) crepBody620_53

def crepBody620_55 : CrepProg (BitVec 64) :=
.seq crepBody620_6 crepBody620_54

def crepBody620_56 : CrepProg (BitVec 64) :=
.dec 46 (Flapjack.CrepExp.const 0#64) crepBody620_55

def crepBody620_57 : CrepProg (BitVec 64) :=
.dec 45 (Flapjack.CrepExp.const 0#64) crepBody620_56

def crepBody620_58 : CrepProg (BitVec 64) :=
.dec 44 (Flapjack.CrepExp.const 0#64) crepBody620_57

def crepBody620_59 : CrepProg (BitVec 64) :=
.dec 43 (Flapjack.CrepExp.const 0#64) crepBody620_58

def crepBody620_60 : CrepProg (BitVec 64) :=
.seq crepBody620_5 crepBody620_59

def crepBody620_61 : CrepProg (BitVec 64) :=
.dec 42 (Flapjack.CrepExp.const 0#64) crepBody620_60

def crepBody620_62 : CrepProg (BitVec 64) :=
.dec 41 (Flapjack.CrepExp.const 0#64) crepBody620_61

def crepBody620_63 : CrepProg (BitVec 64) :=
.dec 40 (Flapjack.CrepExp.const 0#64) crepBody620_62

def crepBody620_64 : CrepProg (BitVec 64) :=
.dec 39 (Flapjack.CrepExp.const 0#64) crepBody620_63

def crepBody620_65 : CrepProg (BitVec 64) :=
.seq crepBody620_4 crepBody620_64

def crepBody620_66 : CrepProg (BitVec 64) :=
.dec 38 (Flapjack.CrepExp.const 0#64) crepBody620_65

def crepBody620_67 : CrepProg (BitVec 64) :=
.dec 37 (Flapjack.CrepExp.const 0#64) crepBody620_66

def crepBody620_68 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.const 0#64) crepBody620_67

def crepBody620_69 : CrepProg (BitVec 64) :=
.dec 35 (Flapjack.CrepExp.const 0#64) crepBody620_68

def crepBody620_70 : CrepProg (BitVec 64) :=
.seq crepBody620_3 crepBody620_69

def crepBody620_71 : CrepProg (BitVec 64) :=
.dec 34 (Flapjack.CrepExp.const 0#64) crepBody620_70

def crepBody620_72 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.const 0#64) crepBody620_71

def crepBody620_73 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody620_72

def crepBody620_74 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.const 0#64) crepBody620_73

def crepBody620_75 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 376#64]),
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64],
          Flapjack.CrepExp.const 32#64],
      Flapjack.CrepExp.const 24#64])) crepBody620_74

def crepBody620_76 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 376#64]),
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64],
          Flapjack.CrepExp.const 32#64],
      Flapjack.CrepExp.const 16#64])) crepBody620_75

def crepBody620_77 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 376#64]),
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64],
          Flapjack.CrepExp.const 32#64],
      Flapjack.CrepExp.const 8#64])) crepBody620_76

def crepBody620_78 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 376#64]),
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64],
      Flapjack.CrepExp.const 32#64])) crepBody620_77

def crepBody620_79 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 376#64]),
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64]],
      Flapjack.CrepExp.const 24#64])) crepBody620_78

def crepBody620_80 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 376#64]),
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64]],
      Flapjack.CrepExp.const 16#64])) crepBody620_79

def crepBody620_81 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 376#64]),
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64]],
      Flapjack.CrepExp.const 8#64])) crepBody620_80

def crepBody620_82 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 376#64]),
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 64#64]])) crepBody620_81

def crepBody620_83 : CrepProg (BitVec 64) :=
.seq crepBody620_2 crepBody620_82

def crepBody620_84 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody620_83

def crepBody620_85 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody620_84

def crepBody620_86 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody620_85

def crepBody620_87 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody620_86

def crepBody620_88 : CrepProg (BitVec 64) :=
.seq crepBody620_1 crepBody620_87

def crepBody620_89 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody620_88

def crepBody620_90 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody620_89

def crepBody620_91 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody620_90

def crepBody620_92 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody620_91

def crepBody620_93 : CrepProg (BitVec 64) :=
.seq crepBody620_0 crepBody620_92

def crepBody620_94 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody620_93

def crepBody620_95 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody620_94

def crepBody620_96 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody620_95

def crepBody620_97 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody620_96

def crepBody620_98 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 6#64],
              Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 24#64])) crepBody620_97

def crepBody620_99 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 6#64],
              Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 16#64])) crepBody620_98

def crepBody620_100 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 6#64],
              Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 8#64])) crepBody620_99

def crepBody620_101 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 1,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 6#64],
          Flapjack.CrepExp.const 32#64]])) crepBody620_100

def crepBody620_102 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 24#64])) crepBody620_101

def crepBody620_103 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 16#64])) crepBody620_102

def crepBody620_104 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 32#64]],
      Flapjack.CrepExp.const 8#64])) crepBody620_103

def crepBody620_105 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 1,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 32#64]])) crepBody620_104

def crepBody620_106 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 6#64)) crepBody620_105

def crepBody620_107 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody620_108 : CrepProg (BitVec 64) :=
.seq crepBody620_106 crepBody620_107

def crepBody620_109 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody620_108

def data620 : CrepProg (BitVec 64) := crepBody620_109
def output620 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 113#8, 49#8, 50#8, 95#8, 102#8, 114#8, 111#8, 98#8], [0, 1], crepProgToHOL data620)
end InitECandidate.Proofs.FrontendStages.Crep
