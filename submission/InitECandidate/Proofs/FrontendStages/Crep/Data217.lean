import InitECandidate.Proofs.FrontendStages.Crep.Translate201
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody217_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 2)

def crepBody217_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody217_2 : CrepProg (BitVec 64) :=
.seq crepBody217_0 crepBody217_1

def crepBody217_3 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 20#64) crepBody217_2

def crepBody217_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 4#64

def crepBody217_5 : CrepProg (BitVec 64) :=
.seq crepBody217_3 crepBody217_4

def crepBody217_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]))
  (Flapjack.CrepExp.const 1#64)) crepBody217_5 crepBody217_1

def crepBody217_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "calculate_excess_blob_gas" [Flapjack.CrepExp.var 0]

def crepBody217_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 3)

def crepBody217_9 : CrepProg (BitVec 64) :=
.seq crepBody217_8 crepBody217_1

def crepBody217_10 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 21#64) crepBody217_9

def crepBody217_11 : CrepProg (BitVec 64) :=
.seq crepBody217_10 crepBody217_4

def crepBody217_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 208#64]))
  (Flapjack.CrepExp.var 2)) crepBody217_11 crepBody217_1

def crepBody217_13 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 22#64) crepBody217_9

def crepBody217_14 : CrepProg (BitVec 64) :=
.seq crepBody217_13 crepBody217_4

def crepBody217_15 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 104#64]))
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 112#64]))) crepBody217_14 crepBody217_1

def crepBody217_16 : CrepProg (BitVec 64) :=
.seq crepBody217_12 crepBody217_15

def crepBody217_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4, 5, 6], none)) "calculate_base_fee_per_gas"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 104#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 104#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 112#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody217_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "u256_eq"
  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 160#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody217_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 8)

def crepBody217_20 : CrepProg (BitVec 64) :=
.seq crepBody217_19 crepBody217_1

def crepBody217_21 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 23#64) crepBody217_20

def crepBody217_22 : CrepProg (BitVec 64) :=
.seq crepBody217_21 crepBody217_4

def crepBody217_23 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody217_22 crepBody217_1

def crepBody217_24 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 24#64) crepBody217_20

def crepBody217_25 : CrepProg (BitVec 64) :=
.seq crepBody217_24 crepBody217_4

def crepBody217_26 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 120#64]))
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 120#64]))) crepBody217_25 crepBody217_1

def crepBody217_27 : CrepProg (BitVec 64) :=
.seq crepBody217_23 crepBody217_26

def crepBody217_28 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 25#64) crepBody217_20

def crepBody217_29 : CrepProg (BitVec 64) :=
.seq crepBody217_28 crepBody217_4

def crepBody217_30 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]))
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64]),
      Flapjack.CrepExp.const 1#64])) crepBody217_29 crepBody217_1

def crepBody217_31 : CrepProg (BitVec 64) :=
.seq crepBody217_27 crepBody217_30

def crepBody217_32 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 26#64) crepBody217_20

def crepBody217_33 : CrepProg (BitVec 64) :=
.seq crepBody217_32 crepBody217_4

def crepBody217_34 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 32#64)
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 136#64]))) crepBody217_33 crepBody217_1

def crepBody217_35 : CrepProg (BitVec 64) :=
.seq crepBody217_31 crepBody217_34

def crepBody217_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "u256_is_zero"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 64#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 64#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 64#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 64#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody217_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 9)

def crepBody217_38 : CrepProg (BitVec 64) :=
.seq crepBody217_37 crepBody217_1

def crepBody217_39 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 27#64) crepBody217_38

def crepBody217_40 : CrepProg (BitVec 64) :=
.seq crepBody217_39 crepBody217_4

def crepBody217_41 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 0#64)) crepBody217_40 crepBody217_1

def crepBody217_42 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "memeq"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 152#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 120#64]),
    Flapjack.CrepExp.const 8#64]

def crepBody217_43 : CrepProg (BitVec 64) :=
.seq crepBody217_41 crepBody217_42

def crepBody217_44 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 28#64) crepBody217_38

def crepBody217_45 : CrepProg (BitVec 64) :=
.seq crepBody217_44 crepBody217_4

def crepBody217_46 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody217_45 crepBody217_1

def crepBody217_47 : CrepProg (BitVec 64) :=
.seq crepBody217_43 crepBody217_46

def crepBody217_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "heap_mark" []

def crepBody217_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "alloc" [Flapjack.CrepExp.const 64#64]

def crepBody217_50 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 192#64)

def crepBody217_51 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "keccak256"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 1#64,
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 32#64]]

def crepBody217_52 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody217_51

def crepBody217_53 : CrepProg (BitVec 64) :=
.seq crepBody217_50 crepBody217_52

def crepBody217_54 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "memeq"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 32#64],
    Flapjack.CrepExp.const 32#64]

def crepBody217_55 : CrepProg (BitVec 64) :=
.seq crepBody217_53 crepBody217_54

def crepBody217_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "heap_release" [Flapjack.CrepExp.var 9]

def crepBody217_57 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody217_56

def crepBody217_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 11)

def crepBody217_59 : CrepProg (BitVec 64) :=
.seq crepBody217_58 crepBody217_1

def crepBody217_60 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 29#64) crepBody217_59

def crepBody217_61 : CrepProg (BitVec 64) :=
.seq crepBody217_60 crepBody217_4

def crepBody217_62 : CrepProg (BitVec 64) :=
.seq crepBody217_57 crepBody217_61

def crepBody217_63 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody217_62 crepBody217_1

def crepBody217_64 : CrepProg (BitVec 64) :=
.seq crepBody217_55 crepBody217_63

def crepBody217_65 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "header_hash" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 10]

def crepBody217_66 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody217_65

def crepBody217_67 : CrepProg (BitVec 64) :=
.seq crepBody217_64 crepBody217_66

def crepBody217_68 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "memeq"
  [Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 32#64]

def crepBody217_69 : CrepProg (BitVec 64) :=
.seq crepBody217_67 crepBody217_68

def crepBody217_70 : CrepProg (BitVec 64) :=
.seq crepBody217_69 crepBody217_57

def crepBody217_71 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 30#64) crepBody217_59

def crepBody217_72 : CrepProg (BitVec 64) :=
.seq crepBody217_71 crepBody217_4

def crepBody217_73 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody217_72 crepBody217_1

def crepBody217_74 : CrepProg (BitVec 64) :=
.seq crepBody217_70 crepBody217_73

def crepBody217_75 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody217_76 : CrepProg (BitVec 64) :=
.seq crepBody217_74 crepBody217_75

def crepBody217_77 : CrepProg (BitVec 64) :=
.seq crepBody217_49 crepBody217_76

def crepBody217_78 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody217_77

def crepBody217_79 : CrepProg (BitVec 64) :=
.seq crepBody217_48 crepBody217_78

def crepBody217_80 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody217_79

def crepBody217_81 : CrepProg (BitVec 64) :=
.seq crepBody217_47 crepBody217_80

def crepBody217_82 : CrepProg (BitVec 64) :=
.seq crepBody217_36 crepBody217_81

def crepBody217_83 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody217_82

def crepBody217_84 : CrepProg (BitVec 64) :=
.seq crepBody217_35 crepBody217_83

def crepBody217_85 : CrepProg (BitVec 64) :=
.seq crepBody217_18 crepBody217_84

def crepBody217_86 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody217_85

def crepBody217_87 : CrepProg (BitVec 64) :=
.seq crepBody217_17 crepBody217_86

def crepBody217_88 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody217_87

def crepBody217_89 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody217_88

def crepBody217_90 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody217_89

def crepBody217_91 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody217_90

def crepBody217_92 : CrepProg (BitVec 64) :=
.seq crepBody217_16 crepBody217_91

def crepBody217_93 : CrepProg (BitVec 64) :=
.seq crepBody217_7 crepBody217_92

def crepBody217_94 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody217_93

def crepBody217_95 : CrepProg (BitVec 64) :=
.seq crepBody217_6 crepBody217_94

def data217 : CrepProg (BitVec 64) := crepBody217_95
def output217 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [118#8, 97#8, 108#8, 105#8, 100#8, 97#8, 116#8, 101#8, 95#8, 104#8, 101#8, 97#8, 100#8, 101#8, 114#8], [0, 1], crepProgToHOL data217)
end InitECandidate.Proofs.FrontendStages.Crep
