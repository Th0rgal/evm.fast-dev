import InitECandidate.Proofs.FrontendStages.Crep.Translate462
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody478_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody478_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "stack_pop" []

def crepBody478_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 9)

def crepBody478_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody478_4 : CrepProg (BitVec 64) :=
.seq crepBody478_2 crepBody478_3

def crepBody478_5 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 2#64) crepBody478_4

def crepBody478_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody478_7 : CrepProg (BitVec 64) :=
.seq crepBody478_5 crepBody478_6

def crepBody478_8 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
        Flapjack.CrepExp.const 16#64]))
  (Flapjack.CrepExp.var 0)) crepBody478_7 crepBody478_3

def crepBody478_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "sat_word"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody478_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10, 11], none)) "extend_memory_cost1"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody478_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12, 13], none)) "mul64x64" [Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.var 9]

def crepBody478_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "add_sat"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.const 375#64,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 375#64, Flapjack.CrepExp.var 0]],
    Flapjack.CrepExp.var 10]

def crepBody478_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 14 (Flapjack.CrepExp.const 18446744073709551615#64)

def crepBody478_14 : CrepProg (BitVec 64) :=
.seq crepBody478_13 crepBody478_3

def crepBody478_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "add_sat" [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 12]

def crepBody478_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 0#64)) crepBody478_14 crepBody478_15

def crepBody478_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "charge_gas" [Flapjack.CrepExp.var 14]

def crepBody478_18 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody478_17

def crepBody478_19 : CrepProg (BitVec 64) :=
.seq crepBody478_16 crepBody478_18

def crepBody478_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64],
        Flapjack.CrepExp.const 8#64]]

def crepBody478_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17, 18, 19, 20], none)) "stack_pop" []

def crepBody478_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "u256_to_be32"
  [Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 15,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 32#64]]]

def crepBody478_23 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody478_22

def crepBody478_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 16 (Flapjack.CrepExp.var 21)

def crepBody478_25 : CrepProg (BitVec 64) :=
.seq crepBody478_24 crepBody478_3

def crepBody478_26 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 1#64]) crepBody478_25

def crepBody478_27 : CrepProg (BitVec 64) :=
.seq crepBody478_23 crepBody478_26

def crepBody478_28 : CrepProg (BitVec 64) :=
.seq crepBody478_21 crepBody478_27

def crepBody478_29 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody478_28

def crepBody478_30 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody478_29

def crepBody478_31 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody478_30

def crepBody478_32 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody478_31

def crepBody478_33 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 16) (Flapjack.CrepExp.var 0)) crepBody478_32

def crepBody478_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "extend_memory" [Flapjack.CrepExp.var 11]

def crepBody478_35 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody478_34

def crepBody478_36 : CrepProg (BitVec 64) :=
.seq crepBody478_33 crepBody478_35

def crepBody478_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "require_not_static" []

def crepBody478_38 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody478_37

def crepBody478_39 : CrepProg (BitVec 64) :=
.seq crepBody478_36 crepBody478_38

def crepBody478_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([17], none)) "alloc" [Flapjack.CrepExp.const 40#64]

def crepBody478_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "alloc" [Flapjack.CrepExp.const 24#64]

def crepBody478_42 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "memcpy"
  [Flapjack.CrepExp.var 18,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.load
                  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
                Flapjack.CrepExp.const 112#64]),
          Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.const 20#64]

def crepBody478_43 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody478_42

def crepBody478_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.var 20)

def crepBody478_45 : CrepProg (BitVec 64) :=
.seq crepBody478_44 crepBody478_3

def crepBody478_46 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 18) crepBody478_45

def crepBody478_47 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 0#64]) crepBody478_46

def crepBody478_48 : CrepProg (BitVec 64) :=
.seq crepBody478_43 crepBody478_47

def crepBody478_49 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 15) crepBody478_45

def crepBody478_50 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 8#64]) crepBody478_49

def crepBody478_51 : CrepProg (BitVec 64) :=
.seq crepBody478_48 crepBody478_50

def crepBody478_52 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 0) crepBody478_45

def crepBody478_53 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 16#64]) crepBody478_52

def crepBody478_54 : CrepProg (BitVec 64) :=
.seq crepBody478_51 crepBody478_53

def crepBody478_55 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64]]

def crepBody478_56 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([20], none)) "sat_word"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody478_57 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "memcpy"
  [Flapjack.CrepExp.var 19,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
              Flapjack.CrepExp.const 24#64]),
        Flapjack.CrepExp.var 20],
    Flapjack.CrepExp.var 9]

def crepBody478_58 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody478_57

def crepBody478_59 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 21) (Flapjack.CrepExp.var 22)

def crepBody478_60 : CrepProg (BitVec 64) :=
.seq crepBody478_59 crepBody478_3

def crepBody478_61 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 19) crepBody478_60

def crepBody478_62 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 24#64]) crepBody478_61

def crepBody478_63 : CrepProg (BitVec 64) :=
.seq crepBody478_58 crepBody478_62

def crepBody478_64 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 9) crepBody478_60

def crepBody478_65 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.const 32#64]) crepBody478_64

def crepBody478_66 : CrepProg (BitVec 64) :=
.seq crepBody478_63 crepBody478_65

def crepBody478_67 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "log_append"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.var 17]

def crepBody478_68 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody478_67

def crepBody478_69 : CrepProg (BitVec 64) :=
.seq crepBody478_66 crepBody478_68

def crepBody478_70 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([21], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody478_71 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody478_70

def crepBody478_72 : CrepProg (BitVec 64) :=
.seq crepBody478_69 crepBody478_71

def crepBody478_73 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody478_74 : CrepProg (BitVec 64) :=
.seq crepBody478_72 crepBody478_73

def crepBody478_75 : CrepProg (BitVec 64) :=
.seq crepBody478_56 crepBody478_74

def crepBody478_76 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody478_75

def crepBody478_77 : CrepProg (BitVec 64) :=
.seq crepBody478_55 crepBody478_76

def crepBody478_78 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody478_77

def crepBody478_79 : CrepProg (BitVec 64) :=
.seq crepBody478_54 crepBody478_78

def crepBody478_80 : CrepProg (BitVec 64) :=
.seq crepBody478_41 crepBody478_79

def crepBody478_81 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody478_80

def crepBody478_82 : CrepProg (BitVec 64) :=
.seq crepBody478_40 crepBody478_81

def crepBody478_83 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody478_82

def crepBody478_84 : CrepProg (BitVec 64) :=
.seq crepBody478_39 crepBody478_83

def crepBody478_85 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody478_84

def crepBody478_86 : CrepProg (BitVec 64) :=
.seq crepBody478_20 crepBody478_85

def crepBody478_87 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody478_86

def crepBody478_88 : CrepProg (BitVec 64) :=
.seq crepBody478_19 crepBody478_87

def crepBody478_89 : CrepProg (BitVec 64) :=
.seq crepBody478_12 crepBody478_88

def crepBody478_90 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody478_89

def crepBody478_91 : CrepProg (BitVec 64) :=
.seq crepBody478_11 crepBody478_90

def crepBody478_92 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody478_91

def crepBody478_93 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody478_92

def crepBody478_94 : CrepProg (BitVec 64) :=
.seq crepBody478_10 crepBody478_93

def crepBody478_95 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody478_94

def crepBody478_96 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody478_95

def crepBody478_97 : CrepProg (BitVec 64) :=
.seq crepBody478_9 crepBody478_96

def crepBody478_98 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody478_97

def crepBody478_99 : CrepProg (BitVec 64) :=
.seq crepBody478_8 crepBody478_98

def crepBody478_100 : CrepProg (BitVec 64) :=
.seq crepBody478_1 crepBody478_99

def crepBody478_101 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody478_100

def crepBody478_102 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody478_101

def crepBody478_103 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody478_102

def crepBody478_104 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody478_103

def crepBody478_105 : CrepProg (BitVec 64) :=
.seq crepBody478_0 crepBody478_104

def crepBody478_106 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody478_105

def crepBody478_107 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody478_106

def crepBody478_108 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody478_107

def crepBody478_109 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody478_108

def data478 : CrepProg (BitVec 64) := crepBody478_109
def output478 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 108#8, 111#8, 103#8], [0], crepProgToHOL data478)
end InitECandidate.Proofs.FrontendStages.Crep
