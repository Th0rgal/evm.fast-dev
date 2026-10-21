import InitECandidate.Proofs.FrontendStages.Crep.Translate539
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody555_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody555_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "stack_pop" []

def crepBody555_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "to_address_masked"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody555_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10, 11, 12, 13], none)) "stack_pop" []

def crepBody555_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14, 15, 16, 17], none)) "stack_pop" []

def crepBody555_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18, 19, 20, 21], none)) "stack_pop" []

def crepBody555_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22, 23, 24, 25], none)) "stack_pop" []

def crepBody555_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27, 28], none)) "extend_memory_cost2"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13,
    Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17,
    Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21,
    Flapjack.CrepExp.var 22, Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25]

def crepBody555_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([29], none)) "is_warm_address" [Flapjack.CrepExp.var 9]

def crepBody555_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 30 (Flapjack.CrepExp.const 3000#64)

def crepBody555_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody555_11 : CrepProg (BitVec 64) :=
.seq crepBody555_9 crepBody555_10

def crepBody555_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 29) (Flapjack.CrepExp.const 0#64)) crepBody555_11 crepBody555_10

def crepBody555_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([31], none)) "add_sat" [Flapjack.CrepExp.var 30, Flapjack.CrepExp.var 27]

def crepBody555_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([32], none)) "charge_gas" [Flapjack.CrepExp.var 31]

def crepBody555_15 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody555_14

def crepBody555_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([32], none)) "warm_address" [Flapjack.CrepExp.var 9]

def crepBody555_17 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody555_16

def crepBody555_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 29) (Flapjack.CrepExp.const 0#64)) crepBody555_17 crepBody555_10

def crepBody555_19 : CrepProg (BitVec 64) :=
.seq crepBody555_15 crepBody555_18

def crepBody555_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([32, 33, 34], none)) "calculate_delegation_cost" [Flapjack.CrepExp.var 9]

def crepBody555_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([36], none)) "charge_gas" [Flapjack.CrepExp.var 34]

def crepBody555_22 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.const 0#64) crepBody555_21

def crepBody555_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([36], none)) "warm_address" [Flapjack.CrepExp.var 35]

def crepBody555_24 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.const 0#64) crepBody555_23

def crepBody555_25 : CrepProg (BitVec 64) :=
.seq crepBody555_22 crepBody555_24

def crepBody555_26 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 32) (Flapjack.CrepExp.const 0#64)) crepBody555_25 crepBody555_10

def crepBody555_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([36, 37], none)) "ext_code_of" [Flapjack.CrepExp.var 35]

def crepBody555_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([38], none)) "sat_word"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody555_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([39, 40], none)) "calculate_message_call_gas"
  [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64,
    Flapjack.CrepExp.var 38,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 64#64]),
    Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody555_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([41], none)) "charge_gas" [Flapjack.CrepExp.var 39]

def crepBody555_31 : CrepProg (BitVec 64) :=
.dec 41 (Flapjack.CrepExp.const 0#64) crepBody555_30

def crepBody555_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 41) (Flapjack.CrepExp.var 42)

def crepBody555_33 : CrepProg (BitVec 64) :=
.seq crepBody555_32 crepBody555_10

def crepBody555_34 : CrepProg (BitVec 64) :=
.dec 42 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 184#64]),
    Flapjack.CrepExp.var 40]) crepBody555_33

def crepBody555_35 : CrepProg (BitVec 64) :=
.dec 41 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 184#64]) crepBody555_34

def crepBody555_36 : CrepProg (BitVec 64) :=
.seq crepBody555_31 crepBody555_35

def crepBody555_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([41], none)) "extend_memory" [Flapjack.CrepExp.var 28]

def crepBody555_38 : CrepProg (BitVec 64) :=
.dec 41 (Flapjack.CrepExp.const 0#64) crepBody555_37

def crepBody555_39 : CrepProg (BitVec 64) :=
.seq crepBody555_36 crepBody555_38

def crepBody555_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 42) (Flapjack.CrepExp.var 43)

def crepBody555_41 : CrepProg (BitVec 64) :=
.seq crepBody555_40 crepBody555_10

def crepBody555_42 : CrepProg (BitVec 64) :=
.dec 43 (Flapjack.CrepExp.const 0#64) crepBody555_41

def crepBody555_43 : CrepProg (BitVec 64) :=
.dec 42 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 72#64]) crepBody555_42

def crepBody555_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([42], none)) "sat_word"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody555_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([43], none)) "sat_word"
  [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17]

def crepBody555_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([44], none)) "sat_word"
  [Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21]

def crepBody555_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([45], none)) "sat_word"
  [Flapjack.CrepExp.var 22, Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25]

def crepBody555_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([46], none)) "generic_call"
  [Flapjack.CrepExp.var 40, Flapjack.CrepExp.var 41,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 26, Flapjack.CrepExp.const 56#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 26, Flapjack.CrepExp.const 56#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 26, Flapjack.CrepExp.const 56#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 26, Flapjack.CrepExp.const 56#64],
          Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 26, Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 26, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.var 35, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.var 42,
    Flapjack.CrepExp.var 43, Flapjack.CrepExp.var 44, Flapjack.CrepExp.var 45, Flapjack.CrepExp.var 36,
    Flapjack.CrepExp.var 37, Flapjack.CrepExp.var 32, Flapjack.CrepExp.const 0#64]

def crepBody555_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([47], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody555_50 : CrepProg (BitVec 64) :=
.dec 47 (Flapjack.CrepExp.const 0#64) crepBody555_49

def crepBody555_51 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 46) (Flapjack.CrepExp.const 0#64)) crepBody555_50 crepBody555_10

def crepBody555_52 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody555_53 : CrepProg (BitVec 64) :=
.seq crepBody555_51 crepBody555_52

def crepBody555_54 : CrepProg (BitVec 64) :=
.seq crepBody555_48 crepBody555_53

def crepBody555_55 : CrepProg (BitVec 64) :=
.dec 46 (Flapjack.CrepExp.const 0#64) crepBody555_54

def crepBody555_56 : CrepProg (BitVec 64) :=
.seq crepBody555_47 crepBody555_55

def crepBody555_57 : CrepProg (BitVec 64) :=
.dec 45 (Flapjack.CrepExp.const 0#64) crepBody555_56

def crepBody555_58 : CrepProg (BitVec 64) :=
.seq crepBody555_46 crepBody555_57

def crepBody555_59 : CrepProg (BitVec 64) :=
.dec 44 (Flapjack.CrepExp.const 0#64) crepBody555_58

def crepBody555_60 : CrepProg (BitVec 64) :=
.seq crepBody555_45 crepBody555_59

def crepBody555_61 : CrepProg (BitVec 64) :=
.dec 43 (Flapjack.CrepExp.const 0#64) crepBody555_60

def crepBody555_62 : CrepProg (BitVec 64) :=
.seq crepBody555_44 crepBody555_61

def crepBody555_63 : CrepProg (BitVec 64) :=
.dec 42 (Flapjack.CrepExp.const 0#64) crepBody555_62

def crepBody555_64 : CrepProg (BitVec 64) :=
.seq crepBody555_43 crepBody555_63

def crepBody555_65 : CrepProg (BitVec 64) :=
.dec 41 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 72#64])) crepBody555_64

def crepBody555_66 : CrepProg (BitVec 64) :=
.seq crepBody555_39 crepBody555_65

def crepBody555_67 : CrepProg (BitVec 64) :=
.seq crepBody555_29 crepBody555_66

def crepBody555_68 : CrepProg (BitVec 64) :=
.dec 40 (Flapjack.CrepExp.const 0#64) crepBody555_67

def crepBody555_69 : CrepProg (BitVec 64) :=
.dec 39 (Flapjack.CrepExp.const 0#64) crepBody555_68

def crepBody555_70 : CrepProg (BitVec 64) :=
.seq crepBody555_28 crepBody555_69

def crepBody555_71 : CrepProg (BitVec 64) :=
.dec 38 (Flapjack.CrepExp.const 0#64) crepBody555_70

def crepBody555_72 : CrepProg (BitVec 64) :=
.seq crepBody555_27 crepBody555_71

def crepBody555_73 : CrepProg (BitVec 64) :=
.dec 37 (Flapjack.CrepExp.const 0#64) crepBody555_72

def crepBody555_74 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.const 0#64) crepBody555_73

def crepBody555_75 : CrepProg (BitVec 64) :=
.seq crepBody555_26 crepBody555_74

def crepBody555_76 : CrepProg (BitVec 64) :=
.dec 35 (Flapjack.CrepExp.var 33) crepBody555_75

def crepBody555_77 : CrepProg (BitVec 64) :=
.seq crepBody555_20 crepBody555_76

def crepBody555_78 : CrepProg (BitVec 64) :=
.dec 34 (Flapjack.CrepExp.const 0#64) crepBody555_77

def crepBody555_79 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.const 0#64) crepBody555_78

def crepBody555_80 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody555_79

def crepBody555_81 : CrepProg (BitVec 64) :=
.seq crepBody555_19 crepBody555_80

def crepBody555_82 : CrepProg (BitVec 64) :=
.seq crepBody555_13 crepBody555_81

def crepBody555_83 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.const 0#64) crepBody555_82

def crepBody555_84 : CrepProg (BitVec 64) :=
.seq crepBody555_12 crepBody555_83

def crepBody555_85 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.const 100#64) crepBody555_84

def crepBody555_86 : CrepProg (BitVec 64) :=
.seq crepBody555_8 crepBody555_85

def crepBody555_87 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.const 0#64) crepBody555_86

def crepBody555_88 : CrepProg (BitVec 64) :=
.seq crepBody555_7 crepBody555_87

def crepBody555_89 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.const 0#64) crepBody555_88

def crepBody555_90 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody555_89

def crepBody555_91 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody555_90

def crepBody555_92 : CrepProg (BitVec 64) :=
.seq crepBody555_6 crepBody555_91

def crepBody555_93 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody555_92

def crepBody555_94 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody555_93

def crepBody555_95 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody555_94

def crepBody555_96 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody555_95

def crepBody555_97 : CrepProg (BitVec 64) :=
.seq crepBody555_5 crepBody555_96

def crepBody555_98 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody555_97

def crepBody555_99 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody555_98

def crepBody555_100 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody555_99

def crepBody555_101 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody555_100

def crepBody555_102 : CrepProg (BitVec 64) :=
.seq crepBody555_4 crepBody555_101

def crepBody555_103 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody555_102

def crepBody555_104 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody555_103

def crepBody555_105 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody555_104

def crepBody555_106 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody555_105

def crepBody555_107 : CrepProg (BitVec 64) :=
.seq crepBody555_3 crepBody555_106

def crepBody555_108 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody555_107

def crepBody555_109 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody555_108

def crepBody555_110 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody555_109

def crepBody555_111 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody555_110

def crepBody555_112 : CrepProg (BitVec 64) :=
.seq crepBody555_2 crepBody555_111

def crepBody555_113 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody555_112

def crepBody555_114 : CrepProg (BitVec 64) :=
.seq crepBody555_1 crepBody555_113

def crepBody555_115 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody555_114

def crepBody555_116 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody555_115

def crepBody555_117 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody555_116

def crepBody555_118 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody555_117

def crepBody555_119 : CrepProg (BitVec 64) :=
.seq crepBody555_0 crepBody555_118

def crepBody555_120 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody555_119

def crepBody555_121 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody555_120

def crepBody555_122 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody555_121

def crepBody555_123 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody555_122

def data555 : CrepProg (BitVec 64) := crepBody555_123
def output555 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [111#8, 112#8, 95#8, 100#8, 101#8, 108#8, 101#8, 103#8, 97#8, 116#8, 101#8, 99#8, 97#8, 108#8, 108#8], [], crepProgToHOL data555)
end InitECandidate.Proofs.FrontendStages.Crep
