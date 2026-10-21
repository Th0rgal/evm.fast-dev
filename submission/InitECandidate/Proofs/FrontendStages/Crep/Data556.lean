import InitECandidate.Proofs.FrontendStages.Crep.Translate540
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody556_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody556_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "stack_pop" []

def crepBody556_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "to_address_masked"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody556_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10, 11, 12, 13], none)) "stack_pop" []

def crepBody556_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14, 15, 16, 17], none)) "stack_pop" []

def crepBody556_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18, 19, 20, 21], none)) "stack_pop" []

def crepBody556_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22, 23, 24, 25], none)) "stack_pop" []

def crepBody556_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([27, 28], none)) "extend_memory_cost2"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13,
    Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17,
    Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21,
    Flapjack.CrepExp.var 22, Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25]

def crepBody556_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([29], none)) "is_warm_address" [Flapjack.CrepExp.var 9]

def crepBody556_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 30 (Flapjack.CrepExp.const 3000#64)

def crepBody556_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody556_11 : CrepProg (BitVec 64) :=
.seq crepBody556_9 crepBody556_10

def crepBody556_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 29) (Flapjack.CrepExp.const 0#64)) crepBody556_11 crepBody556_10

def crepBody556_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([31], none)) "add_sat" [Flapjack.CrepExp.var 30, Flapjack.CrepExp.var 27]

def crepBody556_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([32], none)) "charge_gas" [Flapjack.CrepExp.var 31]

def crepBody556_15 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody556_14

def crepBody556_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([32], none)) "warm_address" [Flapjack.CrepExp.var 9]

def crepBody556_17 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody556_16

def crepBody556_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 29) (Flapjack.CrepExp.const 0#64)) crepBody556_17 crepBody556_10

def crepBody556_19 : CrepProg (BitVec 64) :=
.seq crepBody556_15 crepBody556_18

def crepBody556_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([32, 33, 34], none)) "calculate_delegation_cost" [Flapjack.CrepExp.var 9]

def crepBody556_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([36], none)) "charge_gas" [Flapjack.CrepExp.var 34]

def crepBody556_22 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.const 0#64) crepBody556_21

def crepBody556_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([36], none)) "warm_address" [Flapjack.CrepExp.var 35]

def crepBody556_24 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.const 0#64) crepBody556_23

def crepBody556_25 : CrepProg (BitVec 64) :=
.seq crepBody556_22 crepBody556_24

def crepBody556_26 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 32) (Flapjack.CrepExp.const 0#64)) crepBody556_25 crepBody556_10

def crepBody556_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([36, 37], none)) "ext_code_of" [Flapjack.CrepExp.var 35]

def crepBody556_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([38], none)) "sat_word"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody556_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([39, 40], none)) "calculate_message_call_gas"
  [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64,
    Flapjack.CrepExp.var 38,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 64#64]),
    Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody556_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([41], none)) "charge_gas" [Flapjack.CrepExp.var 39]

def crepBody556_31 : CrepProg (BitVec 64) :=
.dec 41 (Flapjack.CrepExp.const 0#64) crepBody556_30

def crepBody556_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 41) (Flapjack.CrepExp.var 42)

def crepBody556_33 : CrepProg (BitVec 64) :=
.seq crepBody556_32 crepBody556_10

def crepBody556_34 : CrepProg (BitVec 64) :=
.dec 42 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 184#64]),
    Flapjack.CrepExp.var 40]) crepBody556_33

def crepBody556_35 : CrepProg (BitVec 64) :=
.dec 41 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 184#64]) crepBody556_34

def crepBody556_36 : CrepProg (BitVec 64) :=
.seq crepBody556_31 crepBody556_35

def crepBody556_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([41], none)) "extend_memory" [Flapjack.CrepExp.var 28]

def crepBody556_38 : CrepProg (BitVec 64) :=
.dec 41 (Flapjack.CrepExp.const 0#64) crepBody556_37

def crepBody556_39 : CrepProg (BitVec 64) :=
.seq crepBody556_36 crepBody556_38

def crepBody556_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 42) (Flapjack.CrepExp.var 43)

def crepBody556_41 : CrepProg (BitVec 64) :=
.seq crepBody556_40 crepBody556_10

def crepBody556_42 : CrepProg (BitVec 64) :=
.dec 43 (Flapjack.CrepExp.const 0#64) crepBody556_41

def crepBody556_43 : CrepProg (BitVec 64) :=
.dec 42 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 72#64]) crepBody556_42

def crepBody556_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([42], none)) "sat_word"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody556_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([43], none)) "sat_word"
  [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 17]

def crepBody556_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([44], none)) "sat_word"
  [Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 21]

def crepBody556_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([45], none)) "sat_word"
  [Flapjack.CrepExp.var 22, Flapjack.CrepExp.var 23, Flapjack.CrepExp.var 24, Flapjack.CrepExp.var 25]

def crepBody556_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([46], none)) "generic_call"
  [Flapjack.CrepExp.var 40, Flapjack.CrepExp.var 41, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64,
    Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 26, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 35, Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.const 1#64,
    Flapjack.CrepExp.var 42, Flapjack.CrepExp.var 43, Flapjack.CrepExp.var 44, Flapjack.CrepExp.var 45,
    Flapjack.CrepExp.var 36, Flapjack.CrepExp.var 37, Flapjack.CrepExp.var 32, Flapjack.CrepExp.const 0#64]

def crepBody556_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([47], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody556_50 : CrepProg (BitVec 64) :=
.dec 47 (Flapjack.CrepExp.const 0#64) crepBody556_49

def crepBody556_51 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 46) (Flapjack.CrepExp.const 0#64)) crepBody556_50 crepBody556_10

def crepBody556_52 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody556_53 : CrepProg (BitVec 64) :=
.seq crepBody556_51 crepBody556_52

def crepBody556_54 : CrepProg (BitVec 64) :=
.seq crepBody556_48 crepBody556_53

def crepBody556_55 : CrepProg (BitVec 64) :=
.dec 46 (Flapjack.CrepExp.const 0#64) crepBody556_54

def crepBody556_56 : CrepProg (BitVec 64) :=
.seq crepBody556_47 crepBody556_55

def crepBody556_57 : CrepProg (BitVec 64) :=
.dec 45 (Flapjack.CrepExp.const 0#64) crepBody556_56

def crepBody556_58 : CrepProg (BitVec 64) :=
.seq crepBody556_46 crepBody556_57

def crepBody556_59 : CrepProg (BitVec 64) :=
.dec 44 (Flapjack.CrepExp.const 0#64) crepBody556_58

def crepBody556_60 : CrepProg (BitVec 64) :=
.seq crepBody556_45 crepBody556_59

def crepBody556_61 : CrepProg (BitVec 64) :=
.dec 43 (Flapjack.CrepExp.const 0#64) crepBody556_60

def crepBody556_62 : CrepProg (BitVec 64) :=
.seq crepBody556_44 crepBody556_61

def crepBody556_63 : CrepProg (BitVec 64) :=
.dec 42 (Flapjack.CrepExp.const 0#64) crepBody556_62

def crepBody556_64 : CrepProg (BitVec 64) :=
.seq crepBody556_43 crepBody556_63

def crepBody556_65 : CrepProg (BitVec 64) :=
.dec 41 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 72#64])) crepBody556_64

def crepBody556_66 : CrepProg (BitVec 64) :=
.seq crepBody556_39 crepBody556_65

def crepBody556_67 : CrepProg (BitVec 64) :=
.seq crepBody556_29 crepBody556_66

def crepBody556_68 : CrepProg (BitVec 64) :=
.dec 40 (Flapjack.CrepExp.const 0#64) crepBody556_67

def crepBody556_69 : CrepProg (BitVec 64) :=
.dec 39 (Flapjack.CrepExp.const 0#64) crepBody556_68

def crepBody556_70 : CrepProg (BitVec 64) :=
.seq crepBody556_28 crepBody556_69

def crepBody556_71 : CrepProg (BitVec 64) :=
.dec 38 (Flapjack.CrepExp.const 0#64) crepBody556_70

def crepBody556_72 : CrepProg (BitVec 64) :=
.seq crepBody556_27 crepBody556_71

def crepBody556_73 : CrepProg (BitVec 64) :=
.dec 37 (Flapjack.CrepExp.const 0#64) crepBody556_72

def crepBody556_74 : CrepProg (BitVec 64) :=
.dec 36 (Flapjack.CrepExp.const 0#64) crepBody556_73

def crepBody556_75 : CrepProg (BitVec 64) :=
.seq crepBody556_26 crepBody556_74

def crepBody556_76 : CrepProg (BitVec 64) :=
.dec 35 (Flapjack.CrepExp.var 33) crepBody556_75

def crepBody556_77 : CrepProg (BitVec 64) :=
.seq crepBody556_20 crepBody556_76

def crepBody556_78 : CrepProg (BitVec 64) :=
.dec 34 (Flapjack.CrepExp.const 0#64) crepBody556_77

def crepBody556_79 : CrepProg (BitVec 64) :=
.dec 33 (Flapjack.CrepExp.const 0#64) crepBody556_78

def crepBody556_80 : CrepProg (BitVec 64) :=
.dec 32 (Flapjack.CrepExp.const 0#64) crepBody556_79

def crepBody556_81 : CrepProg (BitVec 64) :=
.seq crepBody556_19 crepBody556_80

def crepBody556_82 : CrepProg (BitVec 64) :=
.seq crepBody556_13 crepBody556_81

def crepBody556_83 : CrepProg (BitVec 64) :=
.dec 31 (Flapjack.CrepExp.const 0#64) crepBody556_82

def crepBody556_84 : CrepProg (BitVec 64) :=
.seq crepBody556_12 crepBody556_83

def crepBody556_85 : CrepProg (BitVec 64) :=
.dec 30 (Flapjack.CrepExp.const 100#64) crepBody556_84

def crepBody556_86 : CrepProg (BitVec 64) :=
.seq crepBody556_8 crepBody556_85

def crepBody556_87 : CrepProg (BitVec 64) :=
.dec 29 (Flapjack.CrepExp.const 0#64) crepBody556_86

def crepBody556_88 : CrepProg (BitVec 64) :=
.seq crepBody556_7 crepBody556_87

def crepBody556_89 : CrepProg (BitVec 64) :=
.dec 28 (Flapjack.CrepExp.const 0#64) crepBody556_88

def crepBody556_90 : CrepProg (BitVec 64) :=
.dec 27 (Flapjack.CrepExp.const 0#64) crepBody556_89

def crepBody556_91 : CrepProg (BitVec 64) :=
.dec 26 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody556_90

def crepBody556_92 : CrepProg (BitVec 64) :=
.seq crepBody556_6 crepBody556_91

def crepBody556_93 : CrepProg (BitVec 64) :=
.dec 25 (Flapjack.CrepExp.const 0#64) crepBody556_92

def crepBody556_94 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.const 0#64) crepBody556_93

def crepBody556_95 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.const 0#64) crepBody556_94

def crepBody556_96 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody556_95

def crepBody556_97 : CrepProg (BitVec 64) :=
.seq crepBody556_5 crepBody556_96

def crepBody556_98 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody556_97

def crepBody556_99 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody556_98

def crepBody556_100 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody556_99

def crepBody556_101 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody556_100

def crepBody556_102 : CrepProg (BitVec 64) :=
.seq crepBody556_4 crepBody556_101

def crepBody556_103 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody556_102

def crepBody556_104 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody556_103

def crepBody556_105 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody556_104

def crepBody556_106 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody556_105

def crepBody556_107 : CrepProg (BitVec 64) :=
.seq crepBody556_3 crepBody556_106

def crepBody556_108 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody556_107

def crepBody556_109 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody556_108

def crepBody556_110 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody556_109

def crepBody556_111 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody556_110

def crepBody556_112 : CrepProg (BitVec 64) :=
.seq crepBody556_2 crepBody556_111

def crepBody556_113 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody556_112

def crepBody556_114 : CrepProg (BitVec 64) :=
.seq crepBody556_1 crepBody556_113

def crepBody556_115 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody556_114

def crepBody556_116 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody556_115

def crepBody556_117 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody556_116

def crepBody556_118 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody556_117

def crepBody556_119 : CrepProg (BitVec 64) :=
.seq crepBody556_0 crepBody556_118

def crepBody556_120 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody556_119

def crepBody556_121 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody556_120

def crepBody556_122 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody556_121

def crepBody556_123 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody556_122

def data556 : CrepProg (BitVec 64) := crepBody556_123
def output556 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [111#8, 112#8, 95#8, 115#8, 116#8, 97#8, 116#8, 105#8, 99#8, 99#8, 97#8, 108#8, 108#8], [], crepProgToHOL data556)
end InitECandidate.Proofs.FrontendStages.Crep
