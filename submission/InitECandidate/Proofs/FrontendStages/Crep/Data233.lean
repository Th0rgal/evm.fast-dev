import InitECandidate.Proofs.FrontendStages.Crep.Translate217
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody233_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.loadGlob 0#5)

def crepBody233_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody233_2 : CrepProg (BitVec 64) :=
.seq crepBody233_0 crepBody233_1

def crepBody233_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "mpt_fail" [Flapjack.CrepExp.const 3#64]

def crepBody233_4 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody233_3

def crepBody233_5 : CrepProg (BitVec 64) :=
.seq crepBody233_2 crepBody233_4

def crepBody233_6 : CrepProg (BitVec 64) :=
.call (some (([3, 4, 5, 6]), some ((1#64), crepBody233_5))) ("rlp_decode_fully") ([Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2])

def crepBody233_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody233_8 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody233_7 crepBody233_1

def crepBody233_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "mpt_fail" [Flapjack.CrepExp.const 4#64]

def crepBody233_10 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody233_9

def crepBody233_11 : CrepProg (BitVec 64) :=
.seq crepBody233_8 crepBody233_10

def crepBody233_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody233_11 crepBody233_1

def crepBody233_13 : CrepProg (BitVec 64) :=
.seq crepBody233_6 crepBody233_12

def crepBody233_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8, 9], none)) "rlp_list_to_slices" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody233_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11, 12, 13, 14], none)) "rlp_item"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 10,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 16#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 10,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64])]

def crepBody233_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "mpt_fail" [Flapjack.CrepExp.const 5#64]

def crepBody233_17 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody233_16

def crepBody233_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 0#64)) crepBody233_17 crepBody233_1

def crepBody233_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15, 16, 17], none)) "compact_to_nibbles"
  [Flapjack.CrepExp.var 12, Flapjack.CrepExp.var 13]

def crepBody233_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18, 19, 20, 21], none)) "rlp_item"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 10,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.const 16#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 10,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.const 16#64],
          Flapjack.CrepExp.const 8#64])]

def crepBody233_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "mpt_fail" [Flapjack.CrepExp.const 6#64]

def crepBody233_22 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody233_21

def crepBody233_23 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 18) (Flapjack.CrepExp.const 0#64)) crepBody233_22 crepBody233_1

def crepBody233_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([22], none)) "node_new_leaf"
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 19, Flapjack.CrepExp.var 20]

def crepBody233_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 23) (Flapjack.CrepExp.var 24)

def crepBody233_26 : CrepProg (BitVec 64) :=
.seq crepBody233_25 crepBody233_1

def crepBody233_27 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.var 1) crepBody233_26

def crepBody233_28 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 22, Flapjack.CrepExp.const 8#64]) crepBody233_27

def crepBody233_29 : CrepProg (BitVec 64) :=
.dec 24 (Flapjack.CrepExp.var 2) crepBody233_26

def crepBody233_30 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 22, Flapjack.CrepExp.const 16#64]) crepBody233_29

def crepBody233_31 : CrepProg (BitVec 64) :=
.seq crepBody233_28 crepBody233_30

def crepBody233_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.var 22]

def crepBody233_33 : CrepProg (BitVec 64) :=
.seq crepBody233_31 crepBody233_32

def crepBody233_34 : CrepProg (BitVec 64) :=
.seq crepBody233_24 crepBody233_33

def crepBody233_35 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.const 0#64) crepBody233_34

def crepBody233_36 : CrepProg (BitVec 64) :=
.seq crepBody233_23 crepBody233_35

def crepBody233_37 : CrepProg (BitVec 64) :=
.seq crepBody233_20 crepBody233_36

def crepBody233_38 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.const 0#64) crepBody233_37

def crepBody233_39 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 0#64) crepBody233_38

def crepBody233_40 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody233_39

def crepBody233_41 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody233_40

def crepBody233_42 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 17) (Flapjack.CrepExp.const 0#64)) crepBody233_41 crepBody233_1

def crepBody233_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "mpt_fail" [Flapjack.CrepExp.const 7#64]

def crepBody233_44 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody233_43

def crepBody233_45 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 16) (Flapjack.CrepExp.const 0#64)) crepBody233_44 crepBody233_1

def crepBody233_46 : CrepProg (BitVec 64) :=
.seq crepBody233_42 crepBody233_45

def crepBody233_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "scratch_alloc" [Flapjack.CrepExp.const 88#64]

def crepBody233_48 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.var 20)

def crepBody233_49 : CrepProg (BitVec 64) :=
.seq crepBody233_48 crepBody233_1

def crepBody233_50 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.const 1#64) crepBody233_49

def crepBody233_51 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 8#64]) crepBody233_50

def crepBody233_52 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 10) crepBody233_49

def crepBody233_53 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 24#64]) crepBody233_52

def crepBody233_54 : CrepProg (BitVec 64) :=
.seq crepBody233_51 crepBody233_53

def crepBody233_55 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 1) crepBody233_49

def crepBody233_56 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 48#64]) crepBody233_55

def crepBody233_57 : CrepProg (BitVec 64) :=
.seq crepBody233_54 crepBody233_56

def crepBody233_58 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 2) crepBody233_49

def crepBody233_59 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 56#64]) crepBody233_58

def crepBody233_60 : CrepProg (BitVec 64) :=
.seq crepBody233_57 crepBody233_59

def crepBody233_61 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 15) crepBody233_49

def crepBody233_62 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 64#64]) crepBody233_61

def crepBody233_63 : CrepProg (BitVec 64) :=
.seq crepBody233_60 crepBody233_62

def crepBody233_64 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.var 16) crepBody233_49

def crepBody233_65 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.const 72#64]) crepBody233_64

def crepBody233_66 : CrepProg (BitVec 64) :=
.seq crepBody233_63 crepBody233_65

def crepBody233_67 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.var 18]

def crepBody233_68 : CrepProg (BitVec 64) :=
.seq crepBody233_66 crepBody233_67

def crepBody233_69 : CrepProg (BitVec 64) :=
.seq crepBody233_47 crepBody233_68

def crepBody233_70 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody233_69

def crepBody233_71 : CrepProg (BitVec 64) :=
.seq crepBody233_46 crepBody233_70

def crepBody233_72 : CrepProg (BitVec 64) :=
.seq crepBody233_19 crepBody233_71

def crepBody233_73 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody233_72

def crepBody233_74 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody233_73

def crepBody233_75 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody233_74

def crepBody233_76 : CrepProg (BitVec 64) :=
.seq crepBody233_18 crepBody233_75

def crepBody233_77 : CrepProg (BitVec 64) :=
.seq crepBody233_15 crepBody233_76

def crepBody233_78 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody233_77

def crepBody233_79 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody233_78

def crepBody233_80 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody233_79

def crepBody233_81 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody233_80

def crepBody233_82 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 2#64)) crepBody233_81 crepBody233_1

def crepBody233_83 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "mpt_fail" [Flapjack.CrepExp.const 4#64]

def crepBody233_84 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody233_83

def crepBody233_85 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 17#64)) crepBody233_84 crepBody233_1

def crepBody233_86 : CrepProg (BitVec 64) :=
.seq crepBody233_82 crepBody233_85

def crepBody233_87 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "node_new_branch" []

def crepBody233_88 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "scratch_alloc" [Flapjack.CrepExp.const 88#64]

def crepBody233_89 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.var 14)

def crepBody233_90 : CrepProg (BitVec 64) :=
.seq crepBody233_89 crepBody233_1

def crepBody233_91 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 2#64) crepBody233_90

def crepBody233_92 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64]) crepBody233_91

def crepBody233_93 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 11) crepBody233_90

def crepBody233_94 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 16#64]) crepBody233_93

def crepBody233_95 : CrepProg (BitVec 64) :=
.seq crepBody233_92 crepBody233_94

def crepBody233_96 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 10) crepBody233_90

def crepBody233_97 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 24#64]) crepBody233_96

def crepBody233_98 : CrepProg (BitVec 64) :=
.seq crepBody233_95 crepBody233_97

def crepBody233_99 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody233_90

def crepBody233_100 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 32#64]) crepBody233_99

def crepBody233_101 : CrepProg (BitVec 64) :=
.seq crepBody233_98 crepBody233_100

def crepBody233_102 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 40#64]) crepBody233_99

def crepBody233_103 : CrepProg (BitVec 64) :=
.seq crepBody233_101 crepBody233_102

def crepBody233_104 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 1) crepBody233_90

def crepBody233_105 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 48#64]) crepBody233_104

def crepBody233_106 : CrepProg (BitVec 64) :=
.seq crepBody233_103 crepBody233_105

def crepBody233_107 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 2) crepBody233_90

def crepBody233_108 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 56#64]) crepBody233_107

def crepBody233_109 : CrepProg (BitVec 64) :=
.seq crepBody233_106 crepBody233_108

def crepBody233_110 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.var 12]

def crepBody233_111 : CrepProg (BitVec 64) :=
.seq crepBody233_109 crepBody233_110

def crepBody233_112 : CrepProg (BitVec 64) :=
.seq crepBody233_88 crepBody233_111

def crepBody233_113 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody233_112

def crepBody233_114 : CrepProg (BitVec 64) :=
.seq crepBody233_87 crepBody233_113

def crepBody233_115 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody233_114

def crepBody233_116 : CrepProg (BitVec 64) :=
.seq crepBody233_86 crepBody233_115

def crepBody233_117 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 8) crepBody233_116

def crepBody233_118 : CrepProg (BitVec 64) :=
.seq crepBody233_14 crepBody233_117

def crepBody233_119 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody233_118

def crepBody233_120 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody233_119

def crepBody233_121 : CrepProg (BitVec 64) :=
.seq crepBody233_13 crepBody233_120

def crepBody233_122 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody233_121

def crepBody233_123 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody233_122

def crepBody233_124 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody233_123

def crepBody233_125 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody233_124

def crepBody233_126 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody233_125

def data233 : CrepProg (BitVec 64) := crepBody233_126
def output233 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [95#8, 100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 115#8, 116#8, 101#8, 112#8], [0, 1, 2], crepProgToHOL data233)
end InitECandidate.Proofs.FrontendStages.Crep
