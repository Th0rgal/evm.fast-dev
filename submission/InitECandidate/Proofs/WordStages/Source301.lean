import InitECandidate.Proofs.WordStages.Source285
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody301_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody301_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody301_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 128#64]))

def sourceBody301_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody301_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody301_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody301_0, 301, 2)) (some 79) ([8, 18, 14]) (some (8, sourceBody301_4, 301, 3))

def sourceBody301_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody301_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_5 sourceBody301_6

def sourceBody301_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_7 sourceBody301_0

def sourceBody301_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_3 sourceBody301_8

def sourceBody301_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_2 sourceBody301_9

def sourceBody301_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_1 sourceBody301_10

def sourceBody301_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody301_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody301_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody301_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody301_16 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.reg 14) sourceBody301_14 sourceBody301_15

def sourceBody301_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_16 sourceBody301_6

def sourceBody301_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody301_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody301_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody301_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_20 sourceBody301_0

def sourceBody301_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_19 sourceBody301_21

def sourceBody301_23 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody301_22 sourceBody301_0

def sourceBody301_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_23 sourceBody301_6

def sourceBody301_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_24 sourceBody301_0

def sourceBody301_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_18 sourceBody301_25

def sourceBody301_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_17 sourceBody301_26

def sourceBody301_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_13 sourceBody301_27

def sourceBody301_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_12 sourceBody301_28

def sourceBody301_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody301_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody301_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody301_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 18, 14]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody301_0, 301, 4)) (some 290) ([24, 6]) (some (24, sourceBody301_32, 301, 5))

def sourceBody301_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_33 sourceBody301_6

def sourceBody301_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_34 sourceBody301_0

def sourceBody301_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_31 sourceBody301_35

def sourceBody301_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_30 sourceBody301_36

def sourceBody301_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody301_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody301_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody301_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody301_42 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.WordRegImm.reg 16) sourceBody301_40 sourceBody301_41

def sourceBody301_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_42 sourceBody301_6

def sourceBody301_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody301_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody301_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody301_0, 301, 6)) (some 282) ([6]) (some (6, sourceBody301_45, 301, 7))

def sourceBody301_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_46 sourceBody301_6

def sourceBody301_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_47 sourceBody301_0

def sourceBody301_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_40 sourceBody301_48

def sourceBody301_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_49

def sourceBody301_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_50

def sourceBody301_52 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody301_51 sourceBody301_0

def sourceBody301_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_52 sourceBody301_6

def sourceBody301_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_53 sourceBody301_0

def sourceBody301_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_44 sourceBody301_54

def sourceBody301_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_43 sourceBody301_55

def sourceBody301_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_39 sourceBody301_56

def sourceBody301_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_38 sourceBody301_57

def sourceBody301_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody301_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody301_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody301_62 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody301_0, 301, 8)) (some 300) ([6, 16, 12]) (some (6, sourceBody301_45, 301, 9))

def sourceBody301_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_62 sourceBody301_6

def sourceBody301_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_63 sourceBody301_0

def sourceBody301_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_61 sourceBody301_64

def sourceBody301_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_60 sourceBody301_65

def sourceBody301_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_59 sourceBody301_66

def sourceBody301_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody301_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody301_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody301_71 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 12) sourceBody301_70 sourceBody301_39

def sourceBody301_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_71 sourceBody301_6

def sourceBody301_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 16)

def sourceBody301_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody301_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody301_76 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody301_0, 301, 10)) (some 68) ([16]) (some (16, sourceBody301_75, 301, 11))

def sourceBody301_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_76 sourceBody301_6

def sourceBody301_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_77 sourceBody301_0

def sourceBody301_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_74 sourceBody301_78

def sourceBody301_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 4)

def sourceBody301_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody301_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody301_83 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody301_0, 301, 12)) (some 77) ([12, 22, 10]) (some (12, sourceBody301_82, 301, 13))

def sourceBody301_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_83 sourceBody301_6

def sourceBody301_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_84 sourceBody301_0

def sourceBody301_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_81 sourceBody301_85

def sourceBody301_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_80 sourceBody301_86

def sourceBody301_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_44 sourceBody301_87

def sourceBody301_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_88

def sourceBody301_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_89

def sourceBody301_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody301_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 12)

def sourceBody301_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 16) 22

def sourceBody301_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_93 sourceBody301_0

def sourceBody301_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_92 sourceBody301_94

def sourceBody301_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_95 sourceBody301_0

def sourceBody301_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_44 sourceBody301_96

def sourceBody301_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_97

def sourceBody301_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_91 sourceBody301_98

def sourceBody301_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_99

def sourceBody301_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_90 sourceBody301_100

def sourceBody301_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_79 sourceBody301_101

def sourceBody301_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_102

def sourceBody301_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_103

def sourceBody301_105 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody301_104 sourceBody301_0

def sourceBody301_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_105 sourceBody301_6

def sourceBody301_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_106 sourceBody301_0

def sourceBody301_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_73 sourceBody301_107

def sourceBody301_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_72 sourceBody301_108

def sourceBody301_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_69 sourceBody301_109

def sourceBody301_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_68 sourceBody301_110

def sourceBody301_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 24)

def sourceBody301_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody301_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_113 sourceBody301_0

def sourceBody301_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_112 sourceBody301_114

def sourceBody301_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_111 sourceBody301_115

def sourceBody301_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_67 sourceBody301_116

def sourceBody301_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_117

def sourceBody301_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_118

def sourceBody301_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_58 sourceBody301_119

def sourceBody301_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_37 sourceBody301_120

def sourceBody301_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_121

def sourceBody301_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_122

def sourceBody301_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_123

def sourceBody301_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_124

def sourceBody301_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_125

def sourceBody301_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_126

def sourceBody301_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_29 sourceBody301_127

def sourceBody301_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_11 sourceBody301_128

def sourceBody301_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_129

def sourceBody301_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody301_0 sourceBody301_130

def source301 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (301, 3, sourceBody301_131)
end InitECandidate.Proofs.WordStages
