import InitECandidate.Proofs.WordStages.Source605
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody621_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody621_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody621_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody621_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody621_0, 621, 2)) (some 68) ([16]) (some (16, sourceBody621_2, 621, 3))

def sourceBody621_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody621_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_3 sourceBody621_4

def sourceBody621_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_5 sourceBody621_0

def sourceBody621_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_1 sourceBody621_6

def sourceBody621_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody621_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody621_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody621_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody621_0, 621, 4)) (some 78) ([6, 14]) (some (6, sourceBody621_10, 621, 5))

def sourceBody621_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_11 sourceBody621_4

def sourceBody621_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_12 sourceBody621_0

def sourceBody621_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_9 sourceBody621_13

def sourceBody621_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_8 sourceBody621_14

def sourceBody621_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_15

def sourceBody621_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_16

def sourceBody621_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody621_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody621_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody621_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody621_22 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 10) sourceBody621_20 sourceBody621_21

def sourceBody621_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_22 sourceBody621_4

def sourceBody621_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody621_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody621_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody621_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody621_0, 621, 6)) (some 411) ([14]) (some (14, sourceBody621_26, 621, 7))

def sourceBody621_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_27 sourceBody621_4

def sourceBody621_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_28 sourceBody621_0

def sourceBody621_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_25 sourceBody621_29

def sourceBody621_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody621_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody621_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody621_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 18) sourceBody621_33 sourceBody621_19

def sourceBody621_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_34 sourceBody621_4

def sourceBody621_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody621_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody621_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody621_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody621_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 14) 18

def sourceBody621_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_40 sourceBody621_0

def sourceBody621_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_39 sourceBody621_41

def sourceBody621_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_42 sourceBody621_0

def sourceBody621_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_38 sourceBody621_43

def sourceBody621_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_44

def sourceBody621_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_37 sourceBody621_45

def sourceBody621_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_46

def sourceBody621_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 56#64])

def sourceBody621_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody621_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_49 sourceBody621_43

def sourceBody621_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_50

def sourceBody621_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_48 sourceBody621_51

def sourceBody621_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_52

def sourceBody621_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_47 sourceBody621_53

def sourceBody621_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody621_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody621_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_56 sourceBody621_43

def sourceBody621_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_57

def sourceBody621_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_55 sourceBody621_58

def sourceBody621_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_59

def sourceBody621_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_54 sourceBody621_60

def sourceBody621_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody621_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 264#64]))

def sourceBody621_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_63 sourceBody621_43

def sourceBody621_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_64

def sourceBody621_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_62 sourceBody621_65

def sourceBody621_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_66

def sourceBody621_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_61 sourceBody621_67

def sourceBody621_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody621_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody621_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_70 sourceBody621_0

def sourceBody621_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_69 sourceBody621_71

def sourceBody621_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_68 sourceBody621_72

def sourceBody621_74 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody621_73 sourceBody621_0

def sourceBody621_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_74 sourceBody621_4

def sourceBody621_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_75 sourceBody621_0

def sourceBody621_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_36 sourceBody621_76

def sourceBody621_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_35 sourceBody621_77

def sourceBody621_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_32 sourceBody621_78

def sourceBody621_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_31 sourceBody621_79

def sourceBody621_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody621_82 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody621_0, 621, 8)) (some 604) ([14]) (some (14, sourceBody621_26, 621, 9))

def sourceBody621_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_82 sourceBody621_4

def sourceBody621_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_83 sourceBody621_0

def sourceBody621_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_81 sourceBody621_84

def sourceBody621_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_80 sourceBody621_85

def sourceBody621_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_30 sourceBody621_86

def sourceBody621_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_87

def sourceBody621_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_88

def sourceBody621_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody621_91 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody621_0, 621, 10)) (some 602) ([6]) (some (6, sourceBody621_10, 621, 11))

def sourceBody621_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_91 sourceBody621_4

def sourceBody621_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_92 sourceBody621_0

def sourceBody621_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_90 sourceBody621_93

def sourceBody621_95 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody621_89 sourceBody621_94

def sourceBody621_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_95 sourceBody621_4

def sourceBody621_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_96 sourceBody621_0

def sourceBody621_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_24 sourceBody621_97

def sourceBody621_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_23 sourceBody621_98

def sourceBody621_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_19 sourceBody621_99

def sourceBody621_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_18 sourceBody621_100

def sourceBody621_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody621_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody621_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody621_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 6) 10

def sourceBody621_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_105 sourceBody621_0

def sourceBody621_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_104 sourceBody621_106

def sourceBody621_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_107 sourceBody621_0

def sourceBody621_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_103 sourceBody621_108

def sourceBody621_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_109

def sourceBody621_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_102 sourceBody621_110

def sourceBody621_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_111

def sourceBody621_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_101 sourceBody621_112

def sourceBody621_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody621_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody621_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_115 sourceBody621_108

def sourceBody621_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_116

def sourceBody621_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_114 sourceBody621_117

def sourceBody621_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_118

def sourceBody621_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_113 sourceBody621_119

def sourceBody621_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody621_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 120#64]))

def sourceBody621_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_122 sourceBody621_108

def sourceBody621_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_123

def sourceBody621_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_121 sourceBody621_124

def sourceBody621_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_125

def sourceBody621_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_120 sourceBody621_126

def sourceBody621_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody621_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 128#64]))

def sourceBody621_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_129 sourceBody621_108

def sourceBody621_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_130

def sourceBody621_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_128 sourceBody621_131

def sourceBody621_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_132

def sourceBody621_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_127 sourceBody621_133

def sourceBody621_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 56#64])

def sourceBody621_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 72#64]))

def sourceBody621_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_136 sourceBody621_108

def sourceBody621_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_137

def sourceBody621_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_135 sourceBody621_138

def sourceBody621_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_139

def sourceBody621_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_134 sourceBody621_140

def sourceBody621_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody621_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 184#64]))

def sourceBody621_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_143 sourceBody621_108

def sourceBody621_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_144

def sourceBody621_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_142 sourceBody621_145

def sourceBody621_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_146

def sourceBody621_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_141 sourceBody621_147

def sourceBody621_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody621_150 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody621_0, 621, 12)) (some 469) ([14]) (some (14, sourceBody621_26, 621, 13))

def sourceBody621_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_150 sourceBody621_4

def sourceBody621_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_151 sourceBody621_0

def sourceBody621_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_149 sourceBody621_152

def sourceBody621_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 72#64])

def sourceBody621_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 200#64])])

def sourceBody621_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_155 sourceBody621_43

def sourceBody621_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_156

def sourceBody621_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_154 sourceBody621_157

def sourceBody621_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_158

def sourceBody621_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody621_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody621_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody621_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_162 sourceBody621_43

def sourceBody621_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_163

def sourceBody621_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_161 sourceBody621_164

def sourceBody621_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_165

def sourceBody621_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody621_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 136#64]))

def sourceBody621_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_168 sourceBody621_43

def sourceBody621_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_169

def sourceBody621_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_167 sourceBody621_170

def sourceBody621_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_171

def sourceBody621_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_166 sourceBody621_172

def sourceBody621_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody621_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody621_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody621_177 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 18 (Flapjack.WordRegImm.reg 4) sourceBody621_176 sourceBody621_32

def sourceBody621_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_177 sourceBody621_4

def sourceBody621_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody621_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_21 sourceBody621_0

def sourceBody621_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_180 sourceBody621_0

def sourceBody621_182 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody621_181 sourceBody621_0

def sourceBody621_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_182 sourceBody621_4

def sourceBody621_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_183 sourceBody621_0

def sourceBody621_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_179 sourceBody621_184

def sourceBody621_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_178 sourceBody621_185

def sourceBody621_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_175 sourceBody621_186

def sourceBody621_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_24 sourceBody621_187

def sourceBody621_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody621_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 18)

def sourceBody621_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 4

def sourceBody621_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_191 sourceBody621_0

def sourceBody621_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_190 sourceBody621_192

def sourceBody621_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_193 sourceBody621_0

def sourceBody621_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_24 sourceBody621_194

def sourceBody621_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_195

def sourceBody621_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_189 sourceBody621_196

def sourceBody621_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_197

def sourceBody621_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_188 sourceBody621_198

def sourceBody621_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_174 sourceBody621_199

def sourceBody621_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_200

def sourceBody621_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_173 sourceBody621_201

def sourceBody621_203 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody621_202 sourceBody621_0

def sourceBody621_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_203 sourceBody621_4

def sourceBody621_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_204 sourceBody621_0

def sourceBody621_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_36 sourceBody621_205

def sourceBody621_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_35 sourceBody621_206

def sourceBody621_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_32 sourceBody621_207

def sourceBody621_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_160 sourceBody621_208

def sourceBody621_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_159 sourceBody621_209

def sourceBody621_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 80#64])

def sourceBody621_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 208#64]))

def sourceBody621_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_212 sourceBody621_43

def sourceBody621_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_213

def sourceBody621_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_211 sourceBody621_214

def sourceBody621_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_215

def sourceBody621_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_210 sourceBody621_216

def sourceBody621_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 88#64])

def sourceBody621_219 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 224#64]))

def sourceBody621_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_219 sourceBody621_43

def sourceBody621_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_220

def sourceBody621_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_218 sourceBody621_221

def sourceBody621_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_222

def sourceBody621_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_217 sourceBody621_223

def sourceBody621_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_224 sourceBody621_72

def sourceBody621_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_153 sourceBody621_225

def sourceBody621_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_226

def sourceBody621_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_227

def sourceBody621_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_148 sourceBody621_228

def sourceBody621_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_229

def sourceBody621_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_230

def sourceBody621_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_17 sourceBody621_231

def sourceBody621_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_7 sourceBody621_232

def sourceBody621_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_233

def sourceBody621_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody621_0 sourceBody621_234

def source621 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (621, 2, sourceBody621_235)
end InitECandidate.Proofs.WordStages
