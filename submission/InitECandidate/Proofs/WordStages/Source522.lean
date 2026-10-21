import InitECandidate.Proofs.WordStages.Source506
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody522_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody522_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody522_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 22, 4, 18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody522_0, 522, 2)) (some 471) ([]) (some (12, sourceBody522_1, 522, 3))

def sourceBody522_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody522_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_2 sourceBody522_3

def sourceBody522_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_4 sourceBody522_0

def sourceBody522_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody522_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 26, 2, 16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody522_0, 522, 4)) (some 471) ([]) (some (10, sourceBody522_6, 522, 5))

def sourceBody522_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_7 sourceBody522_3

def sourceBody522_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_8 sourceBody522_0

def sourceBody522_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody522_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody522_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody522_0, 522, 6)) (some 466) ([24]) (some (24, sourceBody522_11, 522, 7))

def sourceBody522_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_12 sourceBody522_3

def sourceBody522_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_13 sourceBody522_0

def sourceBody522_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_10 sourceBody522_14

def sourceBody522_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_15

def sourceBody522_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_16

def sourceBody522_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody522_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 26)

def sourceBody522_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody522_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody522_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody522_0, 522, 8)) (some 102) ([24, 6, 20, 14]) (some (24, sourceBody522_11, 522, 9))

def sourceBody522_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_22 sourceBody522_3

def sourceBody522_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_23 sourceBody522_0

def sourceBody522_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_21 sourceBody522_24

def sourceBody522_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_20 sourceBody522_25

def sourceBody522_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_19 sourceBody522_26

def sourceBody522_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_18 sourceBody522_27

def sourceBody522_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody522_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody522_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody522_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody522_33 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.reg 20) sourceBody522_31 sourceBody522_32

def sourceBody522_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_33 sourceBody522_3

def sourceBody522_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody522_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody522_37 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody522_0, 522, 10)) (some 486) ([6]) (some (6, sourceBody522_36, 522, 11))

def sourceBody522_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_37 sourceBody522_3

def sourceBody522_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_38 sourceBody522_0

def sourceBody522_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_31 sourceBody522_39

def sourceBody522_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_40

def sourceBody522_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_41

def sourceBody522_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody522_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody522_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_44 sourceBody522_0

def sourceBody522_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_43 sourceBody522_45

def sourceBody522_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_42 sourceBody522_46

def sourceBody522_48 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody522_47 sourceBody522_0

def sourceBody522_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_48 sourceBody522_3

def sourceBody522_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_49 sourceBody522_0

def sourceBody522_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_35 sourceBody522_50

def sourceBody522_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_34 sourceBody522_51

def sourceBody522_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_30 sourceBody522_52

def sourceBody522_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_29 sourceBody522_53

def sourceBody522_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody522_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 22)

def sourceBody522_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody522_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 18)

def sourceBody522_59 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody522_0, 522, 12)) (some 482) ([6, 20, 14, 28]) (some (6, sourceBody522_36, 522, 13))

def sourceBody522_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_59 sourceBody522_3

def sourceBody522_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_60 sourceBody522_0

def sourceBody522_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_58 sourceBody522_61

def sourceBody522_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_57 sourceBody522_62

def sourceBody522_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_56 sourceBody522_63

def sourceBody522_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_55 sourceBody522_64

def sourceBody522_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody522_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody522_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody522_69 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 20 (Flapjack.WordRegImm.reg 14) sourceBody522_68 sourceBody522_30

def sourceBody522_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_69 sourceBody522_3

def sourceBody522_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 20)

def sourceBody522_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody522_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 6)

def sourceBody522_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_73 sourceBody522_0

def sourceBody522_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_74 sourceBody522_0

def sourceBody522_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_72 sourceBody522_75

def sourceBody522_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_76

def sourceBody522_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody522_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_78 sourceBody522_36

def sourceBody522_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_77 sourceBody522_79

def sourceBody522_81 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody522_80 sourceBody522_0

def sourceBody522_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_81 sourceBody522_3

def sourceBody522_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_82 sourceBody522_0

def sourceBody522_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_71 sourceBody522_83

def sourceBody522_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_70 sourceBody522_84

def sourceBody522_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_67 sourceBody522_85

def sourceBody522_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_66 sourceBody522_86

def sourceBody522_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 0#64])

def sourceBody522_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody522_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody522_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 6) 14

def sourceBody522_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_91 sourceBody522_0

def sourceBody522_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_90 sourceBody522_92

def sourceBody522_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_93 sourceBody522_0

def sourceBody522_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_89 sourceBody522_94

def sourceBody522_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_95

def sourceBody522_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_88 sourceBody522_96

def sourceBody522_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_97

def sourceBody522_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_87 sourceBody522_98

def sourceBody522_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody522_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_100 sourceBody522_0

def sourceBody522_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_32 sourceBody522_101

def sourceBody522_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_99 sourceBody522_102

def sourceBody522_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_65 sourceBody522_103

def sourceBody522_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_104

def sourceBody522_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_105

def sourceBody522_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_54 sourceBody522_106

def sourceBody522_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_28 sourceBody522_107

def sourceBody522_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_108

def sourceBody522_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_109

def sourceBody522_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_17 sourceBody522_110

def sourceBody522_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_9 sourceBody522_111

def sourceBody522_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_112

def sourceBody522_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_113

def sourceBody522_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_114

def sourceBody522_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_115

def sourceBody522_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_116

def sourceBody522_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_117

def sourceBody522_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_118

def sourceBody522_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_119

def sourceBody522_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_5 sourceBody522_120

def sourceBody522_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_121

def sourceBody522_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_122

def sourceBody522_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_123

def sourceBody522_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_124

def sourceBody522_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_125

def sourceBody522_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_126

def sourceBody522_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_127

def sourceBody522_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody522_0 sourceBody522_128

def source522 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (522, 1, sourceBody522_129)
end InitECandidate.Proofs.WordStages
