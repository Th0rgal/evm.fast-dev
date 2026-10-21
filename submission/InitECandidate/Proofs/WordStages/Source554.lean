import InitECandidate.Proofs.WordStages.Source538
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody554_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody554_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody554_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 28, 6, 24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody554_0, 554, 2)) (some 471) ([]) (some (16, sourceBody554_1, 554, 3))

def sourceBody554_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody554_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_2 sourceBody554_3

def sourceBody554_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_4 sourceBody554_0

def sourceBody554_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody554_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody554_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody554_0, 554, 4)) (some 466) ([32]) (some (32, sourceBody554_7, 554, 5))

def sourceBody554_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_8 sourceBody554_3

def sourceBody554_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_9 sourceBody554_0

def sourceBody554_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_6 sourceBody554_10

def sourceBody554_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_11

def sourceBody554_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_12

def sourceBody554_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody554_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody554_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 28)

def sourceBody554_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody554_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 24)

def sourceBody554_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody554_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody554_0, 554, 6)) (some 458) ([4, 22, 14, 30]) (some (4, sourceBody554_19, 554, 7))

def sourceBody554_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_20 sourceBody554_3

def sourceBody554_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_21 sourceBody554_0

def sourceBody554_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_18 sourceBody554_22

def sourceBody554_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_17 sourceBody554_23

def sourceBody554_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_16 sourceBody554_24

def sourceBody554_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_15 sourceBody554_25

def sourceBody554_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody554_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody554_0, 554, 8)) (some 69) ([]) (some (22, sourceBody554_27, 554, 9))

def sourceBody554_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_28 sourceBody554_3

def sourceBody554_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_29 sourceBody554_0

def sourceBody554_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody554_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody554_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody554_0, 554, 10)) (some 68) ([14]) (some (14, sourceBody554_32, 554, 11))

def sourceBody554_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_33 sourceBody554_3

def sourceBody554_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_34 sourceBody554_0

def sourceBody554_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_31 sourceBody554_35

def sourceBody554_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody554_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody554_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 32)

def sourceBody554_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody554_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 22)

def sourceBody554_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody554_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody554_0, 554, 12)) (some 480) ([30, 8, 26, 18, 34]) (some (30, sourceBody554_42, 554, 13))

def sourceBody554_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_43 sourceBody554_3

def sourceBody554_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_44 sourceBody554_0

def sourceBody554_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_41 sourceBody554_45

def sourceBody554_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_40 sourceBody554_46

def sourceBody554_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_39 sourceBody554_47

def sourceBody554_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_38 sourceBody554_48

def sourceBody554_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_37 sourceBody554_49

def sourceBody554_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_50

def sourceBody554_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_51

def sourceBody554_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 22)

def sourceBody554_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody554_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody554_56 : WordLangProgHOL (BitVec 64) :=
.call (some (([14, 30, 8, 26]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody554_0, 554, 14)) (some 146) ([18, 34]) (some (18, sourceBody554_55, 554, 15))

def sourceBody554_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_56 sourceBody554_3

def sourceBody554_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_57 sourceBody554_0

def sourceBody554_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_54 sourceBody554_58

def sourceBody554_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_53 sourceBody554_59

def sourceBody554_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 4)

def sourceBody554_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody554_63 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody554_0, 554, 16)) (some 70) ([34]) (some (34, sourceBody554_62, 554, 17))

def sourceBody554_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_63 sourceBody554_3

def sourceBody554_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_64 sourceBody554_0

def sourceBody554_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_61 sourceBody554_65

def sourceBody554_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_66

def sourceBody554_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_67

def sourceBody554_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 14)

def sourceBody554_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 30)

def sourceBody554_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody554_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 26)

def sourceBody554_73 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody554_0, 554, 18)) (some 472) ([34, 2, 20, 12]) (some (34, sourceBody554_62, 554, 19))

def sourceBody554_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_73 sourceBody554_3

def sourceBody554_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_74 sourceBody554_0

def sourceBody554_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_72 sourceBody554_75

def sourceBody554_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_71 sourceBody554_76

def sourceBody554_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_70 sourceBody554_77

def sourceBody554_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_69 sourceBody554_78

def sourceBody554_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_79

def sourceBody554_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_80

def sourceBody554_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_68 sourceBody554_81

def sourceBody554_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody554_84 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody554_0, 554, 20)) (some 486) ([34]) (some (34, sourceBody554_62, 554, 21))

def sourceBody554_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_84 sourceBody554_3

def sourceBody554_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_85 sourceBody554_0

def sourceBody554_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_83 sourceBody554_86

def sourceBody554_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_87

def sourceBody554_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_88

def sourceBody554_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_82 sourceBody554_89

def sourceBody554_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody554_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody554_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_92 sourceBody554_0

def sourceBody554_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_91 sourceBody554_93

def sourceBody554_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_90 sourceBody554_94

def sourceBody554_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_60 sourceBody554_95

def sourceBody554_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_96

def sourceBody554_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_97

def sourceBody554_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_98

def sourceBody554_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_99

def sourceBody554_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_100

def sourceBody554_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_101

def sourceBody554_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_102

def sourceBody554_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_103

def sourceBody554_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_52 sourceBody554_104

def sourceBody554_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_36 sourceBody554_105

def sourceBody554_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_106

def sourceBody554_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_107

def sourceBody554_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_30 sourceBody554_108

def sourceBody554_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_109

def sourceBody554_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_110

def sourceBody554_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_26 sourceBody554_111

def sourceBody554_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_112

def sourceBody554_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_113

def sourceBody554_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_14 sourceBody554_114

def sourceBody554_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_115

def sourceBody554_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_13 sourceBody554_116

def sourceBody554_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_5 sourceBody554_117

def sourceBody554_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_118

def sourceBody554_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_119

def sourceBody554_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_120

def sourceBody554_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_121

def sourceBody554_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_122

def sourceBody554_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_123

def sourceBody554_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_124

def sourceBody554_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody554_0 sourceBody554_125

def source554 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (554, 1, sourceBody554_126)
end InitECandidate.Proofs.WordStages
