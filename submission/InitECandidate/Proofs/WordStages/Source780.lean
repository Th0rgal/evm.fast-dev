import InitECandidate.Proofs.WordStages.Source764
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody780_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody780_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody780_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody780_0, 780, 2)) (some 69) ([]) (some (16, sourceBody780_1, 780, 3))

def sourceBody780_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody780_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_2 sourceBody780_3

def sourceBody780_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_4 sourceBody780_0

def sourceBody780_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody780_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody780_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody780_0, 780, 4)) (some 68) ([26]) (some (26, sourceBody780_7, 780, 5))

def sourceBody780_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_8 sourceBody780_3

def sourceBody780_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_9 sourceBody780_0

def sourceBody780_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_6 sourceBody780_10

def sourceBody780_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody780_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody780_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody780_0, 780, 6)) (some 774) ([10]) (some (10, sourceBody780_13, 780, 7))

def sourceBody780_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_14 sourceBody780_3

def sourceBody780_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_15 sourceBody780_0

def sourceBody780_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_12 sourceBody780_16

def sourceBody780_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_17

def sourceBody780_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_18

def sourceBody780_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
    (Flapjack.WordLangExpHOL.const 6#64))

def sourceBody780_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody780_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody780_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody780_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody780_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 14 (Flapjack.WordRegImm.reg 24) sourceBody780_24 sourceBody780_22

def sourceBody780_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_25 sourceBody780_3

def sourceBody780_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody780_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody780_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 18)

def sourceBody780_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_29 sourceBody780_0

def sourceBody780_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_30 sourceBody780_0

def sourceBody780_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_28 sourceBody780_31

def sourceBody780_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_32

def sourceBody780_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody780_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody780_36 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 24) sourceBody780_24 sourceBody780_22

def sourceBody780_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_36 sourceBody780_3

def sourceBody780_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody780_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody780_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody780_41 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody780_0, 780, 8)) (some 778) ([14, 24]) (some (14, sourceBody780_40, 780, 9))

def sourceBody780_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_41 sourceBody780_3

def sourceBody780_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_42 sourceBody780_0

def sourceBody780_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_39 sourceBody780_43

def sourceBody780_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_38 sourceBody780_44

def sourceBody780_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_45

def sourceBody780_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_46

def sourceBody780_48 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody780_47 sourceBody780_0

def sourceBody780_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_48 sourceBody780_3

def sourceBody780_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_49 sourceBody780_0

def sourceBody780_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_27 sourceBody780_50

def sourceBody780_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_37 sourceBody780_51

def sourceBody780_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_35 sourceBody780_52

def sourceBody780_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_34 sourceBody780_53

def sourceBody780_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_33 sourceBody780_54

def sourceBody780_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
        (Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.var 6,
              Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 26)
                  (Flapjack.WordLangExpHOL.const 6#64))
                (Flapjack.WordLangExpHOL.const 3#64)]))
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
          [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 63#64]),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody780_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody780_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody780_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody780_60 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 12) sourceBody780_35 sourceBody780_59

def sourceBody780_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_60 sourceBody780_3

def sourceBody780_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 24)

def sourceBody780_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody780_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 4)

def sourceBody780_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody780_66 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody780_0, 780, 10)) (some 779) ([24, 12, 22]) (some (24, sourceBody780_65, 780, 11))

def sourceBody780_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_66 sourceBody780_3

def sourceBody780_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_67 sourceBody780_0

def sourceBody780_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_64 sourceBody780_68

def sourceBody780_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_63 sourceBody780_69

def sourceBody780_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_39 sourceBody780_70

def sourceBody780_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_71

def sourceBody780_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_72

def sourceBody780_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody780_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_74 sourceBody780_0

def sourceBody780_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_75 sourceBody780_0

def sourceBody780_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_73 sourceBody780_76

def sourceBody780_78 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody780_77 sourceBody780_0

def sourceBody780_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_78 sourceBody780_3

def sourceBody780_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_79 sourceBody780_0

def sourceBody780_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_62 sourceBody780_80

def sourceBody780_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_61 sourceBody780_81

def sourceBody780_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_58 sourceBody780_82

def sourceBody780_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_57 sourceBody780_83

def sourceBody780_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_56 sourceBody780_84

def sourceBody780_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_85

def sourceBody780_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_55 sourceBody780_86

def sourceBody780_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody780_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_87 sourceBody780_88

def sourceBody780_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody780_91 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody780_89 sourceBody780_90

def sourceBody780_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_91 sourceBody780_3

def sourceBody780_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_92 sourceBody780_0

def sourceBody780_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_27 sourceBody780_93

def sourceBody780_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_26 sourceBody780_94

def sourceBody780_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_23 sourceBody780_95

def sourceBody780_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_22 sourceBody780_96

def sourceBody780_98 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody780_97 (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody780_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_98 sourceBody780_3

def sourceBody780_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_3 sourceBody780_99

def sourceBody780_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody780_102 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody780_0, 780, 12)) (some 776) ([14, 24]) (some (14, sourceBody780_40, 780, 13))

def sourceBody780_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_102 sourceBody780_3

def sourceBody780_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_103 sourceBody780_0

def sourceBody780_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_39 sourceBody780_104

def sourceBody780_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_101 sourceBody780_105

def sourceBody780_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_106

def sourceBody780_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_107

def sourceBody780_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_100 sourceBody780_108

def sourceBody780_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody780_111 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody780_0, 780, 14)) (some 70) ([14]) (some (14, sourceBody780_40, 780, 15))

def sourceBody780_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_111 sourceBody780_3

def sourceBody780_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_112 sourceBody780_0

def sourceBody780_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_110 sourceBody780_113

def sourceBody780_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_114

def sourceBody780_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_115

def sourceBody780_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_109 sourceBody780_116

def sourceBody780_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody780_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody780_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_119 sourceBody780_0

def sourceBody780_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_118 sourceBody780_120

def sourceBody780_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_117 sourceBody780_121

def sourceBody780_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_21 sourceBody780_122

def sourceBody780_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_123

def sourceBody780_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_20 sourceBody780_124

def sourceBody780_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_125

def sourceBody780_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_19 sourceBody780_126

def sourceBody780_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_11 sourceBody780_127

def sourceBody780_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_128

def sourceBody780_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_129

def sourceBody780_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_5 sourceBody780_130

def sourceBody780_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_131

def sourceBody780_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody780_0 sourceBody780_132

def source780 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (780, 5, sourceBody780_133)
end InitECandidate.Proofs.WordStages
