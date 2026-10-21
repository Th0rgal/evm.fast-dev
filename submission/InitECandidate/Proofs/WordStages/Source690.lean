import InitECandidate.Proofs.WordStages.Source674
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody690_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody690_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody690_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody690_0, 690, 2)) (some 653) ([]) (some (22, sourceBody690_1, 690, 3))

def sourceBody690_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody690_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_2 sourceBody690_3

def sourceBody690_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_4 sourceBody690_0

def sourceBody690_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_5

def sourceBody690_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_6

def sourceBody690_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody690_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody690_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody690_0, 690, 4)) (some 677) ([22, 16]) (some (22, sourceBody690_1, 690, 5))

def sourceBody690_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_10 sourceBody690_3

def sourceBody690_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_11 sourceBody690_0

def sourceBody690_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_9 sourceBody690_12

def sourceBody690_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_8 sourceBody690_13

def sourceBody690_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody690_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 6)

def sourceBody690_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody690_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody690_0, 690, 6)) (some 677) ([16, 28]) (some (16, sourceBody690_17, 690, 7))

def sourceBody690_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_18 sourceBody690_3

def sourceBody690_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_19 sourceBody690_0

def sourceBody690_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_16 sourceBody690_20

def sourceBody690_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_15 sourceBody690_21

def sourceBody690_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 22])

def sourceBody690_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody690_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody690_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody690_27 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 28 (Flapjack.WordRegImm.reg 8) sourceBody690_25 sourceBody690_26

def sourceBody690_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_27 sourceBody690_3

def sourceBody690_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 28)

def sourceBody690_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody690_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody690_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody690_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody690_0, 690, 8)) (some 675) ([28, 8]) (some (28, sourceBody690_32, 690, 9))

def sourceBody690_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_33 sourceBody690_3

def sourceBody690_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_34 sourceBody690_0

def sourceBody690_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_31 sourceBody690_35

def sourceBody690_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_30 sourceBody690_36

def sourceBody690_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_37

def sourceBody690_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_38

def sourceBody690_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody690_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody690_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_41 sourceBody690_0

def sourceBody690_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_40 sourceBody690_42

def sourceBody690_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_39 sourceBody690_43

def sourceBody690_45 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody690_44 sourceBody690_0

def sourceBody690_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_45 sourceBody690_3

def sourceBody690_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_46 sourceBody690_0

def sourceBody690_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_29 sourceBody690_47

def sourceBody690_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_28 sourceBody690_48

def sourceBody690_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_24 sourceBody690_49

def sourceBody690_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_23 sourceBody690_50

def sourceBody690_52 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody690_0, 690, 10)) (some 69) ([]) (some (28, sourceBody690_32, 690, 11))

def sourceBody690_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_52 sourceBody690_3

def sourceBody690_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_53 sourceBody690_0

def sourceBody690_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1152#64)

def sourceBody690_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody690_57 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody690_0, 690, 12)) (some 68) ([8]) (some (8, sourceBody690_56, 690, 13))

def sourceBody690_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_57 sourceBody690_3

def sourceBody690_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_58 sourceBody690_0

def sourceBody690_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_55 sourceBody690_59

def sourceBody690_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1152#64)

def sourceBody690_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody690_63 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody690_0, 690, 14)) (some 68) ([20]) (some (20, sourceBody690_62, 690, 15))

def sourceBody690_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_63 sourceBody690_3

def sourceBody690_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_64 sourceBody690_0

def sourceBody690_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_61 sourceBody690_65

def sourceBody690_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 384#64)

def sourceBody690_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody690_69 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody690_0, 690, 16)) (some 68) ([14]) (some (14, sourceBody690_68, 690, 17))

def sourceBody690_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_69 sourceBody690_3

def sourceBody690_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_70 sourceBody690_0

def sourceBody690_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_67 sourceBody690_71

def sourceBody690_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 384#64)

def sourceBody690_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody690_75 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody690_0, 690, 18)) (some 68) ([26]) (some (26, sourceBody690_74, 690, 19))

def sourceBody690_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_75 sourceBody690_3

def sourceBody690_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_76 sourceBody690_0

def sourceBody690_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_73 sourceBody690_77

def sourceBody690_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 28)

def sourceBody690_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody690_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody690_82 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody690_0, 690, 20)) (some 682) ([12, 24]) (some (12, sourceBody690_81, 690, 21))

def sourceBody690_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_82 sourceBody690_3

def sourceBody690_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_83 sourceBody690_0

def sourceBody690_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_80 sourceBody690_84

def sourceBody690_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_79 sourceBody690_85

def sourceBody690_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_86

def sourceBody690_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_87

def sourceBody690_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody690_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 6)

def sourceBody690_91 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody690_0, 690, 22)) (some 683) ([12, 24]) (some (12, sourceBody690_81, 690, 23))

def sourceBody690_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_91 sourceBody690_3

def sourceBody690_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_92 sourceBody690_0

def sourceBody690_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_90 sourceBody690_93

def sourceBody690_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_89 sourceBody690_94

def sourceBody690_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_95

def sourceBody690_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_96

def sourceBody690_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_88 sourceBody690_97

def sourceBody690_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 20)

def sourceBody690_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody690_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody690_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 8)

def sourceBody690_103 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody690_0, 690, 24)) (some 689) ([12, 24, 18, 30]) (some (12, sourceBody690_81, 690, 25))

def sourceBody690_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_103 sourceBody690_3

def sourceBody690_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_104 sourceBody690_0

def sourceBody690_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_102 sourceBody690_105

def sourceBody690_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_101 sourceBody690_106

def sourceBody690_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_100 sourceBody690_107

def sourceBody690_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_99 sourceBody690_108

def sourceBody690_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_109

def sourceBody690_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_110

def sourceBody690_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_98 sourceBody690_111

def sourceBody690_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody690_114 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody690_0, 690, 26)) (some 687) ([12, 24]) (some (12, sourceBody690_81, 690, 27))

def sourceBody690_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_114 sourceBody690_3

def sourceBody690_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_115 sourceBody690_0

def sourceBody690_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_100 sourceBody690_116

def sourceBody690_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_113 sourceBody690_117

def sourceBody690_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_118

def sourceBody690_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_119

def sourceBody690_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_112 sourceBody690_120

def sourceBody690_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 20)

def sourceBody690_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody690_124 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody690_0, 690, 28)) (some 664) ([12, 24, 18]) (some (12, sourceBody690_81, 690, 29))

def sourceBody690_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_124 sourceBody690_3

def sourceBody690_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_125 sourceBody690_0

def sourceBody690_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_123 sourceBody690_126

def sourceBody690_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_122 sourceBody690_127

def sourceBody690_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_99 sourceBody690_128

def sourceBody690_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_129

def sourceBody690_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_130

def sourceBody690_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_121 sourceBody690_131

def sourceBody690_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody690_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 384#64]))

def sourceBody690_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 44#64)

def sourceBody690_136 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody690_0, 690, 30)) (some 688) ([12, 24, 18, 30]) (some (12, sourceBody690_81, 690, 31))

def sourceBody690_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_136 sourceBody690_3

def sourceBody690_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_137 sourceBody690_0

def sourceBody690_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_135 sourceBody690_138

def sourceBody690_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_134 sourceBody690_139

def sourceBody690_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_122 sourceBody690_140

def sourceBody690_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_133 sourceBody690_141

def sourceBody690_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_142

def sourceBody690_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_143

def sourceBody690_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_132 sourceBody690_144

def sourceBody690_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody690_147 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody690_0, 690, 32)) (some 70) ([12]) (some (12, sourceBody690_81, 690, 33))

def sourceBody690_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_147 sourceBody690_3

def sourceBody690_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_148 sourceBody690_0

def sourceBody690_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_146 sourceBody690_149

def sourceBody690_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_150

def sourceBody690_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_151

def sourceBody690_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_145 sourceBody690_152

def sourceBody690_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody690_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody690_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_155 sourceBody690_0

def sourceBody690_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_154 sourceBody690_156

def sourceBody690_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_153 sourceBody690_157

def sourceBody690_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_78 sourceBody690_158

def sourceBody690_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_159

def sourceBody690_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_160

def sourceBody690_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_72 sourceBody690_161

def sourceBody690_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_162

def sourceBody690_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_163

def sourceBody690_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_66 sourceBody690_164

def sourceBody690_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_165

def sourceBody690_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_166

def sourceBody690_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_60 sourceBody690_167

def sourceBody690_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_168

def sourceBody690_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_169

def sourceBody690_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_54 sourceBody690_170

def sourceBody690_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_171

def sourceBody690_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_172

def sourceBody690_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_51 sourceBody690_173

def sourceBody690_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_22 sourceBody690_174

def sourceBody690_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_175

def sourceBody690_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_176

def sourceBody690_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_14 sourceBody690_177

def sourceBody690_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_178

def sourceBody690_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_0 sourceBody690_179

def sourceBody690_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody690_7 sourceBody690_180

def source690 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (690, 4, sourceBody690_181)
end InitECandidate.Proofs.WordStages
