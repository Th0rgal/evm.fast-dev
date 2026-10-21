import InitECandidate.Proofs.WordStages.Source679
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody695_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody695_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody695_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody695_0, 695, 2)) (some 69) ([]) (some (10, sourceBody695_1, 695, 3))

def sourceBody695_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody695_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_2 sourceBody695_3

def sourceBody695_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_4 sourceBody695_0

def sourceBody695_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody695_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody695_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody695_0, 695, 4)) (some 68) ([24]) (some (24, sourceBody695_7, 695, 5))

def sourceBody695_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_8 sourceBody695_3

def sourceBody695_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_9 sourceBody695_0

def sourceBody695_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_6 sourceBody695_10

def sourceBody695_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody695_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody695_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody695_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody695_0, 695, 6)) (some 691) ([16, 32]) (some (16, sourceBody695_14, 695, 7))

def sourceBody695_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_15 sourceBody695_3

def sourceBody695_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_16 sourceBody695_0

def sourceBody695_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_13 sourceBody695_17

def sourceBody695_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_12 sourceBody695_18

def sourceBody695_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 24)

def sourceBody695_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody695_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody695_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody695_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.reg 8) sourceBody695_22 sourceBody695_23

def sourceBody695_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_24 sourceBody695_3

def sourceBody695_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 32)

def sourceBody695_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 28)

def sourceBody695_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody695_29 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody695_0, 695, 8)) (some 70) ([32]) (some (32, sourceBody695_28, 695, 9))

def sourceBody695_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_29 sourceBody695_3

def sourceBody695_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_30 sourceBody695_0

def sourceBody695_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_27 sourceBody695_31

def sourceBody695_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_32

def sourceBody695_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_33

def sourceBody695_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody695_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody695_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_36 sourceBody695_0

def sourceBody695_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_35 sourceBody695_37

def sourceBody695_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_34 sourceBody695_38

def sourceBody695_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody695_39 sourceBody695_0

def sourceBody695_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_40 sourceBody695_3

def sourceBody695_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_41 sourceBody695_0

def sourceBody695_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_26 sourceBody695_42

def sourceBody695_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_25 sourceBody695_43

def sourceBody695_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_21 sourceBody695_44

def sourceBody695_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_20 sourceBody695_45

def sourceBody695_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody695_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody695_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody695_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 32, 8, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody695_0, 695, 10)) (some 146) ([14, 30]) (some (14, sourceBody695_49, 695, 11))

def sourceBody695_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_50 sourceBody695_3

def sourceBody695_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_51 sourceBody695_0

def sourceBody695_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_48 sourceBody695_52

def sourceBody695_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_47 sourceBody695_53

def sourceBody695_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody695_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody695_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody695_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody695_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 32)

def sourceBody695_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody695_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 22)

def sourceBody695_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody695_63 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody695_0, 695, 12)) (some 680) ([30, 12, 26, 18, 34, 6, 20]) (some (30, sourceBody695_62, 695, 13))

def sourceBody695_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_63 sourceBody695_3

def sourceBody695_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_64 sourceBody695_0

def sourceBody695_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_61 sourceBody695_65

def sourceBody695_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_60 sourceBody695_66

def sourceBody695_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_59 sourceBody695_67

def sourceBody695_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_58 sourceBody695_68

def sourceBody695_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_57 sourceBody695_69

def sourceBody695_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_56 sourceBody695_70

def sourceBody695_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_55 sourceBody695_71

def sourceBody695_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_72

def sourceBody695_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_73

def sourceBody695_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 10)

def sourceBody695_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody695_77 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody695_0, 695, 14)) (some 693) ([30, 12]) (some (30, sourceBody695_62, 695, 15))

def sourceBody695_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_77 sourceBody695_3

def sourceBody695_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_78 sourceBody695_0

def sourceBody695_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_76 sourceBody695_79

def sourceBody695_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_75 sourceBody695_80

def sourceBody695_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_81

def sourceBody695_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_82

def sourceBody695_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_74 sourceBody695_83

def sourceBody695_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 28)

def sourceBody695_86 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody695_0, 695, 16)) (some 70) ([30]) (some (30, sourceBody695_62, 695, 17))

def sourceBody695_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_86 sourceBody695_3

def sourceBody695_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_87 sourceBody695_0

def sourceBody695_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_85 sourceBody695_88

def sourceBody695_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_89

def sourceBody695_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_90

def sourceBody695_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_84 sourceBody695_91

def sourceBody695_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody695_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody695_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_94 sourceBody695_0

def sourceBody695_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_93 sourceBody695_95

def sourceBody695_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_92 sourceBody695_96

def sourceBody695_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_54 sourceBody695_97

def sourceBody695_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_98

def sourceBody695_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_99

def sourceBody695_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_100

def sourceBody695_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_101

def sourceBody695_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_102

def sourceBody695_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_103

def sourceBody695_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_104

def sourceBody695_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_105

def sourceBody695_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_46 sourceBody695_106

def sourceBody695_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_19 sourceBody695_107

def sourceBody695_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_108

def sourceBody695_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_109

def sourceBody695_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_11 sourceBody695_110

def sourceBody695_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_111

def sourceBody695_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_112

def sourceBody695_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_5 sourceBody695_113

def sourceBody695_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_114

def sourceBody695_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody695_0 sourceBody695_115

def source695 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (695, 3, sourceBody695_116)
end InitECandidate.Proofs.WordStages
