import InitECandidate.Proofs.WordStages.Source795
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody811_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody811_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody811_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody811_0, 811, 2)) (some 69) ([]) (some (10, sourceBody811_1, 811, 3))

def sourceBody811_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody811_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_2 sourceBody811_3

def sourceBody811_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_4 sourceBody811_0

def sourceBody811_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 48#64)

def sourceBody811_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody811_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody811_0, 811, 4)) (some 68) ([28]) (some (28, sourceBody811_7, 811, 5))

def sourceBody811_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_8 sourceBody811_3

def sourceBody811_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_9 sourceBody811_0

def sourceBody811_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_6 sourceBody811_10

def sourceBody811_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 144#64)

def sourceBody811_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody811_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody811_0, 811, 6)) (some 68) ([20]) (some (20, sourceBody811_13, 811, 7))

def sourceBody811_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_14 sourceBody811_3

def sourceBody811_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_15 sourceBody811_0

def sourceBody811_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_12 sourceBody811_16

def sourceBody811_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 2)

def sourceBody811_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody811_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody811_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody811_0, 811, 8)) (some 723) ([38, 8]) (some (38, sourceBody811_20, 811, 9))

def sourceBody811_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_21 sourceBody811_3

def sourceBody811_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_22 sourceBody811_0

def sourceBody811_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_19 sourceBody811_23

def sourceBody811_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_18 sourceBody811_24

def sourceBody811_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 20)

def sourceBody811_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody811_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody811_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody811_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 8 (Flapjack.WordRegImm.reg 26) sourceBody811_28 sourceBody811_29

def sourceBody811_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_30 sourceBody811_3

def sourceBody811_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody811_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 32)

def sourceBody811_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody811_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody811_0, 811, 10)) (some 70) ([8]) (some (8, sourceBody811_34, 811, 11))

def sourceBody811_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_35 sourceBody811_3

def sourceBody811_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_36 sourceBody811_0

def sourceBody811_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_33 sourceBody811_37

def sourceBody811_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_38

def sourceBody811_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_39

def sourceBody811_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody811_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [38]

def sourceBody811_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_42 sourceBody811_0

def sourceBody811_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_41 sourceBody811_43

def sourceBody811_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_40 sourceBody811_44

def sourceBody811_46 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody811_45 sourceBody811_0

def sourceBody811_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_46 sourceBody811_3

def sourceBody811_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_47 sourceBody811_0

def sourceBody811_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_32 sourceBody811_48

def sourceBody811_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_31 sourceBody811_49

def sourceBody811_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_27 sourceBody811_50

def sourceBody811_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_26 sourceBody811_51

def sourceBody811_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 10))

def sourceBody811_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody811_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody811_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody811_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody811_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody811_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 28)

def sourceBody811_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 38)

def sourceBody811_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody811_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody811_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody811_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 36)

def sourceBody811_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody811_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody811_67 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody811_0, 811, 12)) (some 795) ([22, 40, 6, 24, 16, 34, 12]) (some (22, sourceBody811_66, 811, 13))

def sourceBody811_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_67 sourceBody811_3

def sourceBody811_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_68 sourceBody811_0

def sourceBody811_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_65 sourceBody811_69

def sourceBody811_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_64 sourceBody811_70

def sourceBody811_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_63 sourceBody811_71

def sourceBody811_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_62 sourceBody811_72

def sourceBody811_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_61 sourceBody811_73

def sourceBody811_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_60 sourceBody811_74

def sourceBody811_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_59 sourceBody811_75

def sourceBody811_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_76

def sourceBody811_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_77

def sourceBody811_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 4)

def sourceBody811_80 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody811_0, 811, 14)) (some 772) ([22, 40]) (some (22, sourceBody811_66, 811, 15))

def sourceBody811_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_80 sourceBody811_3

def sourceBody811_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_81 sourceBody811_0

def sourceBody811_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_79 sourceBody811_82

def sourceBody811_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_59 sourceBody811_83

def sourceBody811_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_84

def sourceBody811_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_85

def sourceBody811_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_78 sourceBody811_86

def sourceBody811_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 32)

def sourceBody811_89 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody811_0, 811, 16)) (some 70) ([22]) (some (22, sourceBody811_66, 811, 17))

def sourceBody811_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_89 sourceBody811_3

def sourceBody811_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_90 sourceBody811_0

def sourceBody811_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_88 sourceBody811_91

def sourceBody811_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_92

def sourceBody811_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_93

def sourceBody811_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_87 sourceBody811_94

def sourceBody811_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody811_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30]

def sourceBody811_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_97 sourceBody811_0

def sourceBody811_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_96 sourceBody811_98

def sourceBody811_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_95 sourceBody811_99

def sourceBody811_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_58 sourceBody811_100

def sourceBody811_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_101

def sourceBody811_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_57 sourceBody811_102

def sourceBody811_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_103

def sourceBody811_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_56 sourceBody811_104

def sourceBody811_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_105

def sourceBody811_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_55 sourceBody811_106

def sourceBody811_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_107

def sourceBody811_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_54 sourceBody811_108

def sourceBody811_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_109

def sourceBody811_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_53 sourceBody811_110

def sourceBody811_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_111

def sourceBody811_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_52 sourceBody811_112

def sourceBody811_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_25 sourceBody811_113

def sourceBody811_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_114

def sourceBody811_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_115

def sourceBody811_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_17 sourceBody811_116

def sourceBody811_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_117

def sourceBody811_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_118

def sourceBody811_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_11 sourceBody811_119

def sourceBody811_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_120

def sourceBody811_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_121

def sourceBody811_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_5 sourceBody811_122

def sourceBody811_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_123

def sourceBody811_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody811_0 sourceBody811_124

def source811 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (811, 3, sourceBody811_125)
end InitECandidate.Proofs.WordStages
