import InitECandidate.Proofs.WordStages.Source600
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody616_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody616_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody616_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 4)

def sourceBody616_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 6)

def sourceBody616_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 8)

def sourceBody616_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody616_6 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody616_0, 616, 2)) (some 102) ([24, 34, 20, 32]) (some (24, sourceBody616_5, 616, 3))

def sourceBody616_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody616_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_6 sourceBody616_7

def sourceBody616_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_8 sourceBody616_0

def sourceBody616_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_4 sourceBody616_9

def sourceBody616_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_3 sourceBody616_10

def sourceBody616_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_2 sourceBody616_11

def sourceBody616_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_1 sourceBody616_12

def sourceBody616_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody616_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 30)

def sourceBody616_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody616_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody616_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody616_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 20 (Flapjack.WordRegImm.reg 32) sourceBody616_17 sourceBody616_18

def sourceBody616_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_19 sourceBody616_7

def sourceBody616_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 20)

def sourceBody616_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 2300#64)

def sourceBody616_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_22 sourceBody616_0

def sourceBody616_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_23 sourceBody616_0

def sourceBody616_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody616_24 sourceBody616_0

def sourceBody616_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_25 sourceBody616_7

def sourceBody616_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_26 sourceBody616_0

def sourceBody616_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_21 sourceBody616_27

def sourceBody616_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_20 sourceBody616_28

def sourceBody616_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_16 sourceBody616_29

def sourceBody616_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_15 sourceBody616_30

def sourceBody616_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody616_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 14)

def sourceBody616_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody616_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody616_0, 616, 4)) (some 459) ([20, 32]) (some (20, sourceBody616_34, 616, 5))

def sourceBody616_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_35 sourceBody616_7

def sourceBody616_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_36 sourceBody616_0

def sourceBody616_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_33 sourceBody616_37

def sourceBody616_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_32 sourceBody616_38

def sourceBody616_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 12)

def sourceBody616_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 34)

def sourceBody616_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody616_43 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 32 (Flapjack.WordRegImm.reg 26) sourceBody616_42 sourceBody616_16

def sourceBody616_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_43 sourceBody616_7

def sourceBody616_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 32)

def sourceBody616_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody616_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 16)

def sourceBody616_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody616_49 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody616_0, 616, 6)) (some 459) ([32, 26]) (some (32, sourceBody616_48, 616, 7))

def sourceBody616_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_49 sourceBody616_7

def sourceBody616_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_50 sourceBody616_0

def sourceBody616_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_47 sourceBody616_51

def sourceBody616_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_46 sourceBody616_52

def sourceBody616_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody616_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 24)

def sourceBody616_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody616_57 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody616_0, 616, 8)) (some 459) ([26, 36]) (some (26, sourceBody616_56, 616, 9))

def sourceBody616_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_57 sourceBody616_7

def sourceBody616_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_58 sourceBody616_0

def sourceBody616_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_55 sourceBody616_59

def sourceBody616_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_54 sourceBody616_60

def sourceBody616_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26, 36]

def sourceBody616_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_62 sourceBody616_0

def sourceBody616_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_45 sourceBody616_63

def sourceBody616_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_21 sourceBody616_64

def sourceBody616_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_61 sourceBody616_65

def sourceBody616_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_0 sourceBody616_66

def sourceBody616_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_0 sourceBody616_67

def sourceBody616_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_53 sourceBody616_68

def sourceBody616_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_0 sourceBody616_69

def sourceBody616_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_0 sourceBody616_70

def sourceBody616_72 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody616_71 sourceBody616_0

def sourceBody616_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_72 sourceBody616_7

def sourceBody616_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_73 sourceBody616_0

def sourceBody616_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_45 sourceBody616_74

def sourceBody616_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_44 sourceBody616_75

def sourceBody616_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_41 sourceBody616_76

def sourceBody616_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_40 sourceBody616_77

def sourceBody616_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.var 14],
      Flapjack.WordLangExpHOL.var 16])

def sourceBody616_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.var 20,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 20)
        (Flapjack.WordLangExpHOL.const 6#64)])

def sourceBody616_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 32)

def sourceBody616_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 26)

def sourceBody616_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody616_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody616_85 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 18 (Flapjack.WordRegImm.reg 28) sourceBody616_83 sourceBody616_84

def sourceBody616_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_85 sourceBody616_7

def sourceBody616_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody616_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 32)

def sourceBody616_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_88 sourceBody616_0

def sourceBody616_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_89 sourceBody616_0

def sourceBody616_91 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody616_90 sourceBody616_0

def sourceBody616_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_91 sourceBody616_7

def sourceBody616_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_92 sourceBody616_0

def sourceBody616_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_87 sourceBody616_93

def sourceBody616_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_86 sourceBody616_94

def sourceBody616_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_82 sourceBody616_95

def sourceBody616_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_81 sourceBody616_96

def sourceBody616_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.var 16])

def sourceBody616_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.var 24])

def sourceBody616_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [36, 18]

def sourceBody616_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_100 sourceBody616_0

def sourceBody616_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_99 sourceBody616_101

def sourceBody616_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_98 sourceBody616_102

def sourceBody616_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_97 sourceBody616_103

def sourceBody616_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_54 sourceBody616_104

def sourceBody616_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_0 sourceBody616_105

def sourceBody616_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_80 sourceBody616_106

def sourceBody616_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_0 sourceBody616_107

def sourceBody616_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_79 sourceBody616_108

def sourceBody616_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_0 sourceBody616_109

def sourceBody616_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_78 sourceBody616_110

def sourceBody616_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_39 sourceBody616_111

def sourceBody616_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_0 sourceBody616_112

def sourceBody616_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_0 sourceBody616_113

def sourceBody616_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_31 sourceBody616_114

def sourceBody616_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_14 sourceBody616_115

def sourceBody616_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_0 sourceBody616_116

def sourceBody616_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_13 sourceBody616_117

def sourceBody616_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_0 sourceBody616_118

def sourceBody616_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody616_0 sourceBody616_119

def source616 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (616, 9, sourceBody616_120)
end InitECandidate.Proofs.WordStages
