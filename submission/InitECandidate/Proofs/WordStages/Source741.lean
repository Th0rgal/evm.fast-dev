import InitECandidate.Proofs.WordStages.Source725
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody741_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody741_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 2))

def sourceBody741_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody741_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody741_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody741_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody741_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody741_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 14)

def sourceBody741_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 34)

def sourceBody741_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 8)

def sourceBody741_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 28)

def sourceBody741_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 20)

def sourceBody741_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 40)

def sourceBody741_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody741_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody741_0, 741, 2)) (some 719) ([26, 18, 38, 12, 32, 22]) (some (26, sourceBody741_13, 741, 3))

def sourceBody741_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody741_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_14 sourceBody741_15

def sourceBody741_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_16 sourceBody741_0

def sourceBody741_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_12 sourceBody741_17

def sourceBody741_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_11 sourceBody741_18

def sourceBody741_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_10 sourceBody741_19

def sourceBody741_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_9 sourceBody741_20

def sourceBody741_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_8 sourceBody741_21

def sourceBody741_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_7 sourceBody741_22

def sourceBody741_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody741_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody741_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody741_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody741_28 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 18 (Flapjack.WordRegImm.reg 38) sourceBody741_26 sourceBody741_27

def sourceBody741_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_28 sourceBody741_15

def sourceBody741_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody741_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody741_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody741_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_32 sourceBody741_0

def sourceBody741_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_31 sourceBody741_33

def sourceBody741_35 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody741_34 sourceBody741_0

def sourceBody741_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_35 sourceBody741_15

def sourceBody741_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_36 sourceBody741_0

def sourceBody741_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_30 sourceBody741_37

def sourceBody741_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_29 sourceBody741_38

def sourceBody741_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_25 sourceBody741_39

def sourceBody741_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_24 sourceBody741_40

def sourceBody741_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody741_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 34)

def sourceBody741_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody741_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 28)

def sourceBody741_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 20)

def sourceBody741_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 40)

def sourceBody741_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody741_49 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody741_0, 741, 4)) (some 701) ([18, 38, 12, 32, 22, 42]) (some (18, sourceBody741_48, 741, 5))

def sourceBody741_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_49 sourceBody741_15

def sourceBody741_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_50 sourceBody741_0

def sourceBody741_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_47 sourceBody741_51

def sourceBody741_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_46 sourceBody741_52

def sourceBody741_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_45 sourceBody741_53

def sourceBody741_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_44 sourceBody741_54

def sourceBody741_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_43 sourceBody741_55

def sourceBody741_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_42 sourceBody741_56

def sourceBody741_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 26)

def sourceBody741_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody741_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody741_61 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 38 (Flapjack.WordRegImm.reg 12) sourceBody741_25 sourceBody741_60

def sourceBody741_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_61 sourceBody741_15

def sourceBody741_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 38)

def sourceBody741_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody741_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_64 sourceBody741_0

def sourceBody741_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_27 sourceBody741_65

def sourceBody741_67 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody741_66 sourceBody741_0

def sourceBody741_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_67 sourceBody741_15

def sourceBody741_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_68 sourceBody741_0

def sourceBody741_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_63 sourceBody741_69

def sourceBody741_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_62 sourceBody741_70

def sourceBody741_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_59 sourceBody741_71

def sourceBody741_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_58 sourceBody741_72

def sourceBody741_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody741_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody741_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody741_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody741_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody741_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody741_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 18)

def sourceBody741_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 38)

def sourceBody741_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody741_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 32)

def sourceBody741_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 22)

def sourceBody741_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 42)

def sourceBody741_86 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 719) ([0, 4, 24, 16, 36, 10, 30]) (none)

def sourceBody741_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_86 sourceBody741_0

def sourceBody741_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_85 sourceBody741_87

def sourceBody741_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_84 sourceBody741_88

def sourceBody741_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_83 sourceBody741_89

def sourceBody741_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_82 sourceBody741_90

def sourceBody741_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_81 sourceBody741_91

def sourceBody741_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_80 sourceBody741_92

def sourceBody741_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_79 sourceBody741_93

def sourceBody741_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_0 sourceBody741_94

def sourceBody741_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_78 sourceBody741_95

def sourceBody741_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_0 sourceBody741_96

def sourceBody741_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_77 sourceBody741_97

def sourceBody741_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_0 sourceBody741_98

def sourceBody741_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_76 sourceBody741_99

def sourceBody741_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_0 sourceBody741_100

def sourceBody741_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_75 sourceBody741_101

def sourceBody741_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_0 sourceBody741_102

def sourceBody741_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_74 sourceBody741_103

def sourceBody741_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_0 sourceBody741_104

def sourceBody741_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_73 sourceBody741_105

def sourceBody741_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_57 sourceBody741_106

def sourceBody741_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_0 sourceBody741_107

def sourceBody741_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_0 sourceBody741_108

def sourceBody741_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_41 sourceBody741_109

def sourceBody741_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_23 sourceBody741_110

def sourceBody741_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_0 sourceBody741_111

def sourceBody741_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_0 sourceBody741_112

def sourceBody741_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_6 sourceBody741_113

def sourceBody741_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_0 sourceBody741_114

def sourceBody741_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_5 sourceBody741_115

def sourceBody741_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_0 sourceBody741_116

def sourceBody741_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_4 sourceBody741_117

def sourceBody741_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_0 sourceBody741_118

def sourceBody741_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_3 sourceBody741_119

def sourceBody741_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_0 sourceBody741_120

def sourceBody741_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_2 sourceBody741_121

def sourceBody741_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_0 sourceBody741_122

def sourceBody741_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_1 sourceBody741_123

def sourceBody741_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody741_0 sourceBody741_124

def source741 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (741, 2, sourceBody741_125)
end InitECandidate.Proofs.WordStages
