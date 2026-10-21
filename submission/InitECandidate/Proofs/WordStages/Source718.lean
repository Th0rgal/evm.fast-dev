import InitECandidate.Proofs.WordStages.Source702
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody718_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody718_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 8505329371266088957#64)

def sourceBody718_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 17002214543764226050#64)

def sourceBody718_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 6865905132761471162#64)

def sourceBody718_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 8632934651105793861#64)

def sourceBody718_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 6631298214892334189#64)

def sourceBody718_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 1582556514881692819#64)

def sourceBody718_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody718_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
    (Flapjack.WordLangExpHOL.const 6#64))

def sourceBody718_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody718_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody718_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 18)

def sourceBody718_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody718_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 28 (Flapjack.WordRegImm.reg 50) sourceBody718_12 sourceBody718_10

def sourceBody718_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_13 sourceBody718_9

def sourceBody718_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 28)

def sourceBody718_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody718_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 38)

def sourceBody718_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_17 sourceBody718_0

def sourceBody718_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_18 sourceBody718_0

def sourceBody718_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_16 sourceBody718_19

def sourceBody718_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_0 sourceBody718_20

def sourceBody718_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 58)

def sourceBody718_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody718_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 28 (Flapjack.WordRegImm.reg 50) sourceBody718_12 sourceBody718_10

def sourceBody718_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_24 sourceBody718_9

def sourceBody718_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 40)

def sourceBody718_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 30)

def sourceBody718_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 52)

def sourceBody718_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 24)

def sourceBody718_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 46)

def sourceBody718_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 36)

def sourceBody718_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 40)

def sourceBody718_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 30)

def sourceBody718_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 52)

def sourceBody718_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 24)

def sourceBody718_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 46)

def sourceBody718_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 36)

def sourceBody718_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody718_39 : WordLangProgHOL (BitVec 64) :=
.call (some (([40, 30, 52, 24, 46, 36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody718_0, 718, 2)) (some 710) ([38, 28, 50, 22, 44, 34, 56, 20, 42, 32, 54, 26]) (some (38, sourceBody718_38, 718, 3))

def sourceBody718_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_39 sourceBody718_9

def sourceBody718_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_40 sourceBody718_0

def sourceBody718_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_37 sourceBody718_41

def sourceBody718_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_36 sourceBody718_42

def sourceBody718_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_35 sourceBody718_43

def sourceBody718_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_34 sourceBody718_44

def sourceBody718_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_33 sourceBody718_45

def sourceBody718_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_32 sourceBody718_46

def sourceBody718_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_31 sourceBody718_47

def sourceBody718_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_30 sourceBody718_48

def sourceBody718_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_29 sourceBody718_49

def sourceBody718_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_28 sourceBody718_50

def sourceBody718_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_27 sourceBody718_51

def sourceBody718_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_26 sourceBody718_52

def sourceBody718_54 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody718_53 sourceBody718_0

def sourceBody718_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_54 sourceBody718_9

def sourceBody718_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_55 sourceBody718_0

def sourceBody718_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_15 sourceBody718_56

def sourceBody718_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_25 sourceBody718_57

def sourceBody718_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_23 sourceBody718_58

def sourceBody718_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_22 sourceBody718_59

def sourceBody718_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_21 sourceBody718_60

def sourceBody718_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
        (Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.var 14,
              Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 18)
                  (Flapjack.WordLangExpHOL.const 6#64))
                (Flapjack.WordLangExpHOL.const 3#64)]))
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
          [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 63#64]),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody718_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 38)

def sourceBody718_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody718_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody718_66 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 50 (Flapjack.WordRegImm.reg 22) sourceBody718_23 sourceBody718_65

def sourceBody718_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_66 sourceBody718_9

def sourceBody718_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 50)

def sourceBody718_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 40)

def sourceBody718_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 30)

def sourceBody718_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 52)

def sourceBody718_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 24)

def sourceBody718_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 46)

def sourceBody718_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 36)

def sourceBody718_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody718_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 4)

def sourceBody718_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 6)

def sourceBody718_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 8)

def sourceBody718_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody718_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 12)

def sourceBody718_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody718_82 : WordLangProgHOL (BitVec 64) :=
.call (some (([40, 30, 52, 24, 46, 36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody718_0, 718, 4)) (some 710) ([28, 50, 22, 44, 34, 56, 20, 42, 32, 54, 26, 48]) (some (28, sourceBody718_81, 718, 5))

def sourceBody718_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_82 sourceBody718_9

def sourceBody718_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_83 sourceBody718_0

def sourceBody718_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_80 sourceBody718_84

def sourceBody718_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_79 sourceBody718_85

def sourceBody718_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_78 sourceBody718_86

def sourceBody718_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_77 sourceBody718_87

def sourceBody718_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_76 sourceBody718_88

def sourceBody718_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_75 sourceBody718_89

def sourceBody718_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_74 sourceBody718_90

def sourceBody718_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_73 sourceBody718_91

def sourceBody718_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_72 sourceBody718_92

def sourceBody718_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_71 sourceBody718_93

def sourceBody718_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_70 sourceBody718_94

def sourceBody718_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_69 sourceBody718_95

def sourceBody718_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody718_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_97 sourceBody718_0

def sourceBody718_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_98 sourceBody718_0

def sourceBody718_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_96 sourceBody718_99

def sourceBody718_101 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 44 (Flapjack.WordRegImm.imm 0#64) sourceBody718_100 sourceBody718_0

def sourceBody718_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_101 sourceBody718_9

def sourceBody718_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_102 sourceBody718_0

def sourceBody718_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_68 sourceBody718_103

def sourceBody718_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_67 sourceBody718_104

def sourceBody718_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_64 sourceBody718_105

def sourceBody718_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_63 sourceBody718_106

def sourceBody718_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_62 sourceBody718_107

def sourceBody718_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_0 sourceBody718_108

def sourceBody718_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_61 sourceBody718_109

def sourceBody718_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody718_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_110 sourceBody718_111

def sourceBody718_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody718_114 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody718_112 sourceBody718_113

def sourceBody718_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_114 sourceBody718_9

def sourceBody718_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_115 sourceBody718_0

def sourceBody718_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_15 sourceBody718_116

def sourceBody718_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_14 sourceBody718_117

def sourceBody718_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_11 sourceBody718_118

def sourceBody718_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_10 sourceBody718_119

def sourceBody718_121 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody718_120 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody718_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_121 sourceBody718_9

def sourceBody718_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_9 sourceBody718_122

def sourceBody718_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [38, 28, 50, 22, 44, 34]

def sourceBody718_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_124 sourceBody718_0

def sourceBody718_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_31 sourceBody718_125

def sourceBody718_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_30 sourceBody718_126

def sourceBody718_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_29 sourceBody718_127

def sourceBody718_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_28 sourceBody718_128

def sourceBody718_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_27 sourceBody718_129

def sourceBody718_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_26 sourceBody718_130

def sourceBody718_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_123 sourceBody718_131

def sourceBody718_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_8 sourceBody718_132

def sourceBody718_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_0 sourceBody718_133

def sourceBody718_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_7 sourceBody718_134

def sourceBody718_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_0 sourceBody718_135

def sourceBody718_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_6 sourceBody718_136

def sourceBody718_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_0 sourceBody718_137

def sourceBody718_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_5 sourceBody718_138

def sourceBody718_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_0 sourceBody718_139

def sourceBody718_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_4 sourceBody718_140

def sourceBody718_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_0 sourceBody718_141

def sourceBody718_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_3 sourceBody718_142

def sourceBody718_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_0 sourceBody718_143

def sourceBody718_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_2 sourceBody718_144

def sourceBody718_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_0 sourceBody718_145

def sourceBody718_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_1 sourceBody718_146

def sourceBody718_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody718_0 sourceBody718_147

def source718 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (718, 9, sourceBody718_148)
end InitECandidate.Proofs.WordStages
