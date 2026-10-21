import InitECandidate.Proofs.WordStages.Source649
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody665_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody665_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody665_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody665_0, 665, 2)) (some 69) ([]) (some (12, sourceBody665_1, 665, 3))

def sourceBody665_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody665_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_2 sourceBody665_3

def sourceBody665_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_4 sourceBody665_0

def sourceBody665_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 736#64)

def sourceBody665_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody665_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody665_0, 665, 4)) (some 68) ([40]) (some (40, sourceBody665_7, 665, 5))

def sourceBody665_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_8 sourceBody665_3

def sourceBody665_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_9 sourceBody665_0

def sourceBody665_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_6 sourceBody665_10

def sourceBody665_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody665_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 40)

def sourceBody665_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 23#64)

def sourceBody665_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody665_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody665_17 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 56 (Flapjack.WordRegImm.reg 8) sourceBody665_15 sourceBody665_16

def sourceBody665_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_17 sourceBody665_3

def sourceBody665_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 56)

def sourceBody665_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody665_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody665_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody665_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody665_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 11#64)

def sourceBody665_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 40)

def sourceBody665_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody665_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody665_28 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 16 (Flapjack.WordRegImm.reg 44) sourceBody665_26 sourceBody665_27

def sourceBody665_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_28 sourceBody665_3

def sourceBody665_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 16)

def sourceBody665_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 11#64])

def sourceBody665_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_31 sourceBody665_0

def sourceBody665_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_32 sourceBody665_0

def sourceBody665_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody665_33 sourceBody665_0

def sourceBody665_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_34 sourceBody665_3

def sourceBody665_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_35 sourceBody665_0

def sourceBody665_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_30 sourceBody665_36

def sourceBody665_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_29 sourceBody665_37

def sourceBody665_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_25 sourceBody665_38

def sourceBody665_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_24 sourceBody665_39

def sourceBody665_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody665_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.var 22])

def sourceBody665_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 22)
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody665_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 22)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody665_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 22)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody665_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 22)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody665_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.var 22])
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody665_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.var 22])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody665_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.var 22])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody665_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.var 22])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody665_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 52)

def sourceBody665_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody665_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 44)

def sourceBody665_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 30)

def sourceBody665_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 60)

def sourceBody665_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody665_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 34)

def sourceBody665_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 20)

def sourceBody665_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 58

def sourceBody665_60 : WordLangProgHOL (BitVec 64) :=
.call (some (([50, 14, 42, 28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody665_0, 665, 6)) (some 657) ([58, 10, 38, 24, 54, 18, 46, 32]) (some (58, sourceBody665_59, 665, 7))

def sourceBody665_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_60 sourceBody665_3

def sourceBody665_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_61 sourceBody665_0

def sourceBody665_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_58 sourceBody665_62

def sourceBody665_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_57 sourceBody665_63

def sourceBody665_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_56 sourceBody665_64

def sourceBody665_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_55 sourceBody665_65

def sourceBody665_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_54 sourceBody665_66

def sourceBody665_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_53 sourceBody665_67

def sourceBody665_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_52 sourceBody665_68

def sourceBody665_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_51 sourceBody665_69

def sourceBody665_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 26)

def sourceBody665_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 56)

def sourceBody665_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 8)

def sourceBody665_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 36)

def sourceBody665_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 50)

def sourceBody665_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody665_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 42)

def sourceBody665_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 28)

def sourceBody665_79 : WordLangProgHOL (BitVec 64) :=
.call (some (([26, 56, 8, 36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody665_0, 665, 8)) (some 654) ([58, 10, 38, 24, 54, 18, 46, 32]) (some (58, sourceBody665_59, 665, 9))

def sourceBody665_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_79 sourceBody665_3

def sourceBody665_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_80 sourceBody665_0

def sourceBody665_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_78 sourceBody665_81

def sourceBody665_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_77 sourceBody665_82

def sourceBody665_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_76 sourceBody665_83

def sourceBody665_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_75 sourceBody665_84

def sourceBody665_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_74 sourceBody665_85

def sourceBody665_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_73 sourceBody665_86

def sourceBody665_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_72 sourceBody665_87

def sourceBody665_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_71 sourceBody665_88

def sourceBody665_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody665_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 58)

def sourceBody665_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_91 sourceBody665_0

def sourceBody665_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_92 sourceBody665_0

def sourceBody665_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_90 sourceBody665_93

def sourceBody665_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_94

def sourceBody665_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_89 sourceBody665_95

def sourceBody665_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_70 sourceBody665_96

def sourceBody665_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_97

def sourceBody665_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_98

def sourceBody665_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_99

def sourceBody665_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_100

def sourceBody665_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_101

def sourceBody665_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_102

def sourceBody665_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_103

def sourceBody665_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_104

def sourceBody665_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_50 sourceBody665_105

def sourceBody665_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_106

def sourceBody665_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_49 sourceBody665_107

def sourceBody665_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_108

def sourceBody665_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_48 sourceBody665_109

def sourceBody665_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_110

def sourceBody665_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_47 sourceBody665_111

def sourceBody665_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_112

def sourceBody665_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_46 sourceBody665_113

def sourceBody665_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_114

def sourceBody665_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_45 sourceBody665_115

def sourceBody665_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_116

def sourceBody665_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_44 sourceBody665_117

def sourceBody665_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_118

def sourceBody665_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_43 sourceBody665_119

def sourceBody665_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_120

def sourceBody665_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody665_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_121 sourceBody665_122

def sourceBody665_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody665_125 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody665_123 sourceBody665_124

def sourceBody665_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_125 sourceBody665_3

def sourceBody665_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_126 sourceBody665_0

def sourceBody665_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_30 sourceBody665_127

def sourceBody665_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_29 sourceBody665_128

def sourceBody665_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_42 sourceBody665_129

def sourceBody665_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_41 sourceBody665_130

def sourceBody665_132 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
  PUnit.unit Flapjack.Spt.ln) sourceBody665_131 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody665_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_132 sourceBody665_3

def sourceBody665_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_3 sourceBody665_133

def sourceBody665_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_40 sourceBody665_134

def sourceBody665_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 26)

def sourceBody665_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 56)

def sourceBody665_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 8)

def sourceBody665_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 36)

def sourceBody665_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 26)

def sourceBody665_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 56)

def sourceBody665_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 8)

def sourceBody665_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 36)

def sourceBody665_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 52

def sourceBody665_145 : WordLangProgHOL (BitVec 64) :=
.call (some (([26, 56, 8, 36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody665_0, 665, 10)) (some 654) ([52, 16, 44, 30, 60, 6, 34, 20]) (some (52, sourceBody665_144, 665, 11))

def sourceBody665_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_145 sourceBody665_3

def sourceBody665_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_146 sourceBody665_0

def sourceBody665_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_143 sourceBody665_147

def sourceBody665_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_142 sourceBody665_148

def sourceBody665_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_141 sourceBody665_149

def sourceBody665_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_140 sourceBody665_150

def sourceBody665_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_139 sourceBody665_151

def sourceBody665_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_138 sourceBody665_152

def sourceBody665_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_137 sourceBody665_153

def sourceBody665_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_136 sourceBody665_154

def sourceBody665_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_135 sourceBody665_155

def sourceBody665_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody665_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody665_159 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 44) sourceBody665_26 sourceBody665_27

def sourceBody665_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_159 sourceBody665_3

def sourceBody665_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 40)
            (Flapjack.WordLangExpHOL.const 1#64))
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody665_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 40)
                (Flapjack.WordLangExpHOL.const 1#64))
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody665_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 40)
                (Flapjack.WordLangExpHOL.const 1#64))
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody665_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 40)
                (Flapjack.WordLangExpHOL.const 1#64))
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody665_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 52)

def sourceBody665_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody665_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 44)

def sourceBody665_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 30)

def sourceBody665_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 50

def sourceBody665_170 : WordLangProgHOL (BitVec 64) :=
.call (some (([60, 6, 34, 20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody665_0, 665, 12)) (some 657) ([50, 14, 42, 28, 58, 10, 38, 24]) (some (50, sourceBody665_169, 665, 13))

def sourceBody665_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_170 sourceBody665_3

def sourceBody665_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_171 sourceBody665_0

def sourceBody665_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_54 sourceBody665_172

def sourceBody665_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_53 sourceBody665_173

def sourceBody665_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_52 sourceBody665_174

def sourceBody665_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_51 sourceBody665_175

def sourceBody665_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_168 sourceBody665_176

def sourceBody665_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_167 sourceBody665_177

def sourceBody665_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_166 sourceBody665_178

def sourceBody665_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_165 sourceBody665_179

def sourceBody665_181 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 26)

def sourceBody665_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 56)

def sourceBody665_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 8)

def sourceBody665_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 36)

def sourceBody665_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 60)

def sourceBody665_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody665_187 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 34)

def sourceBody665_188 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 20)

def sourceBody665_189 : WordLangProgHOL (BitVec 64) :=
.call (some (([26, 56, 8, 36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody665_0, 665, 14)) (some 654) ([50, 14, 42, 28, 58, 10, 38, 24]) (some (50, sourceBody665_169, 665, 15))

def sourceBody665_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_189 sourceBody665_3

def sourceBody665_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_190 sourceBody665_0

def sourceBody665_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_188 sourceBody665_191

def sourceBody665_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_187 sourceBody665_192

def sourceBody665_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_186 sourceBody665_193

def sourceBody665_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_185 sourceBody665_194

def sourceBody665_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_184 sourceBody665_195

def sourceBody665_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_183 sourceBody665_196

def sourceBody665_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_182 sourceBody665_197

def sourceBody665_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_181 sourceBody665_198

def sourceBody665_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_180 sourceBody665_199

def sourceBody665_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_200

def sourceBody665_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_201

def sourceBody665_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_202

def sourceBody665_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_203

def sourceBody665_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_204

def sourceBody665_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_205

def sourceBody665_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_206

def sourceBody665_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_207

def sourceBody665_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_164 sourceBody665_208

def sourceBody665_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_209

def sourceBody665_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_163 sourceBody665_210

def sourceBody665_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_211

def sourceBody665_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_162 sourceBody665_212

def sourceBody665_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_213

def sourceBody665_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_161 sourceBody665_214

def sourceBody665_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_215

def sourceBody665_217 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody665_216 sourceBody665_0

def sourceBody665_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_217 sourceBody665_3

def sourceBody665_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_218 sourceBody665_0

def sourceBody665_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_30 sourceBody665_219

def sourceBody665_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_160 sourceBody665_220

def sourceBody665_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_158 sourceBody665_221

def sourceBody665_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_157 sourceBody665_222

def sourceBody665_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_156 sourceBody665_223

def sourceBody665_225 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 12,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody665_226 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 26)

def sourceBody665_227 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 56)

def sourceBody665_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 8)

def sourceBody665_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 36)

def sourceBody665_230 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody665_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 52) 6

def sourceBody665_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_231 sourceBody665_0

def sourceBody665_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_230 sourceBody665_232

def sourceBody665_234 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 44)

def sourceBody665_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 52, Flapjack.WordLangExpHOL.const 8#64]) 6

def sourceBody665_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_235 sourceBody665_0

def sourceBody665_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_234 sourceBody665_236

def sourceBody665_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 30)

def sourceBody665_239 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 52, Flapjack.WordLangExpHOL.const 16#64])
  6

def sourceBody665_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_239 sourceBody665_0

def sourceBody665_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_238 sourceBody665_240

def sourceBody665_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 60)

def sourceBody665_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 52, Flapjack.WordLangExpHOL.const 24#64])
  6

def sourceBody665_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_243 sourceBody665_0

def sourceBody665_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_242 sourceBody665_244

def sourceBody665_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_245 sourceBody665_0

def sourceBody665_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_241 sourceBody665_246

def sourceBody665_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_237 sourceBody665_247

def sourceBody665_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_233 sourceBody665_248

def sourceBody665_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_229 sourceBody665_249

def sourceBody665_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_250

def sourceBody665_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_228 sourceBody665_251

def sourceBody665_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_252

def sourceBody665_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_227 sourceBody665_253

def sourceBody665_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_254

def sourceBody665_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_226 sourceBody665_255

def sourceBody665_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_256

def sourceBody665_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_225 sourceBody665_257

def sourceBody665_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_258

def sourceBody665_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_224 sourceBody665_259

def sourceBody665_261 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody665_262 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 52)

def sourceBody665_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_262 sourceBody665_0

def sourceBody665_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_263 sourceBody665_0

def sourceBody665_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_261 sourceBody665_264

def sourceBody665_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_265

def sourceBody665_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_260 sourceBody665_266

def sourceBody665_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_23 sourceBody665_267

def sourceBody665_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_268

def sourceBody665_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_22 sourceBody665_269

def sourceBody665_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_270

def sourceBody665_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_21 sourceBody665_271

def sourceBody665_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_272

def sourceBody665_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_16 sourceBody665_273

def sourceBody665_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_274

def sourceBody665_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_20 sourceBody665_275

def sourceBody665_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_276

def sourceBody665_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_277 sourceBody665_122

def sourceBody665_279 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody665_278 sourceBody665_124

def sourceBody665_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_279 sourceBody665_3

def sourceBody665_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_280 sourceBody665_0

def sourceBody665_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_19 sourceBody665_281

def sourceBody665_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_18 sourceBody665_282

def sourceBody665_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_14 sourceBody665_283

def sourceBody665_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_13 sourceBody665_284

def sourceBody665_286 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
  PUnit.unit Flapjack.Spt.ln) sourceBody665_285 (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody665_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_286 sourceBody665_3

def sourceBody665_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_3 sourceBody665_287

def sourceBody665_289 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 12)

def sourceBody665_290 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 56

def sourceBody665_291 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody665_0, 665, 16)) (some 663) ([56]) (some (56, sourceBody665_290, 665, 17))

def sourceBody665_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_291 sourceBody665_3

def sourceBody665_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_292 sourceBody665_0

def sourceBody665_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_289 sourceBody665_293

def sourceBody665_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_294

def sourceBody665_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_295

def sourceBody665_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_288 sourceBody665_296

def sourceBody665_298 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 2)

def sourceBody665_299 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody665_300 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 384#64)

def sourceBody665_301 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody665_0, 665, 18)) (some 77) ([56, 8, 36]) (some (56, sourceBody665_290, 665, 19))

def sourceBody665_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_301 sourceBody665_3

def sourceBody665_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_302 sourceBody665_0

def sourceBody665_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_300 sourceBody665_303

def sourceBody665_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_299 sourceBody665_304

def sourceBody665_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_298 sourceBody665_305

def sourceBody665_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_306

def sourceBody665_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_307

def sourceBody665_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_297 sourceBody665_308

def sourceBody665_310 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 48)

def sourceBody665_311 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody665_0, 665, 20)) (some 70) ([56]) (some (56, sourceBody665_290, 665, 21))

def sourceBody665_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_311 sourceBody665_3

def sourceBody665_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_312 sourceBody665_0

def sourceBody665_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_310 sourceBody665_313

def sourceBody665_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_314

def sourceBody665_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_315

def sourceBody665_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_309 sourceBody665_316

def sourceBody665_318 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody665_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_318 sourceBody665_0

def sourceBody665_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_20 sourceBody665_319

def sourceBody665_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_317 sourceBody665_320

def sourceBody665_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_12 sourceBody665_321

def sourceBody665_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_322

def sourceBody665_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_11 sourceBody665_323

def sourceBody665_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_324

def sourceBody665_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_325

def sourceBody665_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_5 sourceBody665_326

def sourceBody665_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_327

def sourceBody665_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody665_0 sourceBody665_328

def source665 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (665, 3, sourceBody665_329)
end InitECandidate.Proofs.WordStages
