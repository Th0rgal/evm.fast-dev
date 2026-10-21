import InitECandidate.Proofs.WordStages.Source822
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody838_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody838_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody838_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody838_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 9#64])

def sourceBody838_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody838_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody838_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 16)

def sourceBody838_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 28)

def sourceBody838_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody838_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody838_10 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 8 (Flapjack.WordRegImm.reg 22) sourceBody838_8 sourceBody838_9

def sourceBody838_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_10 sourceBody838_5

def sourceBody838_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody838_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody838_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 9#64])

def sourceBody838_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody838_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody838_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody838_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody838_0, 838, 2)) (some 176) ([14, 30, 12]) (some (14, sourceBody838_17, 838, 3))

def sourceBody838_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_18 sourceBody838_5

def sourceBody838_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_19 sourceBody838_0

def sourceBody838_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_16 sourceBody838_20

def sourceBody838_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_15 sourceBody838_21

def sourceBody838_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_12 sourceBody838_22

def sourceBody838_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 22])

def sourceBody838_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody838_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_25 sourceBody838_0

def sourceBody838_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_26 sourceBody838_0

def sourceBody838_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_24 sourceBody838_27

def sourceBody838_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_28

def sourceBody838_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 9#64])

def sourceBody838_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody838_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody838_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 26)

def sourceBody838_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody838_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody838_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody838_37 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 34 (Flapjack.WordRegImm.reg 6) sourceBody838_35 sourceBody838_36

def sourceBody838_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_37 sourceBody838_5

def sourceBody838_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 34)

def sourceBody838_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 30)

def sourceBody838_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 8#64]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 26)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody838_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody838_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody838_44 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody838_0, 838, 4)) (some 176) ([18, 34, 6]) (some (18, sourceBody838_43, 838, 5))

def sourceBody838_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_44 sourceBody838_5

def sourceBody838_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_45 sourceBody838_0

def sourceBody838_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_42 sourceBody838_46

def sourceBody838_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_41 sourceBody838_47

def sourceBody838_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_40 sourceBody838_48

def sourceBody838_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.var 22])

def sourceBody838_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 18)

def sourceBody838_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_51 sourceBody838_0

def sourceBody838_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_52 sourceBody838_0

def sourceBody838_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_50 sourceBody838_53

def sourceBody838_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_54

def sourceBody838_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_49 sourceBody838_55

def sourceBody838_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody838_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 18)

def sourceBody838_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_58 sourceBody838_0

def sourceBody838_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_59 sourceBody838_0

def sourceBody838_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_57 sourceBody838_60

def sourceBody838_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_61

def sourceBody838_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_56 sourceBody838_62

def sourceBody838_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody838_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_63 sourceBody838_64

def sourceBody838_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody838_67 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody838_65 sourceBody838_66

def sourceBody838_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_67 sourceBody838_5

def sourceBody838_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_68 sourceBody838_0

def sourceBody838_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_39 sourceBody838_69

def sourceBody838_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_38 sourceBody838_70

def sourceBody838_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_34 sourceBody838_71

def sourceBody838_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_33 sourceBody838_72

def sourceBody838_74 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody838_73 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody838_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_74 sourceBody838_5

def sourceBody838_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_5 sourceBody838_75

def sourceBody838_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody838_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 30)

def sourceBody838_79 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody838_0, 838, 6)) (some 836) ([18, 34]) (some (18, sourceBody838_43, 838, 7))

def sourceBody838_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_79 sourceBody838_5

def sourceBody838_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_80 sourceBody838_0

def sourceBody838_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_78 sourceBody838_81

def sourceBody838_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_77 sourceBody838_82

def sourceBody838_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_76 sourceBody838_83

def sourceBody838_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.var 22])

def sourceBody838_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_85 sourceBody838_0

def sourceBody838_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_86 sourceBody838_0

def sourceBody838_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_84 sourceBody838_87

def sourceBody838_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody838_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody838_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody838_92 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody838_0, 838, 8)) (some 176) ([18, 34, 6]) (some (18, sourceBody838_43, 838, 9))

def sourceBody838_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_92 sourceBody838_5

def sourceBody838_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_93 sourceBody838_0

def sourceBody838_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_91 sourceBody838_94

def sourceBody838_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_90 sourceBody838_95

def sourceBody838_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_89 sourceBody838_96

def sourceBody838_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_88 sourceBody838_97

def sourceBody838_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 22])

def sourceBody838_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 18)

def sourceBody838_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_100 sourceBody838_0

def sourceBody838_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_101 sourceBody838_0

def sourceBody838_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_99 sourceBody838_102

def sourceBody838_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_103

def sourceBody838_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_98 sourceBody838_104

def sourceBody838_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody838_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 8)

def sourceBody838_108 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody838_0, 838, 10)) (some 836) ([18, 34]) (some (18, sourceBody838_43, 838, 11))

def sourceBody838_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_108 sourceBody838_5

def sourceBody838_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_109 sourceBody838_0

def sourceBody838_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_107 sourceBody838_110

def sourceBody838_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_106 sourceBody838_111

def sourceBody838_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_105 sourceBody838_112

def sourceBody838_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.var 22])

def sourceBody838_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody838_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_115 sourceBody838_0

def sourceBody838_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_116 sourceBody838_0

def sourceBody838_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_114 sourceBody838_117

def sourceBody838_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_118

def sourceBody838_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_113 sourceBody838_119

def sourceBody838_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody838_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody838_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_122 sourceBody838_0

def sourceBody838_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_123 sourceBody838_0

def sourceBody838_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_121 sourceBody838_124

def sourceBody838_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_125

def sourceBody838_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_120 sourceBody838_126

def sourceBody838_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_32 sourceBody838_127

def sourceBody838_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_128

def sourceBody838_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_31 sourceBody838_129

def sourceBody838_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_130

def sourceBody838_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_30 sourceBody838_131

def sourceBody838_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_132

def sourceBody838_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_12 sourceBody838_133

def sourceBody838_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_134

def sourceBody838_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_29 sourceBody838_135

def sourceBody838_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_23 sourceBody838_136

def sourceBody838_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_137

def sourceBody838_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_138

def sourceBody838_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_14 sourceBody838_139

def sourceBody838_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_140

def sourceBody838_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_13 sourceBody838_141

def sourceBody838_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_142

def sourceBody838_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_143 sourceBody838_64

def sourceBody838_145 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody838_144 sourceBody838_66

def sourceBody838_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_145 sourceBody838_5

def sourceBody838_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_146 sourceBody838_0

def sourceBody838_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_12 sourceBody838_147

def sourceBody838_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_11 sourceBody838_148

def sourceBody838_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_7 sourceBody838_149

def sourceBody838_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_6 sourceBody838_150

def sourceBody838_152 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody838_151 (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody838_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_152 sourceBody838_5

def sourceBody838_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_5 sourceBody838_153

def sourceBody838_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody838_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 24)

def sourceBody838_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody838_158 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody838_0, 838, 12)) (some 836) ([8, 22]) (some (8, sourceBody838_157, 838, 13))

def sourceBody838_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_158 sourceBody838_5

def sourceBody838_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_159 sourceBody838_0

def sourceBody838_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_156 sourceBody838_160

def sourceBody838_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_155 sourceBody838_161

def sourceBody838_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 32)

def sourceBody838_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody838_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_164 sourceBody838_0

def sourceBody838_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_163 sourceBody838_165

def sourceBody838_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_162 sourceBody838_166

def sourceBody838_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_167

def sourceBody838_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_168

def sourceBody838_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_154 sourceBody838_169

def sourceBody838_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_4 sourceBody838_170

def sourceBody838_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_171

def sourceBody838_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_3 sourceBody838_172

def sourceBody838_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_173

def sourceBody838_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_2 sourceBody838_174

def sourceBody838_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_175

def sourceBody838_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_1 sourceBody838_176

def sourceBody838_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody838_0 sourceBody838_177

def source838 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (838, 3, sourceBody838_178)
end InitECandidate.Proofs.WordStages
