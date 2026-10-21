import InitECandidate.Proofs.WordStages.Source838
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody854_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody854_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody854_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody854_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody854_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody854_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody854_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody854_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody854_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody854_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody854_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 8)

def sourceBody854_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody854_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody854_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 14 (Flapjack.WordRegImm.reg 30) sourceBody854_11 sourceBody854_12

def sourceBody854_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_13 sourceBody854_8

def sourceBody854_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody854_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 6)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody854_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 6)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody854_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody854_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody854_0, 854, 2)) (some 342) ([14, 30]) (some (14, sourceBody854_18, 854, 3))

def sourceBody854_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_19 sourceBody854_8

def sourceBody854_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_20 sourceBody854_0

def sourceBody854_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_17 sourceBody854_21

def sourceBody854_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_16 sourceBody854_22

def sourceBody854_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 22)

def sourceBody854_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody854_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody854_0, 854, 4)) (some 851) ([30]) (some (30, sourceBody854_25, 854, 5))

def sourceBody854_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_26 sourceBody854_8

def sourceBody854_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_27 sourceBody854_0

def sourceBody854_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_24 sourceBody854_28

def sourceBody854_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody854_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody854_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody854_33 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 26) sourceBody854_31 sourceBody854_32

def sourceBody854_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_33 sourceBody854_8

def sourceBody854_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody854_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 264#64]))

def sourceBody854_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 30)

def sourceBody854_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody854_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody854_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 18 (Flapjack.WordRegImm.reg 34) sourceBody854_38 sourceBody854_39

def sourceBody854_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_40 sourceBody854_8

def sourceBody854_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 18)

def sourceBody854_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 32)

def sourceBody854_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody854_45 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 18 (Flapjack.WordRegImm.reg 34) sourceBody854_38 sourceBody854_39

def sourceBody854_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_45 sourceBody854_8

def sourceBody854_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody854_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_47 sourceBody854_0

def sourceBody854_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_30 sourceBody854_48

def sourceBody854_50 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody854_49 sourceBody854_0

def sourceBody854_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_50 sourceBody854_8

def sourceBody854_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_51 sourceBody854_0

def sourceBody854_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_42 sourceBody854_52

def sourceBody854_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_46 sourceBody854_53

def sourceBody854_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_44 sourceBody854_54

def sourceBody854_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_43 sourceBody854_55

def sourceBody854_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 10)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody854_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 24,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 32)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody854_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody854_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody854_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody854_0, 854, 6)) (some 79) ([18, 34, 4]) (some (18, sourceBody854_60, 854, 7))

def sourceBody854_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_61 sourceBody854_8

def sourceBody854_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_62 sourceBody854_0

def sourceBody854_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_59 sourceBody854_63

def sourceBody854_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_58 sourceBody854_64

def sourceBody854_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_57 sourceBody854_65

def sourceBody854_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 26)

def sourceBody854_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody854_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody854_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody854_71 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 34 (Flapjack.WordRegImm.reg 4) sourceBody854_69 sourceBody854_70

def sourceBody854_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_71 sourceBody854_8

def sourceBody854_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 34)

def sourceBody854_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody854_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_74 sourceBody854_0

def sourceBody854_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_39 sourceBody854_75

def sourceBody854_77 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody854_76 sourceBody854_0

def sourceBody854_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_77 sourceBody854_8

def sourceBody854_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_78 sourceBody854_0

def sourceBody854_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_73 sourceBody854_79

def sourceBody854_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_72 sourceBody854_80

def sourceBody854_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_68 sourceBody854_81

def sourceBody854_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_67 sourceBody854_82

def sourceBody854_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody854_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 18)

def sourceBody854_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_85 sourceBody854_0

def sourceBody854_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_86 sourceBody854_0

def sourceBody854_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_84 sourceBody854_87

def sourceBody854_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_88

def sourceBody854_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_83 sourceBody854_89

def sourceBody854_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody854_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody854_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_92 sourceBody854_0

def sourceBody854_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_93 sourceBody854_0

def sourceBody854_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_91 sourceBody854_94

def sourceBody854_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_95

def sourceBody854_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_90 sourceBody854_96

def sourceBody854_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_66 sourceBody854_97

def sourceBody854_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_98

def sourceBody854_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_99

def sourceBody854_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_56 sourceBody854_100

def sourceBody854_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody854_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_101 sourceBody854_102

def sourceBody854_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody854_105 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody854_103 sourceBody854_104

def sourceBody854_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_105 sourceBody854_8

def sourceBody854_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_106 sourceBody854_0

def sourceBody854_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_42 sourceBody854_107

def sourceBody854_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_41 sourceBody854_108

def sourceBody854_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_37 sourceBody854_109

def sourceBody854_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_35 sourceBody854_110

def sourceBody854_112 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody854_111 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody854_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_112 sourceBody854_8

def sourceBody854_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_8 sourceBody854_113

def sourceBody854_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_32 sourceBody854_114

def sourceBody854_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_115

def sourceBody854_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_36 sourceBody854_116

def sourceBody854_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_117

def sourceBody854_119 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody854_118 sourceBody854_0

def sourceBody854_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_119 sourceBody854_8

def sourceBody854_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_120 sourceBody854_0

def sourceBody854_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_35 sourceBody854_121

def sourceBody854_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_34 sourceBody854_122

def sourceBody854_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_30 sourceBody854_123

def sourceBody854_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_15 sourceBody854_124

def sourceBody854_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody854_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 30)

def sourceBody854_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_127 sourceBody854_0

def sourceBody854_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_128 sourceBody854_0

def sourceBody854_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_126 sourceBody854_129

def sourceBody854_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_130

def sourceBody854_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_125 sourceBody854_131

def sourceBody854_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_29 sourceBody854_132

def sourceBody854_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_133

def sourceBody854_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_134

def sourceBody854_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_23 sourceBody854_135

def sourceBody854_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_136

def sourceBody854_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_137

def sourceBody854_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_138 sourceBody854_102

def sourceBody854_140 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody854_139 sourceBody854_104

def sourceBody854_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_140 sourceBody854_8

def sourceBody854_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_141 sourceBody854_0

def sourceBody854_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_15 sourceBody854_142

def sourceBody854_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_14 sourceBody854_143

def sourceBody854_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_10 sourceBody854_144

def sourceBody854_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_9 sourceBody854_145

def sourceBody854_147 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody854_146 (Flapjack.Spt.bs
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody854_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_147 sourceBody854_8

def sourceBody854_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_8 sourceBody854_148

def sourceBody854_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 32)

def sourceBody854_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 16)

def sourceBody854_152 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.reg 30) sourceBody854_11 sourceBody854_12

def sourceBody854_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_152 sourceBody854_8

def sourceBody854_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody854_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [22]

def sourceBody854_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_155 sourceBody854_0

def sourceBody854_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_154 sourceBody854_156

def sourceBody854_158 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody854_157 sourceBody854_0

def sourceBody854_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_158 sourceBody854_8

def sourceBody854_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_159 sourceBody854_0

def sourceBody854_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_15 sourceBody854_160

def sourceBody854_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_153 sourceBody854_161

def sourceBody854_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_151 sourceBody854_162

def sourceBody854_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_150 sourceBody854_163

def sourceBody854_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_149 sourceBody854_164

def sourceBody854_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody854_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_166 sourceBody854_156

def sourceBody854_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_165 sourceBody854_167

def sourceBody854_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_7 sourceBody854_168

def sourceBody854_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_169

def sourceBody854_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_6 sourceBody854_170

def sourceBody854_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_171

def sourceBody854_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_5 sourceBody854_172

def sourceBody854_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_173

def sourceBody854_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_4 sourceBody854_174

def sourceBody854_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_175

def sourceBody854_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_3 sourceBody854_176

def sourceBody854_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_177

def sourceBody854_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_2 sourceBody854_178

def sourceBody854_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_179

def sourceBody854_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_1 sourceBody854_180

def sourceBody854_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody854_0 sourceBody854_181

def source854 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (854, 2, sourceBody854_182)
end InitECandidate.Proofs.WordStages
