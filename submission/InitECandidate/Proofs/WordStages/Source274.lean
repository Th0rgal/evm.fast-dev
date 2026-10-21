import InitECandidate.Proofs.WordStages.Source258
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody274_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 256#64)

def sourceBody274_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody274_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody274_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody274_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 8 (Flapjack.WordRegImm.reg 16) sourceBody274_2 sourceBody274_3

def sourceBody274_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody274_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_4 sourceBody274_5

def sourceBody274_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody274_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody274_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody274_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 18)

def sourceBody274_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_10 sourceBody274_8

def sourceBody274_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_11 sourceBody274_8

def sourceBody274_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_9 sourceBody274_12

def sourceBody274_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_8 sourceBody274_13

def sourceBody274_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody274_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody274_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_15 sourceBody274_16

def sourceBody274_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_14 sourceBody274_17

def sourceBody274_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody274_18 sourceBody274_8

def sourceBody274_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_19 sourceBody274_5

def sourceBody274_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_20 sourceBody274_8

def sourceBody274_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_7 sourceBody274_21

def sourceBody274_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_6 sourceBody274_22

def sourceBody274_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_1 sourceBody274_23

def sourceBody274_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_0 sourceBody274_24

def sourceBody274_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody274_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody274_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody274_8, 274, 2)) (some 68) ([8]) (some (8, sourceBody274_27, 274, 3))

def sourceBody274_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_28 sourceBody274_5

def sourceBody274_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_29 sourceBody274_8

def sourceBody274_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_26 sourceBody274_30

def sourceBody274_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 5#64),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody274_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody274_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody274_8, 274, 4)) (some 68) ([16]) (some (16, sourceBody274_33, 274, 5))

def sourceBody274_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_34 sourceBody274_5

def sourceBody274_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_35 sourceBody274_8

def sourceBody274_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_32 sourceBody274_36

def sourceBody274_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody274_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody274_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody274_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody274_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody274_43 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 20 (Flapjack.WordRegImm.reg 6) sourceBody274_41 sourceBody274_42

def sourceBody274_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_43 sourceBody274_5

def sourceBody274_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody274_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody274_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody274_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody274_49 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody274_8, 274, 6)) (some 270) ([20, 6]) (some (20, sourceBody274_48, 274, 7))

def sourceBody274_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_49 sourceBody274_5

def sourceBody274_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_50 sourceBody274_8

def sourceBody274_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_47 sourceBody274_51

def sourceBody274_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_46 sourceBody274_52

def sourceBody274_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 18,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody274_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody274_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody274_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 20) 14

def sourceBody274_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_57 sourceBody274_8

def sourceBody274_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_56 sourceBody274_58

def sourceBody274_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_59 sourceBody274_8

def sourceBody274_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_55 sourceBody274_60

def sourceBody274_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_8 sourceBody274_61

def sourceBody274_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_54 sourceBody274_62

def sourceBody274_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_8 sourceBody274_63

def sourceBody274_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody274_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody274_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 8,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody274_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody274_69 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody274_8, 274, 8)) (some 158) ([6, 14, 10]) (some (6, sourceBody274_68, 274, 9))

def sourceBody274_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_69 sourceBody274_5

def sourceBody274_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_70 sourceBody274_8

def sourceBody274_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_67 sourceBody274_71

def sourceBody274_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_66 sourceBody274_72

def sourceBody274_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_65 sourceBody274_73

def sourceBody274_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_8 sourceBody274_74

def sourceBody274_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_8 sourceBody274_75

def sourceBody274_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_64 sourceBody274_76

def sourceBody274_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody274_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody274_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_79 sourceBody274_8

def sourceBody274_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_80 sourceBody274_8

def sourceBody274_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_78 sourceBody274_81

def sourceBody274_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_8 sourceBody274_82

def sourceBody274_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_77 sourceBody274_83

def sourceBody274_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_53 sourceBody274_84

def sourceBody274_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_8 sourceBody274_85

def sourceBody274_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_8 sourceBody274_86

def sourceBody274_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody274_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_87 sourceBody274_88

def sourceBody274_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody274_91 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody274_89 sourceBody274_90

def sourceBody274_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_91 sourceBody274_5

def sourceBody274_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_92 sourceBody274_8

def sourceBody274_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_45 sourceBody274_93

def sourceBody274_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_44 sourceBody274_94

def sourceBody274_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_40 sourceBody274_95

def sourceBody274_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_39 sourceBody274_96

def sourceBody274_98 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody274_97 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody274_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_98 sourceBody274_5

def sourceBody274_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_5 sourceBody274_99

def sourceBody274_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody274_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_101 sourceBody274_8

def sourceBody274_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_102 sourceBody274_8

def sourceBody274_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_100 sourceBody274_103

def sourceBody274_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.var 18,
              Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
                (Flapjack.WordLangExpHOL.const 3#64)]),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody274_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 8,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody274_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody274_108 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody274_8, 274, 10)) (some 79) ([20, 6, 14]) (some (20, sourceBody274_48, 274, 11))

def sourceBody274_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_108 sourceBody274_5

def sourceBody274_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_109 sourceBody274_8

def sourceBody274_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_107 sourceBody274_110

def sourceBody274_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_106 sourceBody274_111

def sourceBody274_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_105 sourceBody274_112

def sourceBody274_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody274_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody274_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody274_117 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.WordRegImm.reg 14) sourceBody274_115 sourceBody274_116

def sourceBody274_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_117 sourceBody274_5

def sourceBody274_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody274_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody274_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 20)

def sourceBody274_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_121 sourceBody274_8

def sourceBody274_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_122 sourceBody274_8

def sourceBody274_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_120 sourceBody274_123

def sourceBody274_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_8 sourceBody274_124

def sourceBody274_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody274_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_126 sourceBody274_48

def sourceBody274_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_125 sourceBody274_127

def sourceBody274_129 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody274_128 sourceBody274_8

def sourceBody274_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_129 sourceBody274_5

def sourceBody274_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_130 sourceBody274_8

def sourceBody274_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_119 sourceBody274_131

def sourceBody274_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_118 sourceBody274_132

def sourceBody274_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_114 sourceBody274_133

def sourceBody274_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_55 sourceBody274_134

def sourceBody274_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_135 sourceBody274_83

def sourceBody274_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_113 sourceBody274_136

def sourceBody274_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_8 sourceBody274_137

def sourceBody274_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_8 sourceBody274_138

def sourceBody274_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_139 sourceBody274_88

def sourceBody274_141 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody274_140 sourceBody274_90

def sourceBody274_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_141 sourceBody274_5

def sourceBody274_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_142 sourceBody274_8

def sourceBody274_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_45 sourceBody274_143

def sourceBody274_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_44 sourceBody274_144

def sourceBody274_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_40 sourceBody274_145

def sourceBody274_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_39 sourceBody274_146

def sourceBody274_148 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody274_147 (Flapjack.Spt.bs
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody274_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_148 sourceBody274_5

def sourceBody274_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_5 sourceBody274_149

def sourceBody274_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_104 sourceBody274_150

def sourceBody274_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody274_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody274_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12, 20]

def sourceBody274_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_154 sourceBody274_8

def sourceBody274_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_153 sourceBody274_155

def sourceBody274_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_152 sourceBody274_156

def sourceBody274_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_151 sourceBody274_157

def sourceBody274_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_38 sourceBody274_158

def sourceBody274_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_8 sourceBody274_159

def sourceBody274_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_37 sourceBody274_160

def sourceBody274_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_8 sourceBody274_161

def sourceBody274_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_8 sourceBody274_162

def sourceBody274_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_31 sourceBody274_163

def sourceBody274_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_8 sourceBody274_164

def sourceBody274_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_8 sourceBody274_165

def sourceBody274_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody274_25 sourceBody274_166

def source274 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (274, 3, sourceBody274_167)
end InitECandidate.Proofs.WordStages
