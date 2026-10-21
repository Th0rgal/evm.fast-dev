import InitECandidate.Proofs.WordStages.Source596
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody612_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 131072#64)

def sourceBody612_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 14)

def sourceBody612_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody612_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 52 (Flapjack.WordRegImm.reg 36) sourceBody612_2 sourceBody612_3

def sourceBody612_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody612_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_4 sourceBody612_5

def sourceBody612_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 52)

def sourceBody612_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody612_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody612_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 20)

def sourceBody612_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_10 sourceBody612_8

def sourceBody612_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_11 sourceBody612_8

def sourceBody612_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_9 sourceBody612_12

def sourceBody612_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_13

def sourceBody612_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody612_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody612_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_15 sourceBody612_16

def sourceBody612_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_14 sourceBody612_17

def sourceBody612_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 68 (Flapjack.WordRegImm.imm 0#64) sourceBody612_18 sourceBody612_8

def sourceBody612_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_19 sourceBody612_5

def sourceBody612_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_20 sourceBody612_8

def sourceBody612_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_7 sourceBody612_21

def sourceBody612_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_6 sourceBody612_22

def sourceBody612_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_1 sourceBody612_23

def sourceBody612_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_0 sourceBody612_24

def sourceBody612_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 256#64]),
            Flapjack.WordLangExpHOL.const 24#64]),
      Flapjack.WordLangExpHOL.var 12])

def sourceBody612_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 264#64]))

def sourceBody612_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 68

def sourceBody612_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody612_8, 612, 2)) (some 609) ([68, 28]) (some (68, sourceBody612_29, 612, 3))

def sourceBody612_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_30 sourceBody612_5

def sourceBody612_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_31 sourceBody612_8

def sourceBody612_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_28 sourceBody612_32

def sourceBody612_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_7 sourceBody612_33

def sourceBody612_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_34

def sourceBody612_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_35

def sourceBody612_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody612_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody612_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 68)

def sourceBody612_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 60

def sourceBody612_41 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody612_8, 612, 4)) (some 403) ([60]) (some (60, sourceBody612_40, 612, 5))

def sourceBody612_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_41 sourceBody612_5

def sourceBody612_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_42 sourceBody612_8

def sourceBody612_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_39 sourceBody612_43

def sourceBody612_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody612_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody612_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody612_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody612_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 2)

def sourceBody612_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 4)

def sourceBody612_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody612_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 8)

def sourceBody612_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody612_54 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody612_8, 612, 6)) (some 106) ([44, 76, 18, 50, 34, 66, 26, 58]) (some (44, sourceBody612_53, 612, 7))

def sourceBody612_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_54 sourceBody612_5

def sourceBody612_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_55 sourceBody612_8

def sourceBody612_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_52 sourceBody612_56

def sourceBody612_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_51 sourceBody612_57

def sourceBody612_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_50 sourceBody612_58

def sourceBody612_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_49 sourceBody612_59

def sourceBody612_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_48 sourceBody612_60

def sourceBody612_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_47 sourceBody612_61

def sourceBody612_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_46 sourceBody612_62

def sourceBody612_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_45 sourceBody612_63

def sourceBody612_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 60)

def sourceBody612_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody612_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_69 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 76 (Flapjack.WordRegImm.reg 18) sourceBody612_67 sourceBody612_68

def sourceBody612_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_69 sourceBody612_5

def sourceBody612_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody612_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 18446744073709551615#64)

def sourceBody612_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody612_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_75 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 34 (Flapjack.WordRegImm.reg 66) sourceBody612_73 sourceBody612_74

def sourceBody612_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_75 sourceBody612_5

def sourceBody612_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 1024#64)

def sourceBody612_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.const 128#64]),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody612_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody612_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_81 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 58 (Flapjack.WordRegImm.reg 42) sourceBody612_79 sourceBody612_80

def sourceBody612_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_81 sourceBody612_5

def sourceBody612_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 76, Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.var 58])

def sourceBody612_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody612_86 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.reg 54) sourceBody612_85 sourceBody612_83

def sourceBody612_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_86 sourceBody612_5

def sourceBody612_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 22)

def sourceBody612_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 76

def sourceBody612_91 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody612_8, 612, 8)) (some 472) ([76, 18, 50, 34]) (some (76, sourceBody612_90, 612, 9))

def sourceBody612_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_91 sourceBody612_5

def sourceBody612_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_92 sourceBody612_8

def sourceBody612_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_74 sourceBody612_93

def sourceBody612_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_89 sourceBody612_94

def sourceBody612_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_66 sourceBody612_95

def sourceBody612_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_68 sourceBody612_96

def sourceBody612_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_97

def sourceBody612_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_98

def sourceBody612_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [44]

def sourceBody612_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_101 sourceBody612_8

def sourceBody612_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_100 sourceBody612_102

def sourceBody612_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_99 sourceBody612_103

def sourceBody612_105 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.imm 0#64) sourceBody612_104 sourceBody612_8

def sourceBody612_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_105 sourceBody612_5

def sourceBody612_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_106 sourceBody612_8

def sourceBody612_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_88 sourceBody612_107

def sourceBody612_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_87 sourceBody612_108

def sourceBody612_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_84 sourceBody612_109

def sourceBody612_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_83 sourceBody612_110

def sourceBody612_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_82 sourceBody612_111

def sourceBody612_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_78 sourceBody612_112

def sourceBody612_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_77 sourceBody612_113

def sourceBody612_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_76 sourceBody612_114

def sourceBody612_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_72 sourceBody612_115

def sourceBody612_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_71 sourceBody612_116

def sourceBody612_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_70 sourceBody612_117

def sourceBody612_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_66 sourceBody612_118

def sourceBody612_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_65 sourceBody612_119

def sourceBody612_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 10)

def sourceBody612_122 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody612_8, 612, 10)) (some 490) ([76]) (some (76, sourceBody612_90, 612, 11))

def sourceBody612_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_122 sourceBody612_5

def sourceBody612_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_123 sourceBody612_8

def sourceBody612_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_121 sourceBody612_124

def sourceBody612_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_125

def sourceBody612_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_126

def sourceBody612_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_120 sourceBody612_127

def sourceBody612_129 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody612_8, 612, 12)) (some 414) ([76]) (some (76, sourceBody612_90, 612, 13))

def sourceBody612_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_129 sourceBody612_5

def sourceBody612_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_130 sourceBody612_8

def sourceBody612_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_121 sourceBody612_131

def sourceBody612_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 44)

def sourceBody612_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody612_135 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 50 (Flapjack.WordRegImm.reg 34) sourceBody612_134 sourceBody612_89

def sourceBody612_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_135 sourceBody612_5

def sourceBody612_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 50)

def sourceBody612_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_67 sourceBody612_8

def sourceBody612_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_138 sourceBody612_8

def sourceBody612_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 183600#64)

def sourceBody612_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 50

def sourceBody612_142 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody612_8, 612, 14)) (some 467) ([50]) (some (50, sourceBody612_141, 612, 15))

def sourceBody612_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_142 sourceBody612_5

def sourceBody612_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_143 sourceBody612_8

def sourceBody612_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_140 sourceBody612_144

def sourceBody612_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_145

def sourceBody612_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_146

def sourceBody612_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_139 sourceBody612_147

def sourceBody612_149 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 66 (Flapjack.WordRegImm.imm 0#64) sourceBody612_148 sourceBody612_8

def sourceBody612_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_149 sourceBody612_5

def sourceBody612_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_150 sourceBody612_8

def sourceBody612_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_137 sourceBody612_151

def sourceBody612_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_136 sourceBody612_152

def sourceBody612_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_74 sourceBody612_153

def sourceBody612_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_133 sourceBody612_154

def sourceBody612_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody612_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.var 18,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 18)
        (Flapjack.WordLangExpHOL.const 6#64)])

def sourceBody612_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 64#64])

def sourceBody612_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 50])

def sourceBody612_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 66)

def sourceBody612_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 34) 26

def sourceBody612_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_161 sourceBody612_8

def sourceBody612_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_160 sourceBody612_162

def sourceBody612_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_163 sourceBody612_8

def sourceBody612_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_159 sourceBody612_164

def sourceBody612_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_165

def sourceBody612_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_158 sourceBody612_166

def sourceBody612_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_167

def sourceBody612_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 10)

def sourceBody612_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 66

def sourceBody612_171 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody612_8, 612, 16)) (some 411) ([66]) (some (66, sourceBody612_170, 612, 17))

def sourceBody612_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_171 sourceBody612_5

def sourceBody612_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_172 sourceBody612_8

def sourceBody612_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_169 sourceBody612_173

def sourceBody612_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 34)

def sourceBody612_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody612_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_178 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 26 (Flapjack.WordRegImm.reg 58) sourceBody612_176 sourceBody612_177

def sourceBody612_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_178 sourceBody612_5

def sourceBody612_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 26)

def sourceBody612_181 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 68)

def sourceBody612_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody612_183 : WordLangProgHOL (BitVec 64) :=
.call (some (([66]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          Flapjack.Spt.ln)
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody612_8, 612, 18)) (some 426) ([26]) (some (26, sourceBody612_182, 612, 19))

def sourceBody612_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_183 sourceBody612_5

def sourceBody612_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_184 sourceBody612_8

def sourceBody612_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_181 sourceBody612_185

def sourceBody612_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_186

def sourceBody612_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_187

def sourceBody612_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 184#64])

def sourceBody612_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 256#64]),
            Flapjack.WordLangExpHOL.const 184#64]),
      Flapjack.WordLangExpHOL.var 50])

def sourceBody612_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 26)

def sourceBody612_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 66) 58

def sourceBody612_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_192 sourceBody612_8

def sourceBody612_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_191 sourceBody612_193

def sourceBody612_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_194 sourceBody612_8

def sourceBody612_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_190 sourceBody612_195

def sourceBody612_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_196

def sourceBody612_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_189 sourceBody612_197

def sourceBody612_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_198

def sourceBody612_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_188 sourceBody612_199

def sourceBody612_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 76)

def sourceBody612_202 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.reg 58) sourceBody612_176 sourceBody612_177

def sourceBody612_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_202 sourceBody612_5

def sourceBody612_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 183600#64)

def sourceBody612_205 : WordLangProgHOL (BitVec 64) :=
.call (some (([66]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody612_8, 612, 20)) (some 468) ([26]) (some (26, sourceBody612_182, 612, 21))

def sourceBody612_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_205 sourceBody612_5

def sourceBody612_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_206 sourceBody612_8

def sourceBody612_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_204 sourceBody612_207

def sourceBody612_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_208

def sourceBody612_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_209

def sourceBody612_211 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.imm 0#64) sourceBody612_210 sourceBody612_8

def sourceBody612_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_211 sourceBody612_5

def sourceBody612_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_212 sourceBody612_8

def sourceBody612_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_180 sourceBody612_213

def sourceBody612_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_203 sourceBody612_214

def sourceBody612_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_80 sourceBody612_215

def sourceBody612_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_201 sourceBody612_216

def sourceBody612_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_200 sourceBody612_217

def sourceBody612_219 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_221 : WordLangProgHOL (BitVec 64) :=
.call (some (([66]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody612_8, 612, 22)) (some 472) ([26, 58, 42, 74]) (some (26, sourceBody612_182, 612, 23))

def sourceBody612_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_221 sourceBody612_5

def sourceBody612_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_222 sourceBody612_8

def sourceBody612_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_220 sourceBody612_223

def sourceBody612_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_219 sourceBody612_224

def sourceBody612_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_80 sourceBody612_225

def sourceBody612_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_177 sourceBody612_226

def sourceBody612_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_227

def sourceBody612_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_228

def sourceBody612_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_218 sourceBody612_229

def sourceBody612_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [66]

def sourceBody612_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_232 sourceBody612_8

def sourceBody612_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_231 sourceBody612_233

def sourceBody612_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_230 sourceBody612_234

def sourceBody612_236 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.imm 0#64) sourceBody612_235 sourceBody612_8

def sourceBody612_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_236 sourceBody612_5

def sourceBody612_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_237 sourceBody612_8

def sourceBody612_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_180 sourceBody612_238

def sourceBody612_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_179 sourceBody612_239

def sourceBody612_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_80 sourceBody612_240

def sourceBody612_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_175 sourceBody612_241

def sourceBody612_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 72#64]))

def sourceBody612_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 72#64])

def sourceBody612_245 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 58)

def sourceBody612_246 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 26) 42

def sourceBody612_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_246 sourceBody612_8

def sourceBody612_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_245 sourceBody612_247

def sourceBody612_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_248 sourceBody612_8

def sourceBody612_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_80 sourceBody612_249

def sourceBody612_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_250

def sourceBody612_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_244 sourceBody612_251

def sourceBody612_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_252

def sourceBody612_254 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 68)

def sourceBody612_255 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 58

def sourceBody612_256 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody612_8, 612, 24)) (some 426) ([58]) (some (58, sourceBody612_255, 612, 25))

def sourceBody612_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_256 sourceBody612_5

def sourceBody612_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_257 sourceBody612_8

def sourceBody612_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_254 sourceBody612_258

def sourceBody612_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_259

def sourceBody612_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_260

def sourceBody612_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_253 sourceBody612_261

def sourceBody612_263 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody612_8, 612, 26)) (some 75) ([]) (some (58, sourceBody612_255, 612, 27))

def sourceBody612_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_263 sourceBody612_5

def sourceBody612_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_264 sourceBody612_8

def sourceBody612_266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody612_267 : WordLangProgHOL (BitVec 64) :=
.call (some (([58]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody612_8, 612, 28)) (some 72) ([]) (some (42, sourceBody612_266, 612, 29))

def sourceBody612_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_267 sourceBody612_5

def sourceBody612_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_268 sourceBody612_8

def sourceBody612_270 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 68)

def sourceBody612_271 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 10)

def sourceBody612_272 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 50)

def sourceBody612_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 66)

def sourceBody612_274 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 2)

def sourceBody612_275 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 4)

def sourceBody612_276 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 6)

def sourceBody612_277 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 8)

def sourceBody612_278 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 52)

def sourceBody612_279 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_280 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_281 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 20)

def sourceBody612_282 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody612_283 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody612_284 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_285 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_286 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 74

def sourceBody612_287 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          Flapjack.Spt.ln)
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody612_8, 612, 30)) (some 608) ([74, 22, 54, 38, 70, 30, 62, 46, 78, 16, 48, 32, 64, 24, 56, 40, 72]) (some (74, sourceBody612_286, 612, 31))

def sourceBody612_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_287 sourceBody612_5

def sourceBody612_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_288 sourceBody612_8

def sourceBody612_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_285 sourceBody612_289

def sourceBody612_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_284 sourceBody612_290

def sourceBody612_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_283 sourceBody612_291

def sourceBody612_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_282 sourceBody612_292

def sourceBody612_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_281 sourceBody612_293

def sourceBody612_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_280 sourceBody612_294

def sourceBody612_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_279 sourceBody612_295

def sourceBody612_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_278 sourceBody612_296

def sourceBody612_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_277 sourceBody612_297

def sourceBody612_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_276 sourceBody612_298

def sourceBody612_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_275 sourceBody612_299

def sourceBody612_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_274 sourceBody612_300

def sourceBody612_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_273 sourceBody612_301

def sourceBody612_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_272 sourceBody612_302

def sourceBody612_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_271 sourceBody612_303

def sourceBody612_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_83 sourceBody612_304

def sourceBody612_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_270 sourceBody612_305

def sourceBody612_307 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 42)

def sourceBody612_308 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody612_309 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 26)

def sourceBody612_310 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 58)

def sourceBody612_311 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 76)

def sourceBody612_312 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_313 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody612_314 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 10)

def sourceBody612_315 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody612_316 : WordLangProgHOL (BitVec 64) :=
.call (some (([74]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody612_8, 612, 32)) (some 599) ([22, 54, 38, 70, 30, 62, 46, 78]) (some (22, sourceBody612_315, 612, 33))

def sourceBody612_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_316 sourceBody612_5

def sourceBody612_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_317 sourceBody612_8

def sourceBody612_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_314 sourceBody612_318

def sourceBody612_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_313 sourceBody612_319

def sourceBody612_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_312 sourceBody612_320

def sourceBody612_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_311 sourceBody612_321

def sourceBody612_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_310 sourceBody612_322

def sourceBody612_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_309 sourceBody612_323

def sourceBody612_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_308 sourceBody612_324

def sourceBody612_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_307 sourceBody612_325

def sourceBody612_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_326

def sourceBody612_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_327

def sourceBody612_329 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody612_330 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [74]

def sourceBody612_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_330 sourceBody612_8

def sourceBody612_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_329 sourceBody612_331

def sourceBody612_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_328 sourceBody612_332

def sourceBody612_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_306 sourceBody612_333

def sourceBody612_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_334

def sourceBody612_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_335

def sourceBody612_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_269 sourceBody612_336

def sourceBody612_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_337

def sourceBody612_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_338

def sourceBody612_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_265 sourceBody612_339

def sourceBody612_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_340

def sourceBody612_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_341

def sourceBody612_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_262 sourceBody612_342

def sourceBody612_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_243 sourceBody612_343

def sourceBody612_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_344

def sourceBody612_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_242 sourceBody612_345

def sourceBody612_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_174 sourceBody612_346

def sourceBody612_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_347

def sourceBody612_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_348

def sourceBody612_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_168 sourceBody612_349

def sourceBody612_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_157 sourceBody612_350

def sourceBody612_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_351

def sourceBody612_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_156 sourceBody612_352

def sourceBody612_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_353

def sourceBody612_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_155 sourceBody612_354

def sourceBody612_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_68 sourceBody612_355

def sourceBody612_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_356

def sourceBody612_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_132 sourceBody612_357

def sourceBody612_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_358

def sourceBody612_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_359

def sourceBody612_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_128 sourceBody612_360

def sourceBody612_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_64 sourceBody612_361

def sourceBody612_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_362

def sourceBody612_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_363

def sourceBody612_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_44 sourceBody612_364

def sourceBody612_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_365

def sourceBody612_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_366

def sourceBody612_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_38 sourceBody612_367

def sourceBody612_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_368

def sourceBody612_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_37 sourceBody612_369

def sourceBody612_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_370

def sourceBody612_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_36 sourceBody612_371

def sourceBody612_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_27 sourceBody612_372

def sourceBody612_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_373

def sourceBody612_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_26 sourceBody612_374

def sourceBody612_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_8 sourceBody612_375

def sourceBody612_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody612_25 sourceBody612_376

def source612 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (612, 8, sourceBody612_377)
end InitECandidate.Proofs.WordStages
