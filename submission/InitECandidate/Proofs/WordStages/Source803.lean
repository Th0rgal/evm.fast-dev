import InitECandidate.Proofs.WordStages.Source787
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody803_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody803_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 2)

def sourceBody803_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody803_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody803_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([36, 10, 30, 20]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody803_0, 803, 2)) (some 146) ([42, 8]) (some (42, sourceBody803_3, 803, 3))

def sourceBody803_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody803_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_4 sourceBody803_5

def sourceBody803_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_6 sourceBody803_0

def sourceBody803_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_2 sourceBody803_7

def sourceBody803_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_1 sourceBody803_8

def sourceBody803_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 392#64]),
        Flapjack.WordLangExpHOL.const 1344#64]))

def sourceBody803_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 392#64]),
            Flapjack.WordLangExpHOL.const 1344#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody803_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 392#64]),
            Flapjack.WordLangExpHOL.const 1344#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody803_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 392#64]),
            Flapjack.WordLangExpHOL.const 1344#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody803_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 36)

def sourceBody803_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 10)

def sourceBody803_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 30)

def sourceBody803_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 20)

def sourceBody803_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody803_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody803_0, 803, 4)) (some 102) ([14, 34, 24, 46]) (some (14, sourceBody803_18, 803, 5))

def sourceBody803_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_19 sourceBody803_5

def sourceBody803_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_20 sourceBody803_0

def sourceBody803_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_17 sourceBody803_21

def sourceBody803_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_16 sourceBody803_22

def sourceBody803_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_15 sourceBody803_23

def sourceBody803_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_14 sourceBody803_24

def sourceBody803_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 40)

def sourceBody803_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody803_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody803_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody803_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 34 (Flapjack.WordRegImm.reg 24) sourceBody803_28 sourceBody803_29

def sourceBody803_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_30 sourceBody803_5

def sourceBody803_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 34)

def sourceBody803_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody803_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody803_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody803_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody803_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 34)

def sourceBody803_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 14) 26

def sourceBody803_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_38 sourceBody803_0

def sourceBody803_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_37 sourceBody803_39

def sourceBody803_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 24)

def sourceBody803_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 8#64])
  26

def sourceBody803_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_42 sourceBody803_0

def sourceBody803_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_41 sourceBody803_43

def sourceBody803_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 46)

def sourceBody803_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 16#64])
  26

def sourceBody803_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_46 sourceBody803_0

def sourceBody803_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_45 sourceBody803_47

def sourceBody803_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody803_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 24#64])
  26

def sourceBody803_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_50 sourceBody803_0

def sourceBody803_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_49 sourceBody803_51

def sourceBody803_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_52 sourceBody803_0

def sourceBody803_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_48 sourceBody803_53

def sourceBody803_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_44 sourceBody803_54

def sourceBody803_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_40 sourceBody803_55

def sourceBody803_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_36 sourceBody803_56

def sourceBody803_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_57

def sourceBody803_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_35 sourceBody803_58

def sourceBody803_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_59

def sourceBody803_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_34 sourceBody803_60

def sourceBody803_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_61

def sourceBody803_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_29 sourceBody803_62

def sourceBody803_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_63

def sourceBody803_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_33 sourceBody803_64

def sourceBody803_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_65

def sourceBody803_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody803_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody803_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_68 sourceBody803_0

def sourceBody803_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_67 sourceBody803_69

def sourceBody803_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_66 sourceBody803_70

def sourceBody803_72 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 46 (Flapjack.WordRegImm.imm 0#64) sourceBody803_71 sourceBody803_0

def sourceBody803_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_72 sourceBody803_5

def sourceBody803_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_73 sourceBody803_0

def sourceBody803_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_32 sourceBody803_74

def sourceBody803_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_31 sourceBody803_75

def sourceBody803_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_27 sourceBody803_76

def sourceBody803_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_26 sourceBody803_77

def sourceBody803_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 42)

def sourceBody803_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 8)

def sourceBody803_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 28)

def sourceBody803_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 18)

def sourceBody803_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 36)

def sourceBody803_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody803_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 30)

def sourceBody803_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 20)

def sourceBody803_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody803_88 : WordLangProgHOL (BitVec 64) :=
.call (some (([14, 34, 24, 46]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody803_0, 803, 6)) (some 117) ([6, 26, 16, 38, 12, 32, 22, 44]) (some (6, sourceBody803_87, 803, 7))

def sourceBody803_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_88 sourceBody803_5

def sourceBody803_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_89 sourceBody803_0

def sourceBody803_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_86 sourceBody803_90

def sourceBody803_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_85 sourceBody803_91

def sourceBody803_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_84 sourceBody803_92

def sourceBody803_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_83 sourceBody803_93

def sourceBody803_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_82 sourceBody803_94

def sourceBody803_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_81 sourceBody803_95

def sourceBody803_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_80 sourceBody803_96

def sourceBody803_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_79 sourceBody803_97

def sourceBody803_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody803_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 14)

def sourceBody803_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 34)

def sourceBody803_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 24)

def sourceBody803_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 46)

def sourceBody803_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 26)

def sourceBody803_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 6) 32

def sourceBody803_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_105 sourceBody803_0

def sourceBody803_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_104 sourceBody803_106

def sourceBody803_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 16)

def sourceBody803_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 8#64]) 32

def sourceBody803_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_109 sourceBody803_0

def sourceBody803_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_108 sourceBody803_110

def sourceBody803_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 38)

def sourceBody803_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 16#64])
  32

def sourceBody803_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_113 sourceBody803_0

def sourceBody803_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_112 sourceBody803_114

def sourceBody803_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 12)

def sourceBody803_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 24#64])
  32

def sourceBody803_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_117 sourceBody803_0

def sourceBody803_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_116 sourceBody803_118

def sourceBody803_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_119 sourceBody803_0

def sourceBody803_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_115 sourceBody803_120

def sourceBody803_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_111 sourceBody803_121

def sourceBody803_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_107 sourceBody803_122

def sourceBody803_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_103 sourceBody803_123

def sourceBody803_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_124

def sourceBody803_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_102 sourceBody803_125

def sourceBody803_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_126

def sourceBody803_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_101 sourceBody803_127

def sourceBody803_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_128

def sourceBody803_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_100 sourceBody803_129

def sourceBody803_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_130

def sourceBody803_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_99 sourceBody803_131

def sourceBody803_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_132

def sourceBody803_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody803_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_134 sourceBody803_0

def sourceBody803_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_36 sourceBody803_135

def sourceBody803_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_133 sourceBody803_136

def sourceBody803_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_98 sourceBody803_137

def sourceBody803_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_138

def sourceBody803_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_139

def sourceBody803_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_140

def sourceBody803_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_141

def sourceBody803_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_142

def sourceBody803_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_143

def sourceBody803_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_144

def sourceBody803_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_145

def sourceBody803_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_78 sourceBody803_146

def sourceBody803_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_25 sourceBody803_147

def sourceBody803_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_148

def sourceBody803_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_149

def sourceBody803_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_13 sourceBody803_150

def sourceBody803_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_151

def sourceBody803_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_12 sourceBody803_152

def sourceBody803_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_153

def sourceBody803_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_11 sourceBody803_154

def sourceBody803_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_155

def sourceBody803_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_10 sourceBody803_156

def sourceBody803_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_157

def sourceBody803_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_9 sourceBody803_158

def sourceBody803_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_159

def sourceBody803_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_160

def sourceBody803_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_161

def sourceBody803_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_162

def sourceBody803_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_163

def sourceBody803_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_164

def sourceBody803_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_165

def sourceBody803_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody803_0 sourceBody803_166

def source803 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (803, 3, sourceBody803_167)
end InitECandidate.Proofs.WordStages
