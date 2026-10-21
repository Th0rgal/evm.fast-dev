import InitECandidate.Proofs.WordStages.Source390
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody406_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody406_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody406_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody406_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody406_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody406_0, 406, 2)) (some 388) ([8, 18]) (some (8, sourceBody406_3, 406, 3))

def sourceBody406_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody406_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_4 sourceBody406_5

def sourceBody406_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_6 sourceBody406_0

def sourceBody406_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_2 sourceBody406_7

def sourceBody406_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_1 sourceBody406_8

def sourceBody406_10 : WordLangProgHOL (BitVec 64) :=
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
              Flapjack.WordLangExpHOL.const 184#64]),
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody406_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 22)

def sourceBody406_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody406_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody406_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody406_0, 406, 4)) (some 192) ([18, 14, 26]) (some (18, sourceBody406_13, 406, 5))

def sourceBody406_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_14 sourceBody406_5

def sourceBody406_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_15 sourceBody406_0

def sourceBody406_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_12 sourceBody406_16

def sourceBody406_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_11 sourceBody406_17

def sourceBody406_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_10 sourceBody406_18

def sourceBody406_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_19

def sourceBody406_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_20

def sourceBody406_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 184#64]),
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody406_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 2)

def sourceBody406_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody406_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody406_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 18]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody406_0, 406, 6)) (some 405) ([14, 26, 6]) (some (14, sourceBody406_25, 406, 7))

def sourceBody406_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_26 sourceBody406_5

def sourceBody406_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_27 sourceBody406_0

def sourceBody406_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_24 sourceBody406_28

def sourceBody406_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_23 sourceBody406_29

def sourceBody406_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_22 sourceBody406_30

def sourceBody406_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 8)

def sourceBody406_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody406_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody406_35 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.reg 6) sourceBody406_12 sourceBody406_34

def sourceBody406_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_35 sourceBody406_5

def sourceBody406_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 26)

def sourceBody406_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 18))

def sourceBody406_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody406_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody406_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody406_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14, 26, 6, 16]

def sourceBody406_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_42 sourceBody406_0

def sourceBody406_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_41 sourceBody406_43

def sourceBody406_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_40 sourceBody406_44

def sourceBody406_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_39 sourceBody406_45

def sourceBody406_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_38 sourceBody406_46

def sourceBody406_48 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody406_47 sourceBody406_0

def sourceBody406_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_48 sourceBody406_5

def sourceBody406_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_49 sourceBody406_0

def sourceBody406_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_37 sourceBody406_50

def sourceBody406_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_36 sourceBody406_51

def sourceBody406_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_33 sourceBody406_52

def sourceBody406_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_32 sourceBody406_53

def sourceBody406_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 176#64]),
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody406_56 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 18]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody406_0, 406, 8)) (some 405) ([14, 26, 6]) (some (14, sourceBody406_25, 406, 9))

def sourceBody406_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_56 sourceBody406_5

def sourceBody406_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_57 sourceBody406_0

def sourceBody406_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_24 sourceBody406_58

def sourceBody406_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_23 sourceBody406_59

def sourceBody406_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_55 sourceBody406_60

def sourceBody406_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_54 sourceBody406_61

def sourceBody406_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_62 sourceBody406_54

def sourceBody406_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody406_65 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody406_0, 406, 10)) (some 392) ([26]) (some (26, sourceBody406_64, 406, 11))

def sourceBody406_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_65 sourceBody406_5

def sourceBody406_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_66 sourceBody406_0

def sourceBody406_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_23 sourceBody406_67

def sourceBody406_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_68

def sourceBody406_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_69

def sourceBody406_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_63 sourceBody406_70

def sourceBody406_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody406_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody406_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody406_75 : WordLangProgHOL (BitVec 64) :=
.call (some (([14, 26, 6, 16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody406_0, 406, 12)) (some 397) ([12, 24]) (some (12, sourceBody406_74, 406, 13))

def sourceBody406_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_75 sourceBody406_5

def sourceBody406_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_76 sourceBody406_0

def sourceBody406_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_73 sourceBody406_77

def sourceBody406_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_72 sourceBody406_78

def sourceBody406_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody406_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody406_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody406_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody406_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12, 24, 10, 20]

def sourceBody406_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_84 sourceBody406_0

def sourceBody406_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_83 sourceBody406_85

def sourceBody406_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_82 sourceBody406_86

def sourceBody406_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_81 sourceBody406_87

def sourceBody406_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_80 sourceBody406_88

def sourceBody406_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_79 sourceBody406_89

def sourceBody406_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_90

def sourceBody406_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_91

def sourceBody406_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_92

def sourceBody406_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_93

def sourceBody406_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_94

def sourceBody406_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_95

def sourceBody406_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_96

def sourceBody406_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_97

def sourceBody406_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_71 sourceBody406_98

def sourceBody406_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_31 sourceBody406_99

def sourceBody406_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_100

def sourceBody406_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_101

def sourceBody406_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_102

def sourceBody406_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_103

def sourceBody406_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_21 sourceBody406_104

def sourceBody406_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_9 sourceBody406_105

def sourceBody406_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_106

def sourceBody406_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody406_0 sourceBody406_107

def source406 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (406, 3, sourceBody406_108)
end InitECandidate.Proofs.WordStages
