import InitECandidate.Proofs.WordStages.Source391
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody407_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody407_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
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
        Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody407_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody407_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody407_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody407_0, 407, 2)) (some 187) ([8, 18]) (some (8, sourceBody407_3, 407, 3))

def sourceBody407_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody407_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_4 sourceBody407_5

def sourceBody407_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_6 sourceBody407_0

def sourceBody407_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_2 sourceBody407_7

def sourceBody407_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_1 sourceBody407_8

def sourceBody407_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 22)

def sourceBody407_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody407_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody407_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody407_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.reg 14) sourceBody407_12 sourceBody407_13

def sourceBody407_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_14 sourceBody407_5

def sourceBody407_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 18)

def sourceBody407_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody407_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody407_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8, 18, 14, 26]

def sourceBody407_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_19 sourceBody407_0

def sourceBody407_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_18 sourceBody407_20

def sourceBody407_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_11 sourceBody407_21

def sourceBody407_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_13 sourceBody407_22

def sourceBody407_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_17 sourceBody407_23

def sourceBody407_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody407_24 sourceBody407_0

def sourceBody407_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_25 sourceBody407_5

def sourceBody407_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_26 sourceBody407_0

def sourceBody407_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_16 sourceBody407_27

def sourceBody407_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_15 sourceBody407_28

def sourceBody407_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_11 sourceBody407_29

def sourceBody407_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_10 sourceBody407_30

def sourceBody407_32 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody407_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 2)

def sourceBody407_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody407_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody407_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 18]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody407_0, 407, 4)) (some 405) ([14, 26, 6]) (some (14, sourceBody407_35, 407, 5))

def sourceBody407_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_36 sourceBody407_5

def sourceBody407_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_37 sourceBody407_0

def sourceBody407_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_34 sourceBody407_38

def sourceBody407_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_33 sourceBody407_39

def sourceBody407_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_32 sourceBody407_40

def sourceBody407_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 8)

def sourceBody407_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody407_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody407_45 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.reg 6) sourceBody407_44 sourceBody407_18

def sourceBody407_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_45 sourceBody407_5

def sourceBody407_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 26)

def sourceBody407_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 18))

def sourceBody407_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody407_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody407_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody407_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14, 26, 6, 16]

def sourceBody407_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_52 sourceBody407_0

def sourceBody407_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_51 sourceBody407_53

def sourceBody407_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_50 sourceBody407_54

def sourceBody407_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_49 sourceBody407_55

def sourceBody407_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_48 sourceBody407_56

def sourceBody407_58 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody407_57 sourceBody407_0

def sourceBody407_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_58 sourceBody407_5

def sourceBody407_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_59 sourceBody407_0

def sourceBody407_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_47 sourceBody407_60

def sourceBody407_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_46 sourceBody407_61

def sourceBody407_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_43 sourceBody407_62

def sourceBody407_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_42 sourceBody407_63

def sourceBody407_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody407_66 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody407_0, 407, 6)) (some 392) ([26]) (some (26, sourceBody407_65, 407, 7))

def sourceBody407_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_66 sourceBody407_5

def sourceBody407_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_67 sourceBody407_0

def sourceBody407_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_33 sourceBody407_68

def sourceBody407_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_0 sourceBody407_69

def sourceBody407_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_0 sourceBody407_70

def sourceBody407_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_64 sourceBody407_71

def sourceBody407_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody407_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody407_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody407_76 : WordLangProgHOL (BitVec 64) :=
.call (some (([14, 26, 6, 16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody407_0, 407, 8)) (some 397) ([12, 24]) (some (12, sourceBody407_75, 407, 9))

def sourceBody407_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_76 sourceBody407_5

def sourceBody407_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_77 sourceBody407_0

def sourceBody407_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_74 sourceBody407_78

def sourceBody407_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_73 sourceBody407_79

def sourceBody407_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody407_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody407_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody407_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody407_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12, 24, 10, 20]

def sourceBody407_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_85 sourceBody407_0

def sourceBody407_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_84 sourceBody407_86

def sourceBody407_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_83 sourceBody407_87

def sourceBody407_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_82 sourceBody407_88

def sourceBody407_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_81 sourceBody407_89

def sourceBody407_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_80 sourceBody407_90

def sourceBody407_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_0 sourceBody407_91

def sourceBody407_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_0 sourceBody407_92

def sourceBody407_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_0 sourceBody407_93

def sourceBody407_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_0 sourceBody407_94

def sourceBody407_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_0 sourceBody407_95

def sourceBody407_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_0 sourceBody407_96

def sourceBody407_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_0 sourceBody407_97

def sourceBody407_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_0 sourceBody407_98

def sourceBody407_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_72 sourceBody407_99

def sourceBody407_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_41 sourceBody407_100

def sourceBody407_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_0 sourceBody407_101

def sourceBody407_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_0 sourceBody407_102

def sourceBody407_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_0 sourceBody407_103

def sourceBody407_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_0 sourceBody407_104

def sourceBody407_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_31 sourceBody407_105

def sourceBody407_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_9 sourceBody407_106

def sourceBody407_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_0 sourceBody407_107

def sourceBody407_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody407_0 sourceBody407_108

def source407 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (407, 3, sourceBody407_109)
end InitECandidate.Proofs.WordStages
