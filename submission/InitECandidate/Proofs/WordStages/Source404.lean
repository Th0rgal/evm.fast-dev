import InitECandidate.Proofs.WordStages.Source388
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody404_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody404_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody404_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 136#64]))

def sourceBody404_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody404_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody404_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody404_0, 404, 2)) (some 79) ([8, 16, 12]) (some (8, sourceBody404_4, 404, 3))

def sourceBody404_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody404_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_5 sourceBody404_6

def sourceBody404_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_7 sourceBody404_0

def sourceBody404_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_3 sourceBody404_8

def sourceBody404_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_2 sourceBody404_9

def sourceBody404_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_1 sourceBody404_10

def sourceBody404_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody404_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody404_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody404_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody404_16 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 12) sourceBody404_14 sourceBody404_15

def sourceBody404_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_16 sourceBody404_6

def sourceBody404_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody404_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody404_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8, 16]

def sourceBody404_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_20 sourceBody404_0

def sourceBody404_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_15 sourceBody404_21

def sourceBody404_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_19 sourceBody404_22

def sourceBody404_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody404_23 sourceBody404_0

def sourceBody404_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_24 sourceBody404_6

def sourceBody404_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_25 sourceBody404_0

def sourceBody404_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_18 sourceBody404_26

def sourceBody404_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_17 sourceBody404_27

def sourceBody404_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_13 sourceBody404_28

def sourceBody404_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_12 sourceBody404_29

def sourceBody404_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
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
        Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody404_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody404_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody404_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 16]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody404_0, 404, 4)) (some 186) ([12, 20]) (some (12, sourceBody404_33, 404, 5))

def sourceBody404_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_34 sourceBody404_6

def sourceBody404_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_35 sourceBody404_0

def sourceBody404_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_32 sourceBody404_36

def sourceBody404_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_31 sourceBody404_37

def sourceBody404_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody404_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody404_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody404_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody404_43 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.reg 6) sourceBody404_41 sourceBody404_42

def sourceBody404_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_43 sourceBody404_6

def sourceBody404_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody404_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 16))

def sourceBody404_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody404_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12, 20]

def sourceBody404_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_48 sourceBody404_0

def sourceBody404_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_47 sourceBody404_49

def sourceBody404_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_46 sourceBody404_50

def sourceBody404_52 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody404_51 sourceBody404_0

def sourceBody404_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_52 sourceBody404_6

def sourceBody404_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_53 sourceBody404_0

def sourceBody404_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_45 sourceBody404_54

def sourceBody404_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_44 sourceBody404_55

def sourceBody404_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_40 sourceBody404_56

def sourceBody404_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_39 sourceBody404_57

def sourceBody404_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
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
        Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody404_60 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 16]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody404_0, 404, 6)) (some 186) ([12, 20]) (some (12, sourceBody404_33, 404, 7))

def sourceBody404_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_60 sourceBody404_6

def sourceBody404_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_61 sourceBody404_0

def sourceBody404_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_32 sourceBody404_62

def sourceBody404_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_59 sourceBody404_63

def sourceBody404_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_58 sourceBody404_64

def sourceBody404_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_65 sourceBody404_58

def sourceBody404_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody404_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody404_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody404_70 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody404_0, 404, 8)) (some 388) ([20, 6]) (some (20, sourceBody404_69, 404, 9))

def sourceBody404_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_70 sourceBody404_6

def sourceBody404_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_71 sourceBody404_0

def sourceBody404_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_68 sourceBody404_72

def sourceBody404_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_67 sourceBody404_73

def sourceBody404_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
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
        Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody404_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody404_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody404_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody404_79 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody404_0, 404, 10)) (some 192) ([6, 14, 10]) (some (6, sourceBody404_78, 404, 11))

def sourceBody404_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_79 sourceBody404_6

def sourceBody404_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_80 sourceBody404_0

def sourceBody404_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_77 sourceBody404_81

def sourceBody404_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_76 sourceBody404_82

def sourceBody404_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_75 sourceBody404_83

def sourceBody404_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_0 sourceBody404_84

def sourceBody404_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_0 sourceBody404_85

def sourceBody404_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody404_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody404_89 : WordLangProgHOL (BitVec 64) :=
.call (some (([20, 6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody404_0, 404, 12)) (some 398) ([14]) (some (14, sourceBody404_88, 404, 13))

def sourceBody404_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_89 sourceBody404_6

def sourceBody404_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_90 sourceBody404_0

def sourceBody404_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_87 sourceBody404_91

def sourceBody404_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody404_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14, 10]

def sourceBody404_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_94 sourceBody404_0

def sourceBody404_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_93 sourceBody404_95

def sourceBody404_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_45 sourceBody404_96

def sourceBody404_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_92 sourceBody404_97

def sourceBody404_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_0 sourceBody404_98

def sourceBody404_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_0 sourceBody404_99

def sourceBody404_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_0 sourceBody404_100

def sourceBody404_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_0 sourceBody404_101

def sourceBody404_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_86 sourceBody404_102

def sourceBody404_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_74 sourceBody404_103

def sourceBody404_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_0 sourceBody404_104

def sourceBody404_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_0 sourceBody404_105

def sourceBody404_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_66 sourceBody404_106

def sourceBody404_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_38 sourceBody404_107

def sourceBody404_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_0 sourceBody404_108

def sourceBody404_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_0 sourceBody404_109

def sourceBody404_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_0 sourceBody404_110

def sourceBody404_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_0 sourceBody404_111

def sourceBody404_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_30 sourceBody404_112

def sourceBody404_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_11 sourceBody404_113

def sourceBody404_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_0 sourceBody404_114

def sourceBody404_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody404_0 sourceBody404_115

def source404 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (404, 3, sourceBody404_116)
end InitECandidate.Proofs.WordStages
