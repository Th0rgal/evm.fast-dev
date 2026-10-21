import InitECandidate.Proofs.WordStages.Source554
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody570_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody570_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody570_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 26, 6, 22]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody570_0, 570, 2)) (some 471) ([]) (some (14, sourceBody570_1, 570, 3))

def sourceBody570_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody570_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_2 sourceBody570_3

def sourceBody570_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_4 sourceBody570_0

def sourceBody570_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody570_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody570_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody570_0, 570, 4)) (some 466) ([30]) (some (30, sourceBody570_7, 570, 5))

def sourceBody570_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_8 sourceBody570_3

def sourceBody570_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_9 sourceBody570_0

def sourceBody570_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_6 sourceBody570_10

def sourceBody570_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_11

def sourceBody570_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_12

def sourceBody570_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
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
              Flapjack.WordLangExpHOL.const 112#64]),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody570_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 136#64]))

def sourceBody570_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 10)

def sourceBody570_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 26)

def sourceBody570_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 6)

def sourceBody570_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 22)

def sourceBody570_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody570_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody570_0, 570, 6)) (some 458) ([20, 12, 28, 8]) (some (20, sourceBody570_20, 570, 7))

def sourceBody570_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_21 sourceBody570_3

def sourceBody570_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_22 sourceBody570_0

def sourceBody570_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_19 sourceBody570_23

def sourceBody570_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_18 sourceBody570_24

def sourceBody570_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_17 sourceBody570_25

def sourceBody570_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_16 sourceBody570_26

def sourceBody570_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody570_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 30)

def sourceBody570_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody570_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody570_32 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 12 (Flapjack.WordRegImm.reg 28) sourceBody570_30 sourceBody570_31

def sourceBody570_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_32 sourceBody570_3

def sourceBody570_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody570_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 128#64]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody570_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody570_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody570_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([20, 12, 28, 8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody570_0, 570, 8)) (some 146) ([24, 16]) (some (24, sourceBody570_37, 570, 9))

def sourceBody570_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_38 sourceBody570_3

def sourceBody570_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_39 sourceBody570_0

def sourceBody570_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_36 sourceBody570_40

def sourceBody570_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_35 sourceBody570_41

def sourceBody570_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody570_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 12)

def sourceBody570_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 28)

def sourceBody570_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody570_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody570_48 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody570_0, 570, 10)) (some 472) ([16, 32, 2, 18]) (some (16, sourceBody570_47, 570, 11))

def sourceBody570_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_48 sourceBody570_3

def sourceBody570_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_49 sourceBody570_0

def sourceBody570_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_46 sourceBody570_50

def sourceBody570_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_45 sourceBody570_51

def sourceBody570_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_44 sourceBody570_52

def sourceBody570_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_43 sourceBody570_53

def sourceBody570_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_54

def sourceBody570_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_55

def sourceBody570_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_42 sourceBody570_56

def sourceBody570_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_57

def sourceBody570_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_58

def sourceBody570_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_59

def sourceBody570_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_60

def sourceBody570_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_61

def sourceBody570_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_62

def sourceBody570_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_63

def sourceBody570_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_64

def sourceBody570_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody570_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody570_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody570_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody570_70 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody570_0, 570, 12)) (some 472) ([12, 28, 8, 24]) (some (12, sourceBody570_69, 570, 13))

def sourceBody570_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_70 sourceBody570_3

def sourceBody570_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_71 sourceBody570_0

def sourceBody570_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_68 sourceBody570_72

def sourceBody570_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_67 sourceBody570_73

def sourceBody570_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_66 sourceBody570_74

def sourceBody570_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_31 sourceBody570_75

def sourceBody570_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_76

def sourceBody570_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_77

def sourceBody570_79 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody570_65 sourceBody570_78

def sourceBody570_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_79 sourceBody570_3

def sourceBody570_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_80 sourceBody570_0

def sourceBody570_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_34 sourceBody570_81

def sourceBody570_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_33 sourceBody570_82

def sourceBody570_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_29 sourceBody570_83

def sourceBody570_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_28 sourceBody570_84

def sourceBody570_86 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody570_0, 570, 14)) (some 486) ([12]) (some (12, sourceBody570_69, 570, 15))

def sourceBody570_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_86 sourceBody570_3

def sourceBody570_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_87 sourceBody570_0

def sourceBody570_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_30 sourceBody570_88

def sourceBody570_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_89

def sourceBody570_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_90

def sourceBody570_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_85 sourceBody570_91

def sourceBody570_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody570_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody570_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_94 sourceBody570_0

def sourceBody570_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_93 sourceBody570_95

def sourceBody570_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_92 sourceBody570_96

def sourceBody570_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_27 sourceBody570_97

def sourceBody570_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_98

def sourceBody570_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_99

def sourceBody570_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_15 sourceBody570_100

def sourceBody570_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_101

def sourceBody570_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_14 sourceBody570_102

def sourceBody570_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_103

def sourceBody570_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_13 sourceBody570_104

def sourceBody570_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_5 sourceBody570_105

def sourceBody570_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_106

def sourceBody570_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_107

def sourceBody570_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_108

def sourceBody570_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_109

def sourceBody570_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_110

def sourceBody570_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_111

def sourceBody570_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_112

def sourceBody570_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody570_0 sourceBody570_113

def source570 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (570, 1, sourceBody570_114)
end InitECandidate.Proofs.WordStages
