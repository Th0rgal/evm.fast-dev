import InitECandidate.Proofs.WordStages.Source516
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody532_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody532_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody532_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody532_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody532_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 20 (Flapjack.WordRegImm.reg 6) sourceBody532_2 sourceBody532_3

def sourceBody532_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody532_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_4 sourceBody532_5

def sourceBody532_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody532_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody532_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody532_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody532_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody532_8, 532, 2)) (some 466) ([20]) (some (20, sourceBody532_10, 532, 3))

def sourceBody532_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_11 sourceBody532_5

def sourceBody532_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_12 sourceBody532_8

def sourceBody532_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_9 sourceBody532_13

def sourceBody532_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_14

def sourceBody532_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_15

def sourceBody532_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody532_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody532_8, 532, 4)) (some 466) ([20]) (some (20, sourceBody532_10, 532, 5))

def sourceBody532_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_18 sourceBody532_5

def sourceBody532_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_19 sourceBody532_8

def sourceBody532_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_17 sourceBody532_20

def sourceBody532_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_21

def sourceBody532_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_22

def sourceBody532_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody532_16 sourceBody532_23

def sourceBody532_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_24 sourceBody532_5

def sourceBody532_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_25 sourceBody532_8

def sourceBody532_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_7 sourceBody532_26

def sourceBody532_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_6 sourceBody532_27

def sourceBody532_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_1 sourceBody532_28

def sourceBody532_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_0 sourceBody532_29

def sourceBody532_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody532_8, 532, 6)) (some 69) ([]) (some (20, sourceBody532_10, 532, 7))

def sourceBody532_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_31 sourceBody532_5

def sourceBody532_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_32 sourceBody532_8

def sourceBody532_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody532_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody532_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody532_8, 532, 8)) (some 68) ([6]) (some (6, sourceBody532_35, 532, 9))

def sourceBody532_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_36 sourceBody532_5

def sourceBody532_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_37 sourceBody532_8

def sourceBody532_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_34 sourceBody532_38

def sourceBody532_40 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody532_41 : WordLangProgHOL (BitVec 64) :=
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
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody532_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
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
            Flapjack.WordLangExpHOL.const 0#64]),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody532_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody532_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody532_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody532_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody532_8, 532, 10)) (some 480) ([18, 14, 24, 4, 16]) (some (18, sourceBody532_45, 532, 11))

def sourceBody532_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_46 sourceBody532_5

def sourceBody532_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_47 sourceBody532_8

def sourceBody532_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_44 sourceBody532_48

def sourceBody532_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_43 sourceBody532_49

def sourceBody532_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_42 sourceBody532_50

def sourceBody532_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_41 sourceBody532_51

def sourceBody532_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_40 sourceBody532_52

def sourceBody532_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_53

def sourceBody532_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_54

def sourceBody532_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 20)

def sourceBody532_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody532_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody532_59 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 18, 14, 24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody532_8, 532, 12)) (some 146) ([4, 16]) (some (4, sourceBody532_58, 532, 13))

def sourceBody532_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_59 sourceBody532_5

def sourceBody532_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_60 sourceBody532_8

def sourceBody532_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_57 sourceBody532_61

def sourceBody532_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_56 sourceBody532_62

def sourceBody532_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody532_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody532_66 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody532_8, 532, 14)) (some 70) ([16]) (some (16, sourceBody532_65, 532, 15))

def sourceBody532_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_66 sourceBody532_5

def sourceBody532_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_67 sourceBody532_8

def sourceBody532_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_64 sourceBody532_68

def sourceBody532_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_69

def sourceBody532_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_70

def sourceBody532_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody532_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody532_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody532_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 24)

def sourceBody532_76 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody532_8, 532, 16)) (some 472) ([16, 12, 22, 8]) (some (16, sourceBody532_65, 532, 17))

def sourceBody532_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_76 sourceBody532_5

def sourceBody532_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_77 sourceBody532_8

def sourceBody532_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_75 sourceBody532_78

def sourceBody532_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_74 sourceBody532_79

def sourceBody532_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_73 sourceBody532_80

def sourceBody532_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_72 sourceBody532_81

def sourceBody532_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_82

def sourceBody532_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_83

def sourceBody532_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_71 sourceBody532_84

def sourceBody532_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.const 1#64, Flapjack.WordLangExpHOL.var 2])

def sourceBody532_87 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody532_8, 532, 18)) (some 486) ([16]) (some (16, sourceBody532_65, 532, 19))

def sourceBody532_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_87 sourceBody532_5

def sourceBody532_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_88 sourceBody532_8

def sourceBody532_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_86 sourceBody532_89

def sourceBody532_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_90

def sourceBody532_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_91

def sourceBody532_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_85 sourceBody532_92

def sourceBody532_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody532_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody532_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_95 sourceBody532_8

def sourceBody532_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_94 sourceBody532_96

def sourceBody532_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_93 sourceBody532_97

def sourceBody532_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_63 sourceBody532_98

def sourceBody532_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_99

def sourceBody532_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_100

def sourceBody532_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_101

def sourceBody532_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_102

def sourceBody532_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_103

def sourceBody532_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_104

def sourceBody532_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_105

def sourceBody532_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_106

def sourceBody532_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_55 sourceBody532_107

def sourceBody532_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_39 sourceBody532_108

def sourceBody532_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_109

def sourceBody532_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_110

def sourceBody532_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_33 sourceBody532_111

def sourceBody532_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_112

def sourceBody532_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_8 sourceBody532_113

def sourceBody532_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody532_30 sourceBody532_114

def source532 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (532, 2, sourceBody532_115)
end InitECandidate.Proofs.WordStages
