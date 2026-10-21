import InitECandidate.Proofs.WordStages.Source411
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody427_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody427_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody427_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody427_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody427_0, 427, 2)) (some 68) ([18]) (some (18, sourceBody427_2, 427, 3))

def sourceBody427_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody427_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_3 sourceBody427_4

def sourceBody427_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_5 sourceBody427_0

def sourceBody427_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_1 sourceBody427_6

def sourceBody427_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody427_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 6)

def sourceBody427_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody427_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody427_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody427_0, 427, 4)) (some 158) ([14, 20, 8]) (some (14, sourceBody427_11, 427, 5))

def sourceBody427_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_12 sourceBody427_4

def sourceBody427_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_13 sourceBody427_0

def sourceBody427_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_10 sourceBody427_14

def sourceBody427_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_9 sourceBody427_15

def sourceBody427_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_8 sourceBody427_16

def sourceBody427_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_17

def sourceBody427_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_18

def sourceBody427_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody427_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 136#64]))

def sourceBody427_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody427_23 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody427_0, 427, 6)) (some 79) ([14, 20, 8]) (some (14, sourceBody427_11, 427, 7))

def sourceBody427_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_23 sourceBody427_4

def sourceBody427_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_24 sourceBody427_0

def sourceBody427_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_22 sourceBody427_25

def sourceBody427_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_21 sourceBody427_26

def sourceBody427_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_20 sourceBody427_27

def sourceBody427_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 18)

def sourceBody427_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody427_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody427_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody427_33 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 20 (Flapjack.WordRegImm.reg 8) sourceBody427_31 sourceBody427_32

def sourceBody427_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_33 sourceBody427_4

def sourceBody427_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody427_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody427_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody427_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody427_0, 427, 8)) (some 68) ([20]) (some (20, sourceBody427_37, 427, 9))

def sourceBody427_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_38 sourceBody427_4

def sourceBody427_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_39 sourceBody427_0

def sourceBody427_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_36 sourceBody427_40

def sourceBody427_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody427_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody427_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody427_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 20) 16

def sourceBody427_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_45 sourceBody427_0

def sourceBody427_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_44 sourceBody427_46

def sourceBody427_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_47 sourceBody427_0

def sourceBody427_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_43 sourceBody427_48

def sourceBody427_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_49

def sourceBody427_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_42 sourceBody427_50

def sourceBody427_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_51

def sourceBody427_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody427_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody427_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_54 sourceBody427_48

def sourceBody427_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_55

def sourceBody427_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_53 sourceBody427_56

def sourceBody427_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_57

def sourceBody427_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_52 sourceBody427_58

def sourceBody427_60 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody427_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody427_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody427_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody427_64 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody427_0, 427, 10)) (some 384) ([8, 16, 12]) (some (8, sourceBody427_63, 427, 11))

def sourceBody427_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_64 sourceBody427_4

def sourceBody427_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_65 sourceBody427_0

def sourceBody427_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_62 sourceBody427_66

def sourceBody427_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_61 sourceBody427_67

def sourceBody427_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_60 sourceBody427_68

def sourceBody427_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_69

def sourceBody427_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_70

def sourceBody427_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_59 sourceBody427_71

def sourceBody427_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_41 sourceBody427_72

def sourceBody427_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_73

def sourceBody427_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_74

def sourceBody427_76 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody427_75 sourceBody427_0

def sourceBody427_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_76 sourceBody427_4

def sourceBody427_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_77 sourceBody427_0

def sourceBody427_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_35 sourceBody427_78

def sourceBody427_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_34 sourceBody427_79

def sourceBody427_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_30 sourceBody427_80

def sourceBody427_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_29 sourceBody427_81

def sourceBody427_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody427_84 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody427_0, 427, 12)) (some 403) ([20]) (some (20, sourceBody427_37, 427, 13))

def sourceBody427_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_84 sourceBody427_4

def sourceBody427_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_85 sourceBody427_0

def sourceBody427_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_83 sourceBody427_86

def sourceBody427_88 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody427_0, 427, 14)) (some 391) ([20]) (some (20, sourceBody427_37, 427, 15))

def sourceBody427_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_88 sourceBody427_4

def sourceBody427_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_89 sourceBody427_0

def sourceBody427_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_42 sourceBody427_90

def sourceBody427_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody427_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_10 sourceBody427_48

def sourceBody427_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_93

def sourceBody427_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_92 sourceBody427_94

def sourceBody427_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_95

def sourceBody427_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_91 sourceBody427_96

def sourceBody427_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody427_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody427_100 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody427_0, 427, 16)) (some 419) ([8, 16]) (some (8, sourceBody427_63, 427, 17))

def sourceBody427_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_100 sourceBody427_4

def sourceBody427_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_101 sourceBody427_0

def sourceBody427_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_99 sourceBody427_102

def sourceBody427_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_98 sourceBody427_103

def sourceBody427_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_104

def sourceBody427_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_105

def sourceBody427_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_97 sourceBody427_106

def sourceBody427_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody427_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_108 sourceBody427_0

def sourceBody427_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_32 sourceBody427_109

def sourceBody427_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_107 sourceBody427_110

def sourceBody427_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_87 sourceBody427_111

def sourceBody427_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_112

def sourceBody427_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_113

def sourceBody427_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_82 sourceBody427_114

def sourceBody427_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_28 sourceBody427_115

def sourceBody427_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_116

def sourceBody427_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_117

def sourceBody427_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_19 sourceBody427_118

def sourceBody427_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_7 sourceBody427_119

def sourceBody427_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_120

def sourceBody427_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody427_0 sourceBody427_121

def source427 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (427, 4, sourceBody427_122)
end InitECandidate.Proofs.WordStages
