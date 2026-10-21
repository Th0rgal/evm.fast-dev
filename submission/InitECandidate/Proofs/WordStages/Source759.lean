import InitECandidate.Proofs.WordStages.Source743
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody759_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody759_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody759_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody759_0, 759, 2)) (some 69) ([]) (some (8, sourceBody759_1, 759, 3))

def sourceBody759_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody759_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_2 sourceBody759_3

def sourceBody759_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_4 sourceBody759_0

def sourceBody759_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 576#64)

def sourceBody759_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody759_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody759_0, 759, 4)) (some 68) ([18]) (some (18, sourceBody759_7, 759, 5))

def sourceBody759_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_8 sourceBody759_3

def sourceBody759_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_9 sourceBody759_0

def sourceBody759_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_6 sourceBody759_10

def sourceBody759_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 576#64)

def sourceBody759_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody759_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody759_0, 759, 6)) (some 68) ([14]) (some (14, sourceBody759_13, 759, 7))

def sourceBody759_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_14 sourceBody759_3

def sourceBody759_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_15 sourceBody759_0

def sourceBody759_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_12 sourceBody759_16

def sourceBody759_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody759_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody759_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody759_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody759_0, 759, 8)) (some 751) ([24, 6]) (some (24, sourceBody759_20, 759, 9))

def sourceBody759_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_21 sourceBody759_3

def sourceBody759_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_22 sourceBody759_0

def sourceBody759_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_19 sourceBody759_23

def sourceBody759_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_18 sourceBody759_24

def sourceBody759_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_25

def sourceBody759_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_26

def sourceBody759_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody759_29 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody759_0, 759, 10)) (some 752) ([24]) (some (24, sourceBody759_20, 759, 11))

def sourceBody759_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_29 sourceBody759_3

def sourceBody759_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_30 sourceBody759_0

def sourceBody759_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_28 sourceBody759_31

def sourceBody759_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_32

def sourceBody759_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_33

def sourceBody759_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_27 sourceBody759_34

def sourceBody759_36 : WordLangProgHOL (BitVec 64) :=
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
              Flapjack.WordLangExpHOL.const 392#64]),
        Flapjack.WordLangExpHOL.const 1376#64]))

def sourceBody759_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody759_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody759_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody759_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 6)

def sourceBody759_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody759_42 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 12 (Flapjack.WordRegImm.reg 22) sourceBody759_41 sourceBody759_39

def sourceBody759_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_42 sourceBody759_3

def sourceBody759_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody759_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody759_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody759_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_46 sourceBody759_0

def sourceBody759_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_47 sourceBody759_0

def sourceBody759_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_45 sourceBody759_48

def sourceBody759_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_49

def sourceBody759_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 24)

def sourceBody759_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody759_53 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.WordRegImm.reg 22) sourceBody759_41 sourceBody759_39

def sourceBody759_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_53 sourceBody759_3

def sourceBody759_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody759_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody759_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody759_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody759_59 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody759_0, 759, 12)) (some 754) ([12, 22, 10]) (some (12, sourceBody759_58, 759, 13))

def sourceBody759_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_59 sourceBody759_3

def sourceBody759_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_60 sourceBody759_0

def sourceBody759_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_57 sourceBody759_61

def sourceBody759_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_56 sourceBody759_62

def sourceBody759_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_55 sourceBody759_63

def sourceBody759_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_64

def sourceBody759_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_65

def sourceBody759_67 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody759_66 sourceBody759_0

def sourceBody759_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_67 sourceBody759_3

def sourceBody759_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_68 sourceBody759_0

def sourceBody759_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_44 sourceBody759_69

def sourceBody759_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_54 sourceBody759_70

def sourceBody759_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_52 sourceBody759_71

def sourceBody759_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_51 sourceBody759_72

def sourceBody759_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_50 sourceBody759_73

def sourceBody759_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 14) (Flapjack.WordLangExpHOL.var 6),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody759_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody759_77 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody759_0, 759, 14)) (some 754) ([12, 22, 10]) (some (12, sourceBody759_58, 759, 15))

def sourceBody759_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_77 sourceBody759_3

def sourceBody759_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_78 sourceBody759_0

def sourceBody759_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_76 sourceBody759_79

def sourceBody759_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_56 sourceBody759_80

def sourceBody759_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_55 sourceBody759_81

def sourceBody759_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_82

def sourceBody759_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_83

def sourceBody759_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody759_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_85 sourceBody759_0

def sourceBody759_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_86 sourceBody759_0

def sourceBody759_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_84 sourceBody759_87

def sourceBody759_89 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody759_88 sourceBody759_0

def sourceBody759_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_89 sourceBody759_3

def sourceBody759_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_90 sourceBody759_0

def sourceBody759_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_44 sourceBody759_91

def sourceBody759_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_54 sourceBody759_92

def sourceBody759_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_52 sourceBody759_93

def sourceBody759_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_75 sourceBody759_94

def sourceBody759_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_74 sourceBody759_95

def sourceBody759_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody759_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_96 sourceBody759_97

def sourceBody759_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody759_100 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody759_98 sourceBody759_99

def sourceBody759_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_100 sourceBody759_3

def sourceBody759_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_101 sourceBody759_0

def sourceBody759_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_44 sourceBody759_102

def sourceBody759_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_43 sourceBody759_103

def sourceBody759_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_40 sourceBody759_104

def sourceBody759_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_39 sourceBody759_105

def sourceBody759_107 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody759_106 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody759_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_107 sourceBody759_3

def sourceBody759_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_3 sourceBody759_108

def sourceBody759_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody759_111 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody759_0, 759, 16)) (some 751) ([12, 22]) (some (12, sourceBody759_58, 759, 17))

def sourceBody759_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_111 sourceBody759_3

def sourceBody759_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_112 sourceBody759_0

def sourceBody759_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_56 sourceBody759_113

def sourceBody759_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_110 sourceBody759_114

def sourceBody759_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_115

def sourceBody759_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_116

def sourceBody759_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_109 sourceBody759_117

def sourceBody759_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 20)

def sourceBody759_120 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody759_0, 759, 18)) (some 70) ([12]) (some (12, sourceBody759_58, 759, 19))

def sourceBody759_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_120 sourceBody759_3

def sourceBody759_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_121 sourceBody759_0

def sourceBody759_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_119 sourceBody759_122

def sourceBody759_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_123

def sourceBody759_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_124

def sourceBody759_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_118 sourceBody759_125

def sourceBody759_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody759_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody759_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_128 sourceBody759_0

def sourceBody759_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_127 sourceBody759_129

def sourceBody759_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_126 sourceBody759_130

def sourceBody759_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_38 sourceBody759_131

def sourceBody759_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_132

def sourceBody759_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_37 sourceBody759_133

def sourceBody759_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_134

def sourceBody759_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_36 sourceBody759_135

def sourceBody759_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_136

def sourceBody759_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_35 sourceBody759_137

def sourceBody759_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_17 sourceBody759_138

def sourceBody759_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_139

def sourceBody759_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_140

def sourceBody759_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_11 sourceBody759_141

def sourceBody759_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_142

def sourceBody759_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_143

def sourceBody759_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_5 sourceBody759_144

def sourceBody759_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_145

def sourceBody759_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody759_0 sourceBody759_146

def source759 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (759, 3, sourceBody759_147)
end InitECandidate.Proofs.WordStages
