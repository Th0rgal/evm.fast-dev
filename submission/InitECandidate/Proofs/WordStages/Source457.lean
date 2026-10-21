import InitECandidate.Proofs.WordStages.Source441
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody457_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody457_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody457_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 216#64]),
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody457_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody457_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody457_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody457_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 32)

def sourceBody457_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody457_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody457_9 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 20 (Flapjack.WordRegImm.reg 38) sourceBody457_7 sourceBody457_8

def sourceBody457_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_9 sourceBody457_4

def sourceBody457_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 20)

def sourceBody457_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 216#64]))

def sourceBody457_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 8)

def sourceBody457_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody457_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([28, 20, 38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody457_0, 457, 2)) (some 197) ([6, 26]) (some (6, sourceBody457_14, 457, 3))

def sourceBody457_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_15 sourceBody457_4

def sourceBody457_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_16 sourceBody457_0

def sourceBody457_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_13 sourceBody457_17

def sourceBody457_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_12 sourceBody457_18

def sourceBody457_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody457_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody457_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody457_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody457_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.reg 18) sourceBody457_22 sourceBody457_23

def sourceBody457_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_24 sourceBody457_4

def sourceBody457_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 26)

def sourceBody457_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 38)

def sourceBody457_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody457_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody457_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 1#64,
      Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 24#64])])

def sourceBody457_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 36)

def sourceBody457_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_31 sourceBody457_0

def sourceBody457_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_32 sourceBody457_0

def sourceBody457_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_30 sourceBody457_33

def sourceBody457_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_34

def sourceBody457_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody457_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody457_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 12)

def sourceBody457_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 36)

def sourceBody457_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody457_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody457_42 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 22 (Flapjack.WordRegImm.reg 40) sourceBody457_40 sourceBody457_41

def sourceBody457_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_42 sourceBody457_4

def sourceBody457_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 22)

def sourceBody457_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 18)

def sourceBody457_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody457_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody457_48 : WordLangProgHOL (BitVec 64) :=
.call (some (([30, 22, 40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody457_0, 457, 4)) (some 197) ([4, 24]) (some (4, sourceBody457_47, 457, 5))

def sourceBody457_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_48 sourceBody457_4

def sourceBody457_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_49 sourceBody457_0

def sourceBody457_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_46 sourceBody457_50

def sourceBody457_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_45 sourceBody457_51

def sourceBody457_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 30)

def sourceBody457_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody457_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody457_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody457_57 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.reg 16) sourceBody457_55 sourceBody457_56

def sourceBody457_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_57 sourceBody457_4

def sourceBody457_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 24)

def sourceBody457_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody457_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody457_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody457_63 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody457_0, 457, 6)) (some 187) ([24, 16]) (some (24, sourceBody457_62, 457, 7))

def sourceBody457_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_63 sourceBody457_4

def sourceBody457_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_64 sourceBody457_0

def sourceBody457_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_61 sourceBody457_65

def sourceBody457_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_60 sourceBody457_66

def sourceBody457_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody457_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody457_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody457_71 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 34) sourceBody457_70 sourceBody457_54

def sourceBody457_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_71 sourceBody457_4

def sourceBody457_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody457_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody457_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 24)

def sourceBody457_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_75 sourceBody457_0

def sourceBody457_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_76 sourceBody457_0

def sourceBody457_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_74 sourceBody457_77

def sourceBody457_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_78

def sourceBody457_80 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody457_79 sourceBody457_0

def sourceBody457_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_80 sourceBody457_4

def sourceBody457_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_81 sourceBody457_0

def sourceBody457_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_73 sourceBody457_82

def sourceBody457_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_72 sourceBody457_83

def sourceBody457_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_69 sourceBody457_84

def sourceBody457_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_68 sourceBody457_85

def sourceBody457_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_67 sourceBody457_86

def sourceBody457_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_87

def sourceBody457_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_88

def sourceBody457_90 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.imm 0#64) sourceBody457_89 sourceBody457_0

def sourceBody457_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_90 sourceBody457_4

def sourceBody457_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_91 sourceBody457_0

def sourceBody457_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_59 sourceBody457_92

def sourceBody457_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_58 sourceBody457_93

def sourceBody457_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_54 sourceBody457_94

def sourceBody457_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_53 sourceBody457_95

def sourceBody457_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody457_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody457_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_98 sourceBody457_0

def sourceBody457_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_99 sourceBody457_0

def sourceBody457_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_97 sourceBody457_100

def sourceBody457_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_101

def sourceBody457_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_96 sourceBody457_102

def sourceBody457_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_52 sourceBody457_103

def sourceBody457_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_104

def sourceBody457_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_105

def sourceBody457_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_106

def sourceBody457_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_107

def sourceBody457_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_108

def sourceBody457_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_109

def sourceBody457_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody457_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_110 sourceBody457_111

def sourceBody457_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody457_114 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody457_112 sourceBody457_113

def sourceBody457_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_114 sourceBody457_4

def sourceBody457_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_115 sourceBody457_0

def sourceBody457_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_44 sourceBody457_116

def sourceBody457_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_43 sourceBody457_117

def sourceBody457_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_39 sourceBody457_118

def sourceBody457_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_38 sourceBody457_119

def sourceBody457_121 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody457_120 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody457_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_121 sourceBody457_4

def sourceBody457_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_4 sourceBody457_122

def sourceBody457_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_37 sourceBody457_123

def sourceBody457_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_124

def sourceBody457_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_36 sourceBody457_125

def sourceBody457_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_126

def sourceBody457_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_35 sourceBody457_127

def sourceBody457_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_29 sourceBody457_128

def sourceBody457_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_129

def sourceBody457_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_28 sourceBody457_130

def sourceBody457_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_131

def sourceBody457_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_27 sourceBody457_132

def sourceBody457_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_133

def sourceBody457_135 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody457_134 sourceBody457_0

def sourceBody457_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_135 sourceBody457_4

def sourceBody457_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_136 sourceBody457_0

def sourceBody457_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_26 sourceBody457_137

def sourceBody457_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_25 sourceBody457_138

def sourceBody457_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_21 sourceBody457_139

def sourceBody457_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_20 sourceBody457_140

def sourceBody457_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody457_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody457_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_143 sourceBody457_0

def sourceBody457_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_144 sourceBody457_0

def sourceBody457_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_142 sourceBody457_145

def sourceBody457_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_146

def sourceBody457_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_141 sourceBody457_147

def sourceBody457_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_19 sourceBody457_148

def sourceBody457_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_149

def sourceBody457_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_150

def sourceBody457_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_151

def sourceBody457_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_152

def sourceBody457_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_153

def sourceBody457_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_154

def sourceBody457_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_155 sourceBody457_111

def sourceBody457_157 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody457_156 sourceBody457_113

def sourceBody457_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_157 sourceBody457_4

def sourceBody457_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_158 sourceBody457_0

def sourceBody457_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_11 sourceBody457_159

def sourceBody457_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_10 sourceBody457_160

def sourceBody457_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_6 sourceBody457_161

def sourceBody457_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_5 sourceBody457_162

def sourceBody457_164 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody457_163 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln) PUnit.unit
  Flapjack.Spt.ln)

def sourceBody457_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_164 sourceBody457_4

def sourceBody457_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_4 sourceBody457_165

def sourceBody457_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody457_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 2000#64)

def sourceBody457_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody457_170 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody457_0, 457, 8)) (some 95) ([20, 38]) (some (20, sourceBody457_169, 457, 9))

def sourceBody457_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_170 sourceBody457_4

def sourceBody457_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_171 sourceBody457_0

def sourceBody457_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_168 sourceBody457_172

def sourceBody457_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_167 sourceBody457_173

def sourceBody457_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 28)

def sourceBody457_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 14)

def sourceBody457_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody457_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody457_179 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 38 (Flapjack.WordRegImm.reg 6) sourceBody457_177 sourceBody457_178

def sourceBody457_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_179 sourceBody457_4

def sourceBody457_181 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 38)

def sourceBody457_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 40#64)

def sourceBody457_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 20)

def sourceBody457_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_183 sourceBody457_0

def sourceBody457_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_184 sourceBody457_0

def sourceBody457_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_182 sourceBody457_185

def sourceBody457_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_186

def sourceBody457_188 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody457_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_188 sourceBody457_169

def sourceBody457_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_187 sourceBody457_189

def sourceBody457_191 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody457_190 sourceBody457_0

def sourceBody457_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_191 sourceBody457_4

def sourceBody457_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_192 sourceBody457_0

def sourceBody457_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_181 sourceBody457_193

def sourceBody457_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_180 sourceBody457_194

def sourceBody457_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_176 sourceBody457_195

def sourceBody457_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_175 sourceBody457_196

def sourceBody457_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody457_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_198 sourceBody457_0

def sourceBody457_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_8 sourceBody457_199

def sourceBody457_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_197 sourceBody457_200

def sourceBody457_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_174 sourceBody457_201

def sourceBody457_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_202

def sourceBody457_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_203

def sourceBody457_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_166 sourceBody457_204

def sourceBody457_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_3 sourceBody457_205

def sourceBody457_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_206

def sourceBody457_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_2 sourceBody457_207

def sourceBody457_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_208

def sourceBody457_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_1 sourceBody457_209

def sourceBody457_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody457_0 sourceBody457_210

def source457 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (457, 2, sourceBody457_211)
end InitECandidate.Proofs.WordStages
