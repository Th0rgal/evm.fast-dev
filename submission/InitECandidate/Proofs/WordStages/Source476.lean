import InitECandidate.Proofs.WordStages.Source460
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody476_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody476_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody476_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 12)

def sourceBody476_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody476_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 16)

def sourceBody476_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody476_6 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody476_0, 476, 2)) (some 102) ([26, 40, 22, 36]) (some (26, sourceBody476_5, 476, 3))

def sourceBody476_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody476_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_6 sourceBody476_7

def sourceBody476_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_8 sourceBody476_0

def sourceBody476_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_4 sourceBody476_9

def sourceBody476_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_3 sourceBody476_10

def sourceBody476_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_2 sourceBody476_11

def sourceBody476_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_1 sourceBody476_12

def sourceBody476_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 32)

def sourceBody476_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody476_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody476_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody476_18 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.reg 22) sourceBody476_16 sourceBody476_17

def sourceBody476_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_18 sourceBody476_7

def sourceBody476_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 40)

def sourceBody476_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody476_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26, 40]

def sourceBody476_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_22 sourceBody476_0

def sourceBody476_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_17 sourceBody476_23

def sourceBody476_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_21 sourceBody476_24

def sourceBody476_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody476_25 sourceBody476_0

def sourceBody476_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_26 sourceBody476_7

def sourceBody476_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_27 sourceBody476_0

def sourceBody476_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_20 sourceBody476_28

def sourceBody476_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_19 sourceBody476_29

def sourceBody476_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_15 sourceBody476_30

def sourceBody476_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_14 sourceBody476_31

def sourceBody476_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 2)

def sourceBody476_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 4)

def sourceBody476_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 6)

def sourceBody476_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 8)

def sourceBody476_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody476_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody476_0, 476, 4)) (some 458) ([40, 22, 36, 28]) (some (40, sourceBody476_37, 476, 5))

def sourceBody476_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_38 sourceBody476_7

def sourceBody476_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_39 sourceBody476_0

def sourceBody476_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_36 sourceBody476_40

def sourceBody476_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_35 sourceBody476_41

def sourceBody476_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_34 sourceBody476_42

def sourceBody476_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_33 sourceBody476_43

def sourceBody476_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody476_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 12)

def sourceBody476_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 14)

def sourceBody476_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 16)

def sourceBody476_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody476_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody476_0, 476, 6)) (some 458) ([22, 36, 28, 42]) (some (22, sourceBody476_49, 476, 7))

def sourceBody476_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_50 sourceBody476_7

def sourceBody476_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_51 sourceBody476_0

def sourceBody476_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_48 sourceBody476_52

def sourceBody476_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_47 sourceBody476_53

def sourceBody476_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_46 sourceBody476_54

def sourceBody476_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_45 sourceBody476_55

def sourceBody476_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 26)

def sourceBody476_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 40)

def sourceBody476_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody476_60 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody476_0, 476, 8)) (some 459) ([36, 28]) (some (36, sourceBody476_59, 476, 9))

def sourceBody476_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_60 sourceBody476_7

def sourceBody476_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_61 sourceBody476_0

def sourceBody476_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_58 sourceBody476_62

def sourceBody476_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_57 sourceBody476_63

def sourceBody476_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 22)

def sourceBody476_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 18446744073709551615#64)

def sourceBody476_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody476_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody476_69 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 28 (Flapjack.WordRegImm.reg 42) sourceBody476_67 sourceBody476_68

def sourceBody476_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_69 sourceBody476_7

def sourceBody476_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody476_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 18446744073709551615#64)

def sourceBody476_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [36, 28]

def sourceBody476_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_73 sourceBody476_0

def sourceBody476_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_68 sourceBody476_74

def sourceBody476_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_72 sourceBody476_75

def sourceBody476_77 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody476_76 sourceBody476_0

def sourceBody476_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_77 sourceBody476_7

def sourceBody476_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_78 sourceBody476_0

def sourceBody476_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_71 sourceBody476_79

def sourceBody476_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_70 sourceBody476_80

def sourceBody476_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_66 sourceBody476_81

def sourceBody476_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_65 sourceBody476_82

def sourceBody476_84 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody476_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 36)

def sourceBody476_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody476_87 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody476_0, 476, 10)) (some 460) ([42]) (some (42, sourceBody476_86, 476, 11))

def sourceBody476_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_87 sourceBody476_7

def sourceBody476_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_88 sourceBody476_0

def sourceBody476_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_85 sourceBody476_89

def sourceBody476_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 22)

def sourceBody476_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody476_93 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody476_0, 476, 12)) (some 460) ([18]) (some (18, sourceBody476_92, 476, 13))

def sourceBody476_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_93 sourceBody476_7

def sourceBody476_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_94 sourceBody476_0

def sourceBody476_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_91 sourceBody476_95

def sourceBody476_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 28)

def sourceBody476_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 42)

def sourceBody476_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody476_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody476_101 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 30 (Flapjack.WordRegImm.reg 24) sourceBody476_99 sourceBody476_100

def sourceBody476_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_101 sourceBody476_7

def sourceBody476_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 30)

def sourceBody476_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody476_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18, 30]

def sourceBody476_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_105 sourceBody476_0

def sourceBody476_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_100 sourceBody476_106

def sourceBody476_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_104 sourceBody476_107

def sourceBody476_109 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.imm 0#64) sourceBody476_108 sourceBody476_0

def sourceBody476_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_109 sourceBody476_7

def sourceBody476_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_110 sourceBody476_0

def sourceBody476_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_103 sourceBody476_111

def sourceBody476_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_102 sourceBody476_112

def sourceBody476_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_98 sourceBody476_113

def sourceBody476_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_97 sourceBody476_114

def sourceBody476_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 42)

def sourceBody476_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody476_118 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody476_0, 476, 14)) (some 475) ([30]) (some (30, sourceBody476_117, 476, 15))

def sourceBody476_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_118 sourceBody476_7

def sourceBody476_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_119 sourceBody476_0

def sourceBody476_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_116 sourceBody476_120

def sourceBody476_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 28)

def sourceBody476_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody476_124 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody476_0, 476, 16)) (some 475) ([24]) (some (24, sourceBody476_123, 476, 17))

def sourceBody476_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_124 sourceBody476_7

def sourceBody476_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_125 sourceBody476_0

def sourceBody476_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_122 sourceBody476_126

def sourceBody476_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 18)

def sourceBody476_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 18446744073709551615#64)

def sourceBody476_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody476_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody476_132 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 38 (Flapjack.WordRegImm.reg 20) sourceBody476_130 sourceBody476_131

def sourceBody476_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_132 sourceBody476_7

def sourceBody476_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 38)

def sourceBody476_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 18446744073709551615#64)

def sourceBody476_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24, 38]

def sourceBody476_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_136 sourceBody476_0

def sourceBody476_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_131 sourceBody476_137

def sourceBody476_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_135 sourceBody476_138

def sourceBody476_140 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.imm 0#64) sourceBody476_139 sourceBody476_0

def sourceBody476_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_140 sourceBody476_7

def sourceBody476_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_141 sourceBody476_0

def sourceBody476_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_134 sourceBody476_142

def sourceBody476_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_133 sourceBody476_143

def sourceBody476_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_129 sourceBody476_144

def sourceBody476_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_128 sourceBody476_145

def sourceBody476_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 30])

def sourceBody476_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.var 28])

def sourceBody476_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_148 sourceBody476_137

def sourceBody476_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_147 sourceBody476_149

def sourceBody476_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_146 sourceBody476_150

def sourceBody476_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_127 sourceBody476_151

def sourceBody476_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_0 sourceBody476_152

def sourceBody476_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_0 sourceBody476_153

def sourceBody476_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_121 sourceBody476_154

def sourceBody476_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_0 sourceBody476_155

def sourceBody476_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_0 sourceBody476_156

def sourceBody476_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_115 sourceBody476_157

def sourceBody476_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_96 sourceBody476_158

def sourceBody476_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_0 sourceBody476_159

def sourceBody476_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_0 sourceBody476_160

def sourceBody476_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_90 sourceBody476_161

def sourceBody476_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_0 sourceBody476_162

def sourceBody476_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_0 sourceBody476_163

def sourceBody476_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_84 sourceBody476_164

def sourceBody476_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_0 sourceBody476_165

def sourceBody476_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_83 sourceBody476_166

def sourceBody476_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_64 sourceBody476_167

def sourceBody476_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_0 sourceBody476_168

def sourceBody476_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_0 sourceBody476_169

def sourceBody476_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_56 sourceBody476_170

def sourceBody476_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_0 sourceBody476_171

def sourceBody476_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_0 sourceBody476_172

def sourceBody476_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_44 sourceBody476_173

def sourceBody476_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_0 sourceBody476_174

def sourceBody476_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_0 sourceBody476_175

def sourceBody476_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_32 sourceBody476_176

def sourceBody476_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_13 sourceBody476_177

def sourceBody476_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_0 sourceBody476_178

def sourceBody476_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody476_0 sourceBody476_179

def source476 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (476, 9, sourceBody476_180)
end InitECandidate.Proofs.WordStages
