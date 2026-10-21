import InitECandidate.Proofs.WordStages.Source724
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody740_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody740_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody740_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody740_0, 740, 2)) (some 69) ([]) (some (16, sourceBody740_1, 740, 3))

def sourceBody740_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody740_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_2 sourceBody740_3

def sourceBody740_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_4 sourceBody740_0

def sourceBody740_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody740_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody740_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody740_0, 740, 4)) (some 68) ([28]) (some (28, sourceBody740_7, 740, 5))

def sourceBody740_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_8 sourceBody740_3

def sourceBody740_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_9 sourceBody740_0

def sourceBody740_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_6 sourceBody740_10

def sourceBody740_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody740_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody740_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody740_0, 740, 6)) (some 68) ([10]) (some (10, sourceBody740_13, 740, 7))

def sourceBody740_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_14 sourceBody740_3

def sourceBody740_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_15 sourceBody740_0

def sourceBody740_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_12 sourceBody740_16

def sourceBody740_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody740_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody740_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody740_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody740_0, 740, 8)) (some 725) ([20, 14]) (some (20, sourceBody740_20, 740, 9))

def sourceBody740_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_21 sourceBody740_3

def sourceBody740_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_22 sourceBody740_0

def sourceBody740_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_19 sourceBody740_23

def sourceBody740_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_18 sourceBody740_24

def sourceBody740_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_25

def sourceBody740_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_26

def sourceBody740_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 28)

def sourceBody740_29 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody740_0, 740, 10)) (some 727) ([20]) (some (20, sourceBody740_20, 740, 11))

def sourceBody740_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_29 sourceBody740_3

def sourceBody740_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_30 sourceBody740_0

def sourceBody740_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_28 sourceBody740_31

def sourceBody740_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_32

def sourceBody740_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_33

def sourceBody740_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_27 sourceBody740_34

def sourceBody740_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody740_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
    (Flapjack.WordLangExpHOL.const 6#64))

def sourceBody740_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody740_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 20)

def sourceBody740_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody740_41 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 26 (Flapjack.WordRegImm.reg 12) sourceBody740_40 sourceBody740_38

def sourceBody740_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_41 sourceBody740_3

def sourceBody740_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody740_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody740_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody740_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_45 sourceBody740_0

def sourceBody740_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_46 sourceBody740_0

def sourceBody740_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_44 sourceBody740_47

def sourceBody740_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_48

def sourceBody740_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody740_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody740_52 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 26 (Flapjack.WordRegImm.reg 12) sourceBody740_40 sourceBody740_38

def sourceBody740_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_52 sourceBody740_3

def sourceBody740_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody740_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 28)

def sourceBody740_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody740_57 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody740_0, 740, 12)) (some 736) ([26, 12]) (some (26, sourceBody740_56, 740, 13))

def sourceBody740_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_57 sourceBody740_3

def sourceBody740_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_58 sourceBody740_0

def sourceBody740_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_55 sourceBody740_59

def sourceBody740_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_54 sourceBody740_60

def sourceBody740_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_61

def sourceBody740_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_62

def sourceBody740_64 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody740_63 sourceBody740_0

def sourceBody740_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_64 sourceBody740_3

def sourceBody740_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_65 sourceBody740_0

def sourceBody740_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_43 sourceBody740_66

def sourceBody740_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_53 sourceBody740_67

def sourceBody740_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_51 sourceBody740_68

def sourceBody740_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_50 sourceBody740_69

def sourceBody740_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_49 sourceBody740_70

def sourceBody740_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
        (Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.var 6,
              Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 20)
                  (Flapjack.WordLangExpHOL.const 6#64))
                (Flapjack.WordLangExpHOL.const 3#64)]))
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
          [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 63#64]),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody740_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody740_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody740_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody740_76 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.WordRegImm.reg 24) sourceBody740_51 sourceBody740_75

def sourceBody740_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_76 sourceBody740_3

def sourceBody740_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody740_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 28)

def sourceBody740_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody740_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody740_82 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody740_0, 740, 14)) (some 735) ([12, 24, 18]) (some (12, sourceBody740_81, 740, 15))

def sourceBody740_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_82 sourceBody740_3

def sourceBody740_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_83 sourceBody740_0

def sourceBody740_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_80 sourceBody740_84

def sourceBody740_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_79 sourceBody740_85

def sourceBody740_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_55 sourceBody740_86

def sourceBody740_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_87

def sourceBody740_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_88

def sourceBody740_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody740_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_90 sourceBody740_0

def sourceBody740_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_91 sourceBody740_0

def sourceBody740_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_89 sourceBody740_92

def sourceBody740_94 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody740_93 sourceBody740_0

def sourceBody740_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_94 sourceBody740_3

def sourceBody740_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_95 sourceBody740_0

def sourceBody740_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_78 sourceBody740_96

def sourceBody740_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_77 sourceBody740_97

def sourceBody740_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_74 sourceBody740_98

def sourceBody740_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_73 sourceBody740_99

def sourceBody740_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_72 sourceBody740_100

def sourceBody740_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_101

def sourceBody740_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_71 sourceBody740_102

def sourceBody740_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody740_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_103 sourceBody740_104

def sourceBody740_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody740_107 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody740_105 sourceBody740_106

def sourceBody740_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_107 sourceBody740_3

def sourceBody740_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_108 sourceBody740_0

def sourceBody740_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_43 sourceBody740_109

def sourceBody740_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_42 sourceBody740_110

def sourceBody740_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_39 sourceBody740_111

def sourceBody740_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_38 sourceBody740_112

def sourceBody740_114 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody740_113 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody740_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_114 sourceBody740_3

def sourceBody740_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_3 sourceBody740_115

def sourceBody740_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 2)

def sourceBody740_118 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody740_0, 740, 16)) (some 725) ([26, 12]) (some (26, sourceBody740_56, 740, 17))

def sourceBody740_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_118 sourceBody740_3

def sourceBody740_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_119 sourceBody740_0

def sourceBody740_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_55 sourceBody740_120

def sourceBody740_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_117 sourceBody740_121

def sourceBody740_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_122

def sourceBody740_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_123

def sourceBody740_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_116 sourceBody740_124

def sourceBody740_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 22)

def sourceBody740_127 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody740_0, 740, 18)) (some 70) ([26]) (some (26, sourceBody740_56, 740, 19))

def sourceBody740_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_127 sourceBody740_3

def sourceBody740_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_128 sourceBody740_0

def sourceBody740_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_126 sourceBody740_129

def sourceBody740_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_130

def sourceBody740_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_131

def sourceBody740_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_125 sourceBody740_132

def sourceBody740_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody740_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody740_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_135 sourceBody740_0

def sourceBody740_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_134 sourceBody740_136

def sourceBody740_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_133 sourceBody740_137

def sourceBody740_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_37 sourceBody740_138

def sourceBody740_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_139

def sourceBody740_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_36 sourceBody740_140

def sourceBody740_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_141

def sourceBody740_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_35 sourceBody740_142

def sourceBody740_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_17 sourceBody740_143

def sourceBody740_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_144

def sourceBody740_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_145

def sourceBody740_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_11 sourceBody740_146

def sourceBody740_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_147

def sourceBody740_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_148

def sourceBody740_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_5 sourceBody740_149

def sourceBody740_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_150

def sourceBody740_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody740_0 sourceBody740_151

def source740 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (740, 5, sourceBody740_152)
end InitECandidate.Proofs.WordStages
