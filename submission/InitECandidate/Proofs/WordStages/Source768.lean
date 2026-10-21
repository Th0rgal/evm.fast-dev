import InitECandidate.Proofs.WordStages.Source752
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody768_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody768_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody768_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody768_0, 768, 2)) (some 69) ([]) (some (16, sourceBody768_1, 768, 3))

def sourceBody768_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody768_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_2 sourceBody768_3

def sourceBody768_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_4 sourceBody768_0

def sourceBody768_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 144#64)

def sourceBody768_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody768_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody768_0, 768, 4)) (some 68) ([28]) (some (28, sourceBody768_7, 768, 5))

def sourceBody768_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_8 sourceBody768_3

def sourceBody768_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_9 sourceBody768_0

def sourceBody768_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_6 sourceBody768_10

def sourceBody768_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 144#64)

def sourceBody768_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody768_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody768_0, 768, 6)) (some 68) ([10]) (some (10, sourceBody768_13, 768, 7))

def sourceBody768_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_14 sourceBody768_3

def sourceBody768_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_15 sourceBody768_0

def sourceBody768_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_12 sourceBody768_16

def sourceBody768_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 28)

def sourceBody768_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody768_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody768_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody768_0, 768, 8)) (some 764) ([20, 14]) (some (20, sourceBody768_20, 768, 9))

def sourceBody768_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_21 sourceBody768_3

def sourceBody768_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_22 sourceBody768_0

def sourceBody768_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_19 sourceBody768_23

def sourceBody768_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_18 sourceBody768_24

def sourceBody768_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_25

def sourceBody768_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_26

def sourceBody768_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody768_29 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody768_0, 768, 10)) (some 762) ([20]) (some (20, sourceBody768_20, 768, 11))

def sourceBody768_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_29 sourceBody768_3

def sourceBody768_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_30 sourceBody768_0

def sourceBody768_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_28 sourceBody768_31

def sourceBody768_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_32

def sourceBody768_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_33

def sourceBody768_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_27 sourceBody768_34

def sourceBody768_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
    (Flapjack.WordLangExpHOL.const 6#64))

def sourceBody768_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody768_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody768_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody768_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody768_41 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 26 (Flapjack.WordRegImm.reg 12) sourceBody768_40 sourceBody768_38

def sourceBody768_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_41 sourceBody768_3

def sourceBody768_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody768_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody768_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody768_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_45 sourceBody768_0

def sourceBody768_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_46 sourceBody768_0

def sourceBody768_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_44 sourceBody768_47

def sourceBody768_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_48

def sourceBody768_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 20)

def sourceBody768_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody768_52 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 26 (Flapjack.WordRegImm.reg 12) sourceBody768_40 sourceBody768_38

def sourceBody768_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_52 sourceBody768_3

def sourceBody768_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 16)

def sourceBody768_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody768_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody768_57 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody768_0, 768, 12)) (some 766) ([26, 12]) (some (26, sourceBody768_56, 768, 13))

def sourceBody768_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_57 sourceBody768_3

def sourceBody768_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_58 sourceBody768_0

def sourceBody768_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_55 sourceBody768_59

def sourceBody768_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_54 sourceBody768_60

def sourceBody768_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_61

def sourceBody768_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_62

def sourceBody768_64 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody768_63 sourceBody768_0

def sourceBody768_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_64 sourceBody768_3

def sourceBody768_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_65 sourceBody768_0

def sourceBody768_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_43 sourceBody768_66

def sourceBody768_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_53 sourceBody768_67

def sourceBody768_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_51 sourceBody768_68

def sourceBody768_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_50 sourceBody768_69

def sourceBody768_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_49 sourceBody768_70

def sourceBody768_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
        (Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.var 6,
              Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 10)
                  (Flapjack.WordLangExpHOL.const 6#64))
                (Flapjack.WordLangExpHOL.const 3#64)]))
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
          [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 63#64]),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody768_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody768_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody768_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody768_76 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.WordRegImm.reg 24) sourceBody768_51 sourceBody768_75

def sourceBody768_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_76 sourceBody768_3

def sourceBody768_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody768_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody768_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody768_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody768_82 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody768_0, 768, 14)) (some 767) ([12, 24, 18]) (some (12, sourceBody768_81, 768, 15))

def sourceBody768_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_82 sourceBody768_3

def sourceBody768_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_83 sourceBody768_0

def sourceBody768_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_80 sourceBody768_84

def sourceBody768_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_79 sourceBody768_85

def sourceBody768_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_55 sourceBody768_86

def sourceBody768_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_87

def sourceBody768_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_88

def sourceBody768_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody768_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_90 sourceBody768_0

def sourceBody768_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_91 sourceBody768_0

def sourceBody768_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_89 sourceBody768_92

def sourceBody768_94 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody768_93 sourceBody768_0

def sourceBody768_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_94 sourceBody768_3

def sourceBody768_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_95 sourceBody768_0

def sourceBody768_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_78 sourceBody768_96

def sourceBody768_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_77 sourceBody768_97

def sourceBody768_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_74 sourceBody768_98

def sourceBody768_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_73 sourceBody768_99

def sourceBody768_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_72 sourceBody768_100

def sourceBody768_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_101

def sourceBody768_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_71 sourceBody768_102

def sourceBody768_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody768_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_103 sourceBody768_104

def sourceBody768_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody768_107 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody768_105 sourceBody768_106

def sourceBody768_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_107 sourceBody768_3

def sourceBody768_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_108 sourceBody768_0

def sourceBody768_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_43 sourceBody768_109

def sourceBody768_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_42 sourceBody768_110

def sourceBody768_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_39 sourceBody768_111

def sourceBody768_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_38 sourceBody768_112

def sourceBody768_114 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody768_113 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody768_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_114 sourceBody768_3

def sourceBody768_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_3 sourceBody768_115

def sourceBody768_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 2)

def sourceBody768_118 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody768_0, 768, 16)) (some 764) ([26, 12]) (some (26, sourceBody768_56, 768, 17))

def sourceBody768_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_118 sourceBody768_3

def sourceBody768_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_119 sourceBody768_0

def sourceBody768_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_55 sourceBody768_120

def sourceBody768_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_117 sourceBody768_121

def sourceBody768_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_122

def sourceBody768_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_123

def sourceBody768_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_116 sourceBody768_124

def sourceBody768_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 22)

def sourceBody768_127 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody768_0, 768, 18)) (some 70) ([26]) (some (26, sourceBody768_56, 768, 19))

def sourceBody768_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_127 sourceBody768_3

def sourceBody768_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_128 sourceBody768_0

def sourceBody768_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_126 sourceBody768_129

def sourceBody768_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_130

def sourceBody768_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_131

def sourceBody768_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_125 sourceBody768_132

def sourceBody768_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody768_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody768_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_135 sourceBody768_0

def sourceBody768_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_134 sourceBody768_136

def sourceBody768_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_133 sourceBody768_137

def sourceBody768_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_37 sourceBody768_138

def sourceBody768_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_139

def sourceBody768_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_36 sourceBody768_140

def sourceBody768_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_141

def sourceBody768_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_35 sourceBody768_142

def sourceBody768_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_17 sourceBody768_143

def sourceBody768_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_144

def sourceBody768_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_145

def sourceBody768_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_11 sourceBody768_146

def sourceBody768_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_147

def sourceBody768_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_148

def sourceBody768_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_5 sourceBody768_149

def sourceBody768_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_150

def sourceBody768_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody768_0 sourceBody768_151

def source768 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (768, 5, sourceBody768_152)
end InitECandidate.Proofs.WordStages
