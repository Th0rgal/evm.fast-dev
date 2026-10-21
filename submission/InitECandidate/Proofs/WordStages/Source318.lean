import InitECandidate.Proofs.WordStages.Source302
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody318_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody318_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody318_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody318_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody318_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody318_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 24)

def sourceBody318_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody318_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody318_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody318_9 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.WordRegImm.reg 18) sourceBody318_7 sourceBody318_8

def sourceBody318_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody318_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_9 sourceBody318_10

def sourceBody318_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody318_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody318_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody318_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody318_0, 318, 2)) (some 323) ([6]) (some (6, sourceBody318_14, 318, 3))

def sourceBody318_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_15 sourceBody318_10

def sourceBody318_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_16 sourceBody318_0

def sourceBody318_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_13 sourceBody318_17

def sourceBody318_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 28])

def sourceBody318_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody318_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_20 sourceBody318_0

def sourceBody318_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_21 sourceBody318_0

def sourceBody318_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_19 sourceBody318_22

def sourceBody318_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_23

def sourceBody318_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_18 sourceBody318_24

def sourceBody318_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_25

def sourceBody318_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_26

def sourceBody318_28 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody318_27 sourceBody318_0

def sourceBody318_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_28 sourceBody318_10

def sourceBody318_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_29 sourceBody318_0

def sourceBody318_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_12 sourceBody318_30

def sourceBody318_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_11 sourceBody318_31

def sourceBody318_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_6 sourceBody318_32

def sourceBody318_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_5 sourceBody318_33

def sourceBody318_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody318_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody318_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody318_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody318_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody318_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody318_41 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 18 (Flapjack.WordRegImm.reg 12) sourceBody318_39 sourceBody318_40

def sourceBody318_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_41 sourceBody318_10

def sourceBody318_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 18)

def sourceBody318_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 32#64,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 28)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody318_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody318_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody318_0, 318, 4)) (some 323) ([18]) (some (18, sourceBody318_45, 318, 5))

def sourceBody318_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_46 sourceBody318_10

def sourceBody318_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_47 sourceBody318_0

def sourceBody318_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_44 sourceBody318_48

def sourceBody318_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 6])

def sourceBody318_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 18)

def sourceBody318_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_51 sourceBody318_0

def sourceBody318_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_52 sourceBody318_0

def sourceBody318_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_50 sourceBody318_53

def sourceBody318_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_54

def sourceBody318_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody318_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 18)

def sourceBody318_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_57 sourceBody318_0

def sourceBody318_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_58 sourceBody318_0

def sourceBody318_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_56 sourceBody318_59

def sourceBody318_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_60

def sourceBody318_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_55 sourceBody318_61

def sourceBody318_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_49 sourceBody318_62

def sourceBody318_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_63

def sourceBody318_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_64

def sourceBody318_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody318_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_65 sourceBody318_66

def sourceBody318_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody318_69 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody318_67 sourceBody318_68

def sourceBody318_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_69 sourceBody318_10

def sourceBody318_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_70 sourceBody318_0

def sourceBody318_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_43 sourceBody318_71

def sourceBody318_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_42 sourceBody318_72

def sourceBody318_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_38 sourceBody318_73

def sourceBody318_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_37 sourceBody318_74

def sourceBody318_76 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody318_75 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody318_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_76 sourceBody318_10

def sourceBody318_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_10 sourceBody318_77

def sourceBody318_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody318_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 168#64]))

def sourceBody318_81 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody318_0, 318, 6)) (some 322) ([18, 12]) (some (18, sourceBody318_45, 318, 7))

def sourceBody318_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_81 sourceBody318_10

def sourceBody318_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_82 sourceBody318_0

def sourceBody318_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_80 sourceBody318_83

def sourceBody318_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_79 sourceBody318_84

def sourceBody318_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_85 sourceBody318_55

def sourceBody318_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_86

def sourceBody318_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_87

def sourceBody318_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_78 sourceBody318_88

def sourceBody318_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_36 sourceBody318_89

def sourceBody318_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_90

def sourceBody318_92 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody318_91 sourceBody318_0

def sourceBody318_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_92 sourceBody318_10

def sourceBody318_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_93 sourceBody318_0

def sourceBody318_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_12 sourceBody318_94

def sourceBody318_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_11 sourceBody318_95

def sourceBody318_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_35 sourceBody318_96

def sourceBody318_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_5 sourceBody318_97

def sourceBody318_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_34 sourceBody318_98

def sourceBody318_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody318_101 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody318_0, 318, 8)) (some 180) ([6]) (some (6, sourceBody318_14, 318, 9))

def sourceBody318_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_101 sourceBody318_10

def sourceBody318_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_102 sourceBody318_0

def sourceBody318_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_100 sourceBody318_103

def sourceBody318_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.var 8])

def sourceBody318_106 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody318_0, 318, 10)) (some 68) ([18]) (some (18, sourceBody318_45, 318, 11))

def sourceBody318_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_106 sourceBody318_10

def sourceBody318_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_107 sourceBody318_0

def sourceBody318_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_105 sourceBody318_108

def sourceBody318_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 8)

def sourceBody318_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody318_112 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody318_0, 318, 12)) (some 178) ([12, 26]) (some (12, sourceBody318_111, 318, 13))

def sourceBody318_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_112 sourceBody318_10

def sourceBody318_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_113 sourceBody318_0

def sourceBody318_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_110 sourceBody318_114

def sourceBody318_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_12 sourceBody318_115

def sourceBody318_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_116

def sourceBody318_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_117

def sourceBody318_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 24)

def sourceBody318_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody318_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody318_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody318_123 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.reg 10) sourceBody318_121 sourceBody318_122

def sourceBody318_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_123 sourceBody318_10

def sourceBody318_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody318_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 18])

def sourceBody318_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 20)

def sourceBody318_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody318_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody318_130 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody318_0, 318, 14)) (some 176) ([26, 10, 22]) (some (26, sourceBody318_129, 318, 15))

def sourceBody318_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_130 sourceBody318_10

def sourceBody318_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_131 sourceBody318_0

def sourceBody318_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_128 sourceBody318_132

def sourceBody318_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_127 sourceBody318_133

def sourceBody318_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_126 sourceBody318_134

def sourceBody318_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 12])

def sourceBody318_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 26)

def sourceBody318_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_137 sourceBody318_0

def sourceBody318_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_138 sourceBody318_0

def sourceBody318_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_136 sourceBody318_139

def sourceBody318_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_140

def sourceBody318_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 24)

def sourceBody318_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody318_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody318_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody318_146 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 22) sourceBody318_144 sourceBody318_145

def sourceBody318_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_146 sourceBody318_10

def sourceBody318_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody318_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 18])

def sourceBody318_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody318_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody318_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody318_153 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody318_0, 318, 16)) (some 176) ([10, 22, 16]) (some (10, sourceBody318_152, 318, 17))

def sourceBody318_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_153 sourceBody318_10

def sourceBody318_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_154 sourceBody318_0

def sourceBody318_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_151 sourceBody318_155

def sourceBody318_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_150 sourceBody318_156

def sourceBody318_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_149 sourceBody318_157

def sourceBody318_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 26])

def sourceBody318_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody318_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_160 sourceBody318_0

def sourceBody318_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_161 sourceBody318_0

def sourceBody318_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_159 sourceBody318_162

def sourceBody318_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_163

def sourceBody318_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_158 sourceBody318_164

def sourceBody318_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_165

def sourceBody318_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_166

def sourceBody318_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody318_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 18])

def sourceBody318_170 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody318_0, 318, 18)) (some 325) ([10, 22]) (some (10, sourceBody318_152, 318, 19))

def sourceBody318_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_170 sourceBody318_10

def sourceBody318_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_171 sourceBody318_0

def sourceBody318_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_169 sourceBody318_172

def sourceBody318_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_168 sourceBody318_173

def sourceBody318_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_174 sourceBody318_164

def sourceBody318_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_175

def sourceBody318_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_176

def sourceBody318_178 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody318_167 sourceBody318_177

def sourceBody318_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_178 sourceBody318_10

def sourceBody318_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_179 sourceBody318_0

def sourceBody318_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_148 sourceBody318_180

def sourceBody318_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_147 sourceBody318_181

def sourceBody318_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_143 sourceBody318_182

def sourceBody318_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_142 sourceBody318_183

def sourceBody318_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_141 sourceBody318_184

def sourceBody318_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_135 sourceBody318_185

def sourceBody318_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_186

def sourceBody318_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_187

def sourceBody318_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody318_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody318_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody318_192 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 10 (Flapjack.WordRegImm.reg 22) sourceBody318_144 sourceBody318_145

def sourceBody318_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_192 sourceBody318_10

def sourceBody318_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 32#64,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody318_195 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody318_0, 318, 20)) (some 325) ([10, 22]) (some (10, sourceBody318_152, 318, 21))

def sourceBody318_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_195 sourceBody318_10

def sourceBody318_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_196 sourceBody318_0

def sourceBody318_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_169 sourceBody318_197

def sourceBody318_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_194 sourceBody318_198

def sourceBody318_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody318_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody318_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_201 sourceBody318_0

def sourceBody318_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_202 sourceBody318_0

def sourceBody318_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_200 sourceBody318_203

def sourceBody318_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_204

def sourceBody318_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_164 sourceBody318_205

def sourceBody318_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_199 sourceBody318_206

def sourceBody318_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_207

def sourceBody318_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_208

def sourceBody318_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_209 sourceBody318_66

def sourceBody318_211 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody318_210 sourceBody318_68

def sourceBody318_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_211 sourceBody318_10

def sourceBody318_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_212 sourceBody318_0

def sourceBody318_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_148 sourceBody318_213

def sourceBody318_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_193 sourceBody318_214

def sourceBody318_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_191 sourceBody318_215

def sourceBody318_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_190 sourceBody318_216

def sourceBody318_218 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody318_217 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody318_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_218 sourceBody318_10

def sourceBody318_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_10 sourceBody318_219

def sourceBody318_221 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody318_222 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 168#64]))

def sourceBody318_223 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody318_0, 318, 22)) (some 176) ([10, 22, 16]) (some (10, sourceBody318_152, 318, 23))

def sourceBody318_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_223 sourceBody318_10

def sourceBody318_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_224 sourceBody318_0

def sourceBody318_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_222 sourceBody318_225

def sourceBody318_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_221 sourceBody318_226

def sourceBody318_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_149 sourceBody318_227

def sourceBody318_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_228 sourceBody318_164

def sourceBody318_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_229

def sourceBody318_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_230

def sourceBody318_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_220 sourceBody318_231

def sourceBody318_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_189 sourceBody318_232

def sourceBody318_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_233

def sourceBody318_235 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody318_188 sourceBody318_234

def sourceBody318_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_235 sourceBody318_10

def sourceBody318_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_236 sourceBody318_0

def sourceBody318_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_125 sourceBody318_237

def sourceBody318_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_124 sourceBody318_238

def sourceBody318_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_120 sourceBody318_239

def sourceBody318_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_119 sourceBody318_240

def sourceBody318_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody318_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody318_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 26)

def sourceBody318_245 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 12) 10

def sourceBody318_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_245 sourceBody318_0

def sourceBody318_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_244 sourceBody318_246

def sourceBody318_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_247 sourceBody318_0

def sourceBody318_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_243 sourceBody318_248

def sourceBody318_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_249

def sourceBody318_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_242 sourceBody318_250

def sourceBody318_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_251

def sourceBody318_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_241 sourceBody318_252

def sourceBody318_254 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody318_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_43 sourceBody318_248

def sourceBody318_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_255

def sourceBody318_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_254 sourceBody318_256

def sourceBody318_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_257

def sourceBody318_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_253 sourceBody318_258

def sourceBody318_260 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody318_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_260 sourceBody318_0

def sourceBody318_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_189 sourceBody318_261

def sourceBody318_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_259 sourceBody318_262

def sourceBody318_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_37 sourceBody318_263

def sourceBody318_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_264

def sourceBody318_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_118 sourceBody318_265

def sourceBody318_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_109 sourceBody318_266

def sourceBody318_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_267

def sourceBody318_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_268

def sourceBody318_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_104 sourceBody318_269

def sourceBody318_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_270

def sourceBody318_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_271

def sourceBody318_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_99 sourceBody318_272

def sourceBody318_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_4 sourceBody318_273

def sourceBody318_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_274

def sourceBody318_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_3 sourceBody318_275

def sourceBody318_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_276

def sourceBody318_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_2 sourceBody318_277

def sourceBody318_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_278

def sourceBody318_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_1 sourceBody318_279

def sourceBody318_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody318_0 sourceBody318_280

def source318 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (318, 3, sourceBody318_281)
end InitECandidate.Proofs.WordStages
