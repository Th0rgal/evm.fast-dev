import InitECandidate.Proofs.WordStages.Source677
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody693_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody693_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody693_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody693_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody693_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody693_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 42)

def sourceBody693_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 12)

def sourceBody693_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 36)

def sourceBody693_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 24)

def sourceBody693_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody693_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([50]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody693_0, 693, 2)) (some 102) ([8, 32, 20, 46]) (some (8, sourceBody693_9, 693, 3))

def sourceBody693_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody693_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_10 sourceBody693_11

def sourceBody693_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_12 sourceBody693_0

def sourceBody693_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_8 sourceBody693_13

def sourceBody693_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_7 sourceBody693_14

def sourceBody693_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_6 sourceBody693_15

def sourceBody693_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_5 sourceBody693_16

def sourceBody693_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 50)

def sourceBody693_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody693_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody693_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody693_22 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 32 (Flapjack.WordRegImm.reg 20) sourceBody693_20 sourceBody693_21

def sourceBody693_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_22 sourceBody693_11

def sourceBody693_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 32)

def sourceBody693_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 4)

def sourceBody693_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody693_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody693_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody693_0, 693, 4)) (some 78) ([32, 20]) (some (32, sourceBody693_27, 693, 5))

def sourceBody693_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_28 sourceBody693_11

def sourceBody693_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_29 sourceBody693_0

def sourceBody693_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_26 sourceBody693_30

def sourceBody693_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_25 sourceBody693_31

def sourceBody693_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_32

def sourceBody693_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_33

def sourceBody693_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody693_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody693_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_36 sourceBody693_0

def sourceBody693_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_35 sourceBody693_37

def sourceBody693_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_34 sourceBody693_38

def sourceBody693_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 46 (Flapjack.WordRegImm.imm 0#64) sourceBody693_39 sourceBody693_0

def sourceBody693_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_40 sourceBody693_11

def sourceBody693_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_41 sourceBody693_0

def sourceBody693_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_24 sourceBody693_42

def sourceBody693_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_23 sourceBody693_43

def sourceBody693_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_19 sourceBody693_44

def sourceBody693_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_18 sourceBody693_45

def sourceBody693_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 42)

def sourceBody693_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 12)

def sourceBody693_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 36)

def sourceBody693_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 24)

def sourceBody693_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody693_52 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 32, 20, 46]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody693_0, 693, 6)) (some 660) ([16, 40, 28, 54]) (some (16, sourceBody693_51, 693, 7))

def sourceBody693_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_52 sourceBody693_11

def sourceBody693_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_53 sourceBody693_0

def sourceBody693_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_50 sourceBody693_54

def sourceBody693_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_49 sourceBody693_55

def sourceBody693_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_48 sourceBody693_56

def sourceBody693_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_47 sourceBody693_57

def sourceBody693_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 2))

def sourceBody693_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody693_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody693_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody693_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody693_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody693_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody693_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody693_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody693_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 40)

def sourceBody693_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody693_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 54)

def sourceBody693_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody693_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 32)

def sourceBody693_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 20)

def sourceBody693_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 46)

def sourceBody693_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody693_76 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 40, 28, 54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody693_0, 693, 8)) (some 657) ([14, 38, 26, 52, 10, 34, 22, 48]) (some (14, sourceBody693_75, 693, 9))

def sourceBody693_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_76 sourceBody693_11

def sourceBody693_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_77 sourceBody693_0

def sourceBody693_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_74 sourceBody693_78

def sourceBody693_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_73 sourceBody693_79

def sourceBody693_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_72 sourceBody693_80

def sourceBody693_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_71 sourceBody693_81

def sourceBody693_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_70 sourceBody693_82

def sourceBody693_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_69 sourceBody693_83

def sourceBody693_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_68 sourceBody693_84

def sourceBody693_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_67 sourceBody693_85

def sourceBody693_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody693_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 30)

def sourceBody693_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 18)

def sourceBody693_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 44)

def sourceBody693_91 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 30, 18, 44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody693_0, 693, 10)) (some 657) ([14, 38, 26, 52, 10, 34, 22, 48]) (some (14, sourceBody693_75, 693, 11))

def sourceBody693_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_91 sourceBody693_11

def sourceBody693_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_92 sourceBody693_0

def sourceBody693_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_74 sourceBody693_93

def sourceBody693_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_73 sourceBody693_94

def sourceBody693_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_72 sourceBody693_95

def sourceBody693_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_71 sourceBody693_96

def sourceBody693_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_90 sourceBody693_97

def sourceBody693_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_89 sourceBody693_98

def sourceBody693_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_88 sourceBody693_99

def sourceBody693_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_87 sourceBody693_100

def sourceBody693_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_86 sourceBody693_101

def sourceBody693_103 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 40, 28, 54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody693_0, 693, 12)) (some 659) ([14, 38, 26, 52]) (some (14, sourceBody693_75, 693, 13))

def sourceBody693_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_103 sourceBody693_11

def sourceBody693_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_104 sourceBody693_0

def sourceBody693_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_70 sourceBody693_105

def sourceBody693_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_69 sourceBody693_106

def sourceBody693_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_68 sourceBody693_107

def sourceBody693_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_67 sourceBody693_108

def sourceBody693_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_102 sourceBody693_109

def sourceBody693_111 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 30, 18, 44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody693_0, 693, 14)) (some 659) ([14, 38, 26, 52]) (some (14, sourceBody693_75, 693, 15))

def sourceBody693_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_111 sourceBody693_11

def sourceBody693_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_112 sourceBody693_0

def sourceBody693_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_90 sourceBody693_113

def sourceBody693_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_89 sourceBody693_114

def sourceBody693_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_88 sourceBody693_115

def sourceBody693_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_87 sourceBody693_116

def sourceBody693_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_110 sourceBody693_117

def sourceBody693_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 16)

def sourceBody693_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 40)

def sourceBody693_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 28)

def sourceBody693_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 54)

def sourceBody693_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 4)

def sourceBody693_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody693_125 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody693_0, 693, 16)) (some 147) ([38, 26, 52, 10, 34]) (some (38, sourceBody693_124, 693, 17))

def sourceBody693_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_125 sourceBody693_11

def sourceBody693_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_126 sourceBody693_0

def sourceBody693_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_123 sourceBody693_127

def sourceBody693_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_122 sourceBody693_128

def sourceBody693_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_121 sourceBody693_129

def sourceBody693_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_120 sourceBody693_130

def sourceBody693_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_119 sourceBody693_131

def sourceBody693_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_132

def sourceBody693_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_133

def sourceBody693_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_118 sourceBody693_134

def sourceBody693_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 6)

def sourceBody693_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody693_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 18)

def sourceBody693_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 44)

def sourceBody693_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody693_141 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody693_0, 693, 18)) (some 147) ([38, 26, 52, 10, 34]) (some (38, sourceBody693_124, 693, 19))

def sourceBody693_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_141 sourceBody693_11

def sourceBody693_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_142 sourceBody693_0

def sourceBody693_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_140 sourceBody693_143

def sourceBody693_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_139 sourceBody693_144

def sourceBody693_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_138 sourceBody693_145

def sourceBody693_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_137 sourceBody693_146

def sourceBody693_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_136 sourceBody693_147

def sourceBody693_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_148

def sourceBody693_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_149

def sourceBody693_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_135 sourceBody693_150

def sourceBody693_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody693_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody693_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_153 sourceBody693_0

def sourceBody693_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_152 sourceBody693_154

def sourceBody693_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_151 sourceBody693_155

def sourceBody693_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_66 sourceBody693_156

def sourceBody693_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_157

def sourceBody693_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_65 sourceBody693_158

def sourceBody693_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_159

def sourceBody693_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_64 sourceBody693_160

def sourceBody693_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_161

def sourceBody693_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_63 sourceBody693_162

def sourceBody693_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_163

def sourceBody693_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_62 sourceBody693_164

def sourceBody693_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_165

def sourceBody693_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_61 sourceBody693_166

def sourceBody693_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_167

def sourceBody693_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_60 sourceBody693_168

def sourceBody693_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_169

def sourceBody693_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_59 sourceBody693_170

def sourceBody693_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_171

def sourceBody693_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_58 sourceBody693_172

def sourceBody693_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_173

def sourceBody693_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_174

def sourceBody693_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_175

def sourceBody693_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_176

def sourceBody693_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_177

def sourceBody693_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_178

def sourceBody693_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_179

def sourceBody693_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_180

def sourceBody693_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_46 sourceBody693_181

def sourceBody693_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_17 sourceBody693_182

def sourceBody693_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_183

def sourceBody693_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_184

def sourceBody693_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_4 sourceBody693_185

def sourceBody693_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_186

def sourceBody693_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_3 sourceBody693_187

def sourceBody693_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_188

def sourceBody693_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_2 sourceBody693_189

def sourceBody693_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_190

def sourceBody693_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_1 sourceBody693_191

def sourceBody693_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody693_0 sourceBody693_192

def source693 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (693, 3, sourceBody693_193)
end InitECandidate.Proofs.WordStages
