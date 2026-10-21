import InitECandidate.Proofs.WordStages.Source780
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody796_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody796_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody796_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody796_0, 796, 2)) (some 69) ([]) (some (36, sourceBody796_1, 796, 3))

def sourceBody796_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody796_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_2 sourceBody796_3

def sourceBody796_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_4 sourceBody796_0

def sourceBody796_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 576#64)

def sourceBody796_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody796_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody796_0, 796, 4)) (some 68) ([24]) (some (24, sourceBody796_7, 796, 5))

def sourceBody796_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_8 sourceBody796_3

def sourceBody796_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_9 sourceBody796_0

def sourceBody796_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_6 sourceBody796_10

def sourceBody796_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 36)

def sourceBody796_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody796_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody796_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody796_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody796_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.const 480#64])

def sourceBody796_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 24)

def sourceBody796_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 6)

def sourceBody796_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody796_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody796_0, 796, 6)) (some 725) ([38, 28]) (some (38, sourceBody796_20, 796, 7))

def sourceBody796_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_21 sourceBody796_3

def sourceBody796_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_22 sourceBody796_0

def sourceBody796_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_19 sourceBody796_23

def sourceBody796_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_18 sourceBody796_24

def sourceBody796_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_25

def sourceBody796_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_26

def sourceBody796_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody796_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 16)

def sourceBody796_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody796_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody796_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody796_33 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 28 (Flapjack.WordRegImm.reg 50) sourceBody796_31 sourceBody796_32

def sourceBody796_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_33 sourceBody796_3

def sourceBody796_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody796_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 24)

def sourceBody796_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 24)

def sourceBody796_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody796_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody796_40 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody796_0, 796, 8)) (some 735) ([28, 50, 8]) (some (28, sourceBody796_39, 796, 9))

def sourceBody796_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_40 sourceBody796_3

def sourceBody796_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_41 sourceBody796_0

def sourceBody796_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_38 sourceBody796_42

def sourceBody796_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_37 sourceBody796_43

def sourceBody796_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_36 sourceBody796_44

def sourceBody796_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_45

def sourceBody796_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_46

def sourceBody796_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody796_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 38)

def sourceBody796_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_49 sourceBody796_0

def sourceBody796_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_50 sourceBody796_0

def sourceBody796_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_48 sourceBody796_51

def sourceBody796_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_52

def sourceBody796_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_47 sourceBody796_53

def sourceBody796_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody796_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_54 sourceBody796_55

def sourceBody796_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody796_58 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody796_56 sourceBody796_57

def sourceBody796_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_58 sourceBody796_3

def sourceBody796_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_59 sourceBody796_0

def sourceBody796_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_35 sourceBody796_60

def sourceBody796_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_34 sourceBody796_61

def sourceBody796_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_30 sourceBody796_62

def sourceBody796_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_29 sourceBody796_63

def sourceBody796_65 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody796_64 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody796_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_65 sourceBody796_3

def sourceBody796_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_3 sourceBody796_66

def sourceBody796_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 46)

def sourceBody796_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 4)

def sourceBody796_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 24)

def sourceBody796_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody796_0, 796, 10)) (some 735) ([28, 50, 8]) (some (28, sourceBody796_39, 796, 11))

def sourceBody796_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_71 sourceBody796_3

def sourceBody796_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_72 sourceBody796_0

def sourceBody796_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_70 sourceBody796_73

def sourceBody796_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_69 sourceBody796_74

def sourceBody796_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_68 sourceBody796_75

def sourceBody796_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_76

def sourceBody796_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_77

def sourceBody796_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_67 sourceBody796_78

def sourceBody796_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 10)

def sourceBody796_81 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody796_0, 796, 12)) (some 735) ([28, 50, 8]) (some (28, sourceBody796_39, 796, 13))

def sourceBody796_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_81 sourceBody796_3

def sourceBody796_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_82 sourceBody796_0

def sourceBody796_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_38 sourceBody796_83

def sourceBody796_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_37 sourceBody796_84

def sourceBody796_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_80 sourceBody796_85

def sourceBody796_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_86

def sourceBody796_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_87

def sourceBody796_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_79 sourceBody796_88

def sourceBody796_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 46)

def sourceBody796_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody796_92 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody796_0, 796, 14)) (some 735) ([28, 50, 8]) (some (28, sourceBody796_39, 796, 15))

def sourceBody796_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_92 sourceBody796_3

def sourceBody796_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_93 sourceBody796_0

def sourceBody796_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_91 sourceBody796_94

def sourceBody796_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_90 sourceBody796_95

def sourceBody796_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_80 sourceBody796_96

def sourceBody796_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_97

def sourceBody796_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_98

def sourceBody796_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_89 sourceBody796_99

def sourceBody796_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 32)

def sourceBody796_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 10)

def sourceBody796_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 1528#64])

def sourceBody796_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody796_105 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody796_0, 796, 16)) (some 740) ([28, 50, 8, 30]) (some (28, sourceBody796_39, 796, 17))

def sourceBody796_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_105 sourceBody796_3

def sourceBody796_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_106 sourceBody796_0

def sourceBody796_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_104 sourceBody796_107

def sourceBody796_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_103 sourceBody796_108

def sourceBody796_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_102 sourceBody796_109

def sourceBody796_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_101 sourceBody796_110

def sourceBody796_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_111

def sourceBody796_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_112

def sourceBody796_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_100 sourceBody796_113

def sourceBody796_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 32)

def sourceBody796_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 46)

def sourceBody796_117 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody796_0, 796, 18)) (some 735) ([28, 50, 8]) (some (28, sourceBody796_39, 796, 19))

def sourceBody796_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_117 sourceBody796_3

def sourceBody796_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_118 sourceBody796_0

def sourceBody796_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_116 sourceBody796_119

def sourceBody796_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_115 sourceBody796_120

def sourceBody796_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_101 sourceBody796_121

def sourceBody796_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_122

def sourceBody796_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_123

def sourceBody796_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_114 sourceBody796_124

def sourceBody796_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody796_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 2)

def sourceBody796_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 32)

def sourceBody796_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 50

def sourceBody796_130 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody796_0, 796, 20)) (some 725) ([50, 8]) (some (50, sourceBody796_129, 796, 21))

def sourceBody796_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_130 sourceBody796_3

def sourceBody796_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_131 sourceBody796_0

def sourceBody796_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_128 sourceBody796_132

def sourceBody796_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_127 sourceBody796_133

def sourceBody796_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_134

def sourceBody796_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_135

def sourceBody796_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_28 sourceBody796_0

def sourceBody796_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_137 sourceBody796_0

def sourceBody796_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_136 sourceBody796_138

def sourceBody796_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 16)

def sourceBody796_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody796_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody796_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody796_144 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 50 (Flapjack.WordRegImm.reg 8) sourceBody796_142 sourceBody796_143

def sourceBody796_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_144 sourceBody796_3

def sourceBody796_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 50)

def sourceBody796_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody796_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 30 30 50 8))

def sourceBody796_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody796_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 5216#64, Flapjack.WordLangExpHOL.var 30])

def sourceBody796_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 32)

def sourceBody796_152 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody796_0, 796, 22)) (some 735) ([18, 40, 14]) (some (50, sourceBody796_129, 796, 23))

def sourceBody796_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_152 sourceBody796_3

def sourceBody796_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_153 sourceBody796_0

def sourceBody796_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_151 sourceBody796_154

def sourceBody796_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_150 sourceBody796_155

def sourceBody796_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_149 sourceBody796_156

def sourceBody796_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_148 sourceBody796_157

def sourceBody796_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_147 sourceBody796_158

def sourceBody796_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_140 sourceBody796_159

def sourceBody796_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_160

def sourceBody796_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_161

def sourceBody796_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 42)

def sourceBody796_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 20)

def sourceBody796_165 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody796_0, 796, 24)) (some 736) ([50, 8]) (some (50, sourceBody796_129, 796, 25))

def sourceBody796_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_165 sourceBody796_3

def sourceBody796_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_166 sourceBody796_0

def sourceBody796_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_164 sourceBody796_167

def sourceBody796_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_163 sourceBody796_168

def sourceBody796_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_169

def sourceBody796_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_170

def sourceBody796_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_162 sourceBody796_171

def sourceBody796_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 42)

def sourceBody796_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 6)

def sourceBody796_175 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody796_0, 796, 26)) (some 735) ([50, 8, 30]) (some (50, sourceBody796_129, 796, 27))

def sourceBody796_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_175 sourceBody796_3

def sourceBody796_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_176 sourceBody796_0

def sourceBody796_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_174 sourceBody796_177

def sourceBody796_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_173 sourceBody796_178

def sourceBody796_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_163 sourceBody796_179

def sourceBody796_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_180

def sourceBody796_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_181

def sourceBody796_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_172 sourceBody796_182

def sourceBody796_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 4)

def sourceBody796_185 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody796_0, 796, 28)) (some 731) ([50, 8, 30]) (some (50, sourceBody796_129, 796, 29))

def sourceBody796_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_185 sourceBody796_3

def sourceBody796_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_186 sourceBody796_0

def sourceBody796_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_184 sourceBody796_187

def sourceBody796_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_173 sourceBody796_188

def sourceBody796_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_163 sourceBody796_189

def sourceBody796_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_190

def sourceBody796_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_191

def sourceBody796_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_183 sourceBody796_192

def sourceBody796_194 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody796_0, 796, 30)) (some 728) ([50]) (some (50, sourceBody796_129, 796, 31))

def sourceBody796_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_194 sourceBody796_3

def sourceBody796_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_195 sourceBody796_0

def sourceBody796_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_163 sourceBody796_196

def sourceBody796_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody796_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody796_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody796_201 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 8 (Flapjack.WordRegImm.reg 30) sourceBody796_199 sourceBody796_200

def sourceBody796_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_201 sourceBody796_3

def sourceBody796_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody796_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody796_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody796_206 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.reg 14) sourceBody796_205 sourceBody796_203

def sourceBody796_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_206 sourceBody796_3

def sourceBody796_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 38)

def sourceBody796_209 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody796_210 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody796_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody796_212 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 26 (Flapjack.WordRegImm.reg 48) sourceBody796_210 sourceBody796_211

def sourceBody796_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_212 sourceBody796_3

def sourceBody796_214 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody796_215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody796_216 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody796_217 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.reg 22) sourceBody796_216 sourceBody796_214

def sourceBody796_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_217 sourceBody796_3

def sourceBody796_219 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.var 34])

def sourceBody796_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody796_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_220 sourceBody796_0

def sourceBody796_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_221 sourceBody796_0

def sourceBody796_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody796_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 20)

def sourceBody796_225 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody796_226 : WordLangProgHOL (BitVec 64) :=
.call (some (([50]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody796_0, 796, 32)) (some 725) ([8, 30]) (some (8, sourceBody796_225, 796, 33))

def sourceBody796_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_226 sourceBody796_3

def sourceBody796_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_227 sourceBody796_0

def sourceBody796_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_224 sourceBody796_228

def sourceBody796_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_223 sourceBody796_229

def sourceBody796_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_230

def sourceBody796_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_231

def sourceBody796_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_222 sourceBody796_232

def sourceBody796_234 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 44 (Flapjack.WordRegImm.imm 0#64) sourceBody796_233 sourceBody796_0

def sourceBody796_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_234 sourceBody796_3

def sourceBody796_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_235 sourceBody796_0

def sourceBody796_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_219 sourceBody796_236

def sourceBody796_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_218 sourceBody796_237

def sourceBody796_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_215 sourceBody796_238

def sourceBody796_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_214 sourceBody796_239

def sourceBody796_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_213 sourceBody796_240

def sourceBody796_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_209 sourceBody796_241

def sourceBody796_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_208 sourceBody796_242

def sourceBody796_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_207 sourceBody796_243

def sourceBody796_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_204 sourceBody796_244

def sourceBody796_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_203 sourceBody796_245

def sourceBody796_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_202 sourceBody796_246

def sourceBody796_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_198 sourceBody796_247

def sourceBody796_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_35 sourceBody796_248

def sourceBody796_250 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody796_251 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 50)

def sourceBody796_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_251 sourceBody796_0

def sourceBody796_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_252 sourceBody796_0

def sourceBody796_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_250 sourceBody796_253

def sourceBody796_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_254

def sourceBody796_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_249 sourceBody796_255

def sourceBody796_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_197 sourceBody796_256

def sourceBody796_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_257

def sourceBody796_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_258

def sourceBody796_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_193 sourceBody796_259

def sourceBody796_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_260 sourceBody796_55

def sourceBody796_262 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody796_261 sourceBody796_57

def sourceBody796_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_262 sourceBody796_3

def sourceBody796_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_263 sourceBody796_0

def sourceBody796_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_146 sourceBody796_264

def sourceBody796_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_145 sourceBody796_265

def sourceBody796_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_141 sourceBody796_266

def sourceBody796_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_140 sourceBody796_267

def sourceBody796_269 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody796_268 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody796_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_269 sourceBody796_3

def sourceBody796_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_3 sourceBody796_270

def sourceBody796_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_139 sourceBody796_271

def sourceBody796_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 12)

def sourceBody796_274 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody796_0, 796, 34)) (some 70) ([50]) (some (50, sourceBody796_129, 796, 35))

def sourceBody796_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_274 sourceBody796_3

def sourceBody796_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_275 sourceBody796_0

def sourceBody796_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_273 sourceBody796_276

def sourceBody796_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_277

def sourceBody796_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_278

def sourceBody796_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_272 sourceBody796_279

def sourceBody796_281 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 38)

def sourceBody796_282 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [28]

def sourceBody796_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_282 sourceBody796_0

def sourceBody796_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_281 sourceBody796_283

def sourceBody796_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_280 sourceBody796_284

def sourceBody796_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_126 sourceBody796_285

def sourceBody796_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_286

def sourceBody796_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_125 sourceBody796_287

def sourceBody796_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_28 sourceBody796_288

def sourceBody796_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_289

def sourceBody796_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_27 sourceBody796_290

def sourceBody796_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_17 sourceBody796_291

def sourceBody796_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_292

def sourceBody796_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_16 sourceBody796_293

def sourceBody796_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_294

def sourceBody796_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_15 sourceBody796_295

def sourceBody796_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_296

def sourceBody796_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_14 sourceBody796_297

def sourceBody796_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_298

def sourceBody796_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_13 sourceBody796_299

def sourceBody796_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_300

def sourceBody796_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_12 sourceBody796_301

def sourceBody796_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_302

def sourceBody796_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_11 sourceBody796_303

def sourceBody796_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_304

def sourceBody796_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_305

def sourceBody796_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_5 sourceBody796_306

def sourceBody796_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_307

def sourceBody796_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody796_0 sourceBody796_308

def source796 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (796, 4, sourceBody796_309)
end InitECandidate.Proofs.WordStages
