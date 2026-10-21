import InitECandidate.Proofs.WordStages.Source261
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody277_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody277_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 208#64]))

def sourceBody277_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 200#64]))

def sourceBody277_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody277_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody277_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody277_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody277_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.var 58])

def sourceBody277_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 8)

def sourceBody277_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.const 1835008#64)

def sourceBody277_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody277_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody277_12 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 28 (Flapjack.WordRegImm.reg 64) sourceBody277_10 sourceBody277_11

def sourceBody277_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody277_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_12 sourceBody277_13

def sourceBody277_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody277_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody277_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [44]

def sourceBody277_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_17 sourceBody277_0

def sourceBody277_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_16 sourceBody277_18

def sourceBody277_20 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody277_19 sourceBody277_0

def sourceBody277_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_20 sourceBody277_13

def sourceBody277_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_21 sourceBody277_0

def sourceBody277_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_15 sourceBody277_22

def sourceBody277_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_14 sourceBody277_23

def sourceBody277_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_9 sourceBody277_24

def sourceBody277_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_8 sourceBody277_25

def sourceBody277_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 22)

def sourceBody277_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 54

def sourceBody277_29 : WordLangProgHOL (BitVec 64) :=
.call (some (([44, 28, 64, 18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody277_0, 277, 2)) (some 276) ([54]) (some (54, sourceBody277_28, 277, 3))

def sourceBody277_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_29 sourceBody277_13

def sourceBody277_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_30 sourceBody277_0

def sourceBody277_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_27 sourceBody277_31

def sourceBody277_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 131072#64)

def sourceBody277_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody277_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([54, 36, 72, 6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody277_0, 277, 4)) (some 99) ([42]) (some (42, sourceBody277_34, 277, 5))

def sourceBody277_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_35 sourceBody277_13

def sourceBody277_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_36 sourceBody277_0

def sourceBody277_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_33 sourceBody277_37

def sourceBody277_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 54)

def sourceBody277_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 36)

def sourceBody277_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 72)

def sourceBody277_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody277_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 44)

def sourceBody277_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 28)

def sourceBody277_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 64)

def sourceBody277_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 18)

def sourceBody277_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 52

def sourceBody277_48 : WordLangProgHOL (BitVec 64) :=
.call (some (([42, 26, 62, 16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody277_0, 277, 6)) (some 120) ([52, 34, 70, 10, 46, 30, 66, 20]) (some (52, sourceBody277_47, 277, 7))

def sourceBody277_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_48 sourceBody277_13

def sourceBody277_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_49 sourceBody277_0

def sourceBody277_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_46 sourceBody277_50

def sourceBody277_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_45 sourceBody277_51

def sourceBody277_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_44 sourceBody277_52

def sourceBody277_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_43 sourceBody277_53

def sourceBody277_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_42 sourceBody277_54

def sourceBody277_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_41 sourceBody277_55

def sourceBody277_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_40 sourceBody277_56

def sourceBody277_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_39 sourceBody277_57

def sourceBody277_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 8192#64)

def sourceBody277_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody277_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([52, 34, 70, 10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody277_0, 277, 8)) (some 99) ([46]) (some (46, sourceBody277_60, 277, 9))

def sourceBody277_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_61 sourceBody277_13

def sourceBody277_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_62 sourceBody277_0

def sourceBody277_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_59 sourceBody277_63

def sourceBody277_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 52)

def sourceBody277_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 34)

def sourceBody277_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 70)

def sourceBody277_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody277_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 12)

def sourceBody277_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 48)

def sourceBody277_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 32)

def sourceBody277_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 68)

def sourceBody277_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 56

def sourceBody277_74 : WordLangProgHOL (BitVec 64) :=
.call (some (([46, 30, 66, 20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          Flapjack.Spt.ln))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody277_0, 277, 10)) (some 120) ([56, 38, 74, 4, 40, 24, 60, 14]) (some (56, sourceBody277_73, 277, 11))

def sourceBody277_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_74 sourceBody277_13

def sourceBody277_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_75 sourceBody277_0

def sourceBody277_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_72 sourceBody277_76

def sourceBody277_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_71 sourceBody277_77

def sourceBody277_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_70 sourceBody277_78

def sourceBody277_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_69 sourceBody277_79

def sourceBody277_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_68 sourceBody277_80

def sourceBody277_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_67 sourceBody277_81

def sourceBody277_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_66 sourceBody277_82

def sourceBody277_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_65 sourceBody277_83

def sourceBody277_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 46)

def sourceBody277_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 30)

def sourceBody277_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 66)

def sourceBody277_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 20)

def sourceBody277_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 42)

def sourceBody277_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 26)

def sourceBody277_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 62)

def sourceBody277_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 16)

def sourceBody277_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody277_94 : WordLangProgHOL (BitVec 64) :=
.call (some (([56]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody277_0, 277, 12)) (some 107) ([38, 74, 4, 40, 24, 60, 14, 50]) (some (38, sourceBody277_93, 277, 13))

def sourceBody277_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_94 sourceBody277_13

def sourceBody277_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_95 sourceBody277_0

def sourceBody277_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_92 sourceBody277_96

def sourceBody277_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_91 sourceBody277_97

def sourceBody277_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_90 sourceBody277_98

def sourceBody277_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_89 sourceBody277_99

def sourceBody277_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_88 sourceBody277_100

def sourceBody277_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_87 sourceBody277_101

def sourceBody277_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_86 sourceBody277_102

def sourceBody277_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_85 sourceBody277_103

def sourceBody277_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 56)

def sourceBody277_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody277_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody277_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody277_109 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 74 (Flapjack.WordRegImm.reg 4) sourceBody277_107 sourceBody277_108

def sourceBody277_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_109 sourceBody277_13

def sourceBody277_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 74)

def sourceBody277_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 58)

def sourceBody277_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.const 21#64, Flapjack.WordLangExpHOL.const 14#64])

def sourceBody277_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 40 40 74 4))

def sourceBody277_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 40)

def sourceBody277_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.const 21#64)

def sourceBody277_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 74

def sourceBody277_118 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody277_0, 277, 14)) (some 95) ([24, 60]) (some (74, sourceBody277_117, 277, 15))

def sourceBody277_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_118 sourceBody277_13

def sourceBody277_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_119 sourceBody277_0

def sourceBody277_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_116 sourceBody277_120

def sourceBody277_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_115 sourceBody277_121

def sourceBody277_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_114 sourceBody277_122

def sourceBody277_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_113 sourceBody277_123

def sourceBody277_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_112 sourceBody277_124

def sourceBody277_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.var 38])

def sourceBody277_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [74]

def sourceBody277_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_127 sourceBody277_0

def sourceBody277_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_126 sourceBody277_128

def sourceBody277_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_125 sourceBody277_129

def sourceBody277_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_130

def sourceBody277_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_131

def sourceBody277_133 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.imm 0#64) sourceBody277_132 sourceBody277_0

def sourceBody277_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_133 sourceBody277_13

def sourceBody277_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_134 sourceBody277_0

def sourceBody277_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_111 sourceBody277_135

def sourceBody277_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_110 sourceBody277_136

def sourceBody277_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_106 sourceBody277_137

def sourceBody277_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_105 sourceBody277_138

def sourceBody277_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1835008#64])

def sourceBody277_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [38]

def sourceBody277_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_141 sourceBody277_0

def sourceBody277_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_140 sourceBody277_142

def sourceBody277_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_139 sourceBody277_143

def sourceBody277_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_104 sourceBody277_144

def sourceBody277_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_145

def sourceBody277_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_146

def sourceBody277_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_84 sourceBody277_147

def sourceBody277_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_148

def sourceBody277_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_149

def sourceBody277_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_150

def sourceBody277_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_151

def sourceBody277_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_152

def sourceBody277_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_153

def sourceBody277_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_154

def sourceBody277_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_155

def sourceBody277_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_64 sourceBody277_156

def sourceBody277_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_157

def sourceBody277_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_158

def sourceBody277_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_159

def sourceBody277_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_160

def sourceBody277_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_161

def sourceBody277_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_162

def sourceBody277_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_163

def sourceBody277_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_164

def sourceBody277_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_58 sourceBody277_165

def sourceBody277_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_166

def sourceBody277_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_167

def sourceBody277_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_168

def sourceBody277_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_169

def sourceBody277_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_170

def sourceBody277_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_171

def sourceBody277_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_172

def sourceBody277_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_173

def sourceBody277_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_38 sourceBody277_174

def sourceBody277_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_175

def sourceBody277_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_176

def sourceBody277_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_177

def sourceBody277_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_178

def sourceBody277_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_179

def sourceBody277_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_180

def sourceBody277_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_181

def sourceBody277_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_182

def sourceBody277_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_32 sourceBody277_183

def sourceBody277_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_184

def sourceBody277_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_185

def sourceBody277_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_186

def sourceBody277_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_187

def sourceBody277_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_188

def sourceBody277_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_189

def sourceBody277_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_190

def sourceBody277_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_191

def sourceBody277_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_26 sourceBody277_192

def sourceBody277_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_7 sourceBody277_193

def sourceBody277_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_194

def sourceBody277_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_6 sourceBody277_195

def sourceBody277_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_196

def sourceBody277_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_5 sourceBody277_197

def sourceBody277_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_198

def sourceBody277_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_4 sourceBody277_199

def sourceBody277_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_200

def sourceBody277_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_3 sourceBody277_201

def sourceBody277_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_202

def sourceBody277_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_2 sourceBody277_203

def sourceBody277_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_204

def sourceBody277_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_1 sourceBody277_205

def sourceBody277_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody277_0 sourceBody277_206

def source277 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (277, 2, sourceBody277_207)
end InitECandidate.Proofs.WordStages
