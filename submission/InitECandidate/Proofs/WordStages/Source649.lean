import InitECandidate.Proofs.WordStages.Source633
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody649_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody649_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody649_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody649_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody649_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody649_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 22)

def sourceBody649_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 56)

def sourceBody649_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 12)

def sourceBody649_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 48)

def sourceBody649_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 66

def sourceBody649_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody649_0, 649, 2)) (some 102) ([66, 8, 44, 28]) (some (66, sourceBody649_9, 649, 3))

def sourceBody649_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody649_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_10 sourceBody649_11

def sourceBody649_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_12 sourceBody649_0

def sourceBody649_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_8 sourceBody649_13

def sourceBody649_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_7 sourceBody649_14

def sourceBody649_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_6 sourceBody649_15

def sourceBody649_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_5 sourceBody649_16

def sourceBody649_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 32)

def sourceBody649_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody649_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody649_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody649_22 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 8 (Flapjack.WordRegImm.reg 44) sourceBody649_20 sourceBody649_21

def sourceBody649_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_22 sourceBody649_11

def sourceBody649_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 8)

def sourceBody649_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody649_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [66]

def sourceBody649_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_26 sourceBody649_0

def sourceBody649_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_25 sourceBody649_27

def sourceBody649_29 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody649_28 sourceBody649_0

def sourceBody649_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_29 sourceBody649_11

def sourceBody649_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_30 sourceBody649_0

def sourceBody649_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_24 sourceBody649_31

def sourceBody649_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_23 sourceBody649_32

def sourceBody649_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_19 sourceBody649_33

def sourceBody649_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_18 sourceBody649_34

def sourceBody649_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 22)

def sourceBody649_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 56)

def sourceBody649_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 12)

def sourceBody649_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 48)

def sourceBody649_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 62

def sourceBody649_41 : WordLangProgHOL (BitVec 64) :=
.call (some (([66, 8, 44, 28]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody649_0, 649, 4)) (some 643) ([62, 18, 52, 36]) (some (62, sourceBody649_40, 649, 5))

def sourceBody649_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_41 sourceBody649_11

def sourceBody649_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_42 sourceBody649_0

def sourceBody649_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_39 sourceBody649_43

def sourceBody649_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_38 sourceBody649_44

def sourceBody649_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_37 sourceBody649_45

def sourceBody649_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_36 sourceBody649_46

def sourceBody649_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 66)

def sourceBody649_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody649_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 44)

def sourceBody649_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody649_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 70

def sourceBody649_53 : WordLangProgHOL (BitVec 64) :=
.call (some (([62, 18, 52, 36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody649_0, 649, 6)) (some 642) ([70, 6, 42, 26]) (some (70, sourceBody649_52, 649, 7))

def sourceBody649_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_53 sourceBody649_11

def sourceBody649_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_54 sourceBody649_0

def sourceBody649_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_51 sourceBody649_55

def sourceBody649_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_50 sourceBody649_56

def sourceBody649_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_49 sourceBody649_57

def sourceBody649_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_48 sourceBody649_58

def sourceBody649_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 62)

def sourceBody649_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody649_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 52)

def sourceBody649_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 36)

def sourceBody649_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 66)

def sourceBody649_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody649_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 44)

def sourceBody649_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 28)

def sourceBody649_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 60

def sourceBody649_69 : WordLangProgHOL (BitVec 64) :=
.call (some (([70, 6, 42, 26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody649_0, 649, 8)) (some 641) ([60, 16, 50, 34, 68, 10, 46, 30]) (some (60, sourceBody649_68, 649, 9))

def sourceBody649_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_69 sourceBody649_11

def sourceBody649_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_70 sourceBody649_0

def sourceBody649_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_67 sourceBody649_71

def sourceBody649_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_66 sourceBody649_72

def sourceBody649_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_65 sourceBody649_73

def sourceBody649_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_64 sourceBody649_74

def sourceBody649_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_63 sourceBody649_75

def sourceBody649_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_62 sourceBody649_76

def sourceBody649_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_61 sourceBody649_77

def sourceBody649_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_60 sourceBody649_78

def sourceBody649_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 2))

def sourceBody649_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody649_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody649_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody649_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody649_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody649_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody649_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody649_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 60)

def sourceBody649_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody649_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 50)

def sourceBody649_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 34)

def sourceBody649_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 62)

def sourceBody649_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 18)

def sourceBody649_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 52)

def sourceBody649_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 36)

def sourceBody649_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 64

def sourceBody649_97 : WordLangProgHOL (BitVec 64) :=
.call (some (([60, 16, 50, 34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody649_0, 649, 10)) (some 641) ([64, 20, 54, 38, 72, 4, 40, 24]) (some (64, sourceBody649_96, 649, 11))

def sourceBody649_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_97 sourceBody649_11

def sourceBody649_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_98 sourceBody649_0

def sourceBody649_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_95 sourceBody649_99

def sourceBody649_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_94 sourceBody649_100

def sourceBody649_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_93 sourceBody649_101

def sourceBody649_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_92 sourceBody649_102

def sourceBody649_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_91 sourceBody649_103

def sourceBody649_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_90 sourceBody649_104

def sourceBody649_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_89 sourceBody649_105

def sourceBody649_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_88 sourceBody649_106

def sourceBody649_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 68)

def sourceBody649_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 10)

def sourceBody649_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 46)

def sourceBody649_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 30)

def sourceBody649_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 70)

def sourceBody649_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody649_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 42)

def sourceBody649_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody649_116 : WordLangProgHOL (BitVec 64) :=
.call (some (([68, 10, 46, 30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody649_0, 649, 12)) (some 641) ([64, 20, 54, 38, 72, 4, 40, 24]) (some (64, sourceBody649_96, 649, 13))

def sourceBody649_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_116 sourceBody649_11

def sourceBody649_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_117 sourceBody649_0

def sourceBody649_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_115 sourceBody649_118

def sourceBody649_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_114 sourceBody649_119

def sourceBody649_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_113 sourceBody649_120

def sourceBody649_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_112 sourceBody649_121

def sourceBody649_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_111 sourceBody649_122

def sourceBody649_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_110 sourceBody649_123

def sourceBody649_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_109 sourceBody649_124

def sourceBody649_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_108 sourceBody649_125

def sourceBody649_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_107 sourceBody649_126

def sourceBody649_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody649_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 60)

def sourceBody649_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 16)

def sourceBody649_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 50)

def sourceBody649_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 34)

def sourceBody649_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 68)

def sourceBody649_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody649_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 46)

def sourceBody649_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 30)

def sourceBody649_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody649_138 : WordLangProgHOL (BitVec 64) :=
.call (some (([64]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody649_0, 649, 14)) (some 645) ([20, 54, 38, 72, 4, 40, 24, 58, 14]) (some (20, sourceBody649_137, 649, 15))

def sourceBody649_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_138 sourceBody649_11

def sourceBody649_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_139 sourceBody649_0

def sourceBody649_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_136 sourceBody649_140

def sourceBody649_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_135 sourceBody649_141

def sourceBody649_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_134 sourceBody649_142

def sourceBody649_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_133 sourceBody649_143

def sourceBody649_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_132 sourceBody649_144

def sourceBody649_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_131 sourceBody649_145

def sourceBody649_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_130 sourceBody649_146

def sourceBody649_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_129 sourceBody649_147

def sourceBody649_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_128 sourceBody649_148

def sourceBody649_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_149

def sourceBody649_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_150

def sourceBody649_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_127 sourceBody649_151

def sourceBody649_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody649_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [64]

def sourceBody649_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_154 sourceBody649_0

def sourceBody649_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_153 sourceBody649_155

def sourceBody649_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_152 sourceBody649_156

def sourceBody649_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_87 sourceBody649_157

def sourceBody649_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_158

def sourceBody649_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_86 sourceBody649_159

def sourceBody649_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_160

def sourceBody649_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_85 sourceBody649_161

def sourceBody649_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_162

def sourceBody649_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_84 sourceBody649_163

def sourceBody649_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_164

def sourceBody649_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_83 sourceBody649_165

def sourceBody649_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_166

def sourceBody649_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_82 sourceBody649_167

def sourceBody649_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_168

def sourceBody649_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_81 sourceBody649_169

def sourceBody649_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_170

def sourceBody649_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_80 sourceBody649_171

def sourceBody649_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_172

def sourceBody649_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_79 sourceBody649_173

def sourceBody649_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_174

def sourceBody649_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_175

def sourceBody649_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_176

def sourceBody649_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_177

def sourceBody649_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_178

def sourceBody649_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_179

def sourceBody649_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_180

def sourceBody649_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_181

def sourceBody649_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_59 sourceBody649_182

def sourceBody649_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_183

def sourceBody649_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_184

def sourceBody649_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_185

def sourceBody649_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_186

def sourceBody649_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_187

def sourceBody649_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_188

def sourceBody649_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_189

def sourceBody649_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_190

def sourceBody649_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_47 sourceBody649_191

def sourceBody649_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_192

def sourceBody649_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_193

def sourceBody649_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_194

def sourceBody649_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_195

def sourceBody649_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_196

def sourceBody649_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_197

def sourceBody649_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_198

def sourceBody649_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_199

def sourceBody649_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_35 sourceBody649_200

def sourceBody649_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_17 sourceBody649_201

def sourceBody649_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_202

def sourceBody649_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_203

def sourceBody649_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_4 sourceBody649_204

def sourceBody649_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_205

def sourceBody649_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_3 sourceBody649_206

def sourceBody649_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_207

def sourceBody649_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_2 sourceBody649_208

def sourceBody649_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_209

def sourceBody649_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_1 sourceBody649_210

def sourceBody649_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody649_0 sourceBody649_211

def source649 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (649, 2, sourceBody649_212)
end InitECandidate.Proofs.WordStages
