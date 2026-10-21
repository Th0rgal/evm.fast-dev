import InitECandidate.Proofs.WordStages.Source755
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody771_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody771_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody771_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 4)

def sourceBody771_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody771_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody771_0, 771, 2)) (some 723) ([12, 40]) (some (12, sourceBody771_3, 771, 3))

def sourceBody771_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody771_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_4 sourceBody771_5

def sourceBody771_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_6 sourceBody771_0

def sourceBody771_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_2 sourceBody771_7

def sourceBody771_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_1 sourceBody771_8

def sourceBody771_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 48)

def sourceBody771_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody771_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody771_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody771_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 40 (Flapjack.WordRegImm.reg 26) sourceBody771_12 sourceBody771_13

def sourceBody771_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_14 sourceBody771_5

def sourceBody771_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 40)

def sourceBody771_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody771_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody771_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_18 sourceBody771_0

def sourceBody771_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_17 sourceBody771_19

def sourceBody771_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 56 (Flapjack.WordRegImm.imm 0#64) sourceBody771_20 sourceBody771_0

def sourceBody771_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_21 sourceBody771_5

def sourceBody771_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_22 sourceBody771_0

def sourceBody771_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_16 sourceBody771_23

def sourceBody771_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_15 sourceBody771_24

def sourceBody771_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_11 sourceBody771_25

def sourceBody771_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_10 sourceBody771_26

def sourceBody771_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody771_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody771_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody771_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody771_0, 771, 4)) (some 723) ([40, 26]) (some (40, sourceBody771_30, 771, 5))

def sourceBody771_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_31 sourceBody771_5

def sourceBody771_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_32 sourceBody771_0

def sourceBody771_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_29 sourceBody771_33

def sourceBody771_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_28 sourceBody771_34

def sourceBody771_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 12)

def sourceBody771_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody771_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody771_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 26 (Flapjack.WordRegImm.reg 56) sourceBody771_38 sourceBody771_11

def sourceBody771_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_39 sourceBody771_5

def sourceBody771_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 26)

def sourceBody771_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [40]

def sourceBody771_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_42 sourceBody771_0

def sourceBody771_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_13 sourceBody771_43

def sourceBody771_45 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody771_44 sourceBody771_0

def sourceBody771_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_45 sourceBody771_5

def sourceBody771_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_46 sourceBody771_0

def sourceBody771_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_41 sourceBody771_47

def sourceBody771_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_40 sourceBody771_48

def sourceBody771_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_37 sourceBody771_49

def sourceBody771_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_36 sourceBody771_50

def sourceBody771_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 4))

def sourceBody771_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody771_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody771_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody771_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody771_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody771_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody771_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody771_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody771_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody771_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody771_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody771_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 40)

def sourceBody771_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 26)

def sourceBody771_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 56)

def sourceBody771_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 8)

def sourceBody771_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 36)

def sourceBody771_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 22)

def sourceBody771_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody771_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody771_0, 771, 6)) (some 701) ([20, 50, 14, 42, 28, 58]) (some (20, sourceBody771_70, 771, 7))

def sourceBody771_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_71 sourceBody771_5

def sourceBody771_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_72 sourceBody771_0

def sourceBody771_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_69 sourceBody771_73

def sourceBody771_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_68 sourceBody771_74

def sourceBody771_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_67 sourceBody771_75

def sourceBody771_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_66 sourceBody771_76

def sourceBody771_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_65 sourceBody771_77

def sourceBody771_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_64 sourceBody771_78

def sourceBody771_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 52)

def sourceBody771_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody771_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 44)

def sourceBody771_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 30)

def sourceBody771_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 60)

def sourceBody771_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody771_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 50

def sourceBody771_87 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody771_0, 771, 8)) (some 701) ([50, 14, 42, 28, 58, 10]) (some (50, sourceBody771_86, 771, 9))

def sourceBody771_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_87 sourceBody771_5

def sourceBody771_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_88 sourceBody771_0

def sourceBody771_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_85 sourceBody771_89

def sourceBody771_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_84 sourceBody771_90

def sourceBody771_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_83 sourceBody771_91

def sourceBody771_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_82 sourceBody771_92

def sourceBody771_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_81 sourceBody771_93

def sourceBody771_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_80 sourceBody771_94

def sourceBody771_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 34)

def sourceBody771_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody771_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody771_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody771_100 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 42) sourceBody771_98 sourceBody771_99

def sourceBody771_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_100 sourceBody771_5

def sourceBody771_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody771_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody771_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody771_105 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 58 (Flapjack.WordRegImm.reg 10) sourceBody771_104 sourceBody771_102

def sourceBody771_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_105 sourceBody771_5

def sourceBody771_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 20)

def sourceBody771_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody771_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody771_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody771_111 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 54) sourceBody771_109 sourceBody771_110

def sourceBody771_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_111 sourceBody771_5

def sourceBody771_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody771_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 24)

def sourceBody771_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody771_116 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 46 (Flapjack.WordRegImm.reg 32) sourceBody771_115 sourceBody771_113

def sourceBody771_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_116 sourceBody771_5

def sourceBody771_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 58, Flapjack.WordLangExpHOL.var 46])

def sourceBody771_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody771_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody771_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody771_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody771_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody771_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody771_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 50) 24

def sourceBody771_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_125 sourceBody771_0

def sourceBody771_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_124 sourceBody771_126

def sourceBody771_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 42)

def sourceBody771_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 8#64])
  24

def sourceBody771_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_129 sourceBody771_0

def sourceBody771_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_128 sourceBody771_130

def sourceBody771_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 28)

def sourceBody771_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 16#64])
  24

def sourceBody771_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_133 sourceBody771_0

def sourceBody771_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_132 sourceBody771_134

def sourceBody771_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 58)

def sourceBody771_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 24#64])
  24

def sourceBody771_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_137 sourceBody771_0

def sourceBody771_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_136 sourceBody771_138

def sourceBody771_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody771_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 32#64])
  24

def sourceBody771_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_141 sourceBody771_0

def sourceBody771_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_140 sourceBody771_142

def sourceBody771_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 38)

def sourceBody771_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 40#64])
  24

def sourceBody771_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_145 sourceBody771_0

def sourceBody771_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_144 sourceBody771_146

def sourceBody771_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_147 sourceBody771_0

def sourceBody771_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_143 sourceBody771_148

def sourceBody771_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_139 sourceBody771_149

def sourceBody771_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_135 sourceBody771_150

def sourceBody771_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_131 sourceBody771_151

def sourceBody771_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_127 sourceBody771_152

def sourceBody771_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_123 sourceBody771_153

def sourceBody771_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_154

def sourceBody771_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_122 sourceBody771_155

def sourceBody771_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_156

def sourceBody771_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_102 sourceBody771_157

def sourceBody771_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_158

def sourceBody771_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_121 sourceBody771_159

def sourceBody771_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_160

def sourceBody771_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_120 sourceBody771_161

def sourceBody771_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_162

def sourceBody771_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_99 sourceBody771_163

def sourceBody771_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_164

def sourceBody771_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_119 sourceBody771_165

def sourceBody771_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_166

def sourceBody771_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody771_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [50]

def sourceBody771_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_169 sourceBody771_0

def sourceBody771_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_168 sourceBody771_170

def sourceBody771_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_167 sourceBody771_171

def sourceBody771_173 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 62 (Flapjack.WordRegImm.imm 0#64) sourceBody771_172 sourceBody771_0

def sourceBody771_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_173 sourceBody771_5

def sourceBody771_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_174 sourceBody771_0

def sourceBody771_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_118 sourceBody771_175

def sourceBody771_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_117 sourceBody771_176

def sourceBody771_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_114 sourceBody771_177

def sourceBody771_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_113 sourceBody771_178

def sourceBody771_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_112 sourceBody771_179

def sourceBody771_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_108 sourceBody771_180

def sourceBody771_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_107 sourceBody771_181

def sourceBody771_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_106 sourceBody771_182

def sourceBody771_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_103 sourceBody771_183

def sourceBody771_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_102 sourceBody771_184

def sourceBody771_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_101 sourceBody771_185

def sourceBody771_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_97 sourceBody771_186

def sourceBody771_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_96 sourceBody771_187

def sourceBody771_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 8505329371266088957#64)

def sourceBody771_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 17002214543764226050#64)

def sourceBody771_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 6865905132761471162#64)

def sourceBody771_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 8632934651105793861#64)

def sourceBody771_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 6631298214892334189#64)

def sourceBody771_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1582556514881692819#64)

def sourceBody771_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_194 sourceBody771_153

def sourceBody771_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_195

def sourceBody771_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_193 sourceBody771_196

def sourceBody771_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_197

def sourceBody771_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_192 sourceBody771_198

def sourceBody771_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_199

def sourceBody771_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_191 sourceBody771_200

def sourceBody771_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_201

def sourceBody771_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_190 sourceBody771_202

def sourceBody771_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_203

def sourceBody771_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_189 sourceBody771_204

def sourceBody771_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_205

def sourceBody771_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_119 sourceBody771_206

def sourceBody771_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_207

def sourceBody771_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_188 sourceBody771_208

def sourceBody771_210 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 40)

def sourceBody771_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 26)

def sourceBody771_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 56)

def sourceBody771_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 8)

def sourceBody771_214 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 36)

def sourceBody771_215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 22)

def sourceBody771_216 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 52)

def sourceBody771_217 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody771_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 44)

def sourceBody771_219 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 30)

def sourceBody771_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 60)

def sourceBody771_221 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 6)

def sourceBody771_222 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 770) ([0, 50, 14, 42, 28, 58, 10, 38, 24, 54, 18, 46, 32]) (none)

def sourceBody771_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_222 sourceBody771_0

def sourceBody771_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_221 sourceBody771_223

def sourceBody771_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_220 sourceBody771_224

def sourceBody771_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_219 sourceBody771_225

def sourceBody771_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_218 sourceBody771_226

def sourceBody771_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_217 sourceBody771_227

def sourceBody771_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_216 sourceBody771_228

def sourceBody771_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_215 sourceBody771_229

def sourceBody771_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_214 sourceBody771_230

def sourceBody771_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_213 sourceBody771_231

def sourceBody771_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_212 sourceBody771_232

def sourceBody771_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_211 sourceBody771_233

def sourceBody771_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_210 sourceBody771_234

def sourceBody771_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_209 sourceBody771_235

def sourceBody771_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_95 sourceBody771_236

def sourceBody771_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_237

def sourceBody771_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_238

def sourceBody771_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_79 sourceBody771_239

def sourceBody771_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_240

def sourceBody771_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_241

def sourceBody771_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_63 sourceBody771_242

def sourceBody771_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_243

def sourceBody771_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_62 sourceBody771_244

def sourceBody771_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_245

def sourceBody771_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_61 sourceBody771_246

def sourceBody771_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_247

def sourceBody771_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_60 sourceBody771_248

def sourceBody771_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_249

def sourceBody771_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_59 sourceBody771_250

def sourceBody771_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_251

def sourceBody771_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_58 sourceBody771_252

def sourceBody771_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_253

def sourceBody771_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_57 sourceBody771_254

def sourceBody771_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_255

def sourceBody771_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_56 sourceBody771_256

def sourceBody771_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_257

def sourceBody771_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_55 sourceBody771_258

def sourceBody771_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_259

def sourceBody771_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_54 sourceBody771_260

def sourceBody771_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_261

def sourceBody771_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_53 sourceBody771_262

def sourceBody771_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_263

def sourceBody771_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_52 sourceBody771_264

def sourceBody771_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_265

def sourceBody771_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_51 sourceBody771_266

def sourceBody771_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_35 sourceBody771_267

def sourceBody771_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_268

def sourceBody771_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_269

def sourceBody771_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_27 sourceBody771_270

def sourceBody771_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_9 sourceBody771_271

def sourceBody771_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_272

def sourceBody771_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody771_0 sourceBody771_273

def source771 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (771, 3, sourceBody771_274)
end InitECandidate.Proofs.WordStages
