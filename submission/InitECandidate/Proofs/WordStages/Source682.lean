import InitECandidate.Proofs.WordStages.Source666
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody682_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody682_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody682_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1152#64)

def sourceBody682_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody682_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody682_0, 682, 2)) (some 78) ([12, 40]) (some (12, sourceBody682_3, 682, 3))

def sourceBody682_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody682_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_4 sourceBody682_5

def sourceBody682_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_6 sourceBody682_0

def sourceBody682_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_2 sourceBody682_7

def sourceBody682_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_1 sourceBody682_8

def sourceBody682_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_9

def sourceBody682_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_10

def sourceBody682_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody682_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 48)

def sourceBody682_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody682_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody682_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody682_17 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 40 (Flapjack.WordRegImm.reg 26) sourceBody682_15 sourceBody682_16

def sourceBody682_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_17 sourceBody682_5

def sourceBody682_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 40)

def sourceBody682_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 48)
          (Flapjack.WordLangExpHOL.const 6#64)]))

def sourceBody682_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 48)
              (Flapjack.WordLangExpHOL.const 6#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody682_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 48)
              (Flapjack.WordLangExpHOL.const 6#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody682_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 48)
              (Flapjack.WordLangExpHOL.const 6#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody682_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 48)
          (Flapjack.WordLangExpHOL.const 6#64),
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody682_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 48)
              (Flapjack.WordLangExpHOL.const 6#64),
            Flapjack.WordLangExpHOL.const 32#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody682_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 48)
              (Flapjack.WordLangExpHOL.const 6#64),
            Flapjack.WordLangExpHOL.const 32#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody682_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 48)
              (Flapjack.WordLangExpHOL.const 6#64),
            Flapjack.WordLangExpHOL.const 32#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody682_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody682_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 36)

def sourceBody682_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 22)

def sourceBody682_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 52)

def sourceBody682_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 9#64)

def sourceBody682_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody682_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 44, 30, 60]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody682_0, 682, 4)) (some 661) ([6, 34, 20, 50, 14]) (some (6, sourceBody682_33, 682, 5))

def sourceBody682_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_34 sourceBody682_5

def sourceBody682_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_35 sourceBody682_0

def sourceBody682_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_32 sourceBody682_36

def sourceBody682_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_31 sourceBody682_37

def sourceBody682_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_30 sourceBody682_38

def sourceBody682_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_29 sourceBody682_39

def sourceBody682_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_28 sourceBody682_40

def sourceBody682_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody682_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 40)

def sourceBody682_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 26)

def sourceBody682_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 56)

def sourceBody682_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody682_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 44)

def sourceBody682_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 30)

def sourceBody682_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 60)

def sourceBody682_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody682_51 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 34, 20, 50]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody682_0, 682, 6)) (some 655) ([14, 42, 28, 58, 10, 38, 24, 54]) (some (14, sourceBody682_50, 682, 7))

def sourceBody682_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_51 sourceBody682_5

def sourceBody682_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_52 sourceBody682_0

def sourceBody682_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_49 sourceBody682_53

def sourceBody682_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_48 sourceBody682_54

def sourceBody682_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_47 sourceBody682_55

def sourceBody682_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_46 sourceBody682_56

def sourceBody682_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_45 sourceBody682_57

def sourceBody682_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_44 sourceBody682_58

def sourceBody682_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_43 sourceBody682_59

def sourceBody682_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_42 sourceBody682_60

def sourceBody682_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody682_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 48)

def sourceBody682_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody682_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody682_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody682_67 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 28 (Flapjack.WordRegImm.reg 58) sourceBody682_65 sourceBody682_66

def sourceBody682_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_67 sourceBody682_5

def sourceBody682_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 28)

def sourceBody682_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody682_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_70 sourceBody682_0

def sourceBody682_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_71 sourceBody682_0

def sourceBody682_73 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody682_72 sourceBody682_0

def sourceBody682_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_73 sourceBody682_5

def sourceBody682_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_74 sourceBody682_0

def sourceBody682_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_69 sourceBody682_75

def sourceBody682_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_68 sourceBody682_76

def sourceBody682_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_64 sourceBody682_77

def sourceBody682_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_63 sourceBody682_78

def sourceBody682_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody682_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody682_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_81 sourceBody682_0

def sourceBody682_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_82 sourceBody682_0

def sourceBody682_84 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody682_83 sourceBody682_0

def sourceBody682_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_84 sourceBody682_5

def sourceBody682_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_85 sourceBody682_0

def sourceBody682_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_69 sourceBody682_86

def sourceBody682_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_68 sourceBody682_87

def sourceBody682_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_80 sourceBody682_88

def sourceBody682_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_63 sourceBody682_89

def sourceBody682_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_79 sourceBody682_90

def sourceBody682_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 48)

def sourceBody682_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 384#64)

def sourceBody682_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 58 58 42 28))

def sourceBody682_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_94 sourceBody682_0

def sourceBody682_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_93 sourceBody682_95

def sourceBody682_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_92 sourceBody682_96

def sourceBody682_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 58])

def sourceBody682_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody682_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 6)

def sourceBody682_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 34)

def sourceBody682_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody682_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 50)

def sourceBody682_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 24)

def sourceBody682_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 38) 32

def sourceBody682_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_105 sourceBody682_0

def sourceBody682_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_104 sourceBody682_106

def sourceBody682_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 54)

def sourceBody682_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 8#64])
  32

def sourceBody682_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_109 sourceBody682_0

def sourceBody682_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_108 sourceBody682_110

def sourceBody682_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 18)

def sourceBody682_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 16#64])
  32

def sourceBody682_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_113 sourceBody682_0

def sourceBody682_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_112 sourceBody682_114

def sourceBody682_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 46)

def sourceBody682_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 24#64])
  32

def sourceBody682_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_117 sourceBody682_0

def sourceBody682_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_116 sourceBody682_118

def sourceBody682_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_119 sourceBody682_0

def sourceBody682_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_115 sourceBody682_120

def sourceBody682_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_111 sourceBody682_121

def sourceBody682_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_107 sourceBody682_122

def sourceBody682_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_103 sourceBody682_123

def sourceBody682_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_124

def sourceBody682_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_102 sourceBody682_125

def sourceBody682_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_126

def sourceBody682_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_101 sourceBody682_127

def sourceBody682_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_128

def sourceBody682_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_100 sourceBody682_129

def sourceBody682_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_130

def sourceBody682_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_99 sourceBody682_131

def sourceBody682_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_132

def sourceBody682_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 6#64])
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody682_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody682_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 36)

def sourceBody682_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 22)

def sourceBody682_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 52)

def sourceBody682_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_138 sourceBody682_123

def sourceBody682_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_139

def sourceBody682_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_137 sourceBody682_140

def sourceBody682_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_141

def sourceBody682_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_136 sourceBody682_142

def sourceBody682_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_143

def sourceBody682_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_135 sourceBody682_144

def sourceBody682_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_145

def sourceBody682_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_134 sourceBody682_146

def sourceBody682_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_147

def sourceBody682_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_133 sourceBody682_148

def sourceBody682_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody682_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 38)

def sourceBody682_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_151 sourceBody682_0

def sourceBody682_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_152 sourceBody682_0

def sourceBody682_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_150 sourceBody682_153

def sourceBody682_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_154

def sourceBody682_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_149 sourceBody682_155

def sourceBody682_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_98 sourceBody682_156

def sourceBody682_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_97 sourceBody682_157

def sourceBody682_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_91 sourceBody682_158

def sourceBody682_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_62 sourceBody682_159

def sourceBody682_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_160

def sourceBody682_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_61 sourceBody682_161

def sourceBody682_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_162

def sourceBody682_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_163

def sourceBody682_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_164

def sourceBody682_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_165

def sourceBody682_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_166

def sourceBody682_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_167

def sourceBody682_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_168

def sourceBody682_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_169

def sourceBody682_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_41 sourceBody682_170

def sourceBody682_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_171

def sourceBody682_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_172

def sourceBody682_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_173

def sourceBody682_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_174

def sourceBody682_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_175

def sourceBody682_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_176

def sourceBody682_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_177

def sourceBody682_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_178

def sourceBody682_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_27 sourceBody682_179

def sourceBody682_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_180

def sourceBody682_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_26 sourceBody682_181

def sourceBody682_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_182

def sourceBody682_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_25 sourceBody682_183

def sourceBody682_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_184

def sourceBody682_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_24 sourceBody682_185

def sourceBody682_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_186

def sourceBody682_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_23 sourceBody682_187

def sourceBody682_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_188

def sourceBody682_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_22 sourceBody682_189

def sourceBody682_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_190

def sourceBody682_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_21 sourceBody682_191

def sourceBody682_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_192

def sourceBody682_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_20 sourceBody682_193

def sourceBody682_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_194

def sourceBody682_196 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody682_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_195 sourceBody682_196

def sourceBody682_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody682_199 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 56 (Flapjack.WordRegImm.imm 0#64) sourceBody682_197 sourceBody682_198

def sourceBody682_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_199 sourceBody682_5

def sourceBody682_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_200 sourceBody682_0

def sourceBody682_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_19 sourceBody682_201

def sourceBody682_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_18 sourceBody682_202

def sourceBody682_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_14 sourceBody682_203

def sourceBody682_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_13 sourceBody682_204

def sourceBody682_206 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
  PUnit.unit Flapjack.Spt.ln) sourceBody682_205 (Flapjack.Spt.ls PUnit.unit)

def sourceBody682_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_206 sourceBody682_5

def sourceBody682_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_5 sourceBody682_207

def sourceBody682_209 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody682_210 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody682_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_210 sourceBody682_0

def sourceBody682_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_209 sourceBody682_211

def sourceBody682_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_208 sourceBody682_212

def sourceBody682_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_12 sourceBody682_213

def sourceBody682_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_0 sourceBody682_214

def sourceBody682_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody682_11 sourceBody682_215

def source682 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (682, 3, sourceBody682_216)
end InitECandidate.Proofs.WordStages
