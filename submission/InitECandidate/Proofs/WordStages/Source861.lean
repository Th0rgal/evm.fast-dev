import InitECandidate.Proofs.WordStages.Source845
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody861_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody861_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 50

def sourceBody861_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody861_0, 861, 2)) (some 383) ([]) (some (50, sourceBody861_1, 861, 3))

def sourceBody861_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody861_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_2 sourceBody861_3

def sourceBody861_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_4 sourceBody861_0

def sourceBody861_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_5

def sourceBody861_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_6

def sourceBody861_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody861_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody861_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody861_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 12)

def sourceBody861_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 20)

def sourceBody861_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody861_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody861_15 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 28 (Flapjack.WordRegImm.reg 58) sourceBody861_13 sourceBody861_14

def sourceBody861_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_15 sourceBody861_3

def sourceBody861_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody861_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 12)

def sourceBody861_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 44#64)

def sourceBody861_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 58 58 42 28))

def sourceBody861_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_20 sourceBody861_0

def sourceBody861_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_19 sourceBody861_21

def sourceBody861_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_18 sourceBody861_22

def sourceBody861_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.var 58])

def sourceBody861_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 36#64])

def sourceBody861_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 38 (Flapjack.WordLangAddr.addr 38 0#64))

def sourceBody861_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody861_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 24 (Flapjack.WordLangAddr.addr 24 0#64))

def sourceBody861_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody861_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 54 (Flapjack.WordLangAddr.addr 54 0#64))

def sourceBody861_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody861_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 16 (Flapjack.WordLangAddr.addr 16 0#64))

def sourceBody861_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 4#64])

def sourceBody861_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 46 (Flapjack.WordLangAddr.addr 46 0#64))

def sourceBody861_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody861_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 32 (Flapjack.WordLangAddr.addr 32 0#64))

def sourceBody861_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 2#64])

def sourceBody861_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 62 (Flapjack.WordLangAddr.addr 62 0#64))

def sourceBody861_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 3#64])

def sourceBody861_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 6 (Flapjack.WordLangAddr.addr 6 0#64))

def sourceBody861_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_40 sourceBody861_0

def sourceBody861_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_39 sourceBody861_41

def sourceBody861_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_38 sourceBody861_42

def sourceBody861_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_37 sourceBody861_43

def sourceBody861_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_36 sourceBody861_44

def sourceBody861_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_35 sourceBody861_45

def sourceBody861_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_34 sourceBody861_46

def sourceBody861_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_33 sourceBody861_47

def sourceBody861_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_32 sourceBody861_48

def sourceBody861_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_31 sourceBody861_49

def sourceBody861_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_30 sourceBody861_50

def sourceBody861_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_29 sourceBody861_51

def sourceBody861_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_28 sourceBody861_52

def sourceBody861_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_27 sourceBody861_53

def sourceBody861_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_26 sourceBody861_54

def sourceBody861_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_25 sourceBody861_55

def sourceBody861_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 38,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 54)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
        (Flapjack.WordLangExpHOL.const 24#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
          [Flapjack.WordLangExpHOL.var 46,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 32)
              (Flapjack.WordLangExpHOL.const 8#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 62)
              (Flapjack.WordLangExpHOL.const 16#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 6)
              (Flapjack.WordLangExpHOL.const 24#64)])
        (Flapjack.WordLangExpHOL.const 32#64)])

def sourceBody861_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody861_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody861_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody861_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 36)

def sourceBody861_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 22)

def sourceBody861_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 52)

def sourceBody861_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody861_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 1000000000#64)

def sourceBody861_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody861_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody861_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody861_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody861_70 : WordLangProgHOL (BitVec 64) :=
.call (some (([44, 30, 60, 10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody861_0, 861, 4)) (some 120) ([40, 26, 56, 18, 48, 34, 64, 4]) (some (40, sourceBody861_69, 861, 5))

def sourceBody861_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_70 sourceBody861_3

def sourceBody861_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_71 sourceBody861_0

def sourceBody861_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_68 sourceBody861_72

def sourceBody861_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_67 sourceBody861_73

def sourceBody861_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_66 sourceBody861_74

def sourceBody861_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_65 sourceBody861_75

def sourceBody861_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_64 sourceBody861_76

def sourceBody861_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_63 sourceBody861_77

def sourceBody861_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_62 sourceBody861_78

def sourceBody861_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_61 sourceBody861_79

def sourceBody861_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody861_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 44)

def sourceBody861_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 30)

def sourceBody861_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 60)

def sourceBody861_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 10)

def sourceBody861_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody861_87 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody861_0, 861, 6)) (some 424) ([26, 56, 18, 48, 34]) (some (26, sourceBody861_86, 861, 7))

def sourceBody861_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_87 sourceBody861_3

def sourceBody861_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_88 sourceBody861_0

def sourceBody861_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_85 sourceBody861_89

def sourceBody861_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_84 sourceBody861_90

def sourceBody861_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_83 sourceBody861_91

def sourceBody861_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_82 sourceBody861_92

def sourceBody861_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_81 sourceBody861_93

def sourceBody861_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_94

def sourceBody861_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_95

def sourceBody861_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody861_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody861_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 26)

def sourceBody861_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 40) 56

def sourceBody861_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_100 sourceBody861_0

def sourceBody861_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_99 sourceBody861_101

def sourceBody861_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_102 sourceBody861_0

def sourceBody861_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_98 sourceBody861_103

def sourceBody861_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_104

def sourceBody861_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_97 sourceBody861_105

def sourceBody861_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_106

def sourceBody861_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_96 sourceBody861_107

def sourceBody861_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody861_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 40)

def sourceBody861_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_110 sourceBody861_0

def sourceBody861_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_111 sourceBody861_0

def sourceBody861_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_109 sourceBody861_112

def sourceBody861_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_113

def sourceBody861_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_108 sourceBody861_114

def sourceBody861_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_80 sourceBody861_115

def sourceBody861_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_116

def sourceBody861_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_117

def sourceBody861_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_118

def sourceBody861_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_119

def sourceBody861_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_120

def sourceBody861_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_121

def sourceBody861_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_122

def sourceBody861_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_123

def sourceBody861_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_60 sourceBody861_124

def sourceBody861_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_125

def sourceBody861_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_59 sourceBody861_126

def sourceBody861_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_127

def sourceBody861_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_58 sourceBody861_128

def sourceBody861_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_129

def sourceBody861_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_57 sourceBody861_130

def sourceBody861_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_56 sourceBody861_131

def sourceBody861_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_24 sourceBody861_132

def sourceBody861_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_23 sourceBody861_133

def sourceBody861_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody861_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_134 sourceBody861_135

def sourceBody861_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody861_138 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody861_136 sourceBody861_137

def sourceBody861_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_138 sourceBody861_3

def sourceBody861_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_139 sourceBody861_0

def sourceBody861_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_17 sourceBody861_140

def sourceBody861_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_16 sourceBody861_141

def sourceBody861_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_12 sourceBody861_142

def sourceBody861_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_11 sourceBody861_143

def sourceBody861_145 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln) sourceBody861_144 (Flapjack.Spt.ls PUnit.unit)

def sourceBody861_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_145 sourceBody861_3

def sourceBody861_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_3 sourceBody861_146

def sourceBody861_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody861_149 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody861_0, 861, 8)) (some 451) ([]) (some (28, sourceBody861_148, 861, 9))

def sourceBody861_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_149 sourceBody861_3

def sourceBody861_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_150 sourceBody861_0

def sourceBody861_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_151

def sourceBody861_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_152

def sourceBody861_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_147 sourceBody861_153

def sourceBody861_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody861_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [42]

def sourceBody861_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_156 sourceBody861_0

def sourceBody861_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_155 sourceBody861_157

def sourceBody861_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_154 sourceBody861_158

def sourceBody861_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_10 sourceBody861_159

def sourceBody861_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_160

def sourceBody861_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_9 sourceBody861_161

def sourceBody861_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_162

def sourceBody861_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_8 sourceBody861_163

def sourceBody861_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_0 sourceBody861_164

def sourceBody861_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody861_7 sourceBody861_165

def source861 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (861, 2, sourceBody861_166)
end InitECandidate.Proofs.WordStages
