import InitECandidate.Proofs.WordStages.Source847
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody863_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody863_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 416#64]),
        Flapjack.WordLangExpHOL.const 72#64]))

def sourceBody863_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody863_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody863_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody863_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody863_6 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody863_0, 863, 2)) (some 68) ([18]) (some (18, sourceBody863_5, 863, 3))

def sourceBody863_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody863_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_6 sourceBody863_7

def sourceBody863_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_8 sourceBody863_0

def sourceBody863_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_4 sourceBody863_9

def sourceBody863_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody863_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody863_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody863_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody863_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 30)

def sourceBody863_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody863_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody863_18 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 16 (Flapjack.WordRegImm.reg 34) sourceBody863_16 sourceBody863_17

def sourceBody863_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_18 sourceBody863_7

def sourceBody863_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody863_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody863_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody863_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody863_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody863_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 10)

def sourceBody863_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 16)

def sourceBody863_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody863_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody863_29 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 20 (Flapjack.WordRegImm.reg 38) sourceBody863_27 sourceBody863_28

def sourceBody863_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_29 sourceBody863_7

def sourceBody863_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 20)

def sourceBody863_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 34,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 10)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody863_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody863_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 512#64]))

def sourceBody863_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody863_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody863_37 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody863_0, 863, 4)) (some 79) ([38, 2, 22]) (some (38, sourceBody863_36, 863, 5))

def sourceBody863_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_37 sourceBody863_7

def sourceBody863_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_38 sourceBody863_0

def sourceBody863_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_35 sourceBody863_39

def sourceBody863_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_34 sourceBody863_40

def sourceBody863_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_33 sourceBody863_41

def sourceBody863_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody863_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody863_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody863_46 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.WordRegImm.reg 22) sourceBody863_44 sourceBody863_45

def sourceBody863_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_46 sourceBody863_7

def sourceBody863_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody863_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody863_50 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 2 (Flapjack.WordRegImm.reg 22) sourceBody863_44 sourceBody863_45

def sourceBody863_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_50 sourceBody863_7

def sourceBody863_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody863_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 520#64]))

def sourceBody863_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody863_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody863_56 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody863_0, 863, 6)) (some 79) ([2, 22, 14]) (some (2, sourceBody863_55, 863, 7))

def sourceBody863_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_56 sourceBody863_7

def sourceBody863_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_57 sourceBody863_0

def sourceBody863_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_54 sourceBody863_58

def sourceBody863_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_53 sourceBody863_59

def sourceBody863_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_52 sourceBody863_60

def sourceBody863_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 38)

def sourceBody863_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody863_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody863_65 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.reg 14) sourceBody863_64 sourceBody863_43

def sourceBody863_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_65 sourceBody863_7

def sourceBody863_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 22)

def sourceBody863_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 36)

def sourceBody863_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody863_70 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 22 (Flapjack.WordRegImm.reg 14) sourceBody863_64 sourceBody863_43

def sourceBody863_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_70 sourceBody863_7

def sourceBody863_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.const 1024#64])

def sourceBody863_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody863_74 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody863_0, 863, 8)) (some 68) ([22]) (some (22, sourceBody863_73, 863, 9))

def sourceBody863_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_74 sourceBody863_7

def sourceBody863_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_75 sourceBody863_0

def sourceBody863_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_72 sourceBody863_76

def sourceBody863_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 26)

def sourceBody863_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 18)

def sourceBody863_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody863_81 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody863_0, 863, 10)) (some 77) ([14, 32, 8]) (some (14, sourceBody863_80, 863, 11))

def sourceBody863_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_81 sourceBody863_7

def sourceBody863_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_82 sourceBody863_0

def sourceBody863_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_79 sourceBody863_83

def sourceBody863_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_78 sourceBody863_84

def sourceBody863_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_48 sourceBody863_85

def sourceBody863_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_86

def sourceBody863_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_87

def sourceBody863_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 2)

def sourceBody863_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_89 sourceBody863_0

def sourceBody863_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_90 sourceBody863_0

def sourceBody863_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_88 sourceBody863_91

def sourceBody863_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 22)

def sourceBody863_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_93 sourceBody863_0

def sourceBody863_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_94 sourceBody863_0

def sourceBody863_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_72 sourceBody863_95

def sourceBody863_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_96

def sourceBody863_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_92 sourceBody863_97

def sourceBody863_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_77 sourceBody863_98

def sourceBody863_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_99

def sourceBody863_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_100

def sourceBody863_102 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody863_101 sourceBody863_0

def sourceBody863_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_102 sourceBody863_7

def sourceBody863_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_103 sourceBody863_0

def sourceBody863_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_67 sourceBody863_104

def sourceBody863_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_71 sourceBody863_105

def sourceBody863_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_69 sourceBody863_106

def sourceBody863_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_68 sourceBody863_107

def sourceBody863_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody863_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody863_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.var 18])

def sourceBody863_112 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody863_0, 863, 12)) (some 844) ([22, 14, 32]) (some (22, sourceBody863_73, 863, 13))

def sourceBody863_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_112 sourceBody863_7

def sourceBody863_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_113 sourceBody863_0

def sourceBody863_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_111 sourceBody863_114

def sourceBody863_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_110 sourceBody863_115

def sourceBody863_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_109 sourceBody863_116

def sourceBody863_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_117

def sourceBody863_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_118

def sourceBody863_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_108 sourceBody863_119

def sourceBody863_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody863_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody863_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_122 sourceBody863_0

def sourceBody863_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_123 sourceBody863_0

def sourceBody863_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_121 sourceBody863_124

def sourceBody863_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_125

def sourceBody863_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_120 sourceBody863_126

def sourceBody863_128 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody863_127 sourceBody863_0

def sourceBody863_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_128 sourceBody863_7

def sourceBody863_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_129 sourceBody863_0

def sourceBody863_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_67 sourceBody863_130

def sourceBody863_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_66 sourceBody863_131

def sourceBody863_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_63 sourceBody863_132

def sourceBody863_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_62 sourceBody863_133

def sourceBody863_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_61 sourceBody863_134

def sourceBody863_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_135

def sourceBody863_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_136

def sourceBody863_138 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody863_137 sourceBody863_0

def sourceBody863_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_138 sourceBody863_7

def sourceBody863_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_139 sourceBody863_0

def sourceBody863_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_48 sourceBody863_140

def sourceBody863_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_51 sourceBody863_141

def sourceBody863_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_49 sourceBody863_142

def sourceBody863_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_45 sourceBody863_143

def sourceBody863_145 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody863_144 sourceBody863_0

def sourceBody863_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_145 sourceBody863_7

def sourceBody863_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_146 sourceBody863_0

def sourceBody863_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_48 sourceBody863_147

def sourceBody863_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_47 sourceBody863_148

def sourceBody863_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_43 sourceBody863_149

def sourceBody863_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_31 sourceBody863_150

def sourceBody863_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody863_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 38)

def sourceBody863_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_153 sourceBody863_0

def sourceBody863_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_154 sourceBody863_0

def sourceBody863_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_152 sourceBody863_155

def sourceBody863_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_156

def sourceBody863_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_151 sourceBody863_157

def sourceBody863_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_42 sourceBody863_158

def sourceBody863_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_159

def sourceBody863_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_160

def sourceBody863_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_32 sourceBody863_161

def sourceBody863_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_162

def sourceBody863_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody863_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_163 sourceBody863_164

def sourceBody863_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody863_167 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.WordRegImm.imm 0#64) sourceBody863_165 sourceBody863_166

def sourceBody863_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_167 sourceBody863_7

def sourceBody863_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_168 sourceBody863_0

def sourceBody863_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_31 sourceBody863_169

def sourceBody863_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_30 sourceBody863_170

def sourceBody863_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_26 sourceBody863_171

def sourceBody863_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_25 sourceBody863_172

def sourceBody863_174 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody863_173 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody863_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_174 sourceBody863_7

def sourceBody863_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_7 sourceBody863_175

def sourceBody863_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody863_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 28)

def sourceBody863_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_178 sourceBody863_0

def sourceBody863_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_179 sourceBody863_0

def sourceBody863_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_177 sourceBody863_180

def sourceBody863_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_181

def sourceBody863_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_176 sourceBody863_182

def sourceBody863_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_24 sourceBody863_183

def sourceBody863_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_184

def sourceBody863_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_23 sourceBody863_185

def sourceBody863_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_186

def sourceBody863_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_22 sourceBody863_187

def sourceBody863_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_188

def sourceBody863_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_21 sourceBody863_189

def sourceBody863_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_190

def sourceBody863_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_191 sourceBody863_164

def sourceBody863_193 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody863_192 sourceBody863_166

def sourceBody863_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_193 sourceBody863_7

def sourceBody863_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_194 sourceBody863_0

def sourceBody863_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_20 sourceBody863_195

def sourceBody863_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_19 sourceBody863_196

def sourceBody863_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_15 sourceBody863_197

def sourceBody863_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_14 sourceBody863_198

def sourceBody863_200 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln) sourceBody863_199 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
    Flapjack.Spt.ln)
  PUnit.unit Flapjack.Spt.ln)

def sourceBody863_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_200 sourceBody863_7

def sourceBody863_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_7 sourceBody863_201

def sourceBody863_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 18)

def sourceBody863_204 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 16 (Flapjack.WordRegImm.reg 34) sourceBody863_16 sourceBody863_17

def sourceBody863_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_204 sourceBody863_7

def sourceBody863_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 26)

def sourceBody863_207 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody863_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody863_209 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody863_0, 863, 14)) (some 862) ([16, 34, 10]) (some (16, sourceBody863_208, 863, 15))

def sourceBody863_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_209 sourceBody863_7

def sourceBody863_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_210 sourceBody863_0

def sourceBody863_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_207 sourceBody863_211

def sourceBody863_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_206 sourceBody863_212

def sourceBody863_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_17 sourceBody863_213

def sourceBody863_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_214

def sourceBody863_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_215

def sourceBody863_217 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody863_216 sourceBody863_0

def sourceBody863_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_217 sourceBody863_7

def sourceBody863_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_218 sourceBody863_0

def sourceBody863_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_20 sourceBody863_219

def sourceBody863_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_205 sourceBody863_220

def sourceBody863_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_203 sourceBody863_221

def sourceBody863_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_17 sourceBody863_222

def sourceBody863_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_202 sourceBody863_223

def sourceBody863_225 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 480#64]))

def sourceBody863_226 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody863_0, 863, 16)) (some 857) ([16]) (some (16, sourceBody863_208, 863, 17))

def sourceBody863_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_226 sourceBody863_7

def sourceBody863_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_227 sourceBody863_0

def sourceBody863_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_225 sourceBody863_228

def sourceBody863_230 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody863_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody863_232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody863_233 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 34 (Flapjack.WordRegImm.reg 10) sourceBody863_232 sourceBody863_230

def sourceBody863_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_233 sourceBody863_7

def sourceBody863_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 34)

def sourceBody863_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody863_237 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody863_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody863_239 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody863_0, 863, 18)) (some 862) ([34, 10, 28]) (some (34, sourceBody863_238, 863, 19))

def sourceBody863_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_239 sourceBody863_7

def sourceBody863_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_240 sourceBody863_0

def sourceBody863_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_237 sourceBody863_241

def sourceBody863_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_236 sourceBody863_242

def sourceBody863_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_232 sourceBody863_243

def sourceBody863_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_244

def sourceBody863_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_245

def sourceBody863_247 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody863_246 sourceBody863_0

def sourceBody863_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_247 sourceBody863_7

def sourceBody863_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_248 sourceBody863_0

def sourceBody863_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_235 sourceBody863_249

def sourceBody863_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_234 sourceBody863_250

def sourceBody863_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_231 sourceBody863_251

def sourceBody863_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_230 sourceBody863_252

def sourceBody863_254 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 488#64]))

def sourceBody863_255 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody863_0, 863, 20)) (some 857) ([34]) (some (34, sourceBody863_238, 863, 21))

def sourceBody863_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_255 sourceBody863_7

def sourceBody863_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_256 sourceBody863_0

def sourceBody863_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_254 sourceBody863_257

def sourceBody863_259 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody863_260 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody863_261 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 28) sourceBody863_260 sourceBody863_24

def sourceBody863_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_261 sourceBody863_7

def sourceBody863_263 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody863_264 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody863_265 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody863_266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody863_267 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody863_0, 863, 22)) (some 862) ([10, 28, 20]) (some (10, sourceBody863_266, 863, 23))

def sourceBody863_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_267 sourceBody863_7

def sourceBody863_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_268 sourceBody863_0

def sourceBody863_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_265 sourceBody863_269

def sourceBody863_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_264 sourceBody863_270

def sourceBody863_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_263 sourceBody863_271

def sourceBody863_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_272

def sourceBody863_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_273

def sourceBody863_275 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody863_274 sourceBody863_0

def sourceBody863_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_275 sourceBody863_7

def sourceBody863_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_276 sourceBody863_0

def sourceBody863_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_25 sourceBody863_277

def sourceBody863_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_262 sourceBody863_278

def sourceBody863_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_259 sourceBody863_279

def sourceBody863_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_24 sourceBody863_280

def sourceBody863_282 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 496#64]))

def sourceBody863_283 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody863_0, 863, 24)) (some 857) ([10]) (some (10, sourceBody863_266, 863, 25))

def sourceBody863_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_283 sourceBody863_7

def sourceBody863_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_284 sourceBody863_0

def sourceBody863_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_282 sourceBody863_285

def sourceBody863_287 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody863_288 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody863_289 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody863_290 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 28 (Flapjack.WordRegImm.reg 20) sourceBody863_289 sourceBody863_287

def sourceBody863_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_290 sourceBody863_7

def sourceBody863_292 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 28)

def sourceBody863_293 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody863_294 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody863_295 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody863_296 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody863_297 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody863_0, 863, 26)) (some 862) ([28, 20, 38]) (some (28, sourceBody863_296, 863, 27))

def sourceBody863_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_297 sourceBody863_7

def sourceBody863_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_298 sourceBody863_0

def sourceBody863_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_295 sourceBody863_299

def sourceBody863_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_294 sourceBody863_300

def sourceBody863_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_293 sourceBody863_301

def sourceBody863_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_302

def sourceBody863_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_303

def sourceBody863_305 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.imm 0#64) sourceBody863_304 sourceBody863_0

def sourceBody863_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_305 sourceBody863_7

def sourceBody863_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_306 sourceBody863_0

def sourceBody863_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_292 sourceBody863_307

def sourceBody863_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_291 sourceBody863_308

def sourceBody863_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_288 sourceBody863_309

def sourceBody863_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_287 sourceBody863_310

def sourceBody863_312 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 504#64]))

def sourceBody863_313 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody863_0, 863, 28)) (some 857) ([28]) (some (28, sourceBody863_296, 863, 29))

def sourceBody863_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_313 sourceBody863_7

def sourceBody863_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_314 sourceBody863_0

def sourceBody863_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_312 sourceBody863_315

def sourceBody863_317 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody863_318 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 20 (Flapjack.WordRegImm.reg 38) sourceBody863_27 sourceBody863_28

def sourceBody863_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_318 sourceBody863_7

def sourceBody863_320 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody863_321 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody863_322 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody863_323 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody863_324 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody863_0, 863, 30)) (some 862) ([20, 38, 2]) (some (20, sourceBody863_323, 863, 31))

def sourceBody863_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_324 sourceBody863_7

def sourceBody863_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_325 sourceBody863_0

def sourceBody863_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_322 sourceBody863_326

def sourceBody863_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_321 sourceBody863_327

def sourceBody863_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_320 sourceBody863_328

def sourceBody863_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_329

def sourceBody863_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_330

def sourceBody863_332 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.WordRegImm.imm 0#64) sourceBody863_331 sourceBody863_0

def sourceBody863_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_332 sourceBody863_7

def sourceBody863_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_333 sourceBody863_0

def sourceBody863_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_31 sourceBody863_334

def sourceBody863_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_319 sourceBody863_335

def sourceBody863_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_317 sourceBody863_336

def sourceBody863_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_28 sourceBody863_337

def sourceBody863_339 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [28]

def sourceBody863_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_339 sourceBody863_0

def sourceBody863_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_287 sourceBody863_340

def sourceBody863_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_338 sourceBody863_341

def sourceBody863_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_316 sourceBody863_342

def sourceBody863_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_343

def sourceBody863_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_344

def sourceBody863_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_311 sourceBody863_345

def sourceBody863_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_286 sourceBody863_346

def sourceBody863_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_347

def sourceBody863_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_348

def sourceBody863_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_281 sourceBody863_349

def sourceBody863_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_258 sourceBody863_350

def sourceBody863_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_351

def sourceBody863_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_352

def sourceBody863_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_253 sourceBody863_353

def sourceBody863_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_229 sourceBody863_354

def sourceBody863_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_355

def sourceBody863_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_356

def sourceBody863_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_224 sourceBody863_357

def sourceBody863_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_13 sourceBody863_358

def sourceBody863_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_359

def sourceBody863_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_12 sourceBody863_360

def sourceBody863_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_361

def sourceBody863_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_11 sourceBody863_362

def sourceBody863_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_363

def sourceBody863_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_10 sourceBody863_364

def sourceBody863_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_365

def sourceBody863_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_366

def sourceBody863_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_3 sourceBody863_367

def sourceBody863_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_368

def sourceBody863_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_2 sourceBody863_369

def sourceBody863_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_370

def sourceBody863_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_1 sourceBody863_371

def sourceBody863_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody863_0 sourceBody863_372

def source863 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (863, 1, sourceBody863_373)
end InitECandidate.Proofs.WordStages
