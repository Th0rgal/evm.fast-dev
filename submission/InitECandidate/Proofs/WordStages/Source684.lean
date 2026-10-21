import InitECandidate.Proofs.WordStages.Source668
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody684_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody684_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 108 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody684_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody684_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 90 (Flapjack.WordLangExpHOL.var 108)

def sourceBody684_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody684_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 90 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody684_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 90 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody684_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 90 (Flapjack.WordRegImm.reg 56) sourceBody684_5 sourceBody684_6

def sourceBody684_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_7 sourceBody684_2

def sourceBody684_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 126 (Flapjack.WordLangExpHOL.var 90)

def sourceBody684_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 108)
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody684_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 90
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 108)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody684_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 108)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody684_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 126
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 108)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody684_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.var 108, Flapjack.WordLangExpHOL.const 6#64])
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody684_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 108, Flapjack.WordLangExpHOL.const 6#64])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody684_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 108, Flapjack.WordLangExpHOL.const 6#64])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody684_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 118
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 108, Flapjack.WordLangExpHOL.const 6#64])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody684_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody684_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 82)

def sourceBody684_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 48)

def sourceBody684_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 114 (Flapjack.WordLangExpHOL.var 118)

def sourceBody684_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 9#64)

def sourceBody684_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody684_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([32, 100, 66, 136]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody684_0, 684, 2)) (some 661) ([10, 78, 44, 114, 28]) (some (10, sourceBody684_23, 684, 3))

def sourceBody684_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_24 sourceBody684_2

def sourceBody684_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_25 sourceBody684_0

def sourceBody684_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_22 sourceBody684_26

def sourceBody684_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_21 sourceBody684_27

def sourceBody684_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_20 sourceBody684_28

def sourceBody684_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_19 sourceBody684_29

def sourceBody684_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_18 sourceBody684_30

def sourceBody684_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 22)

def sourceBody684_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.var 90)

def sourceBody684_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 56)

def sourceBody684_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 132 (Flapjack.WordLangExpHOL.var 126)

def sourceBody684_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 32)

def sourceBody684_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 86 (Flapjack.WordLangExpHOL.var 100)

def sourceBody684_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 66)

def sourceBody684_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 122 (Flapjack.WordLangExpHOL.var 136)

def sourceBody684_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody684_41 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 78, 44, 114]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody684_0, 684, 4)) (some 654) ([28, 96, 62, 132, 18, 86, 52, 122]) (some (28, sourceBody684_40, 684, 5))

def sourceBody684_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_41 sourceBody684_2

def sourceBody684_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_42 sourceBody684_0

def sourceBody684_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_39 sourceBody684_43

def sourceBody684_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_38 sourceBody684_44

def sourceBody684_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_37 sourceBody684_45

def sourceBody684_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_36 sourceBody684_46

def sourceBody684_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_35 sourceBody684_47

def sourceBody684_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_34 sourceBody684_48

def sourceBody684_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_33 sourceBody684_49

def sourceBody684_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_32 sourceBody684_50

def sourceBody684_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody684_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 86 (Flapjack.WordLangExpHOL.var 82)

def sourceBody684_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 48)

def sourceBody684_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 122 (Flapjack.WordLangExpHOL.var 118)

def sourceBody684_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody684_57 : WordLangProgHOL (BitVec 64) :=
.call (some (([28, 96, 62, 132]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          Flapjack.Spt.ln)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
          Flapjack.Spt.ln)
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody684_0, 684, 6)) (some 656) ([18, 86, 52, 122]) (some (18, sourceBody684_56, 684, 7))

def sourceBody684_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_57 sourceBody684_2

def sourceBody684_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_58 sourceBody684_0

def sourceBody684_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_55 sourceBody684_59

def sourceBody684_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_54 sourceBody684_60

def sourceBody684_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_53 sourceBody684_61

def sourceBody684_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_52 sourceBody684_62

def sourceBody684_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 376#64]),
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 108)
          (Flapjack.WordLangExpHOL.const 6#64)]))

def sourceBody684_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 86
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 376#64]),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 108)
              (Flapjack.WordLangExpHOL.const 6#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody684_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 376#64]),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 108)
              (Flapjack.WordLangExpHOL.const 6#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody684_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 122
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 376#64]),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 108)
              (Flapjack.WordLangExpHOL.const 6#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody684_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 376#64]),
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 108)
          (Flapjack.WordLangExpHOL.const 6#64),
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody684_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 104
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 376#64]),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 108)
              (Flapjack.WordLangExpHOL.const 6#64),
            Flapjack.WordLangExpHOL.const 32#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody684_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 376#64]),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 108)
              (Flapjack.WordLangExpHOL.const 6#64),
            Flapjack.WordLangExpHOL.const 32#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody684_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 140
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 376#64]),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 108)
              (Flapjack.WordLangExpHOL.const 6#64),
            Flapjack.WordLangExpHOL.const 32#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody684_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody684_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 94 (Flapjack.WordLangExpHOL.var 78)

def sourceBody684_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 44)

def sourceBody684_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 130 (Flapjack.WordLangExpHOL.var 114)

def sourceBody684_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody684_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 84 (Flapjack.WordLangExpHOL.var 86)

def sourceBody684_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 52)

def sourceBody684_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 120 (Flapjack.WordLangExpHOL.var 122)

def sourceBody684_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody684_81 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 76, 42, 112]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
        PUnit.unit
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody684_0, 684, 8)) (some 657) ([26, 94, 60, 130, 16, 84, 50, 120]) (some (26, sourceBody684_80, 684, 9))

def sourceBody684_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_81 sourceBody684_2

def sourceBody684_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_82 sourceBody684_0

def sourceBody684_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_79 sourceBody684_83

def sourceBody684_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_78 sourceBody684_84

def sourceBody684_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_77 sourceBody684_85

def sourceBody684_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_76 sourceBody684_86

def sourceBody684_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_75 sourceBody684_87

def sourceBody684_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_74 sourceBody684_88

def sourceBody684_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_73 sourceBody684_89

def sourceBody684_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_72 sourceBody684_90

def sourceBody684_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 28)

def sourceBody684_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 84 (Flapjack.WordLangExpHOL.var 96)

def sourceBody684_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 62)

def sourceBody684_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 120 (Flapjack.WordLangExpHOL.var 132)

def sourceBody684_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 36)

def sourceBody684_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 102 (Flapjack.WordLangExpHOL.var 104)

def sourceBody684_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 70)

def sourceBody684_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 138 (Flapjack.WordLangExpHOL.var 140)

def sourceBody684_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody684_101 : WordLangProgHOL (BitVec 64) :=
.call (some (([26, 94, 60, 130]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
              (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
        PUnit.unit
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
            (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody684_0, 684, 10)) (some 657) ([16, 84, 50, 120, 34, 102, 68, 138]) (some (16, sourceBody684_100, 684, 11))

def sourceBody684_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_101 sourceBody684_2

def sourceBody684_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_102 sourceBody684_0

def sourceBody684_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_99 sourceBody684_103

def sourceBody684_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_98 sourceBody684_104

def sourceBody684_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_97 sourceBody684_105

def sourceBody684_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_96 sourceBody684_106

def sourceBody684_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_95 sourceBody684_107

def sourceBody684_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_94 sourceBody684_108

def sourceBody684_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_93 sourceBody684_109

def sourceBody684_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_92 sourceBody684_110

def sourceBody684_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 10)

def sourceBody684_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 102 (Flapjack.WordLangExpHOL.var 78)

def sourceBody684_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 44)

def sourceBody684_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 138 (Flapjack.WordLangExpHOL.var 114)

def sourceBody684_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 36)

def sourceBody684_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 104)

def sourceBody684_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 70)

def sourceBody684_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 116 (Flapjack.WordLangExpHOL.var 140)

def sourceBody684_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody684_121 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 84, 50, 120]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
            (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
            (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody684_0, 684, 12)) (some 657) ([34, 102, 68, 138, 12, 80, 46, 116]) (some (34, sourceBody684_120, 684, 13))

def sourceBody684_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_121 sourceBody684_2

def sourceBody684_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_122 sourceBody684_0

def sourceBody684_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_119 sourceBody684_123

def sourceBody684_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_118 sourceBody684_124

def sourceBody684_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_117 sourceBody684_125

def sourceBody684_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_116 sourceBody684_126

def sourceBody684_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_115 sourceBody684_127

def sourceBody684_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_114 sourceBody684_128

def sourceBody684_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_113 sourceBody684_129

def sourceBody684_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_112 sourceBody684_130

def sourceBody684_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 28)

def sourceBody684_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 96)

def sourceBody684_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 62)

def sourceBody684_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 116 (Flapjack.WordLangExpHOL.var 132)

def sourceBody684_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 18)

def sourceBody684_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 98 (Flapjack.WordLangExpHOL.var 86)

def sourceBody684_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 52)

def sourceBody684_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 134 (Flapjack.WordLangExpHOL.var 122)

def sourceBody684_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody684_141 : WordLangProgHOL (BitVec 64) :=
.call (some (([34, 102, 68, 138]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
            (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody684_0, 684, 14)) (some 657) ([12, 80, 46, 116, 30, 98, 64, 134]) (some (12, sourceBody684_140, 684, 15))

def sourceBody684_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_141 sourceBody684_2

def sourceBody684_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_142 sourceBody684_0

def sourceBody684_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_139 sourceBody684_143

def sourceBody684_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_138 sourceBody684_144

def sourceBody684_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_137 sourceBody684_145

def sourceBody684_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_136 sourceBody684_146

def sourceBody684_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_135 sourceBody684_147

def sourceBody684_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_134 sourceBody684_148

def sourceBody684_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_133 sourceBody684_149

def sourceBody684_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_132 sourceBody684_150

def sourceBody684_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 8)

def sourceBody684_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 98 (Flapjack.WordLangExpHOL.var 76)

def sourceBody684_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 42)

def sourceBody684_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 134 (Flapjack.WordLangExpHOL.var 112)

def sourceBody684_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 26)

def sourceBody684_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 88 (Flapjack.WordLangExpHOL.var 94)

def sourceBody684_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 60)

def sourceBody684_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 124 (Flapjack.WordLangExpHOL.var 130)

def sourceBody684_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody684_161 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 80, 46, 116]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
          (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody684_0, 684, 16)) (some 655) ([30, 98, 64, 134, 20, 88, 54, 124]) (some (30, sourceBody684_160, 684, 17))

def sourceBody684_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_161 sourceBody684_2

def sourceBody684_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_162 sourceBody684_0

def sourceBody684_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_159 sourceBody684_163

def sourceBody684_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_158 sourceBody684_164

def sourceBody684_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_157 sourceBody684_165

def sourceBody684_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_156 sourceBody684_166

def sourceBody684_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_155 sourceBody684_167

def sourceBody684_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_154 sourceBody684_168

def sourceBody684_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_153 sourceBody684_169

def sourceBody684_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_152 sourceBody684_170

def sourceBody684_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody684_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 88 (Flapjack.WordLangExpHOL.var 84)

def sourceBody684_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 50)

def sourceBody684_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 124 (Flapjack.WordLangExpHOL.var 120)

def sourceBody684_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 34)

def sourceBody684_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 106 (Flapjack.WordLangExpHOL.var 102)

def sourceBody684_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 68)

def sourceBody684_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 142 (Flapjack.WordLangExpHOL.var 138)

def sourceBody684_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody684_181 : WordLangProgHOL (BitVec 64) :=
.call (some (([30, 98, 64, 134]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody684_0, 684, 18)) (some 654) ([20, 88, 54, 124, 38, 106, 72, 142]) (some (20, sourceBody684_180, 684, 19))

def sourceBody684_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_181 sourceBody684_2

def sourceBody684_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_182 sourceBody684_0

def sourceBody684_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_179 sourceBody684_183

def sourceBody684_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_178 sourceBody684_184

def sourceBody684_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_177 sourceBody684_185

def sourceBody684_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_176 sourceBody684_186

def sourceBody684_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_175 sourceBody684_187

def sourceBody684_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_174 sourceBody684_188

def sourceBody684_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_173 sourceBody684_189

def sourceBody684_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_172 sourceBody684_190

def sourceBody684_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 30)

def sourceBody684_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 106 (Flapjack.WordLangExpHOL.var 98)

def sourceBody684_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 64)

def sourceBody684_195 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 142 (Flapjack.WordLangExpHOL.var 134)

def sourceBody684_196 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 9#64)

def sourceBody684_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody684_198 : WordLangProgHOL (BitVec 64) :=
.call (some (([20, 88, 54, 124]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody684_0, 684, 20)) (some 661) ([38, 106, 72, 142, 6]) (some (38, sourceBody684_197, 684, 21))

def sourceBody684_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_198 sourceBody684_2

def sourceBody684_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_199 sourceBody684_0

def sourceBody684_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_196 sourceBody684_200

def sourceBody684_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_195 sourceBody684_201

def sourceBody684_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_194 sourceBody684_202

def sourceBody684_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_193 sourceBody684_203

def sourceBody684_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_192 sourceBody684_204

def sourceBody684_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody684_207 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 80)

def sourceBody684_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 46)

def sourceBody684_209 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 110 (Flapjack.WordLangExpHOL.var 116)

def sourceBody684_210 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 20)

def sourceBody684_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 92 (Flapjack.WordLangExpHOL.var 88)

def sourceBody684_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 54)

def sourceBody684_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 128 (Flapjack.WordLangExpHOL.var 124)

def sourceBody684_214 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody684_215 : WordLangProgHOL (BitVec 64) :=
.call (some (([38, 106, 72, 142]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody684_0, 684, 22)) (some 655) ([6, 74, 40, 110, 24, 92, 58, 128]) (some (6, sourceBody684_214, 684, 23))

def sourceBody684_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_215 sourceBody684_2

def sourceBody684_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_216 sourceBody684_0

def sourceBody684_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_213 sourceBody684_217

def sourceBody684_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_212 sourceBody684_218

def sourceBody684_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_211 sourceBody684_219

def sourceBody684_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_210 sourceBody684_220

def sourceBody684_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_209 sourceBody684_221

def sourceBody684_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_208 sourceBody684_222

def sourceBody684_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_207 sourceBody684_223

def sourceBody684_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_206 sourceBody684_224

def sourceBody684_226 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 108)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody684_227 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 38)

def sourceBody684_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 106)

def sourceBody684_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 110 (Flapjack.WordLangExpHOL.var 72)

def sourceBody684_230 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 142)

def sourceBody684_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 92 (Flapjack.WordLangExpHOL.var 74)

def sourceBody684_232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 6) 92

def sourceBody684_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_232 sourceBody684_0

def sourceBody684_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_231 sourceBody684_233

def sourceBody684_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 92 (Flapjack.WordLangExpHOL.var 40)

def sourceBody684_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 8#64]) 92

def sourceBody684_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_236 sourceBody684_0

def sourceBody684_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_235 sourceBody684_237

def sourceBody684_239 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 92 (Flapjack.WordLangExpHOL.var 110)

def sourceBody684_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 16#64])
  92

def sourceBody684_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_240 sourceBody684_0

def sourceBody684_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_239 sourceBody684_241

def sourceBody684_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 92 (Flapjack.WordLangExpHOL.var 24)

def sourceBody684_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 24#64])
  92

def sourceBody684_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_244 sourceBody684_0

def sourceBody684_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_243 sourceBody684_245

def sourceBody684_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_246 sourceBody684_0

def sourceBody684_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_242 sourceBody684_247

def sourceBody684_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_238 sourceBody684_248

def sourceBody684_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_234 sourceBody684_249

def sourceBody684_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_230 sourceBody684_250

def sourceBody684_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_251

def sourceBody684_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_229 sourceBody684_252

def sourceBody684_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_253

def sourceBody684_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_228 sourceBody684_254

def sourceBody684_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_255

def sourceBody684_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_227 sourceBody684_256

def sourceBody684_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_257

def sourceBody684_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_226 sourceBody684_258

def sourceBody684_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_259

def sourceBody684_261 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 108, Flapjack.WordLangExpHOL.const 6#64])
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody684_262 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 30)

def sourceBody684_263 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 98)

def sourceBody684_264 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 110 (Flapjack.WordLangExpHOL.var 64)

def sourceBody684_265 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 134)

def sourceBody684_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_265 sourceBody684_250

def sourceBody684_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_266

def sourceBody684_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_264 sourceBody684_267

def sourceBody684_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_268

def sourceBody684_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_263 sourceBody684_269

def sourceBody684_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_270

def sourceBody684_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_262 sourceBody684_271

def sourceBody684_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_272

def sourceBody684_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_261 sourceBody684_273

def sourceBody684_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_274

def sourceBody684_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_260 sourceBody684_275

def sourceBody684_277 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 108, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody684_278 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 108 (Flapjack.WordLangExpHOL.var 6)

def sourceBody684_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_278 sourceBody684_0

def sourceBody684_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_279 sourceBody684_0

def sourceBody684_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_277 sourceBody684_280

def sourceBody684_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_281

def sourceBody684_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_276 sourceBody684_282

def sourceBody684_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_225 sourceBody684_283

def sourceBody684_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_284

def sourceBody684_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_285

def sourceBody684_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_286

def sourceBody684_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_287

def sourceBody684_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_288

def sourceBody684_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_289

def sourceBody684_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_290

def sourceBody684_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_291

def sourceBody684_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_205 sourceBody684_292

def sourceBody684_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_293

def sourceBody684_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_294

def sourceBody684_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_295

def sourceBody684_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_296

def sourceBody684_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_297

def sourceBody684_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_298

def sourceBody684_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_299

def sourceBody684_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_300

def sourceBody684_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_191 sourceBody684_301

def sourceBody684_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_302

def sourceBody684_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_303

def sourceBody684_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_304

def sourceBody684_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_305

def sourceBody684_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_306

def sourceBody684_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_307

def sourceBody684_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_308

def sourceBody684_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_309

def sourceBody684_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_171 sourceBody684_310

def sourceBody684_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_311

def sourceBody684_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_312

def sourceBody684_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_313

def sourceBody684_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_314

def sourceBody684_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_315

def sourceBody684_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_316

def sourceBody684_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_317

def sourceBody684_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_318

def sourceBody684_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_151 sourceBody684_319

def sourceBody684_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_320

def sourceBody684_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_321

def sourceBody684_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_322

def sourceBody684_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_323

def sourceBody684_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_324

def sourceBody684_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_325

def sourceBody684_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_326

def sourceBody684_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_327

def sourceBody684_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_131 sourceBody684_328

def sourceBody684_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_329

def sourceBody684_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_330

def sourceBody684_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_331

def sourceBody684_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_332

def sourceBody684_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_333

def sourceBody684_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_334

def sourceBody684_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_335

def sourceBody684_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_336

def sourceBody684_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_111 sourceBody684_337

def sourceBody684_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_338

def sourceBody684_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_339

def sourceBody684_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_340

def sourceBody684_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_341

def sourceBody684_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_342

def sourceBody684_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_343

def sourceBody684_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_344

def sourceBody684_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_345

def sourceBody684_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_91 sourceBody684_346

def sourceBody684_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_347

def sourceBody684_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_348

def sourceBody684_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_349

def sourceBody684_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_350

def sourceBody684_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_351

def sourceBody684_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_352

def sourceBody684_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_353

def sourceBody684_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_354

def sourceBody684_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_71 sourceBody684_355

def sourceBody684_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_356

def sourceBody684_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_70 sourceBody684_357

def sourceBody684_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_358

def sourceBody684_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_69 sourceBody684_359

def sourceBody684_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_360

def sourceBody684_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_68 sourceBody684_361

def sourceBody684_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_362

def sourceBody684_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_67 sourceBody684_363

def sourceBody684_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_364

def sourceBody684_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_66 sourceBody684_365

def sourceBody684_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_366

def sourceBody684_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_65 sourceBody684_367

def sourceBody684_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_368

def sourceBody684_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_64 sourceBody684_369

def sourceBody684_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_370

def sourceBody684_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_63 sourceBody684_371

def sourceBody684_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_372

def sourceBody684_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_373

def sourceBody684_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_374

def sourceBody684_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_375

def sourceBody684_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_376

def sourceBody684_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_377

def sourceBody684_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_378

def sourceBody684_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_379

def sourceBody684_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_51 sourceBody684_380

def sourceBody684_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_381

def sourceBody684_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_382

def sourceBody684_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_383

def sourceBody684_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_384

def sourceBody684_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_385

def sourceBody684_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_386

def sourceBody684_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_387

def sourceBody684_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_388

def sourceBody684_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_31 sourceBody684_389

def sourceBody684_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_390

def sourceBody684_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_391

def sourceBody684_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_392

def sourceBody684_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_393

def sourceBody684_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_394

def sourceBody684_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_395

def sourceBody684_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_396

def sourceBody684_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_397

def sourceBody684_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_17 sourceBody684_398

def sourceBody684_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_399

def sourceBody684_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_16 sourceBody684_400

def sourceBody684_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_401

def sourceBody684_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_15 sourceBody684_402

def sourceBody684_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_403

def sourceBody684_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_14 sourceBody684_404

def sourceBody684_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_405

def sourceBody684_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_13 sourceBody684_406

def sourceBody684_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_407

def sourceBody684_409 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_12 sourceBody684_408

def sourceBody684_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_409

def sourceBody684_411 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_11 sourceBody684_410

def sourceBody684_412 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_411

def sourceBody684_413 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_10 sourceBody684_412

def sourceBody684_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_413

def sourceBody684_415 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody684_416 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_414 sourceBody684_415

def sourceBody684_417 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody684_418 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 126 (Flapjack.WordRegImm.imm 0#64) sourceBody684_416 sourceBody684_417

def sourceBody684_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_418 sourceBody684_2

def sourceBody684_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_419 sourceBody684_0

def sourceBody684_421 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_9 sourceBody684_420

def sourceBody684_422 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_8 sourceBody684_421

def sourceBody684_423 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_4 sourceBody684_422

def sourceBody684_424 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_3 sourceBody684_423

def sourceBody684_425 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln)
      PUnit.unit Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln) sourceBody684_424 (Flapjack.Spt.ls PUnit.unit)

def sourceBody684_426 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_425 sourceBody684_2

def sourceBody684_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_2 sourceBody684_426

def sourceBody684_428 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody684_429 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [22]

def sourceBody684_430 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_429 sourceBody684_0

def sourceBody684_431 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_428 sourceBody684_430

def sourceBody684_432 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_427 sourceBody684_431

def sourceBody684_433 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_1 sourceBody684_432

def sourceBody684_434 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody684_0 sourceBody684_433

def source684 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (684, 3, sourceBody684_434)
end InitECandidate.Proofs.WordStages
