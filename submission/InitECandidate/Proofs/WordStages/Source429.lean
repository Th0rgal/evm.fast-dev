import InitECandidate.Proofs.WordStages.Source413
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody429_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody429_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 176#64]),
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody429_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 184#64]),
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody429_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody429_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody429_0, 429, 2)) (some 428) ([22, 4]) (some (22, sourceBody429_3, 429, 3))

def sourceBody429_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody429_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_4 sourceBody429_5

def sourceBody429_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_6 sourceBody429_0

def sourceBody429_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_2 sourceBody429_7

def sourceBody429_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_1 sourceBody429_8

def sourceBody429_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_9

def sourceBody429_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_10

def sourceBody429_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 176#64]),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody429_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 184#64]),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody429_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody429_0, 429, 4)) (some 428) ([22, 4]) (some (22, sourceBody429_3, 429, 5))

def sourceBody429_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_14 sourceBody429_5

def sourceBody429_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_15 sourceBody429_0

def sourceBody429_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_13 sourceBody429_16

def sourceBody429_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_12 sourceBody429_17

def sourceBody429_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_18

def sourceBody429_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_19

def sourceBody429_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_11 sourceBody429_20

def sourceBody429_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 176#64]),
        Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody429_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 184#64]),
        Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody429_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody429_0, 429, 6)) (some 428) ([22, 4]) (some (22, sourceBody429_3, 429, 7))

def sourceBody429_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_24 sourceBody429_5

def sourceBody429_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_25 sourceBody429_0

def sourceBody429_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_23 sourceBody429_26

def sourceBody429_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_22 sourceBody429_27

def sourceBody429_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_28

def sourceBody429_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_29

def sourceBody429_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_21 sourceBody429_30

def sourceBody429_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 176#64]),
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody429_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 184#64]),
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody429_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody429_0, 429, 8)) (some 428) ([22, 4]) (some (22, sourceBody429_3, 429, 9))

def sourceBody429_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_34 sourceBody429_5

def sourceBody429_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_35 sourceBody429_0

def sourceBody429_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_33 sourceBody429_36

def sourceBody429_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_32 sourceBody429_37

def sourceBody429_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_38

def sourceBody429_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_39

def sourceBody429_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_31 sourceBody429_40

def sourceBody429_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 176#64]),
        Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody429_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 184#64]),
        Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody429_44 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody429_0, 429, 10)) (some 428) ([22, 4]) (some (22, sourceBody429_3, 429, 11))

def sourceBody429_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_44 sourceBody429_5

def sourceBody429_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_45 sourceBody429_0

def sourceBody429_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_43 sourceBody429_46

def sourceBody429_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_42 sourceBody429_47

def sourceBody429_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_48

def sourceBody429_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_49

def sourceBody429_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_41 sourceBody429_50

def sourceBody429_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 184#64]),
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody429_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 176#64]),
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody429_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody429_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody429_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 18)

def sourceBody429_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody429_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody429_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody429_60 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 26 (Flapjack.WordRegImm.reg 2) sourceBody429_58 sourceBody429_59

def sourceBody429_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_60 sourceBody429_5

def sourceBody429_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 26)

def sourceBody429_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody429_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody429_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody429_66 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 26, 2]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody429_0, 429, 12)) (some 197) ([16, 10]) (some (16, sourceBody429_65, 429, 13))

def sourceBody429_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_66 sourceBody429_5

def sourceBody429_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_67 sourceBody429_0

def sourceBody429_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_64 sourceBody429_68

def sourceBody429_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_63 sourceBody429_69

def sourceBody429_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody429_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody429_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody429_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody429_75 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 24) sourceBody429_73 sourceBody429_74

def sourceBody429_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_75 sourceBody429_5

def sourceBody429_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody429_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 22)

def sourceBody429_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 26)

def sourceBody429_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody429_81 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody429_0, 429, 14)) (some 186) ([24, 6]) (some (24, sourceBody429_80, 429, 15))

def sourceBody429_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_81 sourceBody429_5

def sourceBody429_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_82 sourceBody429_0

def sourceBody429_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_79 sourceBody429_83

def sourceBody429_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_78 sourceBody429_84

def sourceBody429_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody429_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody429_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody429_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody429_90 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 20 (Flapjack.WordRegImm.reg 14) sourceBody429_88 sourceBody429_89

def sourceBody429_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_90 sourceBody429_5

def sourceBody429_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 20)

def sourceBody429_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody429_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody429_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody429_96 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody429_0, 429, 16)) (some 182) ([6, 20]) (some (6, sourceBody429_95, 429, 17))

def sourceBody429_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_96 sourceBody429_5

def sourceBody429_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_97 sourceBody429_0

def sourceBody429_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_94 sourceBody429_98

def sourceBody429_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_93 sourceBody429_99

def sourceBody429_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 22)

def sourceBody429_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 26)

def sourceBody429_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 24)

def sourceBody429_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody429_105 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody429_0, 429, 18)) (some 192) ([20, 14, 28]) (some (20, sourceBody429_104, 429, 19))

def sourceBody429_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_105 sourceBody429_5

def sourceBody429_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_106 sourceBody429_0

def sourceBody429_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_103 sourceBody429_107

def sourceBody429_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_102 sourceBody429_108

def sourceBody429_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_101 sourceBody429_109

def sourceBody429_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_110

def sourceBody429_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_111

def sourceBody429_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_100 sourceBody429_112

def sourceBody429_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody429_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_114 sourceBody429_0

def sourceBody429_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_115 sourceBody429_0

def sourceBody429_117 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody429_113 sourceBody429_116

def sourceBody429_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_117 sourceBody429_5

def sourceBody429_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_118 sourceBody429_0

def sourceBody429_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_92 sourceBody429_119

def sourceBody429_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_91 sourceBody429_120

def sourceBody429_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_87 sourceBody429_121

def sourceBody429_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_86 sourceBody429_122

def sourceBody429_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody429_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody429_126 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody429_0, 429, 20)) (some 428) ([20, 14]) (some (20, sourceBody429_104, 429, 21))

def sourceBody429_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_126 sourceBody429_5

def sourceBody429_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_127 sourceBody429_0

def sourceBody429_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_125 sourceBody429_128

def sourceBody429_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_124 sourceBody429_129

def sourceBody429_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_130

def sourceBody429_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_131

def sourceBody429_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_123 sourceBody429_132

def sourceBody429_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_133

def sourceBody429_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_134

def sourceBody429_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_85 sourceBody429_135

def sourceBody429_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_136

def sourceBody429_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_137

def sourceBody429_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_138

def sourceBody429_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_139

def sourceBody429_141 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody429_140 sourceBody429_0

def sourceBody429_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_141 sourceBody429_5

def sourceBody429_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_142 sourceBody429_0

def sourceBody429_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_77 sourceBody429_143

def sourceBody429_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_76 sourceBody429_144

def sourceBody429_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_72 sourceBody429_145

def sourceBody429_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_71 sourceBody429_146

def sourceBody429_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody429_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody429_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_149 sourceBody429_0

def sourceBody429_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_150 sourceBody429_0

def sourceBody429_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_148 sourceBody429_151

def sourceBody429_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_152

def sourceBody429_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_147 sourceBody429_153

def sourceBody429_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_70 sourceBody429_154

def sourceBody429_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_155

def sourceBody429_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_156

def sourceBody429_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_157

def sourceBody429_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_158

def sourceBody429_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_159

def sourceBody429_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_160

def sourceBody429_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody429_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_161 sourceBody429_162

def sourceBody429_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody429_165 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody429_163 sourceBody429_164

def sourceBody429_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_165 sourceBody429_5

def sourceBody429_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_166 sourceBody429_0

def sourceBody429_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_62 sourceBody429_167

def sourceBody429_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_61 sourceBody429_168

def sourceBody429_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_57 sourceBody429_169

def sourceBody429_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_56 sourceBody429_170

def sourceBody429_172 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln) sourceBody429_171 (Flapjack.Spt.ls PUnit.unit)

def sourceBody429_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_172 sourceBody429_5

def sourceBody429_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_5 sourceBody429_173

def sourceBody429_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody429_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody429_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_176 sourceBody429_0

def sourceBody429_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_175 sourceBody429_177

def sourceBody429_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_174 sourceBody429_178

def sourceBody429_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_55 sourceBody429_179

def sourceBody429_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_180

def sourceBody429_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_54 sourceBody429_181

def sourceBody429_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_182

def sourceBody429_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_53 sourceBody429_183

def sourceBody429_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_184

def sourceBody429_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_52 sourceBody429_185

def sourceBody429_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_0 sourceBody429_186

def sourceBody429_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody429_51 sourceBody429_187

def source429 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (429, 1, sourceBody429_188)
end InitECandidate.Proofs.WordStages
