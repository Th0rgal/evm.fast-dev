import InitECandidate.Proofs.WordStages.Source848
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody864_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody864_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody864_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody864_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 88#64)

def sourceBody864_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody864_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 2)) (some 68) ([24]) (some (24, sourceBody864_4, 864, 3))

def sourceBody864_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody864_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_5 sourceBody864_6

def sourceBody864_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_7 sourceBody864_0

def sourceBody864_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_3 sourceBody864_8

def sourceBody864_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 416#64])

def sourceBody864_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 36)

def sourceBody864_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 50)

def sourceBody864_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 24) 8

def sourceBody864_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_13 sourceBody864_0

def sourceBody864_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_12 sourceBody864_14

def sourceBody864_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_15 sourceBody864_0

def sourceBody864_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_11 sourceBody864_16

def sourceBody864_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_17

def sourceBody864_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_10 sourceBody864_18

def sourceBody864_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_19

def sourceBody864_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_9 sourceBody864_20

def sourceBody864_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_21

def sourceBody864_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_22

def sourceBody864_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 416#64]))

def sourceBody864_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 88#64)

def sourceBody864_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 4)) (some 78) ([24, 50]) (some (24, sourceBody864_4, 864, 5))

def sourceBody864_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_26 sourceBody864_6

def sourceBody864_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_27 sourceBody864_0

def sourceBody864_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_25 sourceBody864_28

def sourceBody864_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_24 sourceBody864_29

def sourceBody864_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_30

def sourceBody864_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_31

def sourceBody864_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_23 sourceBody864_32

def sourceBody864_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
        (Flapjack.WordLangExpHOL.const 4#64),
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody864_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 6)) (some 68) ([24]) (some (24, sourceBody864_4, 864, 7))

def sourceBody864_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_35 sourceBody864_6

def sourceBody864_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_36 sourceBody864_0

def sourceBody864_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_34 sourceBody864_37

def sourceBody864_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 416#64]),
      Flapjack.WordLangExpHOL.const 24#64])

def sourceBody864_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_39 sourceBody864_18

def sourceBody864_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_40

def sourceBody864_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
        (Flapjack.WordLangExpHOL.const 4#64),
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody864_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 50

def sourceBody864_44 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 8)) (some 68) ([50]) (some (50, sourceBody864_43, 864, 9))

def sourceBody864_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_44 sourceBody864_6

def sourceBody864_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_45 sourceBody864_0

def sourceBody864_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_42 sourceBody864_46

def sourceBody864_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 416#64]),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody864_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 24)

def sourceBody864_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 8)

def sourceBody864_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 50) 32

def sourceBody864_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_51 sourceBody864_0

def sourceBody864_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_50 sourceBody864_52

def sourceBody864_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_53 sourceBody864_0

def sourceBody864_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_49 sourceBody864_54

def sourceBody864_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_55

def sourceBody864_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_48 sourceBody864_56

def sourceBody864_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_57

def sourceBody864_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody864_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody864_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody864_62 : WordLangProgHOL (BitVec 64) :=
.call (some (([50]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 10)) (some 431) ([8, 32]) (some (8, sourceBody864_61, 864, 11))

def sourceBody864_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_62 sourceBody864_6

def sourceBody864_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_63 sourceBody864_0

def sourceBody864_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_60 sourceBody864_64

def sourceBody864_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_59 sourceBody864_65

def sourceBody864_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 416#64]),
      Flapjack.WordLangExpHOL.const 40#64])

def sourceBody864_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 50)

def sourceBody864_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 32)

def sourceBody864_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 20

def sourceBody864_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_70 sourceBody864_0

def sourceBody864_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_69 sourceBody864_71

def sourceBody864_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_72 sourceBody864_0

def sourceBody864_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_68 sourceBody864_73

def sourceBody864_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_74

def sourceBody864_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_67 sourceBody864_75

def sourceBody864_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_76

def sourceBody864_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody864_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody864_80 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 12)) (some 68) ([32]) (some (32, sourceBody864_79, 864, 13))

def sourceBody864_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_80 sourceBody864_6

def sourceBody864_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_81 sourceBody864_0

def sourceBody864_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_78 sourceBody864_82

def sourceBody864_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 416#64]),
      Flapjack.WordLangExpHOL.const 56#64])

def sourceBody864_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody864_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 20)

def sourceBody864_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 32) 46

def sourceBody864_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_87 sourceBody864_0

def sourceBody864_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_86 sourceBody864_88

def sourceBody864_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_89 sourceBody864_0

def sourceBody864_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_85 sourceBody864_90

def sourceBody864_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_91

def sourceBody864_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_84 sourceBody864_92

def sourceBody864_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_93

def sourceBody864_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody864_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody864_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody864_98 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 14)) (some 431) ([20, 46]) (some (20, sourceBody864_97, 864, 15))

def sourceBody864_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_98 sourceBody864_6

def sourceBody864_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_99 sourceBody864_0

def sourceBody864_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_96 sourceBody864_100

def sourceBody864_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_95 sourceBody864_101

def sourceBody864_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 416#64]),
      Flapjack.WordLangExpHOL.const 72#64])

def sourceBody864_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 32)

def sourceBody864_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 46)

def sourceBody864_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 20) 16

def sourceBody864_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_106 sourceBody864_0

def sourceBody864_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_105 sourceBody864_107

def sourceBody864_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_108 sourceBody864_0

def sourceBody864_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_104 sourceBody864_109

def sourceBody864_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_110

def sourceBody864_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_103 sourceBody864_111

def sourceBody864_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_112

def sourceBody864_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 416#64]),
      Flapjack.WordLangExpHOL.const 80#64])

def sourceBody864_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 12)

def sourceBody864_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_115 sourceBody864_109

def sourceBody864_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_116

def sourceBody864_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_114 sourceBody864_117

def sourceBody864_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_118

def sourceBody864_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_113 sourceBody864_119

def sourceBody864_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody864_122 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 16)) (some 434) ([]) (some (46, sourceBody864_121, 864, 17))

def sourceBody864_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_122 sourceBody864_6

def sourceBody864_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_123 sourceBody864_0

def sourceBody864_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_124

def sourceBody864_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_125

def sourceBody864_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_120 sourceBody864_126

def sourceBody864_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 464#64]))

def sourceBody864_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody864_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody864_131 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 18)) (some 856) ([46, 16, 40]) (some (46, sourceBody864_121, 864, 19))

def sourceBody864_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_131 sourceBody864_6

def sourceBody864_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_132 sourceBody864_0

def sourceBody864_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_130 sourceBody864_133

def sourceBody864_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_129 sourceBody864_134

def sourceBody864_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_128 sourceBody864_135

def sourceBody864_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_136

def sourceBody864_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_137

def sourceBody864_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_127 sourceBody864_138

def sourceBody864_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 432#64]))

def sourceBody864_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody864_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 448#64]))

def sourceBody864_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody864_144 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 16 (Flapjack.WordRegImm.reg 40) sourceBody864_143 sourceBody864_141

def sourceBody864_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_144 sourceBody864_6

def sourceBody864_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 16)

def sourceBody864_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 440#64]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 448#64]),
            Flapjack.WordLangExpHOL.const 1#64])
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody864_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_147 sourceBody864_0

def sourceBody864_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_148 sourceBody864_0

def sourceBody864_150 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody864_149 sourceBody864_0

def sourceBody864_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_150 sourceBody864_6

def sourceBody864_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_151 sourceBody864_0

def sourceBody864_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_146 sourceBody864_152

def sourceBody864_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_145 sourceBody864_153

def sourceBody864_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_142 sourceBody864_154

def sourceBody864_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_141 sourceBody864_155

def sourceBody864_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 472#64]))

def sourceBody864_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 20)

def sourceBody864_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody864_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody864_161 : WordLangProgHOL (BitVec 64) :=
.call (some (([46]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 20)) (some 856) ([16, 40, 28]) (some (16, sourceBody864_160, 864, 21))

def sourceBody864_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_161 sourceBody864_6

def sourceBody864_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_162 sourceBody864_0

def sourceBody864_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_159 sourceBody864_163

def sourceBody864_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_158 sourceBody864_164

def sourceBody864_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_157 sourceBody864_165

def sourceBody864_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_166

def sourceBody864_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_167

def sourceBody864_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_156 sourceBody864_168

def sourceBody864_170 : WordLangProgHOL (BitVec 64) :=
.call (some (([46]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 22)) (some 383) ([]) (some (16, sourceBody864_160, 864, 23))

def sourceBody864_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_170 sourceBody864_6

def sourceBody864_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_171 sourceBody864_0

def sourceBody864_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_172

def sourceBody864_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_173

def sourceBody864_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_169 sourceBody864_174

def sourceBody864_176 : WordLangProgHOL (BitVec 64) :=
.call (some (([46]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 24)) (some 430) ([16]) (some (16, sourceBody864_160, 864, 25))

def sourceBody864_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_176 sourceBody864_6

def sourceBody864_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_177 sourceBody864_0

def sourceBody864_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_143 sourceBody864_178

def sourceBody864_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_179

def sourceBody864_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_180

def sourceBody864_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_175 sourceBody864_181

def sourceBody864_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody864_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 12)

def sourceBody864_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody864_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody864_187 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 28 (Flapjack.WordRegImm.reg 54) sourceBody864_185 sourceBody864_186

def sourceBody864_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_187 sourceBody864_6

def sourceBody864_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 28)

def sourceBody864_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 46,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody864_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 46,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody864_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody864_193 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 26)) (some 342) ([28, 54]) (some (28, sourceBody864_192, 864, 27))

def sourceBody864_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_193 sourceBody864_6

def sourceBody864_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_194 sourceBody864_0

def sourceBody864_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_191 sourceBody864_195

def sourceBody864_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_190 sourceBody864_196

def sourceBody864_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 40)

def sourceBody864_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody864_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 54

def sourceBody864_201 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 28)) (some 859) ([54, 6]) (some (54, sourceBody864_200, 864, 29))

def sourceBody864_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_201 sourceBody864_6

def sourceBody864_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_202 sourceBody864_0

def sourceBody864_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_199 sourceBody864_203

def sourceBody864_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_198 sourceBody864_204

def sourceBody864_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_205

def sourceBody864_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_206

def sourceBody864_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody864_209 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 28)

def sourceBody864_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_209 sourceBody864_0

def sourceBody864_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_210 sourceBody864_0

def sourceBody864_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_208 sourceBody864_211

def sourceBody864_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_212

def sourceBody864_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_207 sourceBody864_213

def sourceBody864_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_197 sourceBody864_214

def sourceBody864_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_215

def sourceBody864_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_216

def sourceBody864_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody864_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_217 sourceBody864_218

def sourceBody864_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody864_221 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody864_219 sourceBody864_220

def sourceBody864_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_221 sourceBody864_6

def sourceBody864_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_222 sourceBody864_0

def sourceBody864_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_189 sourceBody864_223

def sourceBody864_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_188 sourceBody864_224

def sourceBody864_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_184 sourceBody864_225

def sourceBody864_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_146 sourceBody864_226

def sourceBody864_228 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody864_227 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody864_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_228 sourceBody864_6

def sourceBody864_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_6 sourceBody864_229

def sourceBody864_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 224#64])

def sourceBody864_232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody864_233 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 28)

def sourceBody864_234 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 40) 54

def sourceBody864_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_234 sourceBody864_0

def sourceBody864_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_233 sourceBody864_235

def sourceBody864_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_236 sourceBody864_0

def sourceBody864_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_232 sourceBody864_237

def sourceBody864_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_238

def sourceBody864_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_231 sourceBody864_239

def sourceBody864_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_240

def sourceBody864_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_230 sourceBody864_241

def sourceBody864_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 42)

def sourceBody864_244 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 30)) (some 861) ([28]) (some (28, sourceBody864_192, 864, 31))

def sourceBody864_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_244 sourceBody864_6

def sourceBody864_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_245 sourceBody864_0

def sourceBody864_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_243 sourceBody864_246

def sourceBody864_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_247

def sourceBody864_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_248

def sourceBody864_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_242 sourceBody864_249

def sourceBody864_251 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 32)) (some 863) ([]) (some (28, sourceBody864_192, 864, 33))

def sourceBody864_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_251 sourceBody864_6

def sourceBody864_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_252 sourceBody864_0

def sourceBody864_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_253

def sourceBody864_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_254

def sourceBody864_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_250 sourceBody864_255

def sourceBody864_257 : WordLangProgHOL (BitVec 64) :=
.call (some (([40, 28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 34)) (some 456) ([]) (some (54, sourceBody864_200, 864, 35))

def sourceBody864_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_257 sourceBody864_6

def sourceBody864_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_258 sourceBody864_0

def sourceBody864_260 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 408#64]),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody864_261 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody864_262 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 36)) (some 457) ([6]) (some (6, sourceBody864_261, 864, 37))

def sourceBody864_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_262 sourceBody864_6

def sourceBody864_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_263 sourceBody864_0

def sourceBody864_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_260 sourceBody864_264

def sourceBody864_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_265

def sourceBody864_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_266

def sourceBody864_268 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody864_269 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 38)) (some 68) ([6]) (some (6, sourceBody864_261, 864, 39))

def sourceBody864_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_269 sourceBody864_6

def sourceBody864_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_270 sourceBody864_0

def sourceBody864_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_268 sourceBody864_271

def sourceBody864_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 54)

def sourceBody864_274 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody864_275 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 40)) (some 846) ([30]) (some (30, sourceBody864_274, 864, 41))

def sourceBody864_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_275 sourceBody864_6

def sourceBody864_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_276 sourceBody864_0

def sourceBody864_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_273 sourceBody864_277

def sourceBody864_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_278

def sourceBody864_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_279

def sourceBody864_281 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody864_282 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 42)) (some 68) ([30]) (some (30, sourceBody864_274, 864, 43))

def sourceBody864_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_282 sourceBody864_6

def sourceBody864_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_283 sourceBody864_0

def sourceBody864_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_281 sourceBody864_284

def sourceBody864_286 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 36)

def sourceBody864_287 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 12)

def sourceBody864_288 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody864_289 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody864_290 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 44)) (some 328) ([18, 44, 14]) (some (18, sourceBody864_289, 864, 45))

def sourceBody864_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_290 sourceBody864_6

def sourceBody864_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_291 sourceBody864_0

def sourceBody864_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_288 sourceBody864_292

def sourceBody864_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_287 sourceBody864_293

def sourceBody864_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_286 sourceBody864_294

def sourceBody864_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_295

def sourceBody864_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_296

def sourceBody864_298 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody864_299 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 46)) (some 68) ([18]) (some (18, sourceBody864_289, 864, 47))

def sourceBody864_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_299 sourceBody864_6

def sourceBody864_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_300 sourceBody864_0

def sourceBody864_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_298 sourceBody864_301

def sourceBody864_303 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 24)

def sourceBody864_304 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody864_305 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 30)

def sourceBody864_306 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody864_307 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 48)) (some 328) ([44, 14, 38]) (some (44, sourceBody864_306, 864, 49))

def sourceBody864_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_307 sourceBody864_6

def sourceBody864_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_308 sourceBody864_0

def sourceBody864_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_305 sourceBody864_309

def sourceBody864_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_304 sourceBody864_310

def sourceBody864_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_303 sourceBody864_311

def sourceBody864_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_312

def sourceBody864_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_313

def sourceBody864_315 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 256#64)

def sourceBody864_316 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 50)) (some 68) ([44]) (some (44, sourceBody864_306, 864, 51))

def sourceBody864_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_316 sourceBody864_6

def sourceBody864_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_317 sourceBody864_0

def sourceBody864_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_315 sourceBody864_318

def sourceBody864_320 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
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
        Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody864_321 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 18)

def sourceBody864_322 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody864_323 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 52)) (some 835) ([14, 38]) (some (14, sourceBody864_322, 864, 53))

def sourceBody864_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_323 sourceBody864_6

def sourceBody864_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_324 sourceBody864_0

def sourceBody864_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_321 sourceBody864_325

def sourceBody864_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_320 sourceBody864_326

def sourceBody864_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_327

def sourceBody864_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_328

def sourceBody864_330 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody864_331 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 54)) (some 68) ([14]) (some (14, sourceBody864_322, 864, 55))

def sourceBody864_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_331 sourceBody864_6

def sourceBody864_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_332 sourceBody864_0

def sourceBody864_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_330 sourceBody864_333

def sourceBody864_335 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 528#64]))

def sourceBody864_336 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody864_337 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 44)

def sourceBody864_338 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody864_339 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 56)) (some 328) ([38, 26, 52]) (some (38, sourceBody864_338, 864, 57))

def sourceBody864_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_339 sourceBody864_6

def sourceBody864_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_340 sourceBody864_0

def sourceBody864_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_337 sourceBody864_341

def sourceBody864_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_336 sourceBody864_342

def sourceBody864_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_335 sourceBody864_343

def sourceBody864_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_344

def sourceBody864_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_345

def sourceBody864_347 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody864_348 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 58)) (some 68) ([38]) (some (38, sourceBody864_338, 864, 59))

def sourceBody864_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_348 sourceBody864_6

def sourceBody864_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_349 sourceBody864_0

def sourceBody864_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_347 sourceBody864_350

def sourceBody864_352 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
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
        Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody864_353 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
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
        Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody864_354 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody864_355 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody864_356 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 60)) (some 843) ([26, 52, 10]) (some (26, sourceBody864_355, 864, 61))

def sourceBody864_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_356 sourceBody864_6

def sourceBody864_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_357 sourceBody864_0

def sourceBody864_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_354 sourceBody864_358

def sourceBody864_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_353 sourceBody864_359

def sourceBody864_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_352 sourceBody864_360

def sourceBody864_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_361

def sourceBody864_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_362

def sourceBody864_364 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody864_365 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 62)) (some 68) ([26]) (some (26, sourceBody864_355, 864, 63))

def sourceBody864_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_365 sourceBody864_6

def sourceBody864_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_366 sourceBody864_0

def sourceBody864_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_364 sourceBody864_367

def sourceBody864_369 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 40)

def sourceBody864_370 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 28)

def sourceBody864_371 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 38)

def sourceBody864_372 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 52

def sourceBody864_373 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 64)) (some 158) ([52, 10, 34]) (some (52, sourceBody864_372, 864, 65))

def sourceBody864_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_373 sourceBody864_6

def sourceBody864_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_374 sourceBody864_0

def sourceBody864_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_371 sourceBody864_375

def sourceBody864_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_370 sourceBody864_376

def sourceBody864_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_369 sourceBody864_377

def sourceBody864_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_378

def sourceBody864_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_379

def sourceBody864_381 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
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
        Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody864_382 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
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
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody864_383 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 66)) (some 93) ([52, 10]) (some (52, sourceBody864_372, 864, 67))

def sourceBody864_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_383 sourceBody864_6

def sourceBody864_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_384 sourceBody864_0

def sourceBody864_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_382 sourceBody864_385

def sourceBody864_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_381 sourceBody864_386

def sourceBody864_388 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 26)

def sourceBody864_389 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody864_390 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody864_391 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody864_392 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 34) sourceBody864_390 sourceBody864_391

def sourceBody864_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_392 sourceBody864_6

def sourceBody864_394 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody864_395 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 110#64)

def sourceBody864_396 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 52)

def sourceBody864_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_396 sourceBody864_0

def sourceBody864_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_397 sourceBody864_0

def sourceBody864_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_395 sourceBody864_398

def sourceBody864_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_399

def sourceBody864_401 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody864_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_401 sourceBody864_372

def sourceBody864_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_400 sourceBody864_402

def sourceBody864_404 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody864_403 sourceBody864_0

def sourceBody864_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_404 sourceBody864_6

def sourceBody864_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_405 sourceBody864_0

def sourceBody864_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_394 sourceBody864_406

def sourceBody864_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_393 sourceBody864_407

def sourceBody864_409 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_389 sourceBody864_408

def sourceBody864_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_388 sourceBody864_409

def sourceBody864_411 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody864_412 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody864_413 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody864_414 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody864_415 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 68)) (some 79) ([10, 34, 22]) (some (10, sourceBody864_414, 864, 69))

def sourceBody864_416 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_415 sourceBody864_6

def sourceBody864_417 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_416 sourceBody864_0

def sourceBody864_418 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_413 sourceBody864_417

def sourceBody864_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_412 sourceBody864_418

def sourceBody864_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_411 sourceBody864_419

def sourceBody864_421 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 52)

def sourceBody864_422 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody864_423 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody864_424 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody864_425 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 34 (Flapjack.WordRegImm.reg 22) sourceBody864_423 sourceBody864_424

def sourceBody864_426 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_425 sourceBody864_6

def sourceBody864_427 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 34)

def sourceBody864_428 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 111#64)

def sourceBody864_429 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 10)

def sourceBody864_430 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_429 sourceBody864_0

def sourceBody864_431 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_430 sourceBody864_0

def sourceBody864_432 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_428 sourceBody864_431

def sourceBody864_433 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_432

def sourceBody864_434 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody864_435 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_434 sourceBody864_414

def sourceBody864_436 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_433 sourceBody864_435

def sourceBody864_437 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.imm 0#64) sourceBody864_436 sourceBody864_0

def sourceBody864_438 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_437 sourceBody864_6

def sourceBody864_439 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_438 sourceBody864_0

def sourceBody864_440 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_427 sourceBody864_439

def sourceBody864_441 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_426 sourceBody864_440

def sourceBody864_442 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_422 sourceBody864_441

def sourceBody864_443 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_421 sourceBody864_442

def sourceBody864_444 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 54)

def sourceBody864_445 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody864_446 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 70)) (some 79) ([10, 34, 22]) (some (10, sourceBody864_414, 864, 71))

def sourceBody864_447 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_446 sourceBody864_6

def sourceBody864_448 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_447 sourceBody864_0

def sourceBody864_449 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_413 sourceBody864_448

def sourceBody864_450 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_445 sourceBody864_449

def sourceBody864_451 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_444 sourceBody864_450

def sourceBody864_452 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_443 sourceBody864_451

def sourceBody864_453 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 112#64)

def sourceBody864_454 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_453 sourceBody864_431

def sourceBody864_455 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_454

def sourceBody864_456 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_455 sourceBody864_435

def sourceBody864_457 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.imm 0#64) sourceBody864_456 sourceBody864_0

def sourceBody864_458 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_457 sourceBody864_6

def sourceBody864_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_458 sourceBody864_0

def sourceBody864_460 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_427 sourceBody864_459

def sourceBody864_461 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_426 sourceBody864_460

def sourceBody864_462 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_422 sourceBody864_461

def sourceBody864_463 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_421 sourceBody864_462

def sourceBody864_464 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_452 sourceBody864_463

def sourceBody864_465 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 30)

def sourceBody864_466 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody864_467 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 72)) (some 79) ([10, 34, 22]) (some (10, sourceBody864_414, 864, 73))

def sourceBody864_468 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_467 sourceBody864_6

def sourceBody864_469 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_468 sourceBody864_0

def sourceBody864_470 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_413 sourceBody864_469

def sourceBody864_471 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_466 sourceBody864_470

def sourceBody864_472 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_465 sourceBody864_471

def sourceBody864_473 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_464 sourceBody864_472

def sourceBody864_474 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 113#64)

def sourceBody864_475 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_474 sourceBody864_431

def sourceBody864_476 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_475

def sourceBody864_477 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_476 sourceBody864_435

def sourceBody864_478 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.imm 0#64) sourceBody864_477 sourceBody864_0

def sourceBody864_479 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_478 sourceBody864_6

def sourceBody864_480 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_479 sourceBody864_0

def sourceBody864_481 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_427 sourceBody864_480

def sourceBody864_482 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_426 sourceBody864_481

def sourceBody864_483 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_422 sourceBody864_482

def sourceBody864_484 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_421 sourceBody864_483

def sourceBody864_485 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_473 sourceBody864_484

def sourceBody864_486 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody864_487 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody864_488 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 256#64)

def sourceBody864_489 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 74)) (some 79) ([10, 34, 22]) (some (10, sourceBody864_414, 864, 75))

def sourceBody864_490 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_489 sourceBody864_6

def sourceBody864_491 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_490 sourceBody864_0

def sourceBody864_492 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_488 sourceBody864_491

def sourceBody864_493 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_487 sourceBody864_492

def sourceBody864_494 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_486 sourceBody864_493

def sourceBody864_495 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_485 sourceBody864_494

def sourceBody864_496 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 114#64)

def sourceBody864_497 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_496 sourceBody864_431

def sourceBody864_498 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_497

def sourceBody864_499 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_498 sourceBody864_435

def sourceBody864_500 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.imm 0#64) sourceBody864_499 sourceBody864_0

def sourceBody864_501 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_500 sourceBody864_6

def sourceBody864_502 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_501 sourceBody864_0

def sourceBody864_503 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_427 sourceBody864_502

def sourceBody864_504 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_426 sourceBody864_503

def sourceBody864_505 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_422 sourceBody864_504

def sourceBody864_506 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_421 sourceBody864_505

def sourceBody864_507 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_495 sourceBody864_506

def sourceBody864_508 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 44)

def sourceBody864_509 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 192#64]))

def sourceBody864_510 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 76)) (some 79) ([10, 34, 22]) (some (10, sourceBody864_414, 864, 77))

def sourceBody864_511 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_510 sourceBody864_6

def sourceBody864_512 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_511 sourceBody864_0

def sourceBody864_513 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_413 sourceBody864_512

def sourceBody864_514 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_509 sourceBody864_513

def sourceBody864_515 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_508 sourceBody864_514

def sourceBody864_516 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_507 sourceBody864_515

def sourceBody864_517 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 115#64)

def sourceBody864_518 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_517 sourceBody864_431

def sourceBody864_519 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_518

def sourceBody864_520 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_519 sourceBody864_435

def sourceBody864_521 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.imm 0#64) sourceBody864_520 sourceBody864_0

def sourceBody864_522 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_521 sourceBody864_6

def sourceBody864_523 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_522 sourceBody864_0

def sourceBody864_524 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_427 sourceBody864_523

def sourceBody864_525 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_426 sourceBody864_524

def sourceBody864_526 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_422 sourceBody864_525

def sourceBody864_527 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_421 sourceBody864_526

def sourceBody864_528 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_516 sourceBody864_527

def sourceBody864_529 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
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
        Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody864_530 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 200#64]))

def sourceBody864_531 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.reg 22) sourceBody864_423 sourceBody864_424

def sourceBody864_532 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_531 sourceBody864_6

def sourceBody864_533 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 116#64)

def sourceBody864_534 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_533 sourceBody864_431

def sourceBody864_535 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_534

def sourceBody864_536 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_535 sourceBody864_435

def sourceBody864_537 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.imm 0#64) sourceBody864_536 sourceBody864_0

def sourceBody864_538 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_537 sourceBody864_6

def sourceBody864_539 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_538 sourceBody864_0

def sourceBody864_540 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_427 sourceBody864_539

def sourceBody864_541 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_532 sourceBody864_540

def sourceBody864_542 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_530 sourceBody864_541

def sourceBody864_543 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_529 sourceBody864_542

def sourceBody864_544 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_528 sourceBody864_543

def sourceBody864_545 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 224#64]))

def sourceBody864_546 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody864_0, 864, 78)) (some 79) ([10, 34, 22]) (some (10, sourceBody864_414, 864, 79))

def sourceBody864_547 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_546 sourceBody864_6

def sourceBody864_548 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_547 sourceBody864_0

def sourceBody864_549 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_413 sourceBody864_548

def sourceBody864_550 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_545 sourceBody864_549

def sourceBody864_551 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_354 sourceBody864_550

def sourceBody864_552 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_544 sourceBody864_551

def sourceBody864_553 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 117#64)

def sourceBody864_554 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_553 sourceBody864_431

def sourceBody864_555 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_554

def sourceBody864_556 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_555 sourceBody864_435

def sourceBody864_557 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.imm 0#64) sourceBody864_556 sourceBody864_0

def sourceBody864_558 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_557 sourceBody864_6

def sourceBody864_559 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_558 sourceBody864_0

def sourceBody864_560 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_427 sourceBody864_559

def sourceBody864_561 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_426 sourceBody864_560

def sourceBody864_562 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_422 sourceBody864_561

def sourceBody864_563 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_421 sourceBody864_562

def sourceBody864_564 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_552 sourceBody864_563

def sourceBody864_565 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 38)

def sourceBody864_566 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 232#64]))

def sourceBody864_567 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody864_0, 864, 80)) (some 79) ([10, 34, 22]) (some (10, sourceBody864_414, 864, 81))

def sourceBody864_568 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_567 sourceBody864_6

def sourceBody864_569 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_568 sourceBody864_0

def sourceBody864_570 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_413 sourceBody864_569

def sourceBody864_571 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_566 sourceBody864_570

def sourceBody864_572 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_565 sourceBody864_571

def sourceBody864_573 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_564 sourceBody864_572

def sourceBody864_574 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 118#64)

def sourceBody864_575 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_574 sourceBody864_431

def sourceBody864_576 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_575

def sourceBody864_577 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_576 sourceBody864_435

def sourceBody864_578 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.imm 0#64) sourceBody864_577 sourceBody864_0

def sourceBody864_579 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_578 sourceBody864_6

def sourceBody864_580 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_579 sourceBody864_0

def sourceBody864_581 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_427 sourceBody864_580

def sourceBody864_582 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_426 sourceBody864_581

def sourceBody864_583 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_422 sourceBody864_582

def sourceBody864_584 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_421 sourceBody864_583

def sourceBody864_585 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_573 sourceBody864_584

def sourceBody864_586 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody864_587 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_586 sourceBody864_0

def sourceBody864_588 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_391 sourceBody864_587

def sourceBody864_589 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_585 sourceBody864_588

def sourceBody864_590 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_420 sourceBody864_589

def sourceBody864_591 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_590

def sourceBody864_592 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_591

def sourceBody864_593 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_410 sourceBody864_592

def sourceBody864_594 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_387 sourceBody864_593

def sourceBody864_595 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_594

def sourceBody864_596 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_595

def sourceBody864_597 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_380 sourceBody864_596

def sourceBody864_598 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_368 sourceBody864_597

def sourceBody864_599 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_598

def sourceBody864_600 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_599

def sourceBody864_601 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_363 sourceBody864_600

def sourceBody864_602 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_351 sourceBody864_601

def sourceBody864_603 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_602

def sourceBody864_604 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_603

def sourceBody864_605 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_346 sourceBody864_604

def sourceBody864_606 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_334 sourceBody864_605

def sourceBody864_607 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_606

def sourceBody864_608 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_607

def sourceBody864_609 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_329 sourceBody864_608

def sourceBody864_610 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_319 sourceBody864_609

def sourceBody864_611 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_610

def sourceBody864_612 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_611

def sourceBody864_613 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_314 sourceBody864_612

def sourceBody864_614 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_302 sourceBody864_613

def sourceBody864_615 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_614

def sourceBody864_616 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_615

def sourceBody864_617 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_297 sourceBody864_616

def sourceBody864_618 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_285 sourceBody864_617

def sourceBody864_619 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_618

def sourceBody864_620 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_619

def sourceBody864_621 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_280 sourceBody864_620

def sourceBody864_622 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_272 sourceBody864_621

def sourceBody864_623 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_622

def sourceBody864_624 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_623

def sourceBody864_625 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_267 sourceBody864_624

def sourceBody864_626 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_259 sourceBody864_625

def sourceBody864_627 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_626

def sourceBody864_628 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_627

def sourceBody864_629 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_628

def sourceBody864_630 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_629

def sourceBody864_631 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_256 sourceBody864_630

def sourceBody864_632 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_141 sourceBody864_631

def sourceBody864_633 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_632

def sourceBody864_634 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_183 sourceBody864_633

def sourceBody864_635 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_634

def sourceBody864_636 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_182 sourceBody864_635

def sourceBody864_637 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_140 sourceBody864_636

def sourceBody864_638 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_637

def sourceBody864_639 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_139 sourceBody864_638

def sourceBody864_640 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_102 sourceBody864_639

def sourceBody864_641 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_640

def sourceBody864_642 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_641

def sourceBody864_643 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_94 sourceBody864_642

def sourceBody864_644 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_83 sourceBody864_643

def sourceBody864_645 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_644

def sourceBody864_646 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_645

def sourceBody864_647 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_77 sourceBody864_646

def sourceBody864_648 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_66 sourceBody864_647

def sourceBody864_649 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_648

def sourceBody864_650 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_649

def sourceBody864_651 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_58 sourceBody864_650

def sourceBody864_652 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_47 sourceBody864_651

def sourceBody864_653 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_652

def sourceBody864_654 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_653

def sourceBody864_655 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_41 sourceBody864_654

def sourceBody864_656 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_38 sourceBody864_655

def sourceBody864_657 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_656

def sourceBody864_658 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_657

def sourceBody864_659 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_33 sourceBody864_658

def sourceBody864_660 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_2 sourceBody864_659

def sourceBody864_661 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_660

def sourceBody864_662 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_1 sourceBody864_661

def sourceBody864_663 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody864_0 sourceBody864_662

def source864 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (864, 3, sourceBody864_663)
end InitECandidate.Proofs.WordStages
