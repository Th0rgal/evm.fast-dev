import InitECandidate.Proofs.WordStages.Source636
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody652_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody652_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody652_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 6900#64)

def sourceBody652_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody652_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([58]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody652_0, 652, 2)) (some 466) ([10]) (some (10, sourceBody652_3, 652, 3))

def sourceBody652_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody652_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_4 sourceBody652_5

def sourceBody652_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_6 sourceBody652_0

def sourceBody652_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_2 sourceBody652_7

def sourceBody652_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_8

def sourceBody652_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_9

def sourceBody652_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody652_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([58]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody652_0, 652, 4)) (some 68) ([10]) (some (10, sourceBody652_3, 652, 5))

def sourceBody652_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_12 sourceBody652_5

def sourceBody652_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_13 sourceBody652_0

def sourceBody652_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_11 sourceBody652_14

def sourceBody652_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 120#64])

def sourceBody652_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 58)

def sourceBody652_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 48)

def sourceBody652_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 30

def sourceBody652_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_19 sourceBody652_0

def sourceBody652_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_18 sourceBody652_20

def sourceBody652_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_21 sourceBody652_0

def sourceBody652_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_17 sourceBody652_22

def sourceBody652_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_23

def sourceBody652_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_16 sourceBody652_24

def sourceBody652_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_25

def sourceBody652_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody652_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody652_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_28 sourceBody652_22

def sourceBody652_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_29

def sourceBody652_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_27 sourceBody652_30

def sourceBody652_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_31

def sourceBody652_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_26 sourceBody652_32

def sourceBody652_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody652_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 10)

def sourceBody652_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.const 160#64)

def sourceBody652_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody652_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody652_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.reg 68) sourceBody652_37 sourceBody652_38

def sourceBody652_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_39 sourceBody652_5

def sourceBody652_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 30)

def sourceBody652_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [48]

def sourceBody652_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_42 sourceBody652_0

def sourceBody652_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_28 sourceBody652_43

def sourceBody652_45 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody652_44 sourceBody652_0

def sourceBody652_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_45 sourceBody652_5

def sourceBody652_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_46 sourceBody652_0

def sourceBody652_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_41 sourceBody652_47

def sourceBody652_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_40 sourceBody652_48

def sourceBody652_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_36 sourceBody652_49

def sourceBody652_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_35 sourceBody652_50

def sourceBody652_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody652_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody652_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody652_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody652_56 : WordLangProgHOL (BitVec 64) :=
.call (some (([30, 68, 6, 44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody652_0, 652, 6)) (some 146) ([26, 64]) (some (26, sourceBody652_55, 652, 7))

def sourceBody652_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_56 sourceBody652_5

def sourceBody652_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_57 sourceBody652_0

def sourceBody652_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_54 sourceBody652_58

def sourceBody652_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_53 sourceBody652_59

def sourceBody652_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody652_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody652_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody652_64 : WordLangProgHOL (BitVec 64) :=
.call (some (([26, 64, 16, 54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody652_0, 652, 8)) (some 146) ([36, 74]) (some (36, sourceBody652_63, 652, 9))

def sourceBody652_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_64 sourceBody652_5

def sourceBody652_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_65 sourceBody652_0

def sourceBody652_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_62 sourceBody652_66

def sourceBody652_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_61 sourceBody652_67

def sourceBody652_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody652_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody652_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody652_72 : WordLangProgHOL (BitVec 64) :=
.call (some (([36, 74, 4, 42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody652_0, 652, 10)) (some 146) ([24, 62]) (some (24, sourceBody652_71, 652, 11))

def sourceBody652_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_72 sourceBody652_5

def sourceBody652_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_73 sourceBody652_0

def sourceBody652_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_70 sourceBody652_74

def sourceBody652_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_69 sourceBody652_75

def sourceBody652_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 128#64])

def sourceBody652_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody652_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody652_80 : WordLangProgHOL (BitVec 64) :=
.call (some (([24, 62, 14, 52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bn
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody652_0, 652, 12)) (some 146) ([34, 72]) (some (34, sourceBody652_79, 652, 13))

def sourceBody652_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_80 sourceBody652_5

def sourceBody652_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_81 sourceBody652_0

def sourceBody652_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_78 sourceBody652_82

def sourceBody652_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_77 sourceBody652_83

def sourceBody652_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 48)

def sourceBody652_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 30)

def sourceBody652_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 68)

def sourceBody652_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 6)

def sourceBody652_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 44)

def sourceBody652_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 26)

def sourceBody652_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 64)

def sourceBody652_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 16)

def sourceBody652_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 54)

def sourceBody652_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 36)

def sourceBody652_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 74)

def sourceBody652_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 4)

def sourceBody652_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 42)

def sourceBody652_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 24)

def sourceBody652_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 62)

def sourceBody652_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 14)

def sourceBody652_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 52)

def sourceBody652_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 72

def sourceBody652_103 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody652_0, 652, 14)) (some 651) ([72, 8, 46, 28, 66, 18, 56, 38, 76, 2, 40, 22, 60, 12, 50, 32, 70]) (some (72, sourceBody652_102, 652, 15))

def sourceBody652_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_103 sourceBody652_5

def sourceBody652_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_104 sourceBody652_0

def sourceBody652_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_101 sourceBody652_105

def sourceBody652_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_100 sourceBody652_106

def sourceBody652_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_99 sourceBody652_107

def sourceBody652_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_98 sourceBody652_108

def sourceBody652_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_97 sourceBody652_109

def sourceBody652_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_96 sourceBody652_110

def sourceBody652_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_95 sourceBody652_111

def sourceBody652_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_94 sourceBody652_112

def sourceBody652_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_93 sourceBody652_113

def sourceBody652_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_92 sourceBody652_114

def sourceBody652_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_91 sourceBody652_115

def sourceBody652_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_90 sourceBody652_116

def sourceBody652_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_89 sourceBody652_117

def sourceBody652_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_88 sourceBody652_118

def sourceBody652_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_87 sourceBody652_119

def sourceBody652_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_86 sourceBody652_120

def sourceBody652_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_85 sourceBody652_121

def sourceBody652_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 34)

def sourceBody652_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody652_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody652_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody652_127 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 8 (Flapjack.WordRegImm.reg 46) sourceBody652_125 sourceBody652_126

def sourceBody652_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_127 sourceBody652_5

def sourceBody652_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 8)

def sourceBody652_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody652_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody652_132 : WordLangProgHOL (BitVec 64) :=
.call (some (([72]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody652_0, 652, 16)) (some 68) ([8]) (some (8, sourceBody652_131, 652, 17))

def sourceBody652_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_132 sourceBody652_5

def sourceBody652_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_133 sourceBody652_0

def sourceBody652_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_130 sourceBody652_134

def sourceBody652_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 72)

def sourceBody652_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody652_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody652_139 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody652_0, 652, 18)) (some 78) ([46, 28]) (some (46, sourceBody652_138, 652, 19))

def sourceBody652_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_139 sourceBody652_5

def sourceBody652_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_140 sourceBody652_0

def sourceBody652_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_137 sourceBody652_141

def sourceBody652_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_136 sourceBody652_142

def sourceBody652_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_143

def sourceBody652_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_144

def sourceBody652_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 72, Flapjack.WordLangExpHOL.const 31#64])

def sourceBody652_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 46 (Flapjack.WordLangAddr.addr 8 0#64))

def sourceBody652_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_147 sourceBody652_0

def sourceBody652_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_124 sourceBody652_148

def sourceBody652_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_146 sourceBody652_149

def sourceBody652_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_145 sourceBody652_150

def sourceBody652_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 120#64])

def sourceBody652_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 46)

def sourceBody652_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 28

def sourceBody652_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_154 sourceBody652_0

def sourceBody652_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_153 sourceBody652_155

def sourceBody652_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_156 sourceBody652_0

def sourceBody652_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_136 sourceBody652_157

def sourceBody652_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_158

def sourceBody652_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_152 sourceBody652_159

def sourceBody652_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_160

def sourceBody652_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_151 sourceBody652_161

def sourceBody652_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody652_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody652_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_164 sourceBody652_157

def sourceBody652_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_165

def sourceBody652_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_163 sourceBody652_166

def sourceBody652_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_167

def sourceBody652_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_162 sourceBody652_168

def sourceBody652_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_135 sourceBody652_169

def sourceBody652_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_170

def sourceBody652_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_171

def sourceBody652_173 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody652_172 sourceBody652_0

def sourceBody652_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_173 sourceBody652_5

def sourceBody652_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_174 sourceBody652_0

def sourceBody652_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_129 sourceBody652_175

def sourceBody652_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_128 sourceBody652_176

def sourceBody652_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_124 sourceBody652_177

def sourceBody652_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_123 sourceBody652_178

def sourceBody652_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody652_181 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [72]

def sourceBody652_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_181 sourceBody652_0

def sourceBody652_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_180 sourceBody652_182

def sourceBody652_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_179 sourceBody652_183

def sourceBody652_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_122 sourceBody652_184

def sourceBody652_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_185

def sourceBody652_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_186

def sourceBody652_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_84 sourceBody652_187

def sourceBody652_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_188

def sourceBody652_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_189

def sourceBody652_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_190

def sourceBody652_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_191

def sourceBody652_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_192

def sourceBody652_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_193

def sourceBody652_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_194

def sourceBody652_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_195

def sourceBody652_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_76 sourceBody652_196

def sourceBody652_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_197

def sourceBody652_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_198

def sourceBody652_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_199

def sourceBody652_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_200

def sourceBody652_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_201

def sourceBody652_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_202

def sourceBody652_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_203

def sourceBody652_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_204

def sourceBody652_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_68 sourceBody652_205

def sourceBody652_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_206

def sourceBody652_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_207

def sourceBody652_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_208

def sourceBody652_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_209

def sourceBody652_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_210

def sourceBody652_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_211

def sourceBody652_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_212

def sourceBody652_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_213

def sourceBody652_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_60 sourceBody652_214

def sourceBody652_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_215

def sourceBody652_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_216

def sourceBody652_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_217

def sourceBody652_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_218

def sourceBody652_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_219

def sourceBody652_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_220

def sourceBody652_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_221

def sourceBody652_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_222

def sourceBody652_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_52 sourceBody652_223

def sourceBody652_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_224

def sourceBody652_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_51 sourceBody652_225

def sourceBody652_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_34 sourceBody652_226

def sourceBody652_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_227

def sourceBody652_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_33 sourceBody652_228

def sourceBody652_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_15 sourceBody652_229

def sourceBody652_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_230

def sourceBody652_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_231

def sourceBody652_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_10 sourceBody652_232

def sourceBody652_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_1 sourceBody652_233

def sourceBody652_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody652_0 sourceBody652_234

def source652 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (652, 1, sourceBody652_235)
end InitECandidate.Proofs.WordStages
