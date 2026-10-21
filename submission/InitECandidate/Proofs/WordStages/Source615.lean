import InitECandidate.Proofs.WordStages.Source599
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody615_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody615_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 264#64]))

def sourceBody615_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 48)

def sourceBody615_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody615_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 60

def sourceBody615_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([72]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody615_0, 615, 2)) (some 609) ([60, 82]) (some (60, sourceBody615_4, 615, 3))

def sourceBody615_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody615_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_5 sourceBody615_6

def sourceBody615_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_7 sourceBody615_0

def sourceBody615_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_3 sourceBody615_8

def sourceBody615_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_2 sourceBody615_9

def sourceBody615_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_10

def sourceBody615_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_11

def sourceBody615_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72
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

def sourceBody615_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.const 1024#64)

def sourceBody615_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 72, Flapjack.WordLangExpHOL.const 128#64]),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody615_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody615_17 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 82 (Flapjack.WordRegImm.reg 44) sourceBody615_16 sourceBody615_3

def sourceBody615_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_17 sourceBody615_6

def sourceBody615_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 82)

def sourceBody615_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 64#64])

def sourceBody615_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 256#64]),
            Flapjack.WordLangExpHOL.const 64#64]),
      Flapjack.WordLangExpHOL.var 2])

def sourceBody615_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 82)

def sourceBody615_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 60) 44

def sourceBody615_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_23 sourceBody615_0

def sourceBody615_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_22 sourceBody615_24

def sourceBody615_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_25 sourceBody615_0

def sourceBody615_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_21 sourceBody615_26

def sourceBody615_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_27

def sourceBody615_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_20 sourceBody615_28

def sourceBody615_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_29

def sourceBody615_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 72#64])

def sourceBody615_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 256#64]),
            Flapjack.WordLangExpHOL.const 72#64]),
      Flapjack.WordLangExpHOL.var 4])

def sourceBody615_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_32 sourceBody615_26

def sourceBody615_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_33

def sourceBody615_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_31 sourceBody615_34

def sourceBody615_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_35

def sourceBody615_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_30 sourceBody615_36

def sourceBody615_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.var 38)

def sourceBody615_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody615_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 82 (Flapjack.WordRegImm.reg 44) sourceBody615_16 sourceBody615_3

def sourceBody615_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_40 sourceBody615_6

def sourceBody615_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.const 183600#64)

def sourceBody615_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 82

def sourceBody615_44 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody615_0, 615, 4)) (some 468) ([82]) (some (82, sourceBody615_43, 615, 5))

def sourceBody615_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_44 sourceBody615_6

def sourceBody615_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_45 sourceBody615_0

def sourceBody615_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_42 sourceBody615_46

def sourceBody615_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_47

def sourceBody615_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_48

def sourceBody615_50 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 68 (Flapjack.WordRegImm.imm 0#64) sourceBody615_49 sourceBody615_0

def sourceBody615_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_50 sourceBody615_6

def sourceBody615_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_51 sourceBody615_0

def sourceBody615_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_19 sourceBody615_52

def sourceBody615_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_41 sourceBody615_53

def sourceBody615_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_39 sourceBody615_54

def sourceBody615_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_38 sourceBody615_55

def sourceBody615_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_37 sourceBody615_56

def sourceBody615_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody615_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody615_60 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody615_0, 615, 6)) (some 472) ([82, 44, 68, 56]) (some (82, sourceBody615_43, 615, 7))

def sourceBody615_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_60 sourceBody615_6

def sourceBody615_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_61 sourceBody615_0

def sourceBody615_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_59 sourceBody615_62

def sourceBody615_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_58 sourceBody615_63

def sourceBody615_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_39 sourceBody615_64

def sourceBody615_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_3 sourceBody615_65

def sourceBody615_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_66

def sourceBody615_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_67

def sourceBody615_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_57 sourceBody615_68

def sourceBody615_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody615_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [60]

def sourceBody615_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_71 sourceBody615_0

def sourceBody615_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_70 sourceBody615_72

def sourceBody615_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_69 sourceBody615_73

def sourceBody615_75 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 68 (Flapjack.WordRegImm.imm 0#64) sourceBody615_74 sourceBody615_0

def sourceBody615_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_75 sourceBody615_6

def sourceBody615_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_76 sourceBody615_0

def sourceBody615_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_19 sourceBody615_77

def sourceBody615_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_18 sourceBody615_78

def sourceBody615_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_15 sourceBody615_79

def sourceBody615_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_14 sourceBody615_80

def sourceBody615_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 256#64]),
            Flapjack.WordLangExpHOL.const 24#64]),
      Flapjack.WordLangExpHOL.var 24])

def sourceBody615_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody615_84 : WordLangProgHOL (BitVec 64) :=
.call (some (([82]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody615_0, 615, 8)) (some 75) ([]) (some (44, sourceBody615_83, 615, 9))

def sourceBody615_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_84 sourceBody615_6

def sourceBody615_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_85 sourceBody615_0

def sourceBody615_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 68

def sourceBody615_88 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
            (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody615_0, 615, 10)) (some 72) ([]) (some (68, sourceBody615_87, 615, 11))

def sourceBody615_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_88 sourceBody615_6

def sourceBody615_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_89 sourceBody615_0

def sourceBody615_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 14)

def sourceBody615_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 16)

def sourceBody615_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 16)

def sourceBody615_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 2)

def sourceBody615_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 4)

def sourceBody615_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 84 (Flapjack.WordLangExpHOL.var 6)

def sourceBody615_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 8)

def sourceBody615_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 10)

def sourceBody615_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 12)

def sourceBody615_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 60)

def sourceBody615_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 26)

def sourceBody615_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 18)

def sourceBody615_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 32)

def sourceBody615_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 34)

def sourceBody615_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 20)

def sourceBody615_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 22)

def sourceBody615_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 36)

def sourceBody615_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 56

def sourceBody615_109 : WordLangProgHOL (BitVec 64) :=
.call (some (([68]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody615_0, 615, 12)) (some 608) ([56, 78, 50, 74, 62, 84, 40, 64, 52, 76, 46, 70, 58, 80, 42, 66, 54]) (some (56, sourceBody615_108, 615, 13))

def sourceBody615_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_109 sourceBody615_6

def sourceBody615_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_110 sourceBody615_0

def sourceBody615_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_107 sourceBody615_111

def sourceBody615_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_106 sourceBody615_112

def sourceBody615_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_105 sourceBody615_113

def sourceBody615_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_104 sourceBody615_114

def sourceBody615_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_103 sourceBody615_115

def sourceBody615_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_102 sourceBody615_116

def sourceBody615_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_101 sourceBody615_117

def sourceBody615_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_100 sourceBody615_118

def sourceBody615_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_99 sourceBody615_119

def sourceBody615_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_98 sourceBody615_120

def sourceBody615_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_97 sourceBody615_121

def sourceBody615_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_96 sourceBody615_122

def sourceBody615_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_95 sourceBody615_123

def sourceBody615_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_94 sourceBody615_124

def sourceBody615_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_93 sourceBody615_125

def sourceBody615_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_92 sourceBody615_126

def sourceBody615_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_91 sourceBody615_127

def sourceBody615_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 68)

def sourceBody615_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody615_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 82)

def sourceBody615_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 44)

def sourceBody615_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 84 (Flapjack.WordLangExpHOL.var 38)

def sourceBody615_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 28)

def sourceBody615_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 30)

def sourceBody615_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody615_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 78

def sourceBody615_138 : WordLangProgHOL (BitVec 64) :=
.call (some (([56]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody615_0, 615, 14)) (some 599) ([78, 50, 74, 62, 84, 40, 64, 52]) (some (78, sourceBody615_137, 615, 15))

def sourceBody615_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_138 sourceBody615_6

def sourceBody615_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_139 sourceBody615_0

def sourceBody615_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_136 sourceBody615_140

def sourceBody615_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_135 sourceBody615_141

def sourceBody615_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_134 sourceBody615_142

def sourceBody615_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_133 sourceBody615_143

def sourceBody615_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_132 sourceBody615_144

def sourceBody615_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_131 sourceBody615_145

def sourceBody615_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_130 sourceBody615_146

def sourceBody615_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_129 sourceBody615_147

def sourceBody615_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_148

def sourceBody615_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_149

def sourceBody615_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody615_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [56]

def sourceBody615_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_152 sourceBody615_0

def sourceBody615_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_151 sourceBody615_153

def sourceBody615_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_150 sourceBody615_154

def sourceBody615_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_128 sourceBody615_155

def sourceBody615_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_156

def sourceBody615_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_157

def sourceBody615_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_90 sourceBody615_158

def sourceBody615_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_159

def sourceBody615_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_160

def sourceBody615_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_86 sourceBody615_161

def sourceBody615_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_162

def sourceBody615_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_163

def sourceBody615_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_82 sourceBody615_164

def sourceBody615_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_165

def sourceBody615_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_81 sourceBody615_166

def sourceBody615_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_13 sourceBody615_167

def sourceBody615_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_168

def sourceBody615_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_12 sourceBody615_169

def sourceBody615_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_1 sourceBody615_170

def sourceBody615_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody615_0 sourceBody615_171

def source615 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (615, 20, sourceBody615_172)
end InitECandidate.Proofs.WordStages
