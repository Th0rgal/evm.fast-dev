import InitECandidate.Proofs.WordStages.Source754
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody770_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody770_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 14)

def sourceBody770_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 16)

def sourceBody770_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 18)

def sourceBody770_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 20)

def sourceBody770_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 22)

def sourceBody770_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 24)

def sourceBody770_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 74

def sourceBody770_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([68, 52, 82, 28, 58, 42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody770_0, 770, 2)) (some 711) ([74, 36, 66, 50, 80, 32]) (some (74, sourceBody770_7, 770, 3))

def sourceBody770_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody770_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_8 sourceBody770_9

def sourceBody770_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_10 sourceBody770_0

def sourceBody770_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_6 sourceBody770_11

def sourceBody770_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_5 sourceBody770_12

def sourceBody770_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_4 sourceBody770_13

def sourceBody770_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_3 sourceBody770_14

def sourceBody770_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_2 sourceBody770_15

def sourceBody770_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_1 sourceBody770_16

def sourceBody770_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 2)

def sourceBody770_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 4)

def sourceBody770_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 6)

def sourceBody770_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 8)

def sourceBody770_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 10)

def sourceBody770_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 12)

def sourceBody770_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 62

def sourceBody770_25 : WordLangProgHOL (BitVec 64) :=
.call (some (([74, 36, 66, 50, 80, 32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody770_0, 770, 4)) (some 711) ([62, 46, 76, 38, 70, 54]) (some (62, sourceBody770_24, 770, 5))

def sourceBody770_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_25 sourceBody770_9

def sourceBody770_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_26 sourceBody770_0

def sourceBody770_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_23 sourceBody770_27

def sourceBody770_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_22 sourceBody770_28

def sourceBody770_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_21 sourceBody770_29

def sourceBody770_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_20 sourceBody770_30

def sourceBody770_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_19 sourceBody770_31

def sourceBody770_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_18 sourceBody770_32

def sourceBody770_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 74)

def sourceBody770_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 36)

def sourceBody770_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 66)

def sourceBody770_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 50)

def sourceBody770_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 80)

def sourceBody770_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 32)

def sourceBody770_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 84 (Flapjack.WordLangExpHOL.var 2)

def sourceBody770_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 4)

def sourceBody770_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 6)

def sourceBody770_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 8)

def sourceBody770_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 10)

def sourceBody770_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 12)

def sourceBody770_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([74, 36, 66, 50, 80, 32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody770_0, 770, 6)) (some 710) ([62, 46, 76, 38, 70, 54, 84, 26, 56, 40, 72, 34]) (some (62, sourceBody770_24, 770, 7))

def sourceBody770_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_46 sourceBody770_9

def sourceBody770_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_47 sourceBody770_0

def sourceBody770_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_45 sourceBody770_48

def sourceBody770_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_44 sourceBody770_49

def sourceBody770_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_43 sourceBody770_50

def sourceBody770_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_42 sourceBody770_51

def sourceBody770_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_41 sourceBody770_52

def sourceBody770_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_40 sourceBody770_53

def sourceBody770_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_39 sourceBody770_54

def sourceBody770_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_38 sourceBody770_55

def sourceBody770_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_37 sourceBody770_56

def sourceBody770_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_36 sourceBody770_57

def sourceBody770_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_35 sourceBody770_58

def sourceBody770_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_34 sourceBody770_59

def sourceBody770_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 392#64]),
        Flapjack.WordLangExpHOL.const 240#64]))

def sourceBody770_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
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
                  Flapjack.WordLangExpHOL.const 392#64]),
            Flapjack.WordLangExpHOL.const 240#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody770_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76
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
                  Flapjack.WordLangExpHOL.const 392#64]),
            Flapjack.WordLangExpHOL.const 240#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody770_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
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
                  Flapjack.WordLangExpHOL.const 392#64]),
            Flapjack.WordLangExpHOL.const 240#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody770_65 : WordLangProgHOL (BitVec 64) :=
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
                  Flapjack.WordLangExpHOL.const 392#64]),
            Flapjack.WordLangExpHOL.const 240#64],
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody770_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
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
                  Flapjack.WordLangExpHOL.const 392#64]),
            Flapjack.WordLangExpHOL.const 240#64],
        Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody770_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 84 (Flapjack.WordLangExpHOL.var 74)

def sourceBody770_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 36)

def sourceBody770_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 66)

def sourceBody770_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 50)

def sourceBody770_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 80)

def sourceBody770_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 32)

def sourceBody770_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 62)

def sourceBody770_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 46)

def sourceBody770_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 76)

def sourceBody770_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 38)

def sourceBody770_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 70)

def sourceBody770_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 54)

def sourceBody770_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 84

def sourceBody770_80 : WordLangProgHOL (BitVec 64) :=
.call (some (([74, 36, 66, 50, 80, 32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody770_0, 770, 8)) (some 706) ([84, 26, 56, 40, 72, 34, 64, 48, 78, 30, 60, 44]) (some (84, sourceBody770_79, 770, 9))

def sourceBody770_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_80 sourceBody770_9

def sourceBody770_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_81 sourceBody770_0

def sourceBody770_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_78 sourceBody770_82

def sourceBody770_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_77 sourceBody770_83

def sourceBody770_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_76 sourceBody770_84

def sourceBody770_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_75 sourceBody770_85

def sourceBody770_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_74 sourceBody770_86

def sourceBody770_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_73 sourceBody770_87

def sourceBody770_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_72 sourceBody770_88

def sourceBody770_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_71 sourceBody770_89

def sourceBody770_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_70 sourceBody770_90

def sourceBody770_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_69 sourceBody770_91

def sourceBody770_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_68 sourceBody770_92

def sourceBody770_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_67 sourceBody770_93

def sourceBody770_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 84 (Flapjack.WordLangExpHOL.var 68)

def sourceBody770_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 52)

def sourceBody770_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 82)

def sourceBody770_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 28)

def sourceBody770_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 58)

def sourceBody770_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 42)

def sourceBody770_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 74)

def sourceBody770_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 36)

def sourceBody770_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 66)

def sourceBody770_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 50)

def sourceBody770_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 80)

def sourceBody770_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 32)

def sourceBody770_107 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 702) ([0, 84, 26, 56, 40, 72, 34, 64, 48, 78, 30, 60, 44]) (none)

def sourceBody770_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_107 sourceBody770_0

def sourceBody770_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_106 sourceBody770_108

def sourceBody770_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_105 sourceBody770_109

def sourceBody770_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_104 sourceBody770_110

def sourceBody770_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_103 sourceBody770_111

def sourceBody770_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_102 sourceBody770_112

def sourceBody770_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_101 sourceBody770_113

def sourceBody770_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_100 sourceBody770_114

def sourceBody770_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_99 sourceBody770_115

def sourceBody770_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_98 sourceBody770_116

def sourceBody770_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_97 sourceBody770_117

def sourceBody770_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_96 sourceBody770_118

def sourceBody770_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_95 sourceBody770_119

def sourceBody770_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_94 sourceBody770_120

def sourceBody770_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_66 sourceBody770_121

def sourceBody770_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_122

def sourceBody770_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_65 sourceBody770_123

def sourceBody770_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_124

def sourceBody770_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_64 sourceBody770_125

def sourceBody770_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_126

def sourceBody770_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_63 sourceBody770_127

def sourceBody770_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_128

def sourceBody770_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_62 sourceBody770_129

def sourceBody770_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_130

def sourceBody770_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_61 sourceBody770_131

def sourceBody770_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_132

def sourceBody770_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_60 sourceBody770_133

def sourceBody770_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_33 sourceBody770_134

def sourceBody770_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_135

def sourceBody770_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_136

def sourceBody770_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_137

def sourceBody770_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_138

def sourceBody770_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_139

def sourceBody770_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_140

def sourceBody770_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_141

def sourceBody770_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_142

def sourceBody770_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_143

def sourceBody770_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_144

def sourceBody770_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_145

def sourceBody770_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_146

def sourceBody770_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_17 sourceBody770_147

def sourceBody770_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_148

def sourceBody770_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_149

def sourceBody770_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_150

def sourceBody770_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_151

def sourceBody770_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_152

def sourceBody770_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_153

def sourceBody770_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_154

def sourceBody770_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_155

def sourceBody770_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_156

def sourceBody770_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_157

def sourceBody770_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_158

def sourceBody770_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody770_0 sourceBody770_159

def source770 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (770, 13, sourceBody770_160)
end InitECandidate.Proofs.WordStages
