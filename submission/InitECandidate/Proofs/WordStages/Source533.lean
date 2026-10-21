import InitECandidate.Proofs.WordStages.Source517
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody533_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody533_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody533_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody533_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody533_0, 533, 2)) (some 466) ([18]) (some (18, sourceBody533_2, 533, 3))

def sourceBody533_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody533_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_3 sourceBody533_4

def sourceBody533_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_5 sourceBody533_0

def sourceBody533_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_1 sourceBody533_6

def sourceBody533_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_0 sourceBody533_7

def sourceBody533_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_0 sourceBody533_8

def sourceBody533_10 : WordLangProgHOL (BitVec 64) :=
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
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody533_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody533_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody533_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody533_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody533_15 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 6 (Flapjack.WordRegImm.reg 16) sourceBody533_13 sourceBody533_14

def sourceBody533_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_15 sourceBody533_4

def sourceBody533_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody533_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody533_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 18)

def sourceBody533_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_19 sourceBody533_0

def sourceBody533_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_20 sourceBody533_0

def sourceBody533_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_18 sourceBody533_21

def sourceBody533_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_0 sourceBody533_22

def sourceBody533_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody533_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_24 sourceBody533_2

def sourceBody533_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_23 sourceBody533_25

def sourceBody533_27 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody533_26 sourceBody533_0

def sourceBody533_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_27 sourceBody533_4

def sourceBody533_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_28 sourceBody533_0

def sourceBody533_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_17 sourceBody533_29

def sourceBody533_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_16 sourceBody533_30

def sourceBody533_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_12 sourceBody533_31

def sourceBody533_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_11 sourceBody533_32

def sourceBody533_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
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
              Flapjack.WordLangExpHOL.const 8#64]),
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64],
              Flapjack.WordLangExpHOL.var 2])
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody533_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
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
                  Flapjack.WordLangExpHOL.const 8#64]),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                    [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64],
                  Flapjack.WordLangExpHOL.var 2])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody533_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
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
                  Flapjack.WordLangExpHOL.const 8#64]),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                    [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64],
                  Flapjack.WordLangExpHOL.var 2])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody533_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
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
                  Flapjack.WordLangExpHOL.const 8#64]),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                    [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64],
                  Flapjack.WordLangExpHOL.var 2])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody533_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 18)

def sourceBody533_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody533_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody533_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody533_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody533_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody533_0, 533, 4)) (some 472) ([4, 14, 10, 20]) (some (4, sourceBody533_42, 533, 5))

def sourceBody533_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_43 sourceBody533_4

def sourceBody533_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_44 sourceBody533_0

def sourceBody533_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_41 sourceBody533_45

def sourceBody533_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_40 sourceBody533_46

def sourceBody533_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_39 sourceBody533_47

def sourceBody533_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_38 sourceBody533_48

def sourceBody533_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_0 sourceBody533_49

def sourceBody533_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_0 sourceBody533_50

def sourceBody533_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody533_53 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody533_0, 533, 6)) (some 486) ([4]) (some (4, sourceBody533_42, 533, 7))

def sourceBody533_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_53 sourceBody533_4

def sourceBody533_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_54 sourceBody533_0

def sourceBody533_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_52 sourceBody533_55

def sourceBody533_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_0 sourceBody533_56

def sourceBody533_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_0 sourceBody533_57

def sourceBody533_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_51 sourceBody533_58

def sourceBody533_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody533_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [22]

def sourceBody533_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_61 sourceBody533_0

def sourceBody533_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_60 sourceBody533_62

def sourceBody533_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_59 sourceBody533_63

def sourceBody533_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_37 sourceBody533_64

def sourceBody533_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_0 sourceBody533_65

def sourceBody533_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_36 sourceBody533_66

def sourceBody533_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_0 sourceBody533_67

def sourceBody533_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_35 sourceBody533_68

def sourceBody533_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_0 sourceBody533_69

def sourceBody533_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_34 sourceBody533_70

def sourceBody533_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_0 sourceBody533_71

def sourceBody533_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_33 sourceBody533_72

def sourceBody533_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_10 sourceBody533_73

def sourceBody533_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_0 sourceBody533_74

def sourceBody533_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody533_9 sourceBody533_75

def source533 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (533, 2, sourceBody533_76)
end InitECandidate.Proofs.WordStages
