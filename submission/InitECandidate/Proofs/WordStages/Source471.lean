import InitECandidate.Proofs.WordStages.Source455
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody471_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody471_1 : WordLangProgHOL (BitVec 64) :=
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
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody471_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody471_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody471_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody471_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody471_6 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 2 (Flapjack.WordRegImm.reg 8) sourceBody471_4 sourceBody471_5

def sourceBody471_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody471_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_6 sourceBody471_7

def sourceBody471_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody471_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody471_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 10)

def sourceBody471_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_11 sourceBody471_0

def sourceBody471_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_12 sourceBody471_0

def sourceBody471_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_10 sourceBody471_13

def sourceBody471_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_0 sourceBody471_14

def sourceBody471_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody471_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody471_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_16 sourceBody471_17

def sourceBody471_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_15 sourceBody471_18

def sourceBody471_20 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody471_19 sourceBody471_0

def sourceBody471_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_20 sourceBody471_7

def sourceBody471_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_21 sourceBody471_0

def sourceBody471_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_9 sourceBody471_22

def sourceBody471_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_8 sourceBody471_23

def sourceBody471_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_3 sourceBody471_24

def sourceBody471_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_2 sourceBody471_25

def sourceBody471_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody471_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody471_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_28 sourceBody471_0

def sourceBody471_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_29 sourceBody471_0

def sourceBody471_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_27 sourceBody471_30

def sourceBody471_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_0 sourceBody471_31

def sourceBody471_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_26 sourceBody471_32

def sourceBody471_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody471_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody471_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 8

def sourceBody471_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_36 sourceBody471_0

def sourceBody471_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_35 sourceBody471_37

def sourceBody471_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_38 sourceBody471_0

def sourceBody471_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_2 sourceBody471_39

def sourceBody471_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_0 sourceBody471_40

def sourceBody471_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_34 sourceBody471_41

def sourceBody471_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_0 sourceBody471_42

def sourceBody471_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_33 sourceBody471_43

def sourceBody471_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
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
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody471_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
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
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody471_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
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
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody471_48 : WordLangProgHOL (BitVec 64) :=
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
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody471_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10, 2, 8, 6]

def sourceBody471_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_49 sourceBody471_0

def sourceBody471_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_48 sourceBody471_50

def sourceBody471_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_47 sourceBody471_51

def sourceBody471_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_46 sourceBody471_52

def sourceBody471_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_45 sourceBody471_53

def sourceBody471_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_44 sourceBody471_54

def sourceBody471_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_1 sourceBody471_55

def sourceBody471_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody471_0 sourceBody471_56

def source471 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (471, 1, sourceBody471_57)
end InitECandidate.Proofs.WordStages
