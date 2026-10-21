import InitECandidate.Proofs.WordStages.Source450
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody466_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody466_1 : WordLangProgHOL (BitVec 64) :=
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
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody466_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody466_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody466_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody466_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody466_6 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 4 (Flapjack.WordRegImm.reg 10) sourceBody466_4 sourceBody466_5

def sourceBody466_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody466_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_6 sourceBody466_7

def sourceBody466_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody466_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody466_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 12)

def sourceBody466_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_11 sourceBody466_0

def sourceBody466_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_12 sourceBody466_0

def sourceBody466_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_10 sourceBody466_13

def sourceBody466_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_0 sourceBody466_14

def sourceBody466_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody466_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody466_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_16 sourceBody466_17

def sourceBody466_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_15 sourceBody466_18

def sourceBody466_20 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody466_19 sourceBody466_0

def sourceBody466_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_20 sourceBody466_7

def sourceBody466_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_21 sourceBody466_0

def sourceBody466_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_9 sourceBody466_22

def sourceBody466_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_8 sourceBody466_23

def sourceBody466_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_3 sourceBody466_24

def sourceBody466_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_2 sourceBody466_25

def sourceBody466_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 64#64])

def sourceBody466_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 2])

def sourceBody466_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody466_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 12) 10

def sourceBody466_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_30 sourceBody466_0

def sourceBody466_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_29 sourceBody466_31

def sourceBody466_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_32 sourceBody466_0

def sourceBody466_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_28 sourceBody466_33

def sourceBody466_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_0 sourceBody466_34

def sourceBody466_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_27 sourceBody466_35

def sourceBody466_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_0 sourceBody466_36

def sourceBody466_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_26 sourceBody466_37

def sourceBody466_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 184#64])

def sourceBody466_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
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
            Flapjack.WordLangExpHOL.const 184#64]),
      Flapjack.WordLangExpHOL.var 2])

def sourceBody466_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_40 sourceBody466_33

def sourceBody466_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_0 sourceBody466_41

def sourceBody466_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_39 sourceBody466_42

def sourceBody466_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_0 sourceBody466_43

def sourceBody466_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_38 sourceBody466_44

def sourceBody466_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody466_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody466_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_47 sourceBody466_0

def sourceBody466_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_46 sourceBody466_48

def sourceBody466_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_45 sourceBody466_49

def sourceBody466_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_1 sourceBody466_50

def sourceBody466_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody466_0 sourceBody466_51

def source466 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (466, 2, sourceBody466_52)
end InitECandidate.Proofs.WordStages
