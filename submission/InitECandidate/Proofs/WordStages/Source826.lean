import InitECandidate.Proofs.WordStages.Source810
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody826_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody826_1 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody826_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody826_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody826_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody826_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody826_0, 826, 2)) (some 461) ([12]) (some (12, sourceBody826_4, 826, 3))

def sourceBody826_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody826_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_5 sourceBody826_6

def sourceBody826_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_7 sourceBody826_0

def sourceBody826_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_3 sourceBody826_8

def sourceBody826_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody826_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody826_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 2 2 8 16))

def sourceBody826_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.const 15#64, Flapjack.WordLangExpHOL.var 2])

def sourceBody826_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody826_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody826_0, 826, 4)) (some 466) ([10]) (some (8, sourceBody826_14, 826, 5))

def sourceBody826_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_15 sourceBody826_6

def sourceBody826_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_16 sourceBody826_0

def sourceBody826_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_13 sourceBody826_17

def sourceBody826_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_12 sourceBody826_18

def sourceBody826_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_11 sourceBody826_19

def sourceBody826_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_10 sourceBody826_20

def sourceBody826_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_0 sourceBody826_21

def sourceBody826_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_0 sourceBody826_22

def sourceBody826_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 120#64])

def sourceBody826_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody826_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody826_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 12) 16

def sourceBody826_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_27 sourceBody826_0

def sourceBody826_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_26 sourceBody826_28

def sourceBody826_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_29 sourceBody826_0

def sourceBody826_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_25 sourceBody826_30

def sourceBody826_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_0 sourceBody826_31

def sourceBody826_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_24 sourceBody826_32

def sourceBody826_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_0 sourceBody826_33

def sourceBody826_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_23 sourceBody826_34

def sourceBody826_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody826_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody826_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_37 sourceBody826_30

def sourceBody826_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_0 sourceBody826_38

def sourceBody826_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_36 sourceBody826_39

def sourceBody826_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_0 sourceBody826_40

def sourceBody826_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_35 sourceBody826_41

def sourceBody826_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody826_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody826_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_44 sourceBody826_0

def sourceBody826_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_43 sourceBody826_45

def sourceBody826_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_42 sourceBody826_46

def sourceBody826_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_9 sourceBody826_47

def sourceBody826_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_0 sourceBody826_48

def sourceBody826_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_0 sourceBody826_49

def sourceBody826_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_2 sourceBody826_50

def sourceBody826_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_0 sourceBody826_51

def sourceBody826_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_1 sourceBody826_52

def sourceBody826_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody826_0 sourceBody826_53

def source826 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (826, 1, sourceBody826_54)
end InitECandidate.Proofs.WordStages
