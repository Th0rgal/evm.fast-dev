import InitECandidate.Proofs.WordStages.Source466
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody482_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 8])

def sourceBody482_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody482_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody482_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody482_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 18) sourceBody482_2 sourceBody482_3

def sourceBody482_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody482_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_4 sourceBody482_5

def sourceBody482_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody482_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody482_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody482_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody482_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_9 sourceBody482_10

def sourceBody482_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_8 sourceBody482_11

def sourceBody482_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody482_12 sourceBody482_10

def sourceBody482_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_13 sourceBody482_5

def sourceBody482_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_14 sourceBody482_10

def sourceBody482_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_7 sourceBody482_15

def sourceBody482_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_6 sourceBody482_16

def sourceBody482_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_1 sourceBody482_17

def sourceBody482_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_0 sourceBody482_18

def sourceBody482_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody482_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody482_22 : WordLangProgHOL (BitVec 64) :=
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
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody482_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody482_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 18 (Flapjack.WordRegImm.reg 10) sourceBody482_23 sourceBody482_1

def sourceBody482_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_24 sourceBody482_5

def sourceBody482_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody482_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody482_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_27 sourceBody482_10

def sourceBody482_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_3 sourceBody482_28

def sourceBody482_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody482_29 sourceBody482_10

def sourceBody482_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_30 sourceBody482_5

def sourceBody482_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_31 sourceBody482_10

def sourceBody482_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_26 sourceBody482_32

def sourceBody482_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_25 sourceBody482_33

def sourceBody482_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_22 sourceBody482_34

def sourceBody482_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_21 sourceBody482_35

def sourceBody482_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
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
        Flapjack.WordLangExpHOL.const 80#64]))

def sourceBody482_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
        (Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.var 12,
              Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 16)
                  (Flapjack.WordLangExpHOL.const 6#64))
                (Flapjack.WordLangExpHOL.const 3#64)]))
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
          [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 63#64]),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody482_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody482_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_39 sourceBody482_10

def sourceBody482_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_38 sourceBody482_40

def sourceBody482_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_37 sourceBody482_41

def sourceBody482_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_10 sourceBody482_42

def sourceBody482_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_36 sourceBody482_43

def sourceBody482_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_20 sourceBody482_44

def sourceBody482_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_10 sourceBody482_45

def sourceBody482_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody482_19 sourceBody482_46

def source482 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (482, 5, sourceBody482_47)
end InitECandidate.Proofs.WordStages
