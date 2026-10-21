import InitECandidate.Proofs.WordStages.Source520
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody536_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody536_1 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody536_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody536_3 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody536_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody536_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody536_6 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 2 (Flapjack.WordRegImm.reg 8) sourceBody536_4 sourceBody536_5

def sourceBody536_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody536_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody536_6 sourceBody536_7

def sourceBody536_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody536_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
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
            Flapjack.WordLangExpHOL.const 48#64]),
      Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody536_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 10 (Flapjack.WordLangAddr.addr 10 0#64))

def sourceBody536_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 10)

def sourceBody536_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [2]

def sourceBody536_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody536_13 sourceBody536_0

def sourceBody536_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody536_12 sourceBody536_14

def sourceBody536_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody536_11 sourceBody536_15

def sourceBody536_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody536_10 sourceBody536_16

def sourceBody536_18 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody536_17 sourceBody536_0

def sourceBody536_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody536_18 sourceBody536_7

def sourceBody536_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody536_19 sourceBody536_0

def sourceBody536_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody536_9 sourceBody536_20

def sourceBody536_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody536_8 sourceBody536_21

def sourceBody536_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody536_3 sourceBody536_22

def sourceBody536_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody536_2 sourceBody536_23

def sourceBody536_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody536_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody536_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody536_26 sourceBody536_0

def sourceBody536_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody536_25 sourceBody536_27

def sourceBody536_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody536_24 sourceBody536_28

def sourceBody536_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody536_1 sourceBody536_29

def sourceBody536_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody536_0 sourceBody536_30

def source536 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (536, 1, sourceBody536_31)
end InitECandidate.Proofs.WordStages
