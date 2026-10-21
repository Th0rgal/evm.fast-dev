import InitECandidate.Proofs.WordStages.Source799
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody815_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody815_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody815_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody815_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody815_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 4) sourceBody815_2 sourceBody815_3

def sourceBody815_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody815_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody815_4 sourceBody815_5

def sourceBody815_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody815_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 519#64)

def sourceBody815_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody815_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody815_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody815_9 sourceBody815_10

def sourceBody815_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody815_8 sourceBody815_11

def sourceBody815_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody815_12 sourceBody815_10

def sourceBody815_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody815_13 sourceBody815_5

def sourceBody815_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody815_14 sourceBody815_10

def sourceBody815_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody815_7 sourceBody815_15

def sourceBody815_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody815_6 sourceBody815_16

def sourceBody815_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody815_1 sourceBody815_17

def sourceBody815_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody815_0 sourceBody815_18

def sourceBody815_20 : WordLangProgHOL (BitVec 64) :=
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
              Flapjack.WordLangExpHOL.const 400#64]),
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 1#64])
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody815_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody815_20 sourceBody815_11

def sourceBody815_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody815_19 sourceBody815_21

def source815 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (815, 2, sourceBody815_22)
end InitECandidate.Proofs.WordStages
