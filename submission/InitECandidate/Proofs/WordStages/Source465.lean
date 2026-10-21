import InitECandidate.Proofs.WordStages.Source449
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody465_0 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody465_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody465_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody465_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody465_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 4) sourceBody465_2 sourceBody465_3

def sourceBody465_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody465_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody465_4 sourceBody465_5

def sourceBody465_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody465_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody465_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody465_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 6)

def sourceBody465_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody465_10 sourceBody465_8

def sourceBody465_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody465_11 sourceBody465_8

def sourceBody465_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody465_9 sourceBody465_12

def sourceBody465_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody465_8 sourceBody465_13

def sourceBody465_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody465_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody465_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody465_15 sourceBody465_16

def sourceBody465_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody465_14 sourceBody465_17

def sourceBody465_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody465_18 sourceBody465_8

def sourceBody465_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody465_19 sourceBody465_5

def sourceBody465_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody465_20 sourceBody465_8

def sourceBody465_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody465_7 sourceBody465_21

def sourceBody465_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody465_6 sourceBody465_22

def sourceBody465_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody465_1 sourceBody465_23

def sourceBody465_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody465_0 sourceBody465_24

def sourceBody465_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody465_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody465_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody465_27 sourceBody465_8

def sourceBody465_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody465_26 sourceBody465_28

def sourceBody465_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody465_25 sourceBody465_29

def source465 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (465, 2, sourceBody465_30)
end InitECandidate.Proofs.WordStages
