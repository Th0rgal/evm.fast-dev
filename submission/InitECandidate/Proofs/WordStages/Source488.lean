import InitECandidate.Proofs.WordStages.Source472
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody488_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
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
              Flapjack.WordLangExpHOL.const 112#64]),
        Flapjack.WordLangExpHOL.const 144#64]))

def sourceBody488_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody488_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody488_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody488_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.reg 2) sourceBody488_2 sourceBody488_3

def sourceBody488_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody488_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody488_4 sourceBody488_5

def sourceBody488_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody488_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody488_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody488_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4)

def sourceBody488_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody488_10 sourceBody488_8

def sourceBody488_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody488_11 sourceBody488_8

def sourceBody488_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody488_9 sourceBody488_12

def sourceBody488_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody488_8 sourceBody488_13

def sourceBody488_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody488_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody488_9 sourceBody488_15

def sourceBody488_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody488_14 sourceBody488_16

def sourceBody488_18 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody488_17 sourceBody488_8

def sourceBody488_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody488_18 sourceBody488_5

def sourceBody488_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody488_19 sourceBody488_8

def sourceBody488_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody488_7 sourceBody488_20

def sourceBody488_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody488_6 sourceBody488_21

def sourceBody488_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody488_1 sourceBody488_22

def sourceBody488_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody488_0 sourceBody488_23

def sourceBody488_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody488_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody488_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody488_26 sourceBody488_8

def sourceBody488_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody488_25 sourceBody488_27

def sourceBody488_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody488_24 sourceBody488_28

def source488 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (488, 1, sourceBody488_29)
end InitECandidate.Proofs.WordStages
