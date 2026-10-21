import InitECandidate.Proofs.WordStages.Source580
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody596_0 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody596_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody596_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody596_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody596_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.reg 2) sourceBody596_2 sourceBody596_3

def sourceBody596_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody596_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody596_4 sourceBody596_5

def sourceBody596_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody596_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody596_9 : WordLangProgHOL (BitVec 64) :=
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
              Flapjack.WordLangExpHOL.const 288#64]),
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody596_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody596_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody596_8, 596, 2)) (some 387) ([8]) (some (8, sourceBody596_10, 596, 3))

def sourceBody596_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody596_11 sourceBody596_5

def sourceBody596_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody596_12 sourceBody596_8

def sourceBody596_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody596_9 sourceBody596_13

def sourceBody596_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody596_8 sourceBody596_14

def sourceBody596_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody596_8 sourceBody596_15

def sourceBody596_17 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody596_16 sourceBody596_8

def sourceBody596_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody596_17 sourceBody596_5

def sourceBody596_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody596_18 sourceBody596_8

def sourceBody596_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody596_7 sourceBody596_19

def sourceBody596_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody596_6 sourceBody596_20

def sourceBody596_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody596_1 sourceBody596_21

def sourceBody596_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody596_0 sourceBody596_22

def sourceBody596_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody596_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody596_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody596_25 sourceBody596_8

def sourceBody596_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody596_24 sourceBody596_26

def sourceBody596_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody596_23 sourceBody596_27

def source596 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (596, 1, sourceBody596_28)
end InitECandidate.Proofs.WordStages
