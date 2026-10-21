import InitECandidate.Proofs.WordStages.Source800
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody816_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody816_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody816_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody816_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody816_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 4) sourceBody816_2 sourceBody816_3

def sourceBody816_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody816_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody816_4 sourceBody816_5

def sourceBody816_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody816_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 524#64)

def sourceBody816_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody816_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody816_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody816_9 sourceBody816_10

def sourceBody816_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody816_8 sourceBody816_11

def sourceBody816_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody816_12 sourceBody816_10

def sourceBody816_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody816_13 sourceBody816_5

def sourceBody816_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody816_14 sourceBody816_10

def sourceBody816_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody816_7 sourceBody816_15

def sourceBody816_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody816_6 sourceBody816_16

def sourceBody816_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody816_1 sourceBody816_17

def sourceBody816_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody816_0 sourceBody816_18

def sourceBody816_20 : WordLangProgHOL (BitVec 64) :=
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
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.const 128#64, Flapjack.WordLangExpHOL.var 2],
              Flapjack.WordLangExpHOL.const 1#64])
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody816_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody816_20 sourceBody816_11

def sourceBody816_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody816_19 sourceBody816_21

def source816 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (816, 2, sourceBody816_22)
end InitECandidate.Proofs.WordStages
