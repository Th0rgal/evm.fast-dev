import InitECandidate.Proofs.WordStages.Source747
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody763_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody763_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody763_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody763_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody763_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody763_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64],
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody763_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64],
        Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody763_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody763_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody763_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody763_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody763_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody763_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 26)

def sourceBody763_13 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 701) ([0, 4, 16, 12, 24, 8, 20]) (none)

def sourceBody763_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_13 sourceBody763_0

def sourceBody763_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_12 sourceBody763_14

def sourceBody763_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_11 sourceBody763_15

def sourceBody763_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_10 sourceBody763_16

def sourceBody763_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_9 sourceBody763_17

def sourceBody763_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_8 sourceBody763_18

def sourceBody763_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_7 sourceBody763_19

def sourceBody763_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_6 sourceBody763_20

def sourceBody763_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_0 sourceBody763_21

def sourceBody763_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_5 sourceBody763_22

def sourceBody763_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_0 sourceBody763_23

def sourceBody763_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_4 sourceBody763_24

def sourceBody763_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_0 sourceBody763_25

def sourceBody763_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_3 sourceBody763_26

def sourceBody763_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_0 sourceBody763_27

def sourceBody763_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_2 sourceBody763_28

def sourceBody763_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_0 sourceBody763_29

def sourceBody763_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_1 sourceBody763_30

def sourceBody763_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody763_0 sourceBody763_31

def source763 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (763, 2, sourceBody763_32)
end InitECandidate.Proofs.WordStages
