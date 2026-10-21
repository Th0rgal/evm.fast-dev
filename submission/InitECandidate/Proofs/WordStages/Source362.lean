import InitECandidate.Proofs.WordStages.Source346
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody362_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody362_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 208#64]))

def sourceBody362_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 216#64]))

def sourceBody362_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody362_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody362_0, 362, 2)) (some 356) ([14, 6]) (some (14, sourceBody362_3, 362, 3))

def sourceBody362_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody362_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_4 sourceBody362_5

def sourceBody362_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_6 sourceBody362_0

def sourceBody362_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_2 sourceBody362_7

def sourceBody362_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_1 sourceBody362_8

def sourceBody362_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 272#64]))

def sourceBody362_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 280#64]))

def sourceBody362_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody362_13 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody362_0, 362, 4)) (some 360) ([6, 12]) (some (6, sourceBody362_12, 362, 5))

def sourceBody362_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_13 sourceBody362_5

def sourceBody362_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_14 sourceBody362_0

def sourceBody362_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_11 sourceBody362_15

def sourceBody362_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_10 sourceBody362_16

def sourceBody362_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 264#64]))

def sourceBody362_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 33#64)

def sourceBody362_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 10 10 6 12))

def sourceBody362_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_20 sourceBody362_0

def sourceBody362_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_19 sourceBody362_21

def sourceBody362_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_18 sourceBody362_22

def sourceBody362_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody362_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.const 64#64, Flapjack.WordLangExpHOL.const 561#64, Flapjack.WordLangExpHOL.const 30#64,
      Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 200#64]),
      Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.var 16])

def sourceBody362_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody362_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_26 sourceBody362_0

def sourceBody362_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_25 sourceBody362_27

def sourceBody362_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_24 sourceBody362_28

def sourceBody362_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_23 sourceBody362_29

def sourceBody362_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_17 sourceBody362_30

def sourceBody362_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_0 sourceBody362_31

def sourceBody362_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_0 sourceBody362_32

def sourceBody362_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_9 sourceBody362_33

def sourceBody362_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_0 sourceBody362_34

def sourceBody362_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody362_0 sourceBody362_35

def source362 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (362, 2, sourceBody362_36)
end InitECandidate.Proofs.WordStages
