import InitECandidate.Proofs.WordStages.Source422
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody438_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody438_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody438_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody438_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody438_0, 438, 2)) (some 435) ([6]) (some (6, sourceBody438_2, 438, 3))

def sourceBody438_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody438_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody438_3 sourceBody438_4

def sourceBody438_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody438_5 sourceBody438_0

def sourceBody438_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody438_1 sourceBody438_6

def sourceBody438_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody438_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody438_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody438_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody438_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody438_0, 438, 4)) (some 192) ([10, 8, 14]) (some (10, sourceBody438_11, 438, 5))

def sourceBody438_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody438_12 sourceBody438_4

def sourceBody438_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody438_13 sourceBody438_0

def sourceBody438_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody438_10 sourceBody438_14

def sourceBody438_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody438_9 sourceBody438_15

def sourceBody438_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody438_8 sourceBody438_16

def sourceBody438_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody438_0 sourceBody438_17

def sourceBody438_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody438_0 sourceBody438_18

def sourceBody438_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody438_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody438_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody438_21 sourceBody438_0

def sourceBody438_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody438_20 sourceBody438_22

def sourceBody438_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody438_19 sourceBody438_23

def sourceBody438_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody438_7 sourceBody438_24

def sourceBody438_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody438_0 sourceBody438_25

def sourceBody438_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody438_0 sourceBody438_26

def source438 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (438, 3, sourceBody438_27)
end InitECandidate.Proofs.WordStages
