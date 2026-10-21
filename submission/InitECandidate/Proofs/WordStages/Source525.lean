import InitECandidate.Proofs.WordStages.Source509
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody525_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody525_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody525_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody525_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody525_0, 525, 2)) (some 466) ([4]) (some (4, sourceBody525_2, 525, 3))

def sourceBody525_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody525_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody525_3 sourceBody525_4

def sourceBody525_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody525_5 sourceBody525_0

def sourceBody525_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody525_1 sourceBody525_6

def sourceBody525_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody525_0 sourceBody525_7

def sourceBody525_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody525_0 sourceBody525_8

def sourceBody525_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody525_0, 525, 4)) (some 486) ([4]) (some (4, sourceBody525_2, 525, 5))

def sourceBody525_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody525_10 sourceBody525_4

def sourceBody525_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody525_11 sourceBody525_0

def sourceBody525_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody525_1 sourceBody525_12

def sourceBody525_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody525_0 sourceBody525_13

def sourceBody525_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody525_0 sourceBody525_14

def sourceBody525_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody525_9 sourceBody525_15

def sourceBody525_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody525_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [2]

def sourceBody525_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody525_18 sourceBody525_0

def sourceBody525_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody525_17 sourceBody525_19

def sourceBody525_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody525_16 sourceBody525_20

def source525 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (525, 1, sourceBody525_21)
end InitECandidate.Proofs.WordStages
