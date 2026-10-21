import InitECandidate.Proofs.WordStages.Source445
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody461_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody461_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody461_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody461_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody461_0, 461, 2)) (some 460) ([6]) (some (6, sourceBody461_2, 461, 3))

def sourceBody461_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody461_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody461_3 sourceBody461_4

def sourceBody461_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody461_5 sourceBody461_0

def sourceBody461_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody461_1 sourceBody461_6

def sourceBody461_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 4)
    (Flapjack.WordLangExpHOL.const 5#64))

def sourceBody461_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody461_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody461_9 sourceBody461_0

def sourceBody461_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody461_8 sourceBody461_10

def sourceBody461_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody461_7 sourceBody461_11

def sourceBody461_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody461_0 sourceBody461_12

def sourceBody461_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody461_0 sourceBody461_13

def source461 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (461, 2, sourceBody461_14)
end InitECandidate.Proofs.WordStages
