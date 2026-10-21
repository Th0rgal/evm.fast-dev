import InitECandidate.Proofs.WordStages.Source789
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody805_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody805_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody805_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody805_0, 805, 2)) (some 700) ([]) (some (4, sourceBody805_1, 805, 3))

def sourceBody805_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody805_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody805_2 sourceBody805_3

def sourceBody805_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody805_4 sourceBody805_0

def sourceBody805_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody805_0 sourceBody805_5

def sourceBody805_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody805_0 sourceBody805_6

def sourceBody805_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody805_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [2]

def sourceBody805_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody805_9 sourceBody805_0

def sourceBody805_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody805_8 sourceBody805_10

def sourceBody805_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody805_7 sourceBody805_11

def source805 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (805, 1, sourceBody805_12)
end InitECandidate.Proofs.WordStages
