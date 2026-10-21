import InitECandidate.Proofs.WordStages.Source435
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody451_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody451_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody451_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody451_0, 451, 2)) (some 450) ([]) (some (4, sourceBody451_1, 451, 3))

def sourceBody451_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody451_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody451_2 sourceBody451_3

def sourceBody451_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody451_4 sourceBody451_0

def sourceBody451_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody451_0 sourceBody451_5

def sourceBody451_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody451_0 sourceBody451_6

def sourceBody451_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody451_0, 451, 4)) (some 429) ([]) (some (4, sourceBody451_1, 451, 5))

def sourceBody451_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody451_8 sourceBody451_3

def sourceBody451_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody451_9 sourceBody451_0

def sourceBody451_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody451_0 sourceBody451_10

def sourceBody451_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody451_0 sourceBody451_11

def sourceBody451_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody451_7 sourceBody451_12

def sourceBody451_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody451_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [2]

def sourceBody451_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody451_15 sourceBody451_0

def sourceBody451_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody451_14 sourceBody451_16

def sourceBody451_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody451_13 sourceBody451_17

def source451 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (451, 1, sourceBody451_18)
end InitECandidate.Proofs.WordStages
