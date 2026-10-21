import InitECandidate.Proofs.WordStages.Source426
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody442_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody442_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody442_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody442_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody442_0, 442, 2)) (some 435) ([6]) (some (6, sourceBody442_2, 442, 3))

def sourceBody442_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody442_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody442_3 sourceBody442_4

def sourceBody442_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody442_5 sourceBody442_0

def sourceBody442_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody442_1 sourceBody442_6

def sourceBody442_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody442_0 sourceBody442_7

def sourceBody442_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody442_0 sourceBody442_8

def sourceBody442_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody442_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody442_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody442_11 sourceBody442_0

def sourceBody442_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody442_10 sourceBody442_12

def sourceBody442_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody442_9 sourceBody442_13

def source442 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (442, 2, sourceBody442_14)
end InitECandidate.Proofs.WordStages
