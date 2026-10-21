import InitECandidate.Proofs.WordStages.Source839
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody855_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody855_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 200#64)

def sourceBody855_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody855_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody855_0, 855, 2)) (some 68) ([8]) (some (8, sourceBody855_2, 855, 3))

def sourceBody855_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody855_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody855_3 sourceBody855_4

def sourceBody855_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody855_5 sourceBody855_0

def sourceBody855_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody855_1 sourceBody855_6

def sourceBody855_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody855_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 200#64)

def sourceBody855_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody855_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody855_0, 855, 4)) (some 78) ([2, 6]) (some (2, sourceBody855_10, 855, 5))

def sourceBody855_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody855_11 sourceBody855_4

def sourceBody855_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody855_12 sourceBody855_0

def sourceBody855_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody855_9 sourceBody855_13

def sourceBody855_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody855_8 sourceBody855_14

def sourceBody855_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody855_0 sourceBody855_15

def sourceBody855_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody855_0 sourceBody855_16

def sourceBody855_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody855_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody855_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody855_19 sourceBody855_0

def sourceBody855_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody855_18 sourceBody855_20

def sourceBody855_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody855_17 sourceBody855_21

def sourceBody855_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody855_7 sourceBody855_22

def sourceBody855_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody855_0 sourceBody855_23

def sourceBody855_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody855_0 sourceBody855_24

def source855 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (855, 1, sourceBody855_25)
end InitECandidate.Proofs.WordStages
