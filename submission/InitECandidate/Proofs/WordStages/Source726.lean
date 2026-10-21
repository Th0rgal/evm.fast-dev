import InitECandidate.Proofs.WordStages.Source710
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody726_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody726_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody726_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody726_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody726_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody726_0, 726, 2)) (some 78) ([8, 4]) (some (8, sourceBody726_3, 726, 3))

def sourceBody726_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody726_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody726_4 sourceBody726_5

def sourceBody726_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody726_6 sourceBody726_0

def sourceBody726_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody726_2 sourceBody726_7

def sourceBody726_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody726_1 sourceBody726_8

def sourceBody726_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody726_0 sourceBody726_9

def sourceBody726_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody726_0 sourceBody726_10

def sourceBody726_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody726_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody726_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody726_13 sourceBody726_0

def sourceBody726_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody726_12 sourceBody726_14

def sourceBody726_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody726_11 sourceBody726_15

def source726 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (726, 2, sourceBody726_16)
end InitECandidate.Proofs.WordStages
