import InitECandidate.Proofs.WordStages.Source735
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody751_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody751_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody751_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody751_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 576#64)

def sourceBody751_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody751_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody751_0, 751, 2)) (some 77) ([6, 10, 8]) (some (6, sourceBody751_4, 751, 3))

def sourceBody751_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody751_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody751_5 sourceBody751_6

def sourceBody751_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody751_7 sourceBody751_0

def sourceBody751_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody751_3 sourceBody751_8

def sourceBody751_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody751_2 sourceBody751_9

def sourceBody751_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody751_1 sourceBody751_10

def sourceBody751_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody751_0 sourceBody751_11

def sourceBody751_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody751_0 sourceBody751_12

def sourceBody751_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody751_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody751_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody751_15 sourceBody751_0

def sourceBody751_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody751_14 sourceBody751_16

def sourceBody751_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody751_13 sourceBody751_17

def source751 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (751, 3, sourceBody751_18)
end InitECandidate.Proofs.WordStages
