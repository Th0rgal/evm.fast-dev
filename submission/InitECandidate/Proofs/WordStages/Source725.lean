import InitECandidate.Proofs.WordStages.Source709
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody725_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody725_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody725_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody725_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody725_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody725_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody725_0, 725, 2)) (some 77) ([6, 10, 8]) (some (6, sourceBody725_4, 725, 3))

def sourceBody725_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody725_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody725_5 sourceBody725_6

def sourceBody725_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody725_7 sourceBody725_0

def sourceBody725_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody725_3 sourceBody725_8

def sourceBody725_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody725_2 sourceBody725_9

def sourceBody725_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody725_1 sourceBody725_10

def sourceBody725_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody725_0 sourceBody725_11

def sourceBody725_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody725_0 sourceBody725_12

def sourceBody725_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody725_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody725_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody725_15 sourceBody725_0

def sourceBody725_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody725_14 sourceBody725_16

def sourceBody725_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody725_13 sourceBody725_17

def source725 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (725, 3, sourceBody725_18)
end InitECandidate.Proofs.WordStages
