import InitECandidate.Proofs.WordStages.Source726
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody742_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody742_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody742_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody742_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody742_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody742_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody742_0, 742, 2)) (some 77) ([6, 10, 8]) (some (6, sourceBody742_4, 742, 3))

def sourceBody742_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody742_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody742_5 sourceBody742_6

def sourceBody742_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody742_7 sourceBody742_0

def sourceBody742_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody742_3 sourceBody742_8

def sourceBody742_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody742_2 sourceBody742_9

def sourceBody742_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody742_1 sourceBody742_10

def sourceBody742_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody742_0 sourceBody742_11

def sourceBody742_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody742_0 sourceBody742_12

def sourceBody742_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody742_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody742_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody742_15 sourceBody742_0

def sourceBody742_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody742_14 sourceBody742_16

def sourceBody742_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody742_13 sourceBody742_17

def source742 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (742, 3, sourceBody742_18)
end InitECandidate.Proofs.WordStages
