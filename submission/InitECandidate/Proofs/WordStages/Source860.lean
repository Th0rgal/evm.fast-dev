import InitECandidate.Proofs.WordStages.Source844
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody860_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody860_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody860_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody860_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody860_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody860_0, 860, 2)) (some 95) ([8, 4]) (some (8, sourceBody860_3, 860, 3))

def sourceBody860_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody860_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody860_4 sourceBody860_5

def sourceBody860_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody860_6 sourceBody860_0

def sourceBody860_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody860_2 sourceBody860_7

def sourceBody860_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody860_1 sourceBody860_8

def sourceBody860_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody860_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody860_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody860_11 sourceBody860_0

def sourceBody860_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody860_10 sourceBody860_12

def sourceBody860_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody860_9 sourceBody860_13

def sourceBody860_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody860_0 sourceBody860_14

def sourceBody860_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody860_0 sourceBody860_15

def source860 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (860, 2, sourceBody860_16)
end InitECandidate.Proofs.WordStages
