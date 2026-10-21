import InitECandidate.Proofs.WordStages.Source351
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody367_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody367_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody367_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody367_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody367_4 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 366) ([0, 12, 6, 10, 8]) (none)

def sourceBody367_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody367_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody367_4 sourceBody367_5

def sourceBody367_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody367_3 sourceBody367_6

def sourceBody367_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody367_2 sourceBody367_7

def sourceBody367_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody367_1 sourceBody367_8

def sourceBody367_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody367_0 sourceBody367_9

def source367 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (367, 3, sourceBody367_10)
end InitECandidate.Proofs.WordStages
