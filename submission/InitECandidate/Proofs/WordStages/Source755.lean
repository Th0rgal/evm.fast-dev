import InitECandidate.Proofs.WordStages.Source739
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody755_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody755_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody755_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody755_3 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 754) ([0, 10, 6, 8]) (none)

def sourceBody755_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody755_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody755_3 sourceBody755_4

def sourceBody755_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody755_2 sourceBody755_5

def sourceBody755_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody755_1 sourceBody755_6

def sourceBody755_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody755_0 sourceBody755_7

def source755 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (755, 3, sourceBody755_8)
end InitECandidate.Proofs.WordStages
