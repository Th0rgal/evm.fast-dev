import InitECandidate.Proofs.WordStages.Source354
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody370_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody370_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody370_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody370_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody370_4 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 366) ([0, 12, 6, 10, 8]) (none)

def sourceBody370_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody370_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody370_4 sourceBody370_5

def sourceBody370_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody370_3 sourceBody370_6

def sourceBody370_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody370_2 sourceBody370_7

def sourceBody370_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody370_1 sourceBody370_8

def sourceBody370_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody370_0 sourceBody370_9

def source370 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (370, 3, sourceBody370_10)
end InitECandidate.Proofs.WordStages
