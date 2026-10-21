import InitECandidate.Proofs.WordStages.Source353
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody369_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody369_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody369_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody369_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody369_4 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 366) ([0, 12, 6, 10, 8]) (none)

def sourceBody369_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody369_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody369_4 sourceBody369_5

def sourceBody369_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody369_3 sourceBody369_6

def sourceBody369_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody369_2 sourceBody369_7

def sourceBody369_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody369_1 sourceBody369_8

def sourceBody369_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody369_0 sourceBody369_9

def source369 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (369, 3, sourceBody369_10)
end InitECandidate.Proofs.WordStages
