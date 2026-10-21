import InitECandidate.Proofs.WordStages.Source352
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody368_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody368_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody368_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody368_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody368_4 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 366) ([0, 8, 12, 10, 14]) (none)

def sourceBody368_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody368_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody368_4 sourceBody368_5

def sourceBody368_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody368_3 sourceBody368_6

def sourceBody368_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody368_2 sourceBody368_7

def sourceBody368_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody368_1 sourceBody368_8

def sourceBody368_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody368_0 sourceBody368_9

def source368 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (368, 4, sourceBody368_10)
end InitECandidate.Proofs.WordStages
