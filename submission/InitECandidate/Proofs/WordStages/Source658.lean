import InitECandidate.Proofs.WordStages.Source642
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody658_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody658_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody658_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 6)

def sourceBody658_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody658_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 17522657719365597833#64)

def sourceBody658_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 13107472804851548667#64)

def sourceBody658_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 5164255478447964150#64)

def sourceBody658_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 493319470278259999#64)

def sourceBody658_8 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 657) ([0, 20, 16, 24, 10, 18, 14, 22, 12]) (none)

def sourceBody658_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody658_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody658_8 sourceBody658_9

def sourceBody658_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody658_7 sourceBody658_10

def sourceBody658_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody658_6 sourceBody658_11

def sourceBody658_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody658_5 sourceBody658_12

def sourceBody658_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody658_4 sourceBody658_13

def sourceBody658_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody658_3 sourceBody658_14

def sourceBody658_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody658_2 sourceBody658_15

def sourceBody658_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody658_1 sourceBody658_16

def sourceBody658_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody658_0 sourceBody658_17

def source658 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (658, 5, sourceBody658_18)
end InitECandidate.Proofs.WordStages
