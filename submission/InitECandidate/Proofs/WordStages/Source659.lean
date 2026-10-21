import InitECandidate.Proofs.WordStages.Source643
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody659_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody659_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody659_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 6)

def sourceBody659_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody659_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody659_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody659_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody659_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody659_8 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 657) ([0, 20, 16, 24, 10, 18, 14, 22, 12]) (none)

def sourceBody659_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody659_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody659_8 sourceBody659_9

def sourceBody659_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody659_7 sourceBody659_10

def sourceBody659_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody659_6 sourceBody659_11

def sourceBody659_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody659_5 sourceBody659_12

def sourceBody659_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody659_4 sourceBody659_13

def sourceBody659_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody659_3 sourceBody659_14

def sourceBody659_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody659_2 sourceBody659_15

def sourceBody659_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody659_1 sourceBody659_16

def sourceBody659_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody659_0 sourceBody659_17

def source659 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (659, 5, sourceBody659_18)
end InitECandidate.Proofs.WordStages
