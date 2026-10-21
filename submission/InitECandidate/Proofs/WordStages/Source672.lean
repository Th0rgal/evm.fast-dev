import InitECandidate.Proofs.WordStages.Source656
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody672_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody672_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 2)
    (Flapjack.WordLangExpHOL.const 5#64))

def sourceBody672_2 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 80) ([0, 8, 6]) (none)

def sourceBody672_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody672_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody672_2 sourceBody672_3

def sourceBody672_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody672_1 sourceBody672_4

def sourceBody672_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody672_0 sourceBody672_5

def source672 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (672, 3, sourceBody672_6)
end InitECandidate.Proofs.WordStages
