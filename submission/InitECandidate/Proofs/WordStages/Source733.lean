import InitECandidate.Proofs.WordStages.Source717
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody733_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody733_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody733_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody733_3 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 730) ([0, 10, 6, 8]) (none)

def sourceBody733_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody733_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody733_3 sourceBody733_4

def sourceBody733_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody733_2 sourceBody733_5

def sourceBody733_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody733_1 sourceBody733_6

def sourceBody733_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody733_0 sourceBody733_7

def source733 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (733, 3, sourceBody733_8)
end InitECandidate.Proofs.WordStages
