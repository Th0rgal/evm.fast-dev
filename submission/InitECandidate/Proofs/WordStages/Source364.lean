import InitECandidate.Proofs.WordStages.Source348
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody364_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody364_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody364_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody364_3 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 363) ([0, 6, 8, 4]) (none)

def sourceBody364_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody364_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody364_3 sourceBody364_4

def sourceBody364_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody364_2 sourceBody364_5

def sourceBody364_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody364_1 sourceBody364_6

def sourceBody364_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody364_0 sourceBody364_7

def source364 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (364, 2, sourceBody364_8)
end InitECandidate.Proofs.WordStages
