import InitECandidate.Proofs.WordStages.Source759
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody775_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody775_1 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 728) ([0, 4]) (none)

def sourceBody775_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody775_3 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody775_1 sourceBody775_2

def sourceBody775_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody775_0 sourceBody775_3

def source775 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (775, 2, sourceBody775_4)
end InitECandidate.Proofs.WordStages
