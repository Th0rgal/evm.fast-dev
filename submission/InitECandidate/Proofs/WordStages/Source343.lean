import InitECandidate.Proofs.WordStages.Source327
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody343_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 144#64]))

def sourceBody343_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody343_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody343_3 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody343_1 sourceBody343_2

def sourceBody343_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody343_0 sourceBody343_3

def source343 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (343, 2, sourceBody343_4)
end InitECandidate.Proofs.WordStages
