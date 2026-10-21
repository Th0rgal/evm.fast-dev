import InitECandidate.Proofs.WordStages.Source335
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody351_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 264#64]))

def sourceBody351_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody351_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody351_3 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody351_1 sourceBody351_2

def sourceBody351_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody351_0 sourceBody351_3

def source351 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (351, 2, sourceBody351_4)
end InitECandidate.Proofs.WordStages
