import InitECandidate.Proofs.WordStages.Source329
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody345_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 152#64]))

def sourceBody345_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody345_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody345_3 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody345_1 sourceBody345_2

def sourceBody345_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody345_0 sourceBody345_3

def source345 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (345, 2, sourceBody345_4)
end InitECandidate.Proofs.WordStages
