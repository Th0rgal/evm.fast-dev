import InitECandidate.Proofs.WordStages.Source336
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody352_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
    (Flapjack.WordLangExpHOL.load
      (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 264#64]))
    (Flapjack.WordLangExpHOL.const 17#64))

def sourceBody352_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody352_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody352_3 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody352_1 sourceBody352_2

def sourceBody352_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody352_0 sourceBody352_3

def source352 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (352, 2, sourceBody352_4)
end InitECandidate.Proofs.WordStages
