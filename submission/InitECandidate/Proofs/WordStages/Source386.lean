import InitECandidate.Proofs.WordStages.Source370
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody386_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody386_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [2]

def sourceBody386_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody386_3 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody386_1 sourceBody386_2

def sourceBody386_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody386_0 sourceBody386_3

def source386 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (386, 1, sourceBody386_4)
end InitECandidate.Proofs.WordStages
