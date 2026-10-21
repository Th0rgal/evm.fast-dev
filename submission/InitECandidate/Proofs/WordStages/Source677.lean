import InitECandidate.Proofs.WordStages.Source661
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody677_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody677_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 4,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 2)
          (Flapjack.WordLangExpHOL.const 5#64))
        (Flapjack.WordLangExpHOL.const 1#64)])

def sourceBody677_2 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 672) ([0, 8, 6]) (none)

def sourceBody677_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody677_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody677_2 sourceBody677_3

def sourceBody677_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody677_1 sourceBody677_4

def sourceBody677_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody677_0 sourceBody677_5

def source677 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (677, 3, sourceBody677_6)
end InitECandidate.Proofs.WordStages
