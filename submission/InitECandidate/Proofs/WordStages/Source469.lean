import InitECandidate.Proofs.WordStages.Source453
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody469_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody469_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody469_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
        [Flapjack.WordLangExpHOL.load
            (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64]),
          Flapjack.WordLangExpHOL.load
            (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 72#64])],
      Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])])

def sourceBody469_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody469_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody469_3 sourceBody469_0

def sourceBody469_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody469_2 sourceBody469_4

def sourceBody469_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody469_1 sourceBody469_5

def sourceBody469_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody469_0 sourceBody469_6

def source469 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (469, 2, sourceBody469_7)
end InitECandidate.Proofs.WordStages
