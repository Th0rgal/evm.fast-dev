import InitECandidate.Proofs.WordStages.Source328
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody344_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody344_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody344_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody344_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody344_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6, 10, 4, 8]

def sourceBody344_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody344_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody344_4 sourceBody344_5

def sourceBody344_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody344_3 sourceBody344_6

def sourceBody344_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody344_2 sourceBody344_7

def sourceBody344_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody344_1 sourceBody344_8

def sourceBody344_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody344_0 sourceBody344_9

def source344 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (344, 2, sourceBody344_10)
end InitECandidate.Proofs.WordStages
