import InitECandidate.Proofs.WordStages.Source333
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody349_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 352#64]))

def sourceBody349_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 352#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody349_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 352#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody349_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 352#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody349_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6, 10, 4, 8]

def sourceBody349_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody349_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody349_4 sourceBody349_5

def sourceBody349_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody349_3 sourceBody349_6

def sourceBody349_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody349_2 sourceBody349_7

def sourceBody349_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody349_1 sourceBody349_8

def sourceBody349_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody349_0 sourceBody349_9

def source349 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (349, 2, sourceBody349_10)
end InitECandidate.Proofs.WordStages
