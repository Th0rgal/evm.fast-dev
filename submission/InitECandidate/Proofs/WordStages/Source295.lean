import InitECandidate.Proofs.WordStages.Source279
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody295_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody295_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody295_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody295_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 8)

def sourceBody295_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 6) 4

def sourceBody295_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody295_4 sourceBody295_0

def sourceBody295_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody295_3 sourceBody295_5

def sourceBody295_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody295_6 sourceBody295_0

def sourceBody295_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody295_2 sourceBody295_7

def sourceBody295_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody295_0 sourceBody295_8

def sourceBody295_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody295_1 sourceBody295_9

def sourceBody295_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody295_0 sourceBody295_10

def sourceBody295_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody295_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody295_12 sourceBody295_9

def sourceBody295_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody295_0 sourceBody295_13

def sourceBody295_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody295_11 sourceBody295_14

def sourceBody295_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody295_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody295_16 sourceBody295_9

def sourceBody295_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody295_0 sourceBody295_17

def sourceBody295_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody295_15 sourceBody295_18

def sourceBody295_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody295_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody295_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody295_21 sourceBody295_0

def sourceBody295_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody295_20 sourceBody295_22

def sourceBody295_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody295_19 sourceBody295_23

def source295 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (295, 2, sourceBody295_24)
end InitECandidate.Proofs.WordStages
