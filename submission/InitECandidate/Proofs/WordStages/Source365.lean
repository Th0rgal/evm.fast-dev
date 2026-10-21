import InitECandidate.Proofs.WordStages.Source349
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody365_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody365_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 384#64]))

def sourceBody365_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 392#64]))

def sourceBody365_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody365_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody365_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody365_0, 365, 2)) (some 158) ([6, 10, 8]) (some (6, sourceBody365_4, 365, 3))

def sourceBody365_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody365_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody365_5 sourceBody365_6

def sourceBody365_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody365_7 sourceBody365_0

def sourceBody365_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody365_3 sourceBody365_8

def sourceBody365_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody365_2 sourceBody365_9

def sourceBody365_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody365_1 sourceBody365_10

def sourceBody365_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody365_0 sourceBody365_11

def sourceBody365_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody365_0 sourceBody365_12

def sourceBody365_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody365_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody365_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody365_15 sourceBody365_0

def sourceBody365_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody365_14 sourceBody365_16

def sourceBody365_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody365_13 sourceBody365_17

def source365 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (365, 3, sourceBody365_18)
end InitECandidate.Proofs.WordStages
