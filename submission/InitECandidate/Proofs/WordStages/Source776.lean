import InitECandidate.Proofs.WordStages.Source760
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody776_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody776_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody776_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody776_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody776_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody776_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody776_0, 776, 2)) (some 77) ([6, 10, 8]) (some (6, sourceBody776_4, 776, 3))

def sourceBody776_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody776_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody776_5 sourceBody776_6

def sourceBody776_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody776_7 sourceBody776_0

def sourceBody776_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody776_3 sourceBody776_8

def sourceBody776_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody776_2 sourceBody776_9

def sourceBody776_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody776_1 sourceBody776_10

def sourceBody776_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody776_0 sourceBody776_11

def sourceBody776_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody776_0 sourceBody776_12

def sourceBody776_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody776_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody776_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody776_15 sourceBody776_0

def sourceBody776_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody776_14 sourceBody776_16

def sourceBody776_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody776_13 sourceBody776_17

def source776 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (776, 3, sourceBody776_18)
end InitECandidate.Proofs.WordStages
