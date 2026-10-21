import InitECandidate.Proofs.WordStages.Source658
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody674_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody674_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody674_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 2)
    (Flapjack.WordLangExpHOL.const 5#64))

def sourceBody674_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody674_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody674_0, 674, 2)) (some 78) ([6, 8]) (some (6, sourceBody674_3, 674, 3))

def sourceBody674_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody674_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody674_4 sourceBody674_5

def sourceBody674_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody674_6 sourceBody674_0

def sourceBody674_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody674_2 sourceBody674_7

def sourceBody674_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody674_1 sourceBody674_8

def sourceBody674_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody674_0 sourceBody674_9

def sourceBody674_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody674_0 sourceBody674_10

def sourceBody674_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody674_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody674_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody674_13 sourceBody674_0

def sourceBody674_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody674_12 sourceBody674_14

def sourceBody674_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody674_11 sourceBody674_15

def source674 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (674, 3, sourceBody674_16)
end InitECandidate.Proofs.WordStages
