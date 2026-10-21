import InitECandidate.Proofs.WordStages.Source402
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody418_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody418_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody418_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody418_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody418_0, 418, 2)) (some 417) ([8]) (some (8, sourceBody418_2, 418, 3))

def sourceBody418_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody418_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody418_3 sourceBody418_4

def sourceBody418_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody418_5 sourceBody418_0

def sourceBody418_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody418_1 sourceBody418_6

def sourceBody418_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody418_0 sourceBody418_7

def sourceBody418_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody418_0 sourceBody418_8

def sourceBody418_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody418_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody418_0, 418, 4)) (some 415) ([8, 4]) (some (8, sourceBody418_2, 418, 5))

def sourceBody418_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody418_11 sourceBody418_4

def sourceBody418_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody418_12 sourceBody418_0

def sourceBody418_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody418_10 sourceBody418_13

def sourceBody418_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody418_1 sourceBody418_14

def sourceBody418_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody418_0 sourceBody418_15

def sourceBody418_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody418_0 sourceBody418_16

def sourceBody418_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody418_9 sourceBody418_17

def sourceBody418_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody418_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody418_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody418_20 sourceBody418_0

def sourceBody418_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody418_19 sourceBody418_21

def sourceBody418_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody418_18 sourceBody418_22

def source418 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (418, 2, sourceBody418_23)
end InitECandidate.Proofs.WordStages
