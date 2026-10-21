import InitECandidate.Proofs.WordStages.Source468
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody484_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody484_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 176#64)

def sourceBody484_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody484_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody484_0, 484, 2)) (some 74) ([8]) (some (8, sourceBody484_2, 484, 3))

def sourceBody484_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody484_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody484_3 sourceBody484_4

def sourceBody484_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody484_5 sourceBody484_0

def sourceBody484_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody484_1 sourceBody484_6

def sourceBody484_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody484_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 176#64)

def sourceBody484_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody484_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody484_0, 484, 4)) (some 78) ([2, 6]) (some (2, sourceBody484_10, 484, 5))

def sourceBody484_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody484_11 sourceBody484_4

def sourceBody484_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody484_12 sourceBody484_0

def sourceBody484_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody484_9 sourceBody484_13

def sourceBody484_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody484_8 sourceBody484_14

def sourceBody484_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody484_0 sourceBody484_15

def sourceBody484_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody484_0 sourceBody484_16

def sourceBody484_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody484_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody484_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody484_19 sourceBody484_0

def sourceBody484_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody484_18 sourceBody484_20

def sourceBody484_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody484_17 sourceBody484_21

def sourceBody484_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody484_7 sourceBody484_22

def sourceBody484_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody484_0 sourceBody484_23

def sourceBody484_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody484_0 sourceBody484_24

def source484 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (484, 1, sourceBody484_25)
end InitECandidate.Proofs.WordStages
