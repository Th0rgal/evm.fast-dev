import InitECandidate.Proofs.WordStages.Source375
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody391_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody391_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 56#64)

def sourceBody391_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody391_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody391_0, 391, 2)) (some 68) ([12]) (some (12, sourceBody391_2, 391, 3))

def sourceBody391_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody391_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody391_3 sourceBody391_4

def sourceBody391_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody391_5 sourceBody391_0

def sourceBody391_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody391_1 sourceBody391_6

def sourceBody391_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody391_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody391_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 56#64)

def sourceBody391_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody391_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody391_0, 391, 4)) (some 77) ([4, 10, 8]) (some (4, sourceBody391_11, 391, 5))

def sourceBody391_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody391_12 sourceBody391_4

def sourceBody391_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody391_13 sourceBody391_0

def sourceBody391_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody391_10 sourceBody391_14

def sourceBody391_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody391_9 sourceBody391_15

def sourceBody391_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody391_8 sourceBody391_16

def sourceBody391_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody391_0 sourceBody391_17

def sourceBody391_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody391_0 sourceBody391_18

def sourceBody391_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody391_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody391_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody391_21 sourceBody391_0

def sourceBody391_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody391_20 sourceBody391_22

def sourceBody391_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody391_19 sourceBody391_23

def sourceBody391_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody391_7 sourceBody391_24

def sourceBody391_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody391_0 sourceBody391_25

def sourceBody391_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody391_0 sourceBody391_26

def source391 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (391, 2, sourceBody391_27)
end InitECandidate.Proofs.WordStages
