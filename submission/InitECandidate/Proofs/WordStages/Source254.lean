import InitECandidate.Proofs.WordStages.Source238
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody254_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody254_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody254_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody254_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody254_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody254_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody254_6 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody254_0, 254, 2)) (some 235) ([12, 18, 10, 14]) (some (12, sourceBody254_5, 254, 3))

def sourceBody254_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody254_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_6 sourceBody254_7

def sourceBody254_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_8 sourceBody254_0

def sourceBody254_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_4 sourceBody254_9

def sourceBody254_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_3 sourceBody254_10

def sourceBody254_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_2 sourceBody254_11

def sourceBody254_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_1 sourceBody254_12

def sourceBody254_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_0 sourceBody254_13

def sourceBody254_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_0 sourceBody254_14

def sourceBody254_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody254_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody254_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody254_0, 254, 4)) (some 236) ([12, 18, 10]) (some (12, sourceBody254_5, 254, 5))

def sourceBody254_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_18 sourceBody254_7

def sourceBody254_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_19 sourceBody254_0

def sourceBody254_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_17 sourceBody254_20

def sourceBody254_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_2 sourceBody254_21

def sourceBody254_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_16 sourceBody254_22

def sourceBody254_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_0 sourceBody254_23

def sourceBody254_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_0 sourceBody254_24

def sourceBody254_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_15 sourceBody254_25

def sourceBody254_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody254_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody254_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_28 sourceBody254_0

def sourceBody254_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_27 sourceBody254_29

def sourceBody254_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody254_26 sourceBody254_30

def source254 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (254, 5, sourceBody254_31)
end InitECandidate.Proofs.WordStages
