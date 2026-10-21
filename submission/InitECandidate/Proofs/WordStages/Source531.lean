import InitECandidate.Proofs.WordStages.Source515
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody531_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody531_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody531_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([4, 10, 2, 8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody531_0, 531, 2)) (some 471) ([]) (some (6, sourceBody531_1, 531, 3))

def sourceBody531_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody531_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_2 sourceBody531_3

def sourceBody531_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_4 sourceBody531_0

def sourceBody531_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody531_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody531_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody531_0, 531, 4)) (some 466) ([12]) (some (12, sourceBody531_7, 531, 5))

def sourceBody531_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_8 sourceBody531_3

def sourceBody531_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_9 sourceBody531_0

def sourceBody531_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_6 sourceBody531_10

def sourceBody531_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_0 sourceBody531_11

def sourceBody531_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_0 sourceBody531_12

def sourceBody531_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody531_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody531_0, 531, 6)) (some 486) ([12]) (some (12, sourceBody531_7, 531, 7))

def sourceBody531_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_15 sourceBody531_3

def sourceBody531_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_16 sourceBody531_0

def sourceBody531_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_14 sourceBody531_17

def sourceBody531_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_0 sourceBody531_18

def sourceBody531_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_0 sourceBody531_19

def sourceBody531_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_13 sourceBody531_20

def sourceBody531_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody531_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody531_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_23 sourceBody531_0

def sourceBody531_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_22 sourceBody531_24

def sourceBody531_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_21 sourceBody531_25

def sourceBody531_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_5 sourceBody531_26

def sourceBody531_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_0 sourceBody531_27

def sourceBody531_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_0 sourceBody531_28

def sourceBody531_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_0 sourceBody531_29

def sourceBody531_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_0 sourceBody531_30

def sourceBody531_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_0 sourceBody531_31

def sourceBody531_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_0 sourceBody531_32

def sourceBody531_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_0 sourceBody531_33

def sourceBody531_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody531_0 sourceBody531_34

def source531 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (531, 1, sourceBody531_35)
end InitECandidate.Proofs.WordStages
