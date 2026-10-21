import InitECandidate.Proofs.WordStages.Source260
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody276_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody276_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody276_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody276_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 11684671#64)

def sourceBody276_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody276_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 16, 6, 14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody276_0, 276, 2)) (some 275) ([10, 18, 4]) (some (10, sourceBody276_4, 276, 3))

def sourceBody276_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody276_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_5 sourceBody276_6

def sourceBody276_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_7 sourceBody276_0

def sourceBody276_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_3 sourceBody276_8

def sourceBody276_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_2 sourceBody276_9

def sourceBody276_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_1 sourceBody276_10

def sourceBody276_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody276_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody276_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody276_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody276_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10, 18, 4, 12]

def sourceBody276_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_16 sourceBody276_0

def sourceBody276_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_15 sourceBody276_17

def sourceBody276_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_14 sourceBody276_18

def sourceBody276_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_13 sourceBody276_19

def sourceBody276_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_12 sourceBody276_20

def sourceBody276_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_11 sourceBody276_21

def sourceBody276_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_0 sourceBody276_22

def sourceBody276_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_0 sourceBody276_23

def sourceBody276_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_0 sourceBody276_24

def sourceBody276_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_0 sourceBody276_25

def sourceBody276_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_0 sourceBody276_26

def sourceBody276_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_0 sourceBody276_27

def sourceBody276_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_0 sourceBody276_28

def sourceBody276_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody276_0 sourceBody276_29

def source276 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (276, 2, sourceBody276_30)
end InitECandidate.Proofs.WordStages
