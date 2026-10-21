import InitECandidate.Proofs.WordStages.Source447
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody463_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody463_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody463_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody463_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody463_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 16, 6, 14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody463_0, 463, 2)) (some 146) ([10, 18]) (some (10, sourceBody463_3, 463, 3))

def sourceBody463_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody463_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_4 sourceBody463_5

def sourceBody463_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_6 sourceBody463_0

def sourceBody463_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_2 sourceBody463_7

def sourceBody463_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_1 sourceBody463_8

def sourceBody463_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody463_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody463_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody463_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody463_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10, 18, 4, 12]

def sourceBody463_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_14 sourceBody463_0

def sourceBody463_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_13 sourceBody463_15

def sourceBody463_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_12 sourceBody463_16

def sourceBody463_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_11 sourceBody463_17

def sourceBody463_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_10 sourceBody463_18

def sourceBody463_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_9 sourceBody463_19

def sourceBody463_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_0 sourceBody463_20

def sourceBody463_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_0 sourceBody463_21

def sourceBody463_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_0 sourceBody463_22

def sourceBody463_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_0 sourceBody463_23

def sourceBody463_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_0 sourceBody463_24

def sourceBody463_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_0 sourceBody463_25

def sourceBody463_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_0 sourceBody463_26

def sourceBody463_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody463_0 sourceBody463_27

def source463 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (463, 2, sourceBody463_28)
end InitECandidate.Proofs.WordStages
