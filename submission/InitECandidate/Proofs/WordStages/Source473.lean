import InitECandidate.Proofs.WordStages.Source457
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody473_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody473_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody473_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody473_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody473_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody473_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody473_6 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody473_0, 473, 2)) (some 472) ([12, 4, 10, 8]) (some (12, sourceBody473_5, 473, 3))

def sourceBody473_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody473_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody473_6 sourceBody473_7

def sourceBody473_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody473_8 sourceBody473_0

def sourceBody473_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody473_4 sourceBody473_9

def sourceBody473_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody473_3 sourceBody473_10

def sourceBody473_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody473_2 sourceBody473_11

def sourceBody473_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody473_1 sourceBody473_12

def sourceBody473_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody473_0 sourceBody473_13

def sourceBody473_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody473_0 sourceBody473_14

def sourceBody473_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody473_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody473_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody473_17 sourceBody473_0

def sourceBody473_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody473_16 sourceBody473_18

def sourceBody473_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody473_15 sourceBody473_19

def source473 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (473, 2, sourceBody473_20)
end InitECandidate.Proofs.WordStages
