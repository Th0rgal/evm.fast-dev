import InitECandidate.Proofs.WordStages.Source289
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody305_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody305_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody305_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody305_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody305_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody305_0, 305, 2)) (some 301) ([12, 10]) (some (12, sourceBody305_3, 305, 3))

def sourceBody305_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody305_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody305_4 sourceBody305_5

def sourceBody305_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody305_6 sourceBody305_0

def sourceBody305_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody305_2 sourceBody305_7

def sourceBody305_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody305_1 sourceBody305_8

def sourceBody305_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody305_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody305_12 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 304) ([0, 12, 10]) (none)

def sourceBody305_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody305_12 sourceBody305_0

def sourceBody305_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody305_11 sourceBody305_13

def sourceBody305_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody305_10 sourceBody305_14

def sourceBody305_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody305_9 sourceBody305_15

def sourceBody305_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody305_0 sourceBody305_16

def sourceBody305_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody305_0 sourceBody305_17

def source305 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (305, 4, sourceBody305_18)
end InitECandidate.Proofs.WordStages
