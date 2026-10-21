import InitECandidate.Proofs.WordStages.Source467
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody483_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody483_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 176#64)

def sourceBody483_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody483_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody483_0, 483, 2)) (some 68) ([8]) (some (8, sourceBody483_2, 483, 3))

def sourceBody483_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody483_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody483_3 sourceBody483_4

def sourceBody483_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody483_5 sourceBody483_0

def sourceBody483_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody483_1 sourceBody483_6

def sourceBody483_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody483_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 176#64)

def sourceBody483_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody483_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody483_0, 483, 4)) (some 78) ([2, 6]) (some (2, sourceBody483_10, 483, 5))

def sourceBody483_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody483_11 sourceBody483_4

def sourceBody483_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody483_12 sourceBody483_0

def sourceBody483_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody483_9 sourceBody483_13

def sourceBody483_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody483_8 sourceBody483_14

def sourceBody483_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody483_0 sourceBody483_15

def sourceBody483_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody483_0 sourceBody483_16

def sourceBody483_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody483_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody483_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody483_19 sourceBody483_0

def sourceBody483_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody483_18 sourceBody483_20

def sourceBody483_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody483_17 sourceBody483_21

def sourceBody483_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody483_7 sourceBody483_22

def sourceBody483_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody483_0 sourceBody483_23

def sourceBody483_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody483_0 sourceBody483_24

def source483 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (483, 1, sourceBody483_25)
end InitECandidate.Proofs.WordStages
