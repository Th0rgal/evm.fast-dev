import InitECandidate.Proofs.WordStages.Source727
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody743_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody743_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody743_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody743_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody743_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody743_0, 743, 2)) (some 78) ([8, 4]) (some (8, sourceBody743_3, 743, 3))

def sourceBody743_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody743_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody743_4 sourceBody743_5

def sourceBody743_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody743_6 sourceBody743_0

def sourceBody743_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody743_2 sourceBody743_7

def sourceBody743_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody743_1 sourceBody743_8

def sourceBody743_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody743_0 sourceBody743_9

def sourceBody743_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody743_0 sourceBody743_10

def sourceBody743_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody743_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody743_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody743_13 sourceBody743_0

def sourceBody743_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody743_12 sourceBody743_14

def sourceBody743_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody743_11 sourceBody743_15

def source743 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (743, 2, sourceBody743_16)
end InitECandidate.Proofs.WordStages
