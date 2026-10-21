import InitECandidate.Proofs.WordStages.Source748
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody764_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody764_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody764_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody764_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 144#64)

def sourceBody764_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody764_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody764_0, 764, 2)) (some 77) ([6, 10, 8]) (some (6, sourceBody764_4, 764, 3))

def sourceBody764_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody764_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody764_5 sourceBody764_6

def sourceBody764_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody764_7 sourceBody764_0

def sourceBody764_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody764_3 sourceBody764_8

def sourceBody764_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody764_2 sourceBody764_9

def sourceBody764_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody764_1 sourceBody764_10

def sourceBody764_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody764_0 sourceBody764_11

def sourceBody764_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody764_0 sourceBody764_12

def sourceBody764_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody764_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody764_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody764_15 sourceBody764_0

def sourceBody764_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody764_14 sourceBody764_16

def sourceBody764_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody764_13 sourceBody764_17

def source764 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (764, 3, sourceBody764_18)
end InitECandidate.Proofs.WordStages
