import InitECandidate.Proofs.WordStages.Source693
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody709_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 2)

def sourceBody709_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody709_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 6)

def sourceBody709_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 8)

def sourceBody709_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody709_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody709_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 2)

def sourceBody709_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody709_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 6)

def sourceBody709_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody709_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody709_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody709_12 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 706) ([0, 34, 16, 28, 22, 32, 18, 30, 24, 36, 14, 26, 20]) (none)

def sourceBody709_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody709_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody709_12 sourceBody709_13

def sourceBody709_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody709_11 sourceBody709_14

def sourceBody709_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody709_10 sourceBody709_15

def sourceBody709_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody709_9 sourceBody709_16

def sourceBody709_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody709_8 sourceBody709_17

def sourceBody709_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody709_7 sourceBody709_18

def sourceBody709_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody709_6 sourceBody709_19

def sourceBody709_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody709_5 sourceBody709_20

def sourceBody709_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody709_4 sourceBody709_21

def sourceBody709_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody709_3 sourceBody709_22

def sourceBody709_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody709_2 sourceBody709_23

def sourceBody709_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody709_1 sourceBody709_24

def sourceBody709_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody709_0 sourceBody709_25

def source709 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (709, 7, sourceBody709_26)
end InitECandidate.Proofs.WordStages
