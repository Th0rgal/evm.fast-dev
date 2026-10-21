import InitECandidate.Proofs.WordStages.Source695
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody711_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 2)

def sourceBody711_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody711_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 6)

def sourceBody711_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 8)

def sourceBody711_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody711_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody711_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 2)

def sourceBody711_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody711_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 6)

def sourceBody711_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody711_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody711_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody711_12 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 710) ([0, 34, 16, 28, 22, 32, 18, 30, 24, 36, 14, 26, 20]) (none)

def sourceBody711_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody711_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody711_12 sourceBody711_13

def sourceBody711_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody711_11 sourceBody711_14

def sourceBody711_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody711_10 sourceBody711_15

def sourceBody711_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody711_9 sourceBody711_16

def sourceBody711_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody711_8 sourceBody711_17

def sourceBody711_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody711_7 sourceBody711_18

def sourceBody711_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody711_6 sourceBody711_19

def sourceBody711_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody711_5 sourceBody711_20

def sourceBody711_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody711_4 sourceBody711_21

def sourceBody711_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody711_3 sourceBody711_22

def sourceBody711_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody711_2 sourceBody711_23

def sourceBody711_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody711_1 sourceBody711_24

def sourceBody711_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody711_0 sourceBody711_25

def source711 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (711, 7, sourceBody711_26)
end InitECandidate.Proofs.WordStages
