import InitECandidate.Proofs.WordStages.Source558
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody574_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody574_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody574_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody574_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody574_0, 574, 2)) (some 466) ([6]) (some (6, sourceBody574_2, 574, 3))

def sourceBody574_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody574_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_3 sourceBody574_4

def sourceBody574_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_5 sourceBody574_0

def sourceBody574_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_1 sourceBody574_6

def sourceBody574_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_0 sourceBody574_7

def sourceBody574_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_0 sourceBody574_8

def sourceBody574_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody574_0, 574, 4)) (some 568) ([]) (some (6, sourceBody574_2, 574, 5))

def sourceBody574_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_10 sourceBody574_4

def sourceBody574_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_11 sourceBody574_0

def sourceBody574_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 80#64]))

def sourceBody574_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody574_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody574_0, 574, 6)) (some 473) ([2]) (some (2, sourceBody574_14, 574, 7))

def sourceBody574_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_15 sourceBody574_4

def sourceBody574_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_16 sourceBody574_0

def sourceBody574_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_13 sourceBody574_17

def sourceBody574_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_0 sourceBody574_18

def sourceBody574_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_0 sourceBody574_19

def sourceBody574_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody574_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody574_0, 574, 8)) (some 486) ([2]) (some (2, sourceBody574_14, 574, 9))

def sourceBody574_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_22 sourceBody574_4

def sourceBody574_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_23 sourceBody574_0

def sourceBody574_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_21 sourceBody574_24

def sourceBody574_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_0 sourceBody574_25

def sourceBody574_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_0 sourceBody574_26

def sourceBody574_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_20 sourceBody574_27

def sourceBody574_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody574_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody574_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_30 sourceBody574_0

def sourceBody574_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_29 sourceBody574_31

def sourceBody574_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_28 sourceBody574_32

def sourceBody574_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_12 sourceBody574_33

def sourceBody574_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_0 sourceBody574_34

def sourceBody574_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_0 sourceBody574_35

def sourceBody574_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody574_9 sourceBody574_36

def source574 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (574, 1, sourceBody574_37)
end InitECandidate.Proofs.WordStages
