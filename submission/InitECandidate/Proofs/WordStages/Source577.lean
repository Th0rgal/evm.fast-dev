import InitECandidate.Proofs.WordStages.Source561
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody577_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody577_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody577_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody577_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody577_0, 577, 2)) (some 466) ([6]) (some (6, sourceBody577_2, 577, 3))

def sourceBody577_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody577_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_3 sourceBody577_4

def sourceBody577_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_5 sourceBody577_0

def sourceBody577_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_1 sourceBody577_6

def sourceBody577_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_0 sourceBody577_7

def sourceBody577_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_0 sourceBody577_8

def sourceBody577_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody577_0, 577, 4)) (some 568) ([]) (some (6, sourceBody577_2, 577, 5))

def sourceBody577_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_10 sourceBody577_4

def sourceBody577_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_11 sourceBody577_0

def sourceBody577_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody577_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody577_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody577_0, 577, 6)) (some 473) ([2]) (some (2, sourceBody577_14, 577, 7))

def sourceBody577_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_15 sourceBody577_4

def sourceBody577_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_16 sourceBody577_0

def sourceBody577_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_13 sourceBody577_17

def sourceBody577_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_0 sourceBody577_18

def sourceBody577_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_0 sourceBody577_19

def sourceBody577_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody577_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody577_0, 577, 8)) (some 486) ([2]) (some (2, sourceBody577_14, 577, 9))

def sourceBody577_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_22 sourceBody577_4

def sourceBody577_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_23 sourceBody577_0

def sourceBody577_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_21 sourceBody577_24

def sourceBody577_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_0 sourceBody577_25

def sourceBody577_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_0 sourceBody577_26

def sourceBody577_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_20 sourceBody577_27

def sourceBody577_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody577_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody577_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_30 sourceBody577_0

def sourceBody577_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_29 sourceBody577_31

def sourceBody577_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_28 sourceBody577_32

def sourceBody577_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_12 sourceBody577_33

def sourceBody577_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_0 sourceBody577_34

def sourceBody577_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_0 sourceBody577_35

def sourceBody577_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody577_9 sourceBody577_36

def source577 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (577, 1, sourceBody577_37)
end InitECandidate.Proofs.WordStages
