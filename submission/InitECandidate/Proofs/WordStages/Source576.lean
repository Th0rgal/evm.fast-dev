import InitECandidate.Proofs.WordStages.Source560
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody576_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody576_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody576_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody576_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody576_0, 576, 2)) (some 466) ([6]) (some (6, sourceBody576_2, 576, 3))

def sourceBody576_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody576_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_3 sourceBody576_4

def sourceBody576_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_5 sourceBody576_0

def sourceBody576_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_1 sourceBody576_6

def sourceBody576_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_0 sourceBody576_7

def sourceBody576_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_0 sourceBody576_8

def sourceBody576_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody576_0, 576, 4)) (some 568) ([]) (some (6, sourceBody576_2, 576, 5))

def sourceBody576_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_10 sourceBody576_4

def sourceBody576_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_11 sourceBody576_0

def sourceBody576_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody576_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody576_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody576_0, 576, 6)) (some 473) ([2]) (some (2, sourceBody576_14, 576, 7))

def sourceBody576_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_15 sourceBody576_4

def sourceBody576_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_16 sourceBody576_0

def sourceBody576_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_13 sourceBody576_17

def sourceBody576_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_0 sourceBody576_18

def sourceBody576_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_0 sourceBody576_19

def sourceBody576_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody576_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody576_0, 576, 8)) (some 486) ([2]) (some (2, sourceBody576_14, 576, 9))

def sourceBody576_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_22 sourceBody576_4

def sourceBody576_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_23 sourceBody576_0

def sourceBody576_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_21 sourceBody576_24

def sourceBody576_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_0 sourceBody576_25

def sourceBody576_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_0 sourceBody576_26

def sourceBody576_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_20 sourceBody576_27

def sourceBody576_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody576_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody576_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_30 sourceBody576_0

def sourceBody576_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_29 sourceBody576_31

def sourceBody576_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_28 sourceBody576_32

def sourceBody576_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_12 sourceBody576_33

def sourceBody576_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_0 sourceBody576_34

def sourceBody576_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_0 sourceBody576_35

def sourceBody576_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody576_9 sourceBody576_36

def source576 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (576, 1, sourceBody576_37)
end InitECandidate.Proofs.WordStages
