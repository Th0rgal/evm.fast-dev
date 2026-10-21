import InitECandidate.Proofs.WordStages.Source559
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody575_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody575_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody575_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody575_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody575_0, 575, 2)) (some 466) ([6]) (some (6, sourceBody575_2, 575, 3))

def sourceBody575_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody575_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_3 sourceBody575_4

def sourceBody575_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_5 sourceBody575_0

def sourceBody575_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_1 sourceBody575_6

def sourceBody575_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_0 sourceBody575_7

def sourceBody575_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_0 sourceBody575_8

def sourceBody575_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody575_0, 575, 4)) (some 568) ([]) (some (6, sourceBody575_2, 575, 5))

def sourceBody575_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_10 sourceBody575_4

def sourceBody575_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_11 sourceBody575_0

def sourceBody575_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody575_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody575_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody575_0, 575, 6)) (some 473) ([2]) (some (2, sourceBody575_14, 575, 7))

def sourceBody575_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_15 sourceBody575_4

def sourceBody575_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_16 sourceBody575_0

def sourceBody575_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_13 sourceBody575_17

def sourceBody575_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_0 sourceBody575_18

def sourceBody575_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_0 sourceBody575_19

def sourceBody575_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody575_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody575_0, 575, 8)) (some 486) ([2]) (some (2, sourceBody575_14, 575, 9))

def sourceBody575_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_22 sourceBody575_4

def sourceBody575_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_23 sourceBody575_0

def sourceBody575_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_21 sourceBody575_24

def sourceBody575_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_0 sourceBody575_25

def sourceBody575_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_0 sourceBody575_26

def sourceBody575_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_20 sourceBody575_27

def sourceBody575_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody575_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody575_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_30 sourceBody575_0

def sourceBody575_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_29 sourceBody575_31

def sourceBody575_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_28 sourceBody575_32

def sourceBody575_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_12 sourceBody575_33

def sourceBody575_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_0 sourceBody575_34

def sourceBody575_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_0 sourceBody575_35

def sourceBody575_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody575_9 sourceBody575_36

def source575 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (575, 1, sourceBody575_37)
end InitECandidate.Proofs.WordStages
