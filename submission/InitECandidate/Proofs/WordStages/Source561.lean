import InitECandidate.Proofs.WordStages.Source545
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody561_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody561_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody561_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody561_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody561_0, 561, 2)) (some 403) ([12]) (some (12, sourceBody561_2, 561, 3))

def sourceBody561_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody561_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_3 sourceBody561_4

def sourceBody561_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_5 sourceBody561_0

def sourceBody561_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_1 sourceBody561_6

def sourceBody561_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody561_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody561_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody561_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody561_0, 561, 4)) (some 404) ([10, 8]) (some (10, sourceBody561_10, 561, 5))

def sourceBody561_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_11 sourceBody561_4

def sourceBody561_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_12 sourceBody561_0

def sourceBody561_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_9 sourceBody561_13

def sourceBody561_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_8 sourceBody561_14

def sourceBody561_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody561_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody561_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10, 8]

def sourceBody561_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_18 sourceBody561_0

def sourceBody561_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_17 sourceBody561_19

def sourceBody561_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_16 sourceBody561_20

def sourceBody561_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_15 sourceBody561_21

def sourceBody561_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_0 sourceBody561_22

def sourceBody561_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_0 sourceBody561_23

def sourceBody561_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_0 sourceBody561_24

def sourceBody561_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_0 sourceBody561_25

def sourceBody561_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_7 sourceBody561_26

def sourceBody561_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_0 sourceBody561_27

def sourceBody561_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody561_0 sourceBody561_28

def source561 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (561, 2, sourceBody561_29)
end InitECandidate.Proofs.WordStages
