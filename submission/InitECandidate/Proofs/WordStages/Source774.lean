import InitECandidate.Proofs.WordStages.Source758
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody774_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody774_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody774_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody774_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody774_0, 774, 2)) (some 727) ([6]) (some (6, sourceBody774_2, 774, 3))

def sourceBody774_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody774_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_3 sourceBody774_4

def sourceBody774_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_5 sourceBody774_0

def sourceBody774_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_1 sourceBody774_6

def sourceBody774_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_0 sourceBody774_7

def sourceBody774_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_0 sourceBody774_8

def sourceBody774_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody774_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody774_0, 774, 4)) (some 727) ([6]) (some (6, sourceBody774_2, 774, 5))

def sourceBody774_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_11 sourceBody774_4

def sourceBody774_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_12 sourceBody774_0

def sourceBody774_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_10 sourceBody774_13

def sourceBody774_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_0 sourceBody774_14

def sourceBody774_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_0 sourceBody774_15

def sourceBody774_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_9 sourceBody774_16

def sourceBody774_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody774_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody774_0, 774, 6)) (some 726) ([6]) (some (6, sourceBody774_2, 774, 7))

def sourceBody774_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_19 sourceBody774_4

def sourceBody774_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_20 sourceBody774_0

def sourceBody774_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_18 sourceBody774_21

def sourceBody774_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_0 sourceBody774_22

def sourceBody774_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_0 sourceBody774_23

def sourceBody774_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_17 sourceBody774_24

def sourceBody774_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody774_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody774_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_27 sourceBody774_0

def sourceBody774_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_26 sourceBody774_28

def sourceBody774_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody774_25 sourceBody774_29

def source774 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (774, 2, sourceBody774_30)
end InitECandidate.Proofs.WordStages
