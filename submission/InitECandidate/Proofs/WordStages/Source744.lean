import InitECandidate.Proofs.WordStages.Source728
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody744_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody744_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody744_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody744_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody744_0, 744, 2)) (some 727) ([6]) (some (6, sourceBody744_2, 744, 3))

def sourceBody744_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody744_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_3 sourceBody744_4

def sourceBody744_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_5 sourceBody744_0

def sourceBody744_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_1 sourceBody744_6

def sourceBody744_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_0 sourceBody744_7

def sourceBody744_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_0 sourceBody744_8

def sourceBody744_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody744_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody744_0, 744, 4)) (some 726) ([6]) (some (6, sourceBody744_2, 744, 5))

def sourceBody744_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_11 sourceBody744_4

def sourceBody744_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_12 sourceBody744_0

def sourceBody744_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_10 sourceBody744_13

def sourceBody744_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_0 sourceBody744_14

def sourceBody744_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_0 sourceBody744_15

def sourceBody744_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_9 sourceBody744_16

def sourceBody744_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody744_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody744_0, 744, 6)) (some 726) ([6]) (some (6, sourceBody744_2, 744, 7))

def sourceBody744_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_19 sourceBody744_4

def sourceBody744_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_20 sourceBody744_0

def sourceBody744_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_18 sourceBody744_21

def sourceBody744_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_0 sourceBody744_22

def sourceBody744_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_0 sourceBody744_23

def sourceBody744_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_17 sourceBody744_24

def sourceBody744_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody744_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody744_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_27 sourceBody744_0

def sourceBody744_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_26 sourceBody744_28

def sourceBody744_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody744_25 sourceBody744_29

def source744 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (744, 2, sourceBody744_30)
end InitECandidate.Proofs.WordStages
