import InitECandidate.Proofs.WordStages.Source736
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody752_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody752_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody752_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody752_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody752_0, 752, 2)) (some 744) ([6]) (some (6, sourceBody752_2, 752, 3))

def sourceBody752_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody752_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody752_3 sourceBody752_4

def sourceBody752_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody752_5 sourceBody752_0

def sourceBody752_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody752_1 sourceBody752_6

def sourceBody752_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody752_0 sourceBody752_7

def sourceBody752_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody752_0 sourceBody752_8

def sourceBody752_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody752_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody752_0, 752, 4)) (some 743) ([6]) (some (6, sourceBody752_2, 752, 5))

def sourceBody752_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody752_11 sourceBody752_4

def sourceBody752_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody752_12 sourceBody752_0

def sourceBody752_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody752_10 sourceBody752_13

def sourceBody752_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody752_0 sourceBody752_14

def sourceBody752_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody752_0 sourceBody752_15

def sourceBody752_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody752_9 sourceBody752_16

def sourceBody752_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody752_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody752_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody752_19 sourceBody752_0

def sourceBody752_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody752_18 sourceBody752_20

def sourceBody752_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody752_17 sourceBody752_21

def source752 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (752, 2, sourceBody752_22)
end InitECandidate.Proofs.WordStages
