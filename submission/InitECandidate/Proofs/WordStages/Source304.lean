import InitECandidate.Proofs.WordStages.Source288
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody304_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody304_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody304_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody304_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody304_0, 304, 2)) (some 68) ([6]) (some (6, sourceBody304_2, 304, 3))

def sourceBody304_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody304_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_3 sourceBody304_4

def sourceBody304_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_5 sourceBody304_0

def sourceBody304_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_1 sourceBody304_6

def sourceBody304_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody304_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody304_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody304_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 6) 8

def sourceBody304_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_11 sourceBody304_0

def sourceBody304_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_10 sourceBody304_12

def sourceBody304_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_13 sourceBody304_0

def sourceBody304_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_9 sourceBody304_14

def sourceBody304_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_0 sourceBody304_15

def sourceBody304_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_8 sourceBody304_16

def sourceBody304_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_0 sourceBody304_17

def sourceBody304_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody304_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody304_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_20 sourceBody304_14

def sourceBody304_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_0 sourceBody304_21

def sourceBody304_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_19 sourceBody304_22

def sourceBody304_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_0 sourceBody304_23

def sourceBody304_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_18 sourceBody304_24

def sourceBody304_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody304_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody304_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_27 sourceBody304_0

def sourceBody304_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_26 sourceBody304_28

def sourceBody304_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_25 sourceBody304_29

def sourceBody304_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_7 sourceBody304_30

def sourceBody304_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_0 sourceBody304_31

def sourceBody304_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody304_0 sourceBody304_32

def source304 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (304, 3, sourceBody304_33)
end InitECandidate.Proofs.WordStages
