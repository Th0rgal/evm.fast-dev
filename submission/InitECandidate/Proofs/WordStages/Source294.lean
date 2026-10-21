import InitECandidate.Proofs.WordStages.Source278
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody294_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody294_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 176#64)

def sourceBody294_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody294_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody294_0, 294, 2)) (some 68) ([8]) (some (8, sourceBody294_2, 294, 3))

def sourceBody294_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody294_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_3 sourceBody294_4

def sourceBody294_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_5 sourceBody294_0

def sourceBody294_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_1 sourceBody294_6

def sourceBody294_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody294_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 176#64)

def sourceBody294_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody294_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody294_0, 294, 4)) (some 78) ([2, 6]) (some (2, sourceBody294_10, 294, 5))

def sourceBody294_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_11 sourceBody294_4

def sourceBody294_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_12 sourceBody294_0

def sourceBody294_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_9 sourceBody294_13

def sourceBody294_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_8 sourceBody294_14

def sourceBody294_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_0 sourceBody294_15

def sourceBody294_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_0 sourceBody294_16

def sourceBody294_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody294_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody294_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody294_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 6

def sourceBody294_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_21 sourceBody294_0

def sourceBody294_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_20 sourceBody294_22

def sourceBody294_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_23 sourceBody294_0

def sourceBody294_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_19 sourceBody294_24

def sourceBody294_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_0 sourceBody294_25

def sourceBody294_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_18 sourceBody294_26

def sourceBody294_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_0 sourceBody294_27

def sourceBody294_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_17 sourceBody294_28

def sourceBody294_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody294_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody294_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_31 sourceBody294_0

def sourceBody294_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_30 sourceBody294_32

def sourceBody294_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_29 sourceBody294_33

def sourceBody294_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_7 sourceBody294_34

def sourceBody294_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_0 sourceBody294_35

def sourceBody294_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody294_0 sourceBody294_36

def source294 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (294, 1, sourceBody294_37)
end InitECandidate.Proofs.WordStages
