import InitECandidate.Proofs.WordStages.Source731
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody747_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody747_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody747_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody747_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody747_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody747_0, 747, 2)) (some 732) ([6, 8]) (some (6, sourceBody747_3, 747, 3))

def sourceBody747_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody747_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_4 sourceBody747_5

def sourceBody747_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_6 sourceBody747_0

def sourceBody747_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_2 sourceBody747_7

def sourceBody747_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_1 sourceBody747_8

def sourceBody747_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_0 sourceBody747_9

def sourceBody747_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_0 sourceBody747_10

def sourceBody747_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody747_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody747_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody747_0, 747, 4)) (some 732) ([6, 8]) (some (6, sourceBody747_3, 747, 5))

def sourceBody747_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_14 sourceBody747_5

def sourceBody747_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_15 sourceBody747_0

def sourceBody747_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_13 sourceBody747_16

def sourceBody747_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_12 sourceBody747_17

def sourceBody747_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_0 sourceBody747_18

def sourceBody747_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_0 sourceBody747_19

def sourceBody747_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_11 sourceBody747_20

def sourceBody747_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody747_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody747_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody747_0, 747, 6)) (some 732) ([6, 8]) (some (6, sourceBody747_3, 747, 7))

def sourceBody747_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_24 sourceBody747_5

def sourceBody747_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_25 sourceBody747_0

def sourceBody747_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_23 sourceBody747_26

def sourceBody747_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_22 sourceBody747_27

def sourceBody747_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_0 sourceBody747_28

def sourceBody747_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_0 sourceBody747_29

def sourceBody747_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_21 sourceBody747_30

def sourceBody747_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody747_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody747_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_33 sourceBody747_0

def sourceBody747_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_32 sourceBody747_34

def sourceBody747_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody747_31 sourceBody747_35

def source747 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (747, 3, sourceBody747_36)
end InitECandidate.Proofs.WordStages
