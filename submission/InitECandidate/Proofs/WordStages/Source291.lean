import InitECandidate.Proofs.WordStages.Source275
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody291_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody291_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody291_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody291_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody291_0, 291, 2)) (some 68) ([10]) (some (10, sourceBody291_2, 291, 3))

def sourceBody291_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody291_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_3 sourceBody291_4

def sourceBody291_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_5 sourceBody291_0

def sourceBody291_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_1 sourceBody291_6

def sourceBody291_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody291_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody291_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody291_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 8

def sourceBody291_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_11 sourceBody291_0

def sourceBody291_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_10 sourceBody291_12

def sourceBody291_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_13 sourceBody291_0

def sourceBody291_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_9 sourceBody291_14

def sourceBody291_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_0 sourceBody291_15

def sourceBody291_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_8 sourceBody291_16

def sourceBody291_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_0 sourceBody291_17

def sourceBody291_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody291_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_19 sourceBody291_16

def sourceBody291_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_0 sourceBody291_20

def sourceBody291_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_18 sourceBody291_21

def sourceBody291_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody291_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_23 sourceBody291_16

def sourceBody291_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_0 sourceBody291_24

def sourceBody291_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_22 sourceBody291_25

def sourceBody291_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody291_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody291_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_28 sourceBody291_14

def sourceBody291_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_0 sourceBody291_29

def sourceBody291_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_27 sourceBody291_30

def sourceBody291_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_0 sourceBody291_31

def sourceBody291_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_26 sourceBody291_32

def sourceBody291_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody291_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody291_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_35 sourceBody291_0

def sourceBody291_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_34 sourceBody291_36

def sourceBody291_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_33 sourceBody291_37

def sourceBody291_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_7 sourceBody291_38

def sourceBody291_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_0 sourceBody291_39

def sourceBody291_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody291_0 sourceBody291_40

def source291 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (291, 2, sourceBody291_41)
end InitECandidate.Proofs.WordStages
