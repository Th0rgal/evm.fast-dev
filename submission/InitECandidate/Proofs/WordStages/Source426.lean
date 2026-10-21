import InitECandidate.Proofs.WordStages.Source410
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody426_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody426_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody426_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody426_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody426_0, 426, 2)) (some 403) ([10]) (some (10, sourceBody426_2, 426, 3))

def sourceBody426_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody426_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_3 sourceBody426_4

def sourceBody426_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_5 sourceBody426_0

def sourceBody426_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_1 sourceBody426_6

def sourceBody426_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody426_9 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody426_0, 426, 4)) (some 391) ([10]) (some (10, sourceBody426_2, 426, 5))

def sourceBody426_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_9 sourceBody426_4

def sourceBody426_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_10 sourceBody426_0

def sourceBody426_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_8 sourceBody426_11

def sourceBody426_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody426_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 0#64]),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody426_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody426_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 8

def sourceBody426_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_16 sourceBody426_0

def sourceBody426_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_15 sourceBody426_17

def sourceBody426_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_18 sourceBody426_0

def sourceBody426_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_14 sourceBody426_19

def sourceBody426_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_0 sourceBody426_20

def sourceBody426_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_13 sourceBody426_21

def sourceBody426_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_0 sourceBody426_22

def sourceBody426_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_12 sourceBody426_23

def sourceBody426_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody426_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody426_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody426_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody426_0, 426, 6)) (some 419) ([4, 8]) (some (4, sourceBody426_27, 426, 7))

def sourceBody426_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_28 sourceBody426_4

def sourceBody426_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_29 sourceBody426_0

def sourceBody426_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_26 sourceBody426_30

def sourceBody426_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_25 sourceBody426_31

def sourceBody426_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_0 sourceBody426_32

def sourceBody426_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_0 sourceBody426_33

def sourceBody426_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_24 sourceBody426_34

def sourceBody426_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody426_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody426_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_37 sourceBody426_0

def sourceBody426_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_36 sourceBody426_38

def sourceBody426_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_35 sourceBody426_39

def sourceBody426_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_7 sourceBody426_40

def sourceBody426_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_0 sourceBody426_41

def sourceBody426_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody426_0 sourceBody426_42

def source426 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (426, 2, sourceBody426_43)
end InitECandidate.Proofs.WordStages
