import InitECandidate.Proofs.WordStages.Source831
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody847_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody847_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody847_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody847_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody847_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody847_0, 847, 2)) (some 88) ([10, 14]) (some (10, sourceBody847_3, 847, 3))

def sourceBody847_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody847_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_4 sourceBody847_5

def sourceBody847_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_6 sourceBody847_0

def sourceBody847_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_2 sourceBody847_7

def sourceBody847_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_1 sourceBody847_8

def sourceBody847_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_0 sourceBody847_9

def sourceBody847_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_0 sourceBody847_10

def sourceBody847_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 4#64])

def sourceBody847_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody847_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody847_0, 847, 4)) (some 89) ([10, 14]) (some (10, sourceBody847_3, 847, 5))

def sourceBody847_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_14 sourceBody847_5

def sourceBody847_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_15 sourceBody847_0

def sourceBody847_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_13 sourceBody847_16

def sourceBody847_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_12 sourceBody847_17

def sourceBody847_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_0 sourceBody847_18

def sourceBody847_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_0 sourceBody847_19

def sourceBody847_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_11 sourceBody847_20

def sourceBody847_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 12#64])

def sourceBody847_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody847_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody847_0, 847, 6)) (some 89) ([10, 14]) (some (10, sourceBody847_3, 847, 7))

def sourceBody847_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_24 sourceBody847_5

def sourceBody847_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_25 sourceBody847_0

def sourceBody847_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_23 sourceBody847_26

def sourceBody847_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_22 sourceBody847_27

def sourceBody847_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_0 sourceBody847_28

def sourceBody847_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_0 sourceBody847_29

def sourceBody847_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_21 sourceBody847_30

def sourceBody847_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody847_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody847_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_33 sourceBody847_0

def sourceBody847_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_32 sourceBody847_34

def sourceBody847_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody847_31 sourceBody847_35

def source847 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (847, 5, sourceBody847_36)
end InitECandidate.Proofs.WordStages
