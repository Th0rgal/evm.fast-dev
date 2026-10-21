import InitECandidate.Proofs.WordStages.Source525
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody541_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody541_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody541_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody541_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody541_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody541_0, 541, 2)) (some 433) ([6, 10]) (some (6, sourceBody541_3, 541, 3))

def sourceBody541_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody541_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody541_4 sourceBody541_5

def sourceBody541_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody541_6 sourceBody541_0

def sourceBody541_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody541_2 sourceBody541_7

def sourceBody541_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody541_1 sourceBody541_8

def sourceBody541_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody541_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody541_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody541_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 6) 8

def sourceBody541_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody541_13 sourceBody541_0

def sourceBody541_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody541_12 sourceBody541_14

def sourceBody541_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody541_15 sourceBody541_0

def sourceBody541_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody541_11 sourceBody541_16

def sourceBody541_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody541_0 sourceBody541_17

def sourceBody541_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody541_10 sourceBody541_18

def sourceBody541_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody541_0 sourceBody541_19

def sourceBody541_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody541_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody541_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody541_22 sourceBody541_0

def sourceBody541_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody541_21 sourceBody541_23

def sourceBody541_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody541_20 sourceBody541_24

def sourceBody541_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody541_9 sourceBody541_25

def sourceBody541_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody541_0 sourceBody541_26

def sourceBody541_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody541_0 sourceBody541_27

def source541 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (541, 3, sourceBody541_28)
end InitECandidate.Proofs.WordStages
