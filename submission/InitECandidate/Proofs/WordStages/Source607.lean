import InitECandidate.Proofs.WordStages.Source591
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody607_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody607_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 168#64]))

def sourceBody607_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 264#64]))

def sourceBody607_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody607_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody607_0, 607, 2)) (some 194) ([8, 4]) (some (8, sourceBody607_3, 607, 3))

def sourceBody607_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody607_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody607_4 sourceBody607_5

def sourceBody607_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody607_6 sourceBody607_0

def sourceBody607_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody607_2 sourceBody607_7

def sourceBody607_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody607_1 sourceBody607_8

def sourceBody607_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody607_0 sourceBody607_9

def sourceBody607_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody607_0 sourceBody607_10

def sourceBody607_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 176#64]))

def sourceBody607_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 272#64]))

def sourceBody607_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody607_0, 607, 4)) (some 194) ([8, 4]) (some (8, sourceBody607_3, 607, 5))

def sourceBody607_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody607_14 sourceBody607_5

def sourceBody607_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody607_15 sourceBody607_0

def sourceBody607_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody607_13 sourceBody607_16

def sourceBody607_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody607_12 sourceBody607_17

def sourceBody607_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody607_0 sourceBody607_18

def sourceBody607_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody607_0 sourceBody607_19

def sourceBody607_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody607_11 sourceBody607_20

def sourceBody607_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody607_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody607_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody607_23 sourceBody607_0

def sourceBody607_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody607_22 sourceBody607_24

def sourceBody607_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody607_21 sourceBody607_25

def source607 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (607, 2, sourceBody607_26)
end InitECandidate.Proofs.WordStages
