import InitECandidate.Proofs.WordStages.Source475
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody491_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody491_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody491_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody491_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody491_0, 491, 2)) (some 489) ([12]) (some (12, sourceBody491_2, 491, 3))

def sourceBody491_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody491_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody491_3 sourceBody491_4

def sourceBody491_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody491_5 sourceBody491_0

def sourceBody491_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody491_1 sourceBody491_6

def sourceBody491_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody491_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody491_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody491_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody491_12 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.reg 10) sourceBody491_10 sourceBody491_11

def sourceBody491_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody491_12 sourceBody491_4

def sourceBody491_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody491_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 100#64)

def sourceBody491_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody491_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody491_16 sourceBody491_0

def sourceBody491_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody491_15 sourceBody491_17

def sourceBody491_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody491_18 sourceBody491_0

def sourceBody491_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody491_19 sourceBody491_4

def sourceBody491_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody491_20 sourceBody491_0

def sourceBody491_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody491_14 sourceBody491_21

def sourceBody491_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody491_13 sourceBody491_22

def sourceBody491_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody491_9 sourceBody491_23

def sourceBody491_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody491_8 sourceBody491_24

def sourceBody491_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 3000#64)

def sourceBody491_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody491_26 sourceBody491_17

def sourceBody491_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody491_25 sourceBody491_27

def sourceBody491_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody491_7 sourceBody491_28

def sourceBody491_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody491_0 sourceBody491_29

def sourceBody491_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody491_0 sourceBody491_30

def source491 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (491, 2, sourceBody491_31)
end InitECandidate.Proofs.WordStages
