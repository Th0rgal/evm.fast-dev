import InitECandidate.Proofs.WordStages.Source326
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody342_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody342_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody342_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody342_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody342_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody342_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.lookup (Flapjack.WordStore.temp 0#5))

def sourceBody342_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_5 sourceBody342_0

def sourceBody342_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_6 sourceBody342_0

def sourceBody342_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.const 100#64, Flapjack.WordLangExpHOL.var 6])

def sourceBody342_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 10)

def sourceBody342_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_9 sourceBody342_0

def sourceBody342_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_10 sourceBody342_0

def sourceBody342_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_8 sourceBody342_11

def sourceBody342_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_0 sourceBody342_12

def sourceBody342_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody342_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_14 sourceBody342_3

def sourceBody342_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_13 sourceBody342_15

def sourceBody342_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_7 sourceBody342_16

def sourceBody342_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_4 sourceBody342_17

def sourceBody342_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 1#64) sourceBody342_3 sourceBody342_18

def sourceBody342_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_19 sourceBody342_4

def sourceBody342_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody342_0, 342, 2)) (some 341) ([10, 8]) (some (10, sourceBody342_20, 342, 3))

def sourceBody342_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_21 sourceBody342_4

def sourceBody342_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_22 sourceBody342_0

def sourceBody342_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_2 sourceBody342_23

def sourceBody342_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_1 sourceBody342_24

def sourceBody342_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody342_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody342_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_27 sourceBody342_0

def sourceBody342_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_26 sourceBody342_28

def sourceBody342_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_25 sourceBody342_29

def sourceBody342_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_0 sourceBody342_30

def sourceBody342_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_0 sourceBody342_31

def sourceBody342_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_0 sourceBody342_32

def sourceBody342_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody342_0 sourceBody342_33

def source342 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (342, 3, sourceBody342_34)
end InitECandidate.Proofs.WordStages
