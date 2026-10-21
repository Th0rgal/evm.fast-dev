import InitECandidate.Proofs.WordStages.Source851
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody867_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody867_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody867_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody867_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody867_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.lookup (Flapjack.WordStore.temp 0#5))

def sourceBody867_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_4 sourceBody867_0

def sourceBody867_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_5 sourceBody867_0

def sourceBody867_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody867_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.shareInst Flapjack.WordMemOp.store8 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.const 2688614400#64, Flapjack.WordLangExpHOL.const 70#64])

def sourceBody867_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_8 sourceBody867_0

def sourceBody867_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_7 sourceBody867_9

def sourceBody867_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_0 sourceBody867_10

def sourceBody867_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody867_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4)

def sourceBody867_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_13 sourceBody867_0

def sourceBody867_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_14 sourceBody867_0

def sourceBody867_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_12 sourceBody867_15

def sourceBody867_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_0 sourceBody867_16

def sourceBody867_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 9#64)

def sourceBody867_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_18 sourceBody867_2

def sourceBody867_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_17 sourceBody867_19

def sourceBody867_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_11 sourceBody867_20

def sourceBody867_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_6 sourceBody867_21

def sourceBody867_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_3 sourceBody867_22

def sourceBody867_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 3#64) sourceBody867_2 sourceBody867_23

def sourceBody867_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_24 sourceBody867_3

def sourceBody867_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody867_0, 867, 2)) (some 866) ([4]) (some (4, sourceBody867_25, 867, 3))

def sourceBody867_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_26 sourceBody867_3

def sourceBody867_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_27 sourceBody867_0

def sourceBody867_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_1 sourceBody867_28

def sourceBody867_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_0 sourceBody867_29

def sourceBody867_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_0 sourceBody867_30

def sourceBody867_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody867_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody867_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_33 sourceBody867_0

def sourceBody867_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_32 sourceBody867_34

def sourceBody867_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_31 sourceBody867_35

def sourceBody867_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_0 sourceBody867_36

def sourceBody867_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody867_0 sourceBody867_37

def source867 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (867, 2, sourceBody867_38)
end InitECandidate.Proofs.WordStages
