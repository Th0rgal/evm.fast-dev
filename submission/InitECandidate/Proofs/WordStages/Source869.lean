import InitECandidate.Proofs.WordStages.Source853
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody869_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody869_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody869_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody869_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody869_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.lookup (Flapjack.WordStore.temp 0#5))

def sourceBody869_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_4 sourceBody869_0

def sourceBody869_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_5 sourceBody869_0

def sourceBody869_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody869_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.shareInst Flapjack.WordMemOp.store8 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.const 2688614400#64, Flapjack.WordLangExpHOL.const 70#64])

def sourceBody869_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_8 sourceBody869_0

def sourceBody869_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_7 sourceBody869_9

def sourceBody869_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_0 sourceBody869_10

def sourceBody869_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody869_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4)

def sourceBody869_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_13 sourceBody869_0

def sourceBody869_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_14 sourceBody869_0

def sourceBody869_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_12 sourceBody869_15

def sourceBody869_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_0 sourceBody869_16

def sourceBody869_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 9#64)

def sourceBody869_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_18 sourceBody869_2

def sourceBody869_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_17 sourceBody869_19

def sourceBody869_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_11 sourceBody869_20

def sourceBody869_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_6 sourceBody869_21

def sourceBody869_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_3 sourceBody869_22

def sourceBody869_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 5#64) sourceBody869_2 sourceBody869_23

def sourceBody869_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_24 sourceBody869_3

def sourceBody869_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody869_0, 869, 2)) (some 868) ([4]) (some (4, sourceBody869_25, 869, 3))

def sourceBody869_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_26 sourceBody869_3

def sourceBody869_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_27 sourceBody869_0

def sourceBody869_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_1 sourceBody869_28

def sourceBody869_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_0 sourceBody869_29

def sourceBody869_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_0 sourceBody869_30

def sourceBody869_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody869_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody869_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_33 sourceBody869_0

def sourceBody869_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_32 sourceBody869_34

def sourceBody869_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_31 sourceBody869_35

def sourceBody869_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_0 sourceBody869_36

def sourceBody869_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody869_0 sourceBody869_37

def source869 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (869, 2, sourceBody869_38)
end InitECandidate.Proofs.WordStages
