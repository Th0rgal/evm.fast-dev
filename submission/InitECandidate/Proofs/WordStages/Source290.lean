import InitECandidate.Proofs.WordStages.Source274
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody290_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody290_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody290_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody290_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody290_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([14, 8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody290_0, 290, 2)) (some 186) ([12, 10]) (some (12, sourceBody290_3, 290, 3))

def sourceBody290_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody290_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_4 sourceBody290_5

def sourceBody290_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_6 sourceBody290_0

def sourceBody290_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_2 sourceBody290_7

def sourceBody290_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_1 sourceBody290_8

def sourceBody290_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody290_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody290_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody290_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody290_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 16) sourceBody290_12 sourceBody290_13

def sourceBody290_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_14 sourceBody290_5

def sourceBody290_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody290_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody290_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12, 10, 16]

def sourceBody290_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_18 sourceBody290_0

def sourceBody290_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_11 sourceBody290_19

def sourceBody290_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_13 sourceBody290_20

def sourceBody290_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_17 sourceBody290_21

def sourceBody290_23 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody290_22 sourceBody290_0

def sourceBody290_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_23 sourceBody290_5

def sourceBody290_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_24 sourceBody290_0

def sourceBody290_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_16 sourceBody290_25

def sourceBody290_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_15 sourceBody290_26

def sourceBody290_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_11 sourceBody290_27

def sourceBody290_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_10 sourceBody290_28

def sourceBody290_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody290_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 8))

def sourceBody290_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody290_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_32 sourceBody290_19

def sourceBody290_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_31 sourceBody290_33

def sourceBody290_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_30 sourceBody290_34

def sourceBody290_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_29 sourceBody290_35

def sourceBody290_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_9 sourceBody290_36

def sourceBody290_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_0 sourceBody290_37

def sourceBody290_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_0 sourceBody290_38

def sourceBody290_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_0 sourceBody290_39

def sourceBody290_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody290_0 sourceBody290_40

def source290 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (290, 3, sourceBody290_41)
end InitECandidate.Proofs.WordStages
