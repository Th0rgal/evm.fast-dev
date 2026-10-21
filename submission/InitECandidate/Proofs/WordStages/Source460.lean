import InitECandidate.Proofs.WordStages.Source444
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody460_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody460_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 31#64])

def sourceBody460_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody460_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody460_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody460_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody460_6 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.WordRegImm.reg 10) sourceBody460_4 sourceBody460_5

def sourceBody460_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody460_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_6 sourceBody460_7

def sourceBody460_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody460_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody460_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody460_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_11 sourceBody460_0

def sourceBody460_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_10 sourceBody460_12

def sourceBody460_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody460_13 sourceBody460_0

def sourceBody460_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_14 sourceBody460_7

def sourceBody460_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_15 sourceBody460_0

def sourceBody460_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_9 sourceBody460_16

def sourceBody460_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_8 sourceBody460_17

def sourceBody460_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_3 sourceBody460_18

def sourceBody460_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_2 sourceBody460_19

def sourceBody460_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody460_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.const 32#64, Flapjack.WordLangExpHOL.var 6])

def sourceBody460_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody460_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody460_0, 460, 2)) (some 459) ([4, 10]) (some (4, sourceBody460_23, 460, 3))

def sourceBody460_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_24 sourceBody460_7

def sourceBody460_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_25 sourceBody460_0

def sourceBody460_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_22 sourceBody460_26

def sourceBody460_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_21 sourceBody460_27

def sourceBody460_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 12)

def sourceBody460_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody460_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_30 sourceBody460_0

def sourceBody460_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_29 sourceBody460_31

def sourceBody460_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_28 sourceBody460_32

def sourceBody460_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_0 sourceBody460_33

def sourceBody460_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_0 sourceBody460_34

def sourceBody460_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_20 sourceBody460_35

def sourceBody460_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_1 sourceBody460_36

def sourceBody460_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody460_0 sourceBody460_37

def source460 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (460, 2, sourceBody460_38)
end InitECandidate.Proofs.WordStages
