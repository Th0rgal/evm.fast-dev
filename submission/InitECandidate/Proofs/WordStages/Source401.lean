import InitECandidate.Proofs.WordStages.Source385
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody401_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody401_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody401_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody401_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody401_0, 401, 2)) (some 400) ([12]) (some (12, sourceBody401_2, 401, 3))

def sourceBody401_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody401_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_3 sourceBody401_4

def sourceBody401_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_5 sourceBody401_0

def sourceBody401_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_1 sourceBody401_6

def sourceBody401_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody401_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody401_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody401_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody401_12 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.WordRegImm.reg 10) sourceBody401_10 sourceBody401_11

def sourceBody401_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_12 sourceBody401_4

def sourceBody401_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody401_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody401_0, 401, 4)) (some 390) ([]) (some (12, sourceBody401_2, 401, 5))

def sourceBody401_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_15 sourceBody401_4

def sourceBody401_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_16 sourceBody401_0

def sourceBody401_18 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody401_17 sourceBody401_0

def sourceBody401_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_18 sourceBody401_4

def sourceBody401_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_19 sourceBody401_0

def sourceBody401_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_14 sourceBody401_20

def sourceBody401_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_13 sourceBody401_21

def sourceBody401_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_9 sourceBody401_22

def sourceBody401_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_8 sourceBody401_23

def sourceBody401_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody401_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody401_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_26 sourceBody401_0

def sourceBody401_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_25 sourceBody401_27

def sourceBody401_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_24 sourceBody401_28

def sourceBody401_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_7 sourceBody401_29

def sourceBody401_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_0 sourceBody401_30

def sourceBody401_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody401_0 sourceBody401_31

def source401 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (401, 2, sourceBody401_32)
end InitECandidate.Proofs.WordStages
