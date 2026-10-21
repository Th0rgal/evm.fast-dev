import InitECandidate.Proofs.WordStages.Source393
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody409_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody409_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody409_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody409_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody409_0, 409, 2)) (some 402) ([12]) (some (12, sourceBody409_2, 409, 3))

def sourceBody409_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody409_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody409_3 sourceBody409_4

def sourceBody409_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody409_5 sourceBody409_0

def sourceBody409_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody409_1 sourceBody409_6

def sourceBody409_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody409_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody409_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody409_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody409_12 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.WordRegImm.reg 10) sourceBody409_10 sourceBody409_11

def sourceBody409_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody409_12 sourceBody409_4

def sourceBody409_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody409_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody409_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody409_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody409_16 sourceBody409_0

def sourceBody409_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody409_15 sourceBody409_17

def sourceBody409_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody409_18 sourceBody409_0

def sourceBody409_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody409_19 sourceBody409_4

def sourceBody409_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody409_20 sourceBody409_0

def sourceBody409_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody409_14 sourceBody409_21

def sourceBody409_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody409_13 sourceBody409_22

def sourceBody409_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody409_9 sourceBody409_23

def sourceBody409_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody409_8 sourceBody409_24

def sourceBody409_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody409_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody409_26 sourceBody409_17

def sourceBody409_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody409_25 sourceBody409_27

def sourceBody409_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody409_7 sourceBody409_28

def sourceBody409_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody409_0 sourceBody409_29

def sourceBody409_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody409_0 sourceBody409_30

def source409 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (409, 2, sourceBody409_31)
end InitECandidate.Proofs.WordStages
