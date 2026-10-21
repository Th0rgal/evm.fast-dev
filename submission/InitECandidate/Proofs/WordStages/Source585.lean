import InitECandidate.Proofs.WordStages.Source569
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody585_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody585_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody585_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody585_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody585_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody585_0, 585, 2)) (some 464) ([6, 10]) (some (6, sourceBody585_3, 585, 3))

def sourceBody585_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody585_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_4 sourceBody585_5

def sourceBody585_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_6 sourceBody585_0

def sourceBody585_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_2 sourceBody585_7

def sourceBody585_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_1 sourceBody585_8

def sourceBody585_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody585_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody585_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody585_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody585_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 8) sourceBody585_12 sourceBody585_13

def sourceBody585_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_14 sourceBody585_5

def sourceBody585_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody585_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody585_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody585_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_18 sourceBody585_0

def sourceBody585_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_17 sourceBody585_19

def sourceBody585_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody585_20 sourceBody585_0

def sourceBody585_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_21 sourceBody585_5

def sourceBody585_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_22 sourceBody585_0

def sourceBody585_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_16 sourceBody585_23

def sourceBody585_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_15 sourceBody585_24

def sourceBody585_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_11 sourceBody585_25

def sourceBody585_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_10 sourceBody585_26

def sourceBody585_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody585_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_28 sourceBody585_19

def sourceBody585_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_27 sourceBody585_29

def sourceBody585_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_9 sourceBody585_30

def sourceBody585_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_0 sourceBody585_31

def sourceBody585_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody585_0 sourceBody585_32

def source585 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (585, 3, sourceBody585_33)
end InitECandidate.Proofs.WordStages
