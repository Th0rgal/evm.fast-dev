import InitECandidate.Proofs.WordStages.Source835
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody851_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody851_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody851_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody851_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody851_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 4) sourceBody851_2 sourceBody851_3

def sourceBody851_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody851_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody851_4 sourceBody851_5

def sourceBody851_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody851_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody851_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody851_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody851_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody851_9 sourceBody851_10

def sourceBody851_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody851_8 sourceBody851_11

def sourceBody851_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody851_12 sourceBody851_10

def sourceBody851_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody851_13 sourceBody851_5

def sourceBody851_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody851_14 sourceBody851_10

def sourceBody851_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody851_7 sourceBody851_15

def sourceBody851_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody851_6 sourceBody851_16

def sourceBody851_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody851_1 sourceBody851_17

def sourceBody851_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody851_0 sourceBody851_18

def sourceBody851_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody851_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody851_20 sourceBody851_11

def sourceBody851_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody851_19 sourceBody851_21

def source851 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (851, 2, sourceBody851_22)
end InitECandidate.Proofs.WordStages
