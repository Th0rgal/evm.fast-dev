import InitECandidate.Proofs.WordStages.Source836
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody852_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody852_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody852_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody852_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody852_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 4) sourceBody852_2 sourceBody852_3

def sourceBody852_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody852_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody852_4 sourceBody852_5

def sourceBody852_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody852_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody852_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody852_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody852_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody852_9 sourceBody852_10

def sourceBody852_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody852_8 sourceBody852_11

def sourceBody852_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody852_12 sourceBody852_10

def sourceBody852_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody852_13 sourceBody852_5

def sourceBody852_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody852_14 sourceBody852_10

def sourceBody852_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody852_7 sourceBody852_15

def sourceBody852_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody852_6 sourceBody852_16

def sourceBody852_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody852_1 sourceBody852_17

def sourceBody852_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody852_0 sourceBody852_18

def sourceBody852_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody852_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody852_20 sourceBody852_11

def sourceBody852_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody852_19 sourceBody852_21

def source852 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (852, 2, sourceBody852_22)
end InitECandidate.Proofs.WordStages
