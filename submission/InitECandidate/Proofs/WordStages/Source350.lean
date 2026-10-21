import InitECandidate.Proofs.WordStages.Source334
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody350_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody350_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody350_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody350_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody350_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 4) sourceBody350_2 sourceBody350_3

def sourceBody350_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody350_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody350_4 sourceBody350_5

def sourceBody350_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody350_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody350_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody350_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody350_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody350_9 sourceBody350_10

def sourceBody350_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody350_8 sourceBody350_11

def sourceBody350_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody350_12 sourceBody350_10

def sourceBody350_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody350_13 sourceBody350_5

def sourceBody350_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody350_14 sourceBody350_10

def sourceBody350_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody350_7 sourceBody350_15

def sourceBody350_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody350_6 sourceBody350_16

def sourceBody350_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody350_1 sourceBody350_17

def sourceBody350_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody350_0 sourceBody350_18

def sourceBody350_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody350_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody350_20 sourceBody350_11

def sourceBody350_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody350_19 sourceBody350_21

def source350 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (350, 2, sourceBody350_22)
end InitECandidate.Proofs.WordStages
