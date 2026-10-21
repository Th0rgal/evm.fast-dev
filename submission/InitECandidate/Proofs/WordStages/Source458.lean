import InitECandidate.Proofs.WordStages.Source442
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody458_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 8])

def sourceBody458_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody458_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody458_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody458_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 16) sourceBody458_2 sourceBody458_3

def sourceBody458_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody458_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody458_4 sourceBody458_5

def sourceBody458_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody458_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 18446744073709551615#64)

def sourceBody458_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody458_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody458_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody458_9 sourceBody458_10

def sourceBody458_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody458_8 sourceBody458_11

def sourceBody458_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody458_12 sourceBody458_10

def sourceBody458_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody458_13 sourceBody458_5

def sourceBody458_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody458_14 sourceBody458_10

def sourceBody458_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody458_7 sourceBody458_15

def sourceBody458_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody458_6 sourceBody458_16

def sourceBody458_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody458_1 sourceBody458_17

def sourceBody458_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody458_0 sourceBody458_18

def sourceBody458_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody458_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody458_20 sourceBody458_11

def sourceBody458_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody458_19 sourceBody458_21

def source458 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (458, 5, sourceBody458_22)
end InitECandidate.Proofs.WordStages
