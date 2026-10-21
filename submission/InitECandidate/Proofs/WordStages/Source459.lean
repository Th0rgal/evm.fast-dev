import InitECandidate.Proofs.WordStages.Source443
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody459_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody459_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 4])

def sourceBody459_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody459_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody459_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody459_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody459_6 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 8) sourceBody459_4 sourceBody459_5

def sourceBody459_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody459_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody459_6 sourceBody459_7

def sourceBody459_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody459_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 18446744073709551615#64)

def sourceBody459_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody459_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody459_11 sourceBody459_0

def sourceBody459_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody459_10 sourceBody459_12

def sourceBody459_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody459_13 sourceBody459_0

def sourceBody459_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody459_14 sourceBody459_7

def sourceBody459_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody459_15 sourceBody459_0

def sourceBody459_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody459_9 sourceBody459_16

def sourceBody459_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody459_8 sourceBody459_17

def sourceBody459_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody459_3 sourceBody459_18

def sourceBody459_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody459_2 sourceBody459_19

def sourceBody459_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody459_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody459_21 sourceBody459_12

def sourceBody459_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody459_20 sourceBody459_22

def sourceBody459_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody459_1 sourceBody459_23

def sourceBody459_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody459_0 sourceBody459_24

def source459 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (459, 3, sourceBody459_25)
end InitECandidate.Proofs.WordStages
