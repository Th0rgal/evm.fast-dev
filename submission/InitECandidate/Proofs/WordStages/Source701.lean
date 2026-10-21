import InitECandidate.Proofs.WordStages.Source685
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody701_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 12])

def sourceBody701_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody701_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody701_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody701_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 18) sourceBody701_2 sourceBody701_3

def sourceBody701_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody701_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody701_4 sourceBody701_5

def sourceBody701_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody701_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody701_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody701_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody701_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody701_9 sourceBody701_10

def sourceBody701_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody701_8 sourceBody701_11

def sourceBody701_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody701_12 sourceBody701_10

def sourceBody701_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody701_13 sourceBody701_5

def sourceBody701_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody701_14 sourceBody701_10

def sourceBody701_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody701_7 sourceBody701_15

def sourceBody701_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody701_6 sourceBody701_16

def sourceBody701_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody701_1 sourceBody701_17

def sourceBody701_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody701_0 sourceBody701_18

def sourceBody701_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody701_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody701_20 sourceBody701_11

def sourceBody701_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody701_19 sourceBody701_21

def source701 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (701, 7, sourceBody701_22)
end InitECandidate.Proofs.WordStages
