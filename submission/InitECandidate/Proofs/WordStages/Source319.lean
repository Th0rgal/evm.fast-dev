import InitECandidate.Proofs.WordStages.Source303
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody319_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody319_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody319_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody319_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody319_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 4) sourceBody319_2 sourceBody319_3

def sourceBody319_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody319_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_4 sourceBody319_5

def sourceBody319_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody319_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody319_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody319_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody319_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_9 sourceBody319_10

def sourceBody319_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_8 sourceBody319_11

def sourceBody319_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody319_12 sourceBody319_10

def sourceBody319_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_13 sourceBody319_5

def sourceBody319_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_14 sourceBody319_10

def sourceBody319_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_7 sourceBody319_15

def sourceBody319_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_6 sourceBody319_16

def sourceBody319_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_1 sourceBody319_17

def sourceBody319_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_0 sourceBody319_18

def sourceBody319_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody319_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_20 sourceBody319_18

def sourceBody319_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_19 sourceBody319_21

def sourceBody319_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody319_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 4) sourceBody319_2 sourceBody319_3

def sourceBody319_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_24 sourceBody319_5

def sourceBody319_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_25 sourceBody319_16

def sourceBody319_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_1 sourceBody319_26

def sourceBody319_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_23 sourceBody319_27

def sourceBody319_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_22 sourceBody319_28

def sourceBody319_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody319_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_30 sourceBody319_11

def sourceBody319_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody319_29 sourceBody319_31

def source319 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (319, 2, sourceBody319_32)
end InitECandidate.Proofs.WordStages
