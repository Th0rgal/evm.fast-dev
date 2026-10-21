import InitECandidate.Proofs.WordStages.Source686
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody702_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 14],
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 16],
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 18],
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 20],
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 22],
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.var 24]])

def sourceBody702_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody702_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody702_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody702_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 28 (Flapjack.WordRegImm.reg 32) sourceBody702_2 sourceBody702_3

def sourceBody702_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody702_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody702_4 sourceBody702_5

def sourceBody702_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody702_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody702_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30]

def sourceBody702_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody702_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody702_9 sourceBody702_10

def sourceBody702_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody702_8 sourceBody702_11

def sourceBody702_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody702_12 sourceBody702_10

def sourceBody702_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody702_13 sourceBody702_5

def sourceBody702_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody702_14 sourceBody702_10

def sourceBody702_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody702_7 sourceBody702_15

def sourceBody702_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody702_6 sourceBody702_16

def sourceBody702_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody702_1 sourceBody702_17

def sourceBody702_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody702_0 sourceBody702_18

def sourceBody702_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody702_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody702_20 sourceBody702_11

def sourceBody702_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody702_19 sourceBody702_21

def source702 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (702, 13, sourceBody702_22)
end InitECandidate.Proofs.WordStages
