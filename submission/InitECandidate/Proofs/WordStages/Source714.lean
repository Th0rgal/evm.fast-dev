import InitECandidate.Proofs.WordStages.Source698
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody714_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 2)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 63#64)])

def sourceBody714_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 6)
        (Flapjack.WordLangExpHOL.const 63#64)])

def sourceBody714_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 6)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
        (Flapjack.WordLangExpHOL.const 63#64)])

def sourceBody714_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 8)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 10)
        (Flapjack.WordLangExpHOL.const 63#64)])

def sourceBody714_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 10)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
        (Flapjack.WordLangExpHOL.const 63#64)])

def sourceBody714_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 12)
    (Flapjack.WordLangExpHOL.const 1#64))

def sourceBody714_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24, 14, 20, 18, 22, 16]

def sourceBody714_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody714_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody714_6 sourceBody714_7

def sourceBody714_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody714_5 sourceBody714_8

def sourceBody714_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody714_4 sourceBody714_9

def sourceBody714_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody714_3 sourceBody714_10

def sourceBody714_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody714_2 sourceBody714_11

def sourceBody714_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody714_1 sourceBody714_12

def sourceBody714_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody714_0 sourceBody714_13

def source714 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (714, 7, sourceBody714_14)
end InitECandidate.Proofs.WordStages
