import InitECandidate.Proofs.WordStages.Source248
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody264_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody264_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody264_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody264_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody264_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody264_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody264_0, 264, 2)) (some 77) ([18, 12, 16]) (some (18, sourceBody264_4, 264, 3))

def sourceBody264_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody264_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_5 sourceBody264_6

def sourceBody264_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_7 sourceBody264_0

def sourceBody264_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_3 sourceBody264_8

def sourceBody264_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_2 sourceBody264_9

def sourceBody264_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_1 sourceBody264_10

def sourceBody264_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_0 sourceBody264_11

def sourceBody264_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_0 sourceBody264_12

def sourceBody264_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody264_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody264_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 18 (Flapjack.WordLangAddr.addr 14 0#64))

def sourceBody264_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_16 sourceBody264_0

def sourceBody264_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_15 sourceBody264_17

def sourceBody264_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_14 sourceBody264_18

def sourceBody264_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_13 sourceBody264_19

def sourceBody264_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 33#64])

def sourceBody264_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody264_23 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody264_0, 264, 4)) (some 87) ([18, 12]) (some (18, sourceBody264_4, 264, 5))

def sourceBody264_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_23 sourceBody264_6

def sourceBody264_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_24 sourceBody264_0

def sourceBody264_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_22 sourceBody264_25

def sourceBody264_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_21 sourceBody264_26

def sourceBody264_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_0 sourceBody264_27

def sourceBody264_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_0 sourceBody264_28

def sourceBody264_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_20 sourceBody264_29

def sourceBody264_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 41#64])

def sourceBody264_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 255#64])

def sourceBody264_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_32 sourceBody264_17

def sourceBody264_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_31 sourceBody264_33

def sourceBody264_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_30 sourceBody264_34

def sourceBody264_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 42#64])

def sourceBody264_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 10)
    (Flapjack.WordLangExpHOL.const 8#64))

def sourceBody264_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_37 sourceBody264_17

def sourceBody264_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_36 sourceBody264_38

def sourceBody264_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_35 sourceBody264_39

def sourceBody264_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 43#64)

def sourceBody264_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody264_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_42 sourceBody264_0

def sourceBody264_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_41 sourceBody264_43

def sourceBody264_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody264_40 sourceBody264_44

def source264 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (264, 6, sourceBody264_45)
end InitECandidate.Proofs.WordStages
