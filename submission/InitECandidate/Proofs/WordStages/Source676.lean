import InitECandidate.Proofs.WordStages.Source660
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody676_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody676_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 2)
    (Flapjack.WordLangExpHOL.const 5#64))

def sourceBody676_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody676_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody676_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody676_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody676_0, 676, 2)) (some 675) ([10, 8]) (some (10, sourceBody676_4, 676, 3))

def sourceBody676_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody676_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_5 sourceBody676_6

def sourceBody676_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_7 sourceBody676_0

def sourceBody676_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_3 sourceBody676_8

def sourceBody676_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_2 sourceBody676_9

def sourceBody676_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_0 sourceBody676_10

def sourceBody676_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_0 sourceBody676_11

def sourceBody676_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 12])

def sourceBody676_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody676_0, 676, 4)) (some 675) ([10, 8]) (some (10, sourceBody676_4, 676, 5))

def sourceBody676_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_14 sourceBody676_6

def sourceBody676_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_15 sourceBody676_0

def sourceBody676_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_13 sourceBody676_16

def sourceBody676_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_2 sourceBody676_17

def sourceBody676_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_0 sourceBody676_18

def sourceBody676_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_0 sourceBody676_19

def sourceBody676_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_12 sourceBody676_20

def sourceBody676_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 4,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
        (Flapjack.WordLangExpHOL.const 1#64)])

def sourceBody676_23 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody676_0, 676, 6)) (some 674) ([10, 8]) (some (10, sourceBody676_4, 676, 7))

def sourceBody676_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_23 sourceBody676_6

def sourceBody676_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_24 sourceBody676_0

def sourceBody676_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_22 sourceBody676_25

def sourceBody676_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_2 sourceBody676_26

def sourceBody676_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_0 sourceBody676_27

def sourceBody676_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_0 sourceBody676_28

def sourceBody676_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_21 sourceBody676_29

def sourceBody676_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody676_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody676_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_32 sourceBody676_0

def sourceBody676_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_31 sourceBody676_33

def sourceBody676_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_30 sourceBody676_34

def sourceBody676_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_1 sourceBody676_35

def sourceBody676_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody676_0 sourceBody676_36

def source676 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (676, 3, sourceBody676_37)
end InitECandidate.Proofs.WordStages
