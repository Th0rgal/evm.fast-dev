import InitECandidate.Proofs.WordStages.Source729
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody745_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody745_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody745_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody745_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody745_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody745_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody745_0, 745, 2)) (some 730) ([12, 10, 14]) (some (12, sourceBody745_4, 745, 3))

def sourceBody745_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody745_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_5 sourceBody745_6

def sourceBody745_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_7 sourceBody745_0

def sourceBody745_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_3 sourceBody745_8

def sourceBody745_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_2 sourceBody745_9

def sourceBody745_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_1 sourceBody745_10

def sourceBody745_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_0 sourceBody745_11

def sourceBody745_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_0 sourceBody745_12

def sourceBody745_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody745_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody745_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody745_17 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody745_0, 745, 4)) (some 730) ([12, 10, 14]) (some (12, sourceBody745_4, 745, 5))

def sourceBody745_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_17 sourceBody745_6

def sourceBody745_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_18 sourceBody745_0

def sourceBody745_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_16 sourceBody745_19

def sourceBody745_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_15 sourceBody745_20

def sourceBody745_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_14 sourceBody745_21

def sourceBody745_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_0 sourceBody745_22

def sourceBody745_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_0 sourceBody745_23

def sourceBody745_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_13 sourceBody745_24

def sourceBody745_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody745_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody745_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody745_29 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody745_0, 745, 6)) (some 730) ([12, 10, 14]) (some (12, sourceBody745_4, 745, 7))

def sourceBody745_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_29 sourceBody745_6

def sourceBody745_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_30 sourceBody745_0

def sourceBody745_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_28 sourceBody745_31

def sourceBody745_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_27 sourceBody745_32

def sourceBody745_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_26 sourceBody745_33

def sourceBody745_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_0 sourceBody745_34

def sourceBody745_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_0 sourceBody745_35

def sourceBody745_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_25 sourceBody745_36

def sourceBody745_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody745_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody745_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_39 sourceBody745_0

def sourceBody745_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_38 sourceBody745_40

def sourceBody745_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody745_37 sourceBody745_41

def source745 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (745, 4, sourceBody745_42)
end InitECandidate.Proofs.WordStages
