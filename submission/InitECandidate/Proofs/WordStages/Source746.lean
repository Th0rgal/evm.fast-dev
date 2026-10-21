import InitECandidate.Proofs.WordStages.Source730
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody746_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody746_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody746_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody746_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody746_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody746_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody746_0, 746, 2)) (some 731) ([12, 10, 14]) (some (12, sourceBody746_4, 746, 3))

def sourceBody746_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody746_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_5 sourceBody746_6

def sourceBody746_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_7 sourceBody746_0

def sourceBody746_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_3 sourceBody746_8

def sourceBody746_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_2 sourceBody746_9

def sourceBody746_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_1 sourceBody746_10

def sourceBody746_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_0 sourceBody746_11

def sourceBody746_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_0 sourceBody746_12

def sourceBody746_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody746_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody746_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody746_17 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody746_0, 746, 4)) (some 731) ([12, 10, 14]) (some (12, sourceBody746_4, 746, 5))

def sourceBody746_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_17 sourceBody746_6

def sourceBody746_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_18 sourceBody746_0

def sourceBody746_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_16 sourceBody746_19

def sourceBody746_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_15 sourceBody746_20

def sourceBody746_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_14 sourceBody746_21

def sourceBody746_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_0 sourceBody746_22

def sourceBody746_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_0 sourceBody746_23

def sourceBody746_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_13 sourceBody746_24

def sourceBody746_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody746_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody746_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody746_29 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody746_0, 746, 6)) (some 731) ([12, 10, 14]) (some (12, sourceBody746_4, 746, 7))

def sourceBody746_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_29 sourceBody746_6

def sourceBody746_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_30 sourceBody746_0

def sourceBody746_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_28 sourceBody746_31

def sourceBody746_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_27 sourceBody746_32

def sourceBody746_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_26 sourceBody746_33

def sourceBody746_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_0 sourceBody746_34

def sourceBody746_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_0 sourceBody746_35

def sourceBody746_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_25 sourceBody746_36

def sourceBody746_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody746_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody746_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_39 sourceBody746_0

def sourceBody746_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_38 sourceBody746_40

def sourceBody746_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody746_37 sourceBody746_41

def source746 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (746, 4, sourceBody746_42)
end InitECandidate.Proofs.WordStages
