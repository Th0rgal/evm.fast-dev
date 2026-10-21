import InitECandidate.Proofs.WordStages.Source425
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody441_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody441_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody441_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody441_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody441_0, 441, 2)) (some 435) ([12]) (some (12, sourceBody441_2, 441, 3))

def sourceBody441_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody441_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_3 sourceBody441_4

def sourceBody441_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_5 sourceBody441_0

def sourceBody441_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_1 sourceBody441_6

def sourceBody441_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody441_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody441_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody441_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody441_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody441_0, 441, 4)) (some 436) ([18, 10, 14]) (some (18, sourceBody441_11, 441, 5))

def sourceBody441_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_12 sourceBody441_4

def sourceBody441_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_13 sourceBody441_0

def sourceBody441_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_10 sourceBody441_14

def sourceBody441_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_9 sourceBody441_15

def sourceBody441_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_8 sourceBody441_16

def sourceBody441_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody441_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody441_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody441_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 18) 14

def sourceBody441_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_21 sourceBody441_0

def sourceBody441_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_20 sourceBody441_22

def sourceBody441_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_23 sourceBody441_0

def sourceBody441_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_19 sourceBody441_24

def sourceBody441_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_0 sourceBody441_25

def sourceBody441_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_18 sourceBody441_26

def sourceBody441_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_0 sourceBody441_27

def sourceBody441_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody441_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody441_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_30 sourceBody441_24

def sourceBody441_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_0 sourceBody441_31

def sourceBody441_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_29 sourceBody441_32

def sourceBody441_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_0 sourceBody441_33

def sourceBody441_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_28 sourceBody441_34

def sourceBody441_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody441_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody441_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_37 sourceBody441_0

def sourceBody441_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_36 sourceBody441_38

def sourceBody441_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_35 sourceBody441_39

def sourceBody441_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_17 sourceBody441_40

def sourceBody441_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_0 sourceBody441_41

def sourceBody441_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_0 sourceBody441_42

def sourceBody441_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_7 sourceBody441_43

def sourceBody441_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_0 sourceBody441_44

def sourceBody441_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody441_0 sourceBody441_45

def source441 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (441, 5, sourceBody441_46)
end InitECandidate.Proofs.WordStages
