import InitECandidate.Proofs.WordStages.Source404
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody420_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody420_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody420_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody420_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody420_0, 420, 2)) (some 417) ([10]) (some (10, sourceBody420_2, 420, 3))

def sourceBody420_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody420_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_3 sourceBody420_4

def sourceBody420_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_5 sourceBody420_0

def sourceBody420_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_1 sourceBody420_6

def sourceBody420_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_0 sourceBody420_7

def sourceBody420_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_0 sourceBody420_8

def sourceBody420_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody420_0, 420, 4)) (some 403) ([10]) (some (10, sourceBody420_2, 420, 5))

def sourceBody420_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_10 sourceBody420_4

def sourceBody420_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_11 sourceBody420_0

def sourceBody420_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_1 sourceBody420_12

def sourceBody420_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody420_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody420_0, 420, 6)) (some 391) ([10]) (some (10, sourceBody420_2, 420, 7))

def sourceBody420_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_15 sourceBody420_4

def sourceBody420_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_16 sourceBody420_0

def sourceBody420_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_14 sourceBody420_17

def sourceBody420_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody420_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody420_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody420_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 8

def sourceBody420_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_22 sourceBody420_0

def sourceBody420_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_21 sourceBody420_23

def sourceBody420_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_24 sourceBody420_0

def sourceBody420_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_20 sourceBody420_25

def sourceBody420_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_0 sourceBody420_26

def sourceBody420_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_19 sourceBody420_27

def sourceBody420_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_0 sourceBody420_28

def sourceBody420_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_18 sourceBody420_29

def sourceBody420_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody420_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 136#64]))

def sourceBody420_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_32 sourceBody420_25

def sourceBody420_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_0 sourceBody420_33

def sourceBody420_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_31 sourceBody420_34

def sourceBody420_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_0 sourceBody420_35

def sourceBody420_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_30 sourceBody420_36

def sourceBody420_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody420_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody420_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody420_41 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody420_0, 420, 8)) (some 419) ([4, 8]) (some (4, sourceBody420_40, 420, 9))

def sourceBody420_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_41 sourceBody420_4

def sourceBody420_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_42 sourceBody420_0

def sourceBody420_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_39 sourceBody420_43

def sourceBody420_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_38 sourceBody420_44

def sourceBody420_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_0 sourceBody420_45

def sourceBody420_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_0 sourceBody420_46

def sourceBody420_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_37 sourceBody420_47

def sourceBody420_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody420_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody420_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_50 sourceBody420_0

def sourceBody420_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_49 sourceBody420_51

def sourceBody420_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_48 sourceBody420_52

def sourceBody420_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_13 sourceBody420_53

def sourceBody420_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_0 sourceBody420_54

def sourceBody420_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_0 sourceBody420_55

def sourceBody420_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody420_9 sourceBody420_56

def source420 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (420, 2, sourceBody420_57)
end InitECandidate.Proofs.WordStages
