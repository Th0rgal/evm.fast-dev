import InitECandidate.Proofs.WordStages.Source784
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody800_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody800_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody800_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody800_0, 800, 2)) (some 69) ([]) (some (8, sourceBody800_1, 800, 3))

def sourceBody800_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody800_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_2 sourceBody800_3

def sourceBody800_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_4 sourceBody800_0

def sourceBody800_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody800_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody800_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody800_0, 800, 4)) (some 68) ([14]) (some (14, sourceBody800_7, 800, 5))

def sourceBody800_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_8 sourceBody800_3

def sourceBody800_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_9 sourceBody800_0

def sourceBody800_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_6 sourceBody800_10

def sourceBody800_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody800_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody800_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody800_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody800_0, 800, 6)) (some 797) ([10, 18]) (some (10, sourceBody800_14, 800, 7))

def sourceBody800_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_15 sourceBody800_3

def sourceBody800_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_16 sourceBody800_0

def sourceBody800_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_13 sourceBody800_17

def sourceBody800_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_12 sourceBody800_18

def sourceBody800_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_0 sourceBody800_19

def sourceBody800_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_0 sourceBody800_20

def sourceBody800_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody800_23 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody800_0, 800, 8)) (some 799) ([10, 18]) (some (10, sourceBody800_14, 800, 9))

def sourceBody800_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_23 sourceBody800_3

def sourceBody800_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_24 sourceBody800_0

def sourceBody800_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_22 sourceBody800_25

def sourceBody800_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_12 sourceBody800_26

def sourceBody800_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_0 sourceBody800_27

def sourceBody800_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_0 sourceBody800_28

def sourceBody800_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_21 sourceBody800_29

def sourceBody800_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody800_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 1632#64])

def sourceBody800_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody800_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody800_0, 800, 10)) (some 780) ([10, 18, 6, 12]) (some (10, sourceBody800_14, 800, 11))

def sourceBody800_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_34 sourceBody800_3

def sourceBody800_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_35 sourceBody800_0

def sourceBody800_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_33 sourceBody800_36

def sourceBody800_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_32 sourceBody800_37

def sourceBody800_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_22 sourceBody800_38

def sourceBody800_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_31 sourceBody800_39

def sourceBody800_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_0 sourceBody800_40

def sourceBody800_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_0 sourceBody800_41

def sourceBody800_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_30 sourceBody800_42

def sourceBody800_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody800_45 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody800_0, 800, 12)) (some 70) ([10]) (some (10, sourceBody800_14, 800, 13))

def sourceBody800_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_45 sourceBody800_3

def sourceBody800_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_46 sourceBody800_0

def sourceBody800_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_44 sourceBody800_47

def sourceBody800_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_0 sourceBody800_48

def sourceBody800_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_0 sourceBody800_49

def sourceBody800_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_43 sourceBody800_50

def sourceBody800_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody800_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody800_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_53 sourceBody800_0

def sourceBody800_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_52 sourceBody800_54

def sourceBody800_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_51 sourceBody800_55

def sourceBody800_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_11 sourceBody800_56

def sourceBody800_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_0 sourceBody800_57

def sourceBody800_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_0 sourceBody800_58

def sourceBody800_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_5 sourceBody800_59

def sourceBody800_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_0 sourceBody800_60

def sourceBody800_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody800_0 sourceBody800_61

def source800 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (800, 3, sourceBody800_62)
end InitECandidate.Proofs.WordStages
