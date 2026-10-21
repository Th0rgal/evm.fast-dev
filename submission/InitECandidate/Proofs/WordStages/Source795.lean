import InitECandidate.Proofs.WordStages.Source779
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody795_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody795_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody795_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody795_0, 795, 2)) (some 69) ([]) (some (28, sourceBody795_1, 795, 3))

def sourceBody795_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody795_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_2 sourceBody795_3

def sourceBody795_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_4 sourceBody795_0

def sourceBody795_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 144#64)

def sourceBody795_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody795_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody795_0, 795, 4)) (some 68) ([22]) (some (22, sourceBody795_7, 795, 5))

def sourceBody795_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_8 sourceBody795_3

def sourceBody795_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_9 sourceBody795_0

def sourceBody795_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_6 sourceBody795_10

def sourceBody795_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 28)

def sourceBody795_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody795_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 6)

def sourceBody795_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody795_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 10)

def sourceBody795_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody795_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 14)

def sourceBody795_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody795_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody795_0, 795, 6)) (some 792) ([32, 20, 30, 24, 34, 16, 26]) (some (32, sourceBody795_19, 795, 7))

def sourceBody795_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_20 sourceBody795_3

def sourceBody795_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_21 sourceBody795_0

def sourceBody795_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_18 sourceBody795_22

def sourceBody795_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_17 sourceBody795_23

def sourceBody795_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_16 sourceBody795_24

def sourceBody795_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_15 sourceBody795_25

def sourceBody795_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_14 sourceBody795_26

def sourceBody795_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_13 sourceBody795_27

def sourceBody795_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_12 sourceBody795_28

def sourceBody795_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_0 sourceBody795_29

def sourceBody795_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_0 sourceBody795_30

def sourceBody795_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 28)

def sourceBody795_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody795_0, 795, 8)) (some 794) ([32, 20]) (some (32, sourceBody795_19, 795, 9))

def sourceBody795_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_33 sourceBody795_3

def sourceBody795_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_34 sourceBody795_0

def sourceBody795_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_32 sourceBody795_35

def sourceBody795_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_12 sourceBody795_36

def sourceBody795_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_0 sourceBody795_37

def sourceBody795_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_0 sourceBody795_38

def sourceBody795_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_31 sourceBody795_39

def sourceBody795_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 2)

def sourceBody795_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 1624#64])

def sourceBody795_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody795_44 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody795_0, 795, 10)) (some 768) ([32, 20, 30, 24]) (some (32, sourceBody795_19, 795, 11))

def sourceBody795_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_44 sourceBody795_3

def sourceBody795_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_45 sourceBody795_0

def sourceBody795_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_43 sourceBody795_46

def sourceBody795_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_42 sourceBody795_47

def sourceBody795_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_32 sourceBody795_48

def sourceBody795_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_41 sourceBody795_49

def sourceBody795_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_0 sourceBody795_50

def sourceBody795_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_0 sourceBody795_51

def sourceBody795_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_40 sourceBody795_52

def sourceBody795_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 18)

def sourceBody795_55 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody795_0, 795, 12)) (some 70) ([32]) (some (32, sourceBody795_19, 795, 13))

def sourceBody795_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_55 sourceBody795_3

def sourceBody795_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_56 sourceBody795_0

def sourceBody795_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_54 sourceBody795_57

def sourceBody795_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_0 sourceBody795_58

def sourceBody795_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_0 sourceBody795_59

def sourceBody795_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_53 sourceBody795_60

def sourceBody795_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody795_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [22]

def sourceBody795_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_63 sourceBody795_0

def sourceBody795_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_62 sourceBody795_64

def sourceBody795_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_61 sourceBody795_65

def sourceBody795_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_11 sourceBody795_66

def sourceBody795_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_0 sourceBody795_67

def sourceBody795_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_0 sourceBody795_68

def sourceBody795_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_5 sourceBody795_69

def sourceBody795_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_0 sourceBody795_70

def sourceBody795_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody795_0 sourceBody795_71

def source795 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (795, 8, sourceBody795_72)
end InitECandidate.Proofs.WordStages
