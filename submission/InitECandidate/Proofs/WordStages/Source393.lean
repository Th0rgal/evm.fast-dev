import InitECandidate.Proofs.WordStages.Source377
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody393_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody393_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody393_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody393_0, 393, 2)) (some 69) ([]) (some (16, sourceBody393_1, 393, 3))

def sourceBody393_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody393_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_2 sourceBody393_3

def sourceBody393_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_4 sourceBody393_0

def sourceBody393_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody393_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody393_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody393_0, 393, 4)) (some 68) ([6]) (some (6, sourceBody393_7, 393, 5))

def sourceBody393_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_8 sourceBody393_3

def sourceBody393_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_9 sourceBody393_0

def sourceBody393_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_6 sourceBody393_10

def sourceBody393_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody393_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody393_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody393_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody393_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody393_0, 393, 6)) (some 158) ([14, 10, 18]) (some (14, sourceBody393_15, 393, 7))

def sourceBody393_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_16 sourceBody393_3

def sourceBody393_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_17 sourceBody393_0

def sourceBody393_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_14 sourceBody393_18

def sourceBody393_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_13 sourceBody393_19

def sourceBody393_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_12 sourceBody393_20

def sourceBody393_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_0 sourceBody393_21

def sourceBody393_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_0 sourceBody393_22

def sourceBody393_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 168#64]),
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody393_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 16)

def sourceBody393_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody393_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 14, 10]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody393_0, 393, 8)) (some 303) ([18, 4]) (some (18, sourceBody393_26, 393, 9))

def sourceBody393_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_27 sourceBody393_3

def sourceBody393_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_28 sourceBody393_0

def sourceBody393_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_25 sourceBody393_29

def sourceBody393_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_24 sourceBody393_30

def sourceBody393_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 8)

def sourceBody393_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody393_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody393_0, 393, 10)) (some 70) ([4]) (some (4, sourceBody393_33, 393, 11))

def sourceBody393_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_34 sourceBody393_3

def sourceBody393_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_35 sourceBody393_0

def sourceBody393_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_32 sourceBody393_36

def sourceBody393_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_0 sourceBody393_37

def sourceBody393_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_0 sourceBody393_38

def sourceBody393_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody393_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 14)

def sourceBody393_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody393_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18, 4, 12]

def sourceBody393_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_43 sourceBody393_0

def sourceBody393_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_42 sourceBody393_44

def sourceBody393_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_41 sourceBody393_45

def sourceBody393_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_40 sourceBody393_46

def sourceBody393_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_39 sourceBody393_47

def sourceBody393_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_31 sourceBody393_48

def sourceBody393_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_0 sourceBody393_49

def sourceBody393_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_0 sourceBody393_50

def sourceBody393_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_0 sourceBody393_51

def sourceBody393_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_0 sourceBody393_52

def sourceBody393_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_0 sourceBody393_53

def sourceBody393_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_0 sourceBody393_54

def sourceBody393_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_23 sourceBody393_55

def sourceBody393_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_11 sourceBody393_56

def sourceBody393_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_0 sourceBody393_57

def sourceBody393_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_0 sourceBody393_58

def sourceBody393_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_5 sourceBody393_59

def sourceBody393_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_0 sourceBody393_60

def sourceBody393_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody393_0 sourceBody393_61

def source393 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (393, 2, sourceBody393_62)
end InitECandidate.Proofs.WordStages
