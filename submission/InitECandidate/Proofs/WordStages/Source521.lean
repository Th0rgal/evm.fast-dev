import InitECandidate.Proofs.WordStages.Source505
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody521_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody521_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody521_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 16, 4, 14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody521_0, 521, 2)) (some 471) ([]) (some (10, sourceBody521_1, 521, 3))

def sourceBody521_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody521_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_2 sourceBody521_3

def sourceBody521_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_4 sourceBody521_0

def sourceBody521_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody521_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody521_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody521_0, 521, 4)) (some 466) ([18]) (some (18, sourceBody521_7, 521, 5))

def sourceBody521_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_8 sourceBody521_3

def sourceBody521_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_9 sourceBody521_0

def sourceBody521_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_6 sourceBody521_10

def sourceBody521_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_0 sourceBody521_11

def sourceBody521_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_0 sourceBody521_12

def sourceBody521_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody521_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 16)

def sourceBody521_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody521_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody521_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody521_0, 521, 6)) (some 482) ([18, 2, 12, 8]) (some (18, sourceBody521_7, 521, 7))

def sourceBody521_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_18 sourceBody521_3

def sourceBody521_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_19 sourceBody521_0

def sourceBody521_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_17 sourceBody521_20

def sourceBody521_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_16 sourceBody521_21

def sourceBody521_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_15 sourceBody521_22

def sourceBody521_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_14 sourceBody521_23

def sourceBody521_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 10)

def sourceBody521_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody521_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody521_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody521_29 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 2 (Flapjack.WordRegImm.reg 12) sourceBody521_27 sourceBody521_28

def sourceBody521_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_29 sourceBody521_3

def sourceBody521_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody521_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody521_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 18)

def sourceBody521_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_33 sourceBody521_0

def sourceBody521_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_34 sourceBody521_0

def sourceBody521_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_32 sourceBody521_35

def sourceBody521_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_0 sourceBody521_36

def sourceBody521_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_6 sourceBody521_7

def sourceBody521_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_37 sourceBody521_38

def sourceBody521_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody521_39 sourceBody521_0

def sourceBody521_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_40 sourceBody521_3

def sourceBody521_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_41 sourceBody521_0

def sourceBody521_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_31 sourceBody521_42

def sourceBody521_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_30 sourceBody521_43

def sourceBody521_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_26 sourceBody521_44

def sourceBody521_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_25 sourceBody521_45

def sourceBody521_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 0#64])

def sourceBody521_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 6)

def sourceBody521_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody521_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 18) 12

def sourceBody521_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_50 sourceBody521_0

def sourceBody521_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_49 sourceBody521_51

def sourceBody521_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_52 sourceBody521_0

def sourceBody521_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_48 sourceBody521_53

def sourceBody521_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_0 sourceBody521_54

def sourceBody521_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_47 sourceBody521_55

def sourceBody521_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_0 sourceBody521_56

def sourceBody521_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_46 sourceBody521_57

def sourceBody521_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody521_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody521_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_60 sourceBody521_0

def sourceBody521_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_59 sourceBody521_61

def sourceBody521_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_58 sourceBody521_62

def sourceBody521_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_24 sourceBody521_63

def sourceBody521_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_0 sourceBody521_64

def sourceBody521_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_0 sourceBody521_65

def sourceBody521_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_13 sourceBody521_66

def sourceBody521_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_5 sourceBody521_67

def sourceBody521_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_0 sourceBody521_68

def sourceBody521_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_0 sourceBody521_69

def sourceBody521_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_0 sourceBody521_70

def sourceBody521_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_0 sourceBody521_71

def sourceBody521_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_0 sourceBody521_72

def sourceBody521_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_0 sourceBody521_73

def sourceBody521_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_0 sourceBody521_74

def sourceBody521_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody521_0 sourceBody521_75

def source521 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (521, 1, sourceBody521_76)
end InitECandidate.Proofs.WordStages
