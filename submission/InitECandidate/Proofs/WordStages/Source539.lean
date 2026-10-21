import InitECandidate.Proofs.WordStages.Source523
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody539_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody539_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody539_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody539_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody539_0, 539, 2)) (some 466) ([10]) (some (10, sourceBody539_2, 539, 3))

def sourceBody539_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody539_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_3 sourceBody539_4

def sourceBody539_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_5 sourceBody539_0

def sourceBody539_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_1 sourceBody539_6

def sourceBody539_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_0 sourceBody539_7

def sourceBody539_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_0 sourceBody539_8

def sourceBody539_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody539_0, 539, 4)) (some 536) ([]) (some (10, sourceBody539_2, 539, 5))

def sourceBody539_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_10 sourceBody539_4

def sourceBody539_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_11 sourceBody539_0

def sourceBody539_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody539_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody539_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody539_0, 539, 6)) (some 537) ([2]) (some (2, sourceBody539_14, 539, 7))

def sourceBody539_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_15 sourceBody539_4

def sourceBody539_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_16 sourceBody539_0

def sourceBody539_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_13 sourceBody539_17

def sourceBody539_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody539_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody539_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody539_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody539_23 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 8 (Flapjack.WordRegImm.reg 6) sourceBody539_21 sourceBody539_22

def sourceBody539_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_23 sourceBody539_4

def sourceBody539_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody539_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody539_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 2)

def sourceBody539_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_27 sourceBody539_0

def sourceBody539_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_28 sourceBody539_0

def sourceBody539_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_26 sourceBody539_29

def sourceBody539_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_0 sourceBody539_30

def sourceBody539_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody539_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_32 sourceBody539_14

def sourceBody539_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_31 sourceBody539_33

def sourceBody539_35 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody539_34 sourceBody539_0

def sourceBody539_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_35 sourceBody539_4

def sourceBody539_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_36 sourceBody539_0

def sourceBody539_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_25 sourceBody539_37

def sourceBody539_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_24 sourceBody539_38

def sourceBody539_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_20 sourceBody539_39

def sourceBody539_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_19 sourceBody539_40

def sourceBody539_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody539_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody539_44 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody539_0, 539, 8)) (some 534) ([8, 6]) (some (8, sourceBody539_43, 539, 9))

def sourceBody539_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_44 sourceBody539_4

def sourceBody539_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_45 sourceBody539_0

def sourceBody539_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_42 sourceBody539_46

def sourceBody539_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_22 sourceBody539_47

def sourceBody539_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_0 sourceBody539_48

def sourceBody539_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_0 sourceBody539_49

def sourceBody539_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_41 sourceBody539_50

def sourceBody539_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody539_53 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody539_0, 539, 10)) (some 486) ([8]) (some (8, sourceBody539_43, 539, 11))

def sourceBody539_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_53 sourceBody539_4

def sourceBody539_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_54 sourceBody539_0

def sourceBody539_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_52 sourceBody539_55

def sourceBody539_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_0 sourceBody539_56

def sourceBody539_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_0 sourceBody539_57

def sourceBody539_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_51 sourceBody539_58

def sourceBody539_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody539_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [2]

def sourceBody539_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_61 sourceBody539_0

def sourceBody539_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_60 sourceBody539_62

def sourceBody539_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_59 sourceBody539_63

def sourceBody539_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_18 sourceBody539_64

def sourceBody539_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_0 sourceBody539_65

def sourceBody539_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_0 sourceBody539_66

def sourceBody539_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_12 sourceBody539_67

def sourceBody539_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_0 sourceBody539_68

def sourceBody539_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_0 sourceBody539_69

def sourceBody539_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody539_9 sourceBody539_70

def source539 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (539, 1, sourceBody539_71)
end InitECandidate.Proofs.WordStages
