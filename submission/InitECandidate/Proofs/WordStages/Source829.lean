import InitECandidate.Proofs.WordStages.Source813
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody829_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody829_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
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
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody829_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody829_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody829_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody829_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody829_0, 829, 2)) (some 461) ([12]) (some (12, sourceBody829_4, 829, 3))

def sourceBody829_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody829_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_5 sourceBody829_6

def sourceBody829_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_7 sourceBody829_0

def sourceBody829_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_3 sourceBody829_8

def sourceBody829_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody829_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 120#64)

def sourceBody829_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 2 2 8 16))

def sourceBody829_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.const 600#64, Flapjack.WordLangExpHOL.var 2])

def sourceBody829_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody829_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody829_0, 829, 4)) (some 466) ([10]) (some (8, sourceBody829_14, 829, 5))

def sourceBody829_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_15 sourceBody829_6

def sourceBody829_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_16 sourceBody829_0

def sourceBody829_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_13 sourceBody829_17

def sourceBody829_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_12 sourceBody829_18

def sourceBody829_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_11 sourceBody829_19

def sourceBody829_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_10 sourceBody829_20

def sourceBody829_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_0 sourceBody829_21

def sourceBody829_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_0 sourceBody829_22

def sourceBody829_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody829_25 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody829_0, 829, 6)) (some 68) ([8]) (some (8, sourceBody829_14, 829, 7))

def sourceBody829_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_25 sourceBody829_6

def sourceBody829_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_26 sourceBody829_0

def sourceBody829_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_24 sourceBody829_27

def sourceBody829_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody829_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody829_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody829_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody829_0, 829, 8)) (some 78) ([16, 2]) (some (16, sourceBody829_31, 829, 9))

def sourceBody829_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_32 sourceBody829_6

def sourceBody829_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_33 sourceBody829_0

def sourceBody829_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_30 sourceBody829_34

def sourceBody829_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_29 sourceBody829_35

def sourceBody829_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_0 sourceBody829_36

def sourceBody829_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_0 sourceBody829_37

def sourceBody829_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody829_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 14)

def sourceBody829_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 12#64])

def sourceBody829_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody829_0, 829, 10)) (some 627) ([16, 2, 10]) (some (16, sourceBody829_31, 829, 11))

def sourceBody829_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_42 sourceBody829_6

def sourceBody829_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_43 sourceBody829_0

def sourceBody829_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_41 sourceBody829_44

def sourceBody829_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_40 sourceBody829_45

def sourceBody829_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_39 sourceBody829_46

def sourceBody829_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_0 sourceBody829_47

def sourceBody829_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_0 sourceBody829_48

def sourceBody829_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_38 sourceBody829_49

def sourceBody829_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 120#64])

def sourceBody829_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 16)

def sourceBody829_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 2

def sourceBody829_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_53 sourceBody829_0

def sourceBody829_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_52 sourceBody829_54

def sourceBody829_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_55 sourceBody829_0

def sourceBody829_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_29 sourceBody829_56

def sourceBody829_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_0 sourceBody829_57

def sourceBody829_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_51 sourceBody829_58

def sourceBody829_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_0 sourceBody829_59

def sourceBody829_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_50 sourceBody829_60

def sourceBody829_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody829_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody829_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_63 sourceBody829_56

def sourceBody829_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_0 sourceBody829_64

def sourceBody829_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_62 sourceBody829_65

def sourceBody829_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_0 sourceBody829_66

def sourceBody829_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_61 sourceBody829_67

def sourceBody829_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody829_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody829_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_70 sourceBody829_0

def sourceBody829_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_69 sourceBody829_71

def sourceBody829_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_68 sourceBody829_72

def sourceBody829_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_28 sourceBody829_73

def sourceBody829_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_0 sourceBody829_74

def sourceBody829_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_0 sourceBody829_75

def sourceBody829_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_23 sourceBody829_76

def sourceBody829_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_9 sourceBody829_77

def sourceBody829_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_0 sourceBody829_78

def sourceBody829_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_0 sourceBody829_79

def sourceBody829_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_2 sourceBody829_80

def sourceBody829_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_0 sourceBody829_81

def sourceBody829_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_1 sourceBody829_82

def sourceBody829_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody829_0 sourceBody829_83

def source829 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (829, 1, sourceBody829_84)
end InitECandidate.Proofs.WordStages
