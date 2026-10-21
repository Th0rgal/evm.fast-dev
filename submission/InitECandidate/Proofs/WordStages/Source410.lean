import InitECandidate.Proofs.WordStages.Source394
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody410_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody410_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 184#64]),
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody410_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody410_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody410_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 12]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody410_0, 410, 2)) (some 186) ([4, 10]) (some (4, sourceBody410_3, 410, 3))

def sourceBody410_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody410_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_4 sourceBody410_5

def sourceBody410_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_6 sourceBody410_0

def sourceBody410_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_2 sourceBody410_7

def sourceBody410_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_1 sourceBody410_8

def sourceBody410_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody410_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody410_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody410_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody410_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 8) sourceBody410_12 sourceBody410_13

def sourceBody410_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_14 sourceBody410_5

def sourceBody410_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody410_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody410_18 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 8) sourceBody410_12 sourceBody410_13

def sourceBody410_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_18 sourceBody410_5

def sourceBody410_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody410_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody410_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_21 sourceBody410_0

def sourceBody410_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_20 sourceBody410_22

def sourceBody410_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody410_23 sourceBody410_0

def sourceBody410_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_24 sourceBody410_5

def sourceBody410_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_25 sourceBody410_0

def sourceBody410_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_16 sourceBody410_26

def sourceBody410_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_19 sourceBody410_27

def sourceBody410_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_17 sourceBody410_28

def sourceBody410_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_13 sourceBody410_29

def sourceBody410_31 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody410_30 sourceBody410_0

def sourceBody410_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_31 sourceBody410_5

def sourceBody410_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_32 sourceBody410_0

def sourceBody410_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_16 sourceBody410_33

def sourceBody410_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_15 sourceBody410_34

def sourceBody410_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_11 sourceBody410_35

def sourceBody410_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_10 sourceBody410_36

def sourceBody410_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 176#64]),
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody410_39 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 12]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody410_0, 410, 4)) (some 186) ([4, 10]) (some (4, sourceBody410_3, 410, 5))

def sourceBody410_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_39 sourceBody410_5

def sourceBody410_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_40 sourceBody410_0

def sourceBody410_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_2 sourceBody410_41

def sourceBody410_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_38 sourceBody410_42

def sourceBody410_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_37 sourceBody410_43

def sourceBody410_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_44 sourceBody410_37

def sourceBody410_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody410_47 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody410_0, 410, 6)) (some 392) ([10]) (some (10, sourceBody410_46, 410, 7))

def sourceBody410_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_47 sourceBody410_5

def sourceBody410_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_48 sourceBody410_0

def sourceBody410_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_2 sourceBody410_49

def sourceBody410_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_0 sourceBody410_50

def sourceBody410_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_0 sourceBody410_51

def sourceBody410_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_45 sourceBody410_52

def sourceBody410_54 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody410_0, 410, 8)) (some 399) ([10]) (some (10, sourceBody410_46, 410, 9))

def sourceBody410_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_54 sourceBody410_5

def sourceBody410_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_55 sourceBody410_0

def sourceBody410_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_2 sourceBody410_56

def sourceBody410_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody410_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody410_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_59 sourceBody410_0

def sourceBody410_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_58 sourceBody410_60

def sourceBody410_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_57 sourceBody410_61

def sourceBody410_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_0 sourceBody410_62

def sourceBody410_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_0 sourceBody410_63

def sourceBody410_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_53 sourceBody410_64

def sourceBody410_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_9 sourceBody410_65

def sourceBody410_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_0 sourceBody410_66

def sourceBody410_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_0 sourceBody410_67

def sourceBody410_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_0 sourceBody410_68

def sourceBody410_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody410_0 sourceBody410_69

def source410 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (410, 2, sourceBody410_70)
end InitECandidate.Proofs.WordStages
