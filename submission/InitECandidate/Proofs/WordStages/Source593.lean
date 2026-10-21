import InitECandidate.Proofs.WordStages.Source577
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody593_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody593_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody593_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody593_0, 593, 2)) (some 470) ([]) (some (10, sourceBody593_1, 593, 3))

def sourceBody593_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody593_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_2 sourceBody593_3

def sourceBody593_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_4 sourceBody593_0

def sourceBody593_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_0 sourceBody593_5

def sourceBody593_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_0 sourceBody593_6

def sourceBody593_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody593_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody593_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody593_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody593_12 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 4) sourceBody593_10 sourceBody593_11

def sourceBody593_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_12 sourceBody593_3

def sourceBody593_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody593_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody593_0, 593, 4)) (some 600) ([10]) (some (10, sourceBody593_1, 593, 5))

def sourceBody593_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_15 sourceBody593_3

def sourceBody593_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_16 sourceBody593_0

def sourceBody593_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_8 sourceBody593_17

def sourceBody593_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_0 sourceBody593_18

def sourceBody593_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_0 sourceBody593_19

def sourceBody593_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 120#64])

def sourceBody593_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 264#64]))

def sourceBody593_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody593_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 6) 4

def sourceBody593_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_24 sourceBody593_0

def sourceBody593_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_23 sourceBody593_25

def sourceBody593_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_26 sourceBody593_0

def sourceBody593_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_22 sourceBody593_27

def sourceBody593_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_0 sourceBody593_28

def sourceBody593_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_21 sourceBody593_29

def sourceBody593_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_0 sourceBody593_30

def sourceBody593_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_20 sourceBody593_31

def sourceBody593_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody593_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_11 sourceBody593_27

def sourceBody593_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_0 sourceBody593_34

def sourceBody593_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_33 sourceBody593_35

def sourceBody593_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_0 sourceBody593_36

def sourceBody593_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_32 sourceBody593_37

def sourceBody593_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 160#64])

def sourceBody593_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_8 sourceBody593_27

def sourceBody593_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_0 sourceBody593_40

def sourceBody593_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_39 sourceBody593_41

def sourceBody593_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_0 sourceBody593_42

def sourceBody593_44 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody593_38 sourceBody593_43

def sourceBody593_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_44 sourceBody593_3

def sourceBody593_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_45 sourceBody593_0

def sourceBody593_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_14 sourceBody593_46

def sourceBody593_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_13 sourceBody593_47

def sourceBody593_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_9 sourceBody593_48

def sourceBody593_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_8 sourceBody593_49

def sourceBody593_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_7 sourceBody593_50

def sourceBody593_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 288#64]),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody593_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_10 sourceBody593_27

def sourceBody593_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_0 sourceBody593_53

def sourceBody593_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_52 sourceBody593_54

def sourceBody593_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_0 sourceBody593_55

def sourceBody593_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_51 sourceBody593_56

def sourceBody593_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody593_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody593_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_59 sourceBody593_0

def sourceBody593_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_58 sourceBody593_60

def sourceBody593_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody593_57 sourceBody593_61

def source593 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (593, 2, sourceBody593_62)
end InitECandidate.Proofs.WordStages
