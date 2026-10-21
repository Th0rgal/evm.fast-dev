import InitECandidate.Proofs.WordStages.Source264
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody280_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 120#64]))

def sourceBody280_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody280_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody280_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody280_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.reg 2) sourceBody280_2 sourceBody280_3

def sourceBody280_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody280_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_4 sourceBody280_5

def sourceBody280_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody280_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody280_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody280_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody280_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_9 sourceBody280_10

def sourceBody280_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_8 sourceBody280_11

def sourceBody280_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody280_12 sourceBody280_10

def sourceBody280_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_13 sourceBody280_5

def sourceBody280_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_14 sourceBody280_10

def sourceBody280_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_7 sourceBody280_15

def sourceBody280_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_6 sourceBody280_16

def sourceBody280_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_1 sourceBody280_17

def sourceBody280_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_0 sourceBody280_18

def sourceBody280_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody280_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody280_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody280_10, 280, 2)) (some 68) ([8]) (some (8, sourceBody280_21, 280, 3))

def sourceBody280_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_22 sourceBody280_5

def sourceBody280_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_23 sourceBody280_10

def sourceBody280_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_20 sourceBody280_24

def sourceBody280_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 120#64])

def sourceBody280_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody280_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody280_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 6

def sourceBody280_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_29 sourceBody280_10

def sourceBody280_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_28 sourceBody280_30

def sourceBody280_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_31 sourceBody280_10

def sourceBody280_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_27 sourceBody280_32

def sourceBody280_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_10 sourceBody280_33

def sourceBody280_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_26 sourceBody280_34

def sourceBody280_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_10 sourceBody280_35

def sourceBody280_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_25 sourceBody280_36

def sourceBody280_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_10 sourceBody280_37

def sourceBody280_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_10 sourceBody280_38

def sourceBody280_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_19 sourceBody280_39

def sourceBody280_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody280_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody280_10, 280, 4)) (some 78) ([8, 2]) (some (8, sourceBody280_21, 280, 5))

def sourceBody280_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_42 sourceBody280_5

def sourceBody280_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_43 sourceBody280_10

def sourceBody280_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_41 sourceBody280_44

def sourceBody280_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_0 sourceBody280_45

def sourceBody280_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_10 sourceBody280_46

def sourceBody280_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_10 sourceBody280_47

def sourceBody280_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_40 sourceBody280_48

def sourceBody280_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody280_49 sourceBody280_12

def source280 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (280, 1, sourceBody280_50)
end InitECandidate.Proofs.WordStages
