import InitECandidate.Proofs.WordStages.Source519
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody535_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody535_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody535_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody535_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody535_0, 535, 2)) (some 466) ([10]) (some (10, sourceBody535_2, 535, 3))

def sourceBody535_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody535_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_3 sourceBody535_4

def sourceBody535_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_5 sourceBody535_0

def sourceBody535_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_1 sourceBody535_6

def sourceBody535_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_0 sourceBody535_7

def sourceBody535_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_0 sourceBody535_8

def sourceBody535_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody535_11 : WordLangProgHOL (BitVec 64) :=
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
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody535_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody535_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody535_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 10 (Flapjack.WordRegImm.reg 4) sourceBody535_12 sourceBody535_13

def sourceBody535_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_14 sourceBody535_4

def sourceBody535_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody535_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody535_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 6)

def sourceBody535_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_18 sourceBody535_0

def sourceBody535_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_19 sourceBody535_0

def sourceBody535_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_17 sourceBody535_20

def sourceBody535_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_0 sourceBody535_21

def sourceBody535_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody535_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody535_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_23 sourceBody535_24

def sourceBody535_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_22 sourceBody535_25

def sourceBody535_27 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody535_26 sourceBody535_0

def sourceBody535_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_27 sourceBody535_4

def sourceBody535_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_28 sourceBody535_0

def sourceBody535_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_16 sourceBody535_29

def sourceBody535_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_15 sourceBody535_30

def sourceBody535_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_11 sourceBody535_31

def sourceBody535_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_10 sourceBody535_32

def sourceBody535_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_9 sourceBody535_33

def sourceBody535_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody535_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody535_0, 535, 4)) (some 534) ([10, 4]) (some (10, sourceBody535_2, 535, 5))

def sourceBody535_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_36 sourceBody535_4

def sourceBody535_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_37 sourceBody535_0

def sourceBody535_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_35 sourceBody535_38

def sourceBody535_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_13 sourceBody535_39

def sourceBody535_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_0 sourceBody535_40

def sourceBody535_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_0 sourceBody535_41

def sourceBody535_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_34 sourceBody535_42

def sourceBody535_44 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody535_0, 535, 6)) (some 486) ([10]) (some (10, sourceBody535_2, 535, 7))

def sourceBody535_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_44 sourceBody535_4

def sourceBody535_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_45 sourceBody535_0

def sourceBody535_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_12 sourceBody535_46

def sourceBody535_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_0 sourceBody535_47

def sourceBody535_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_0 sourceBody535_48

def sourceBody535_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_43 sourceBody535_49

def sourceBody535_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody535_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody535_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_52 sourceBody535_0

def sourceBody535_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_51 sourceBody535_53

def sourceBody535_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody535_50 sourceBody535_54

def source535 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (535, 2, sourceBody535_55)
end InitECandidate.Proofs.WordStages
