import InitECandidate.Proofs.WordStages.Source383
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody399_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody399_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody399_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody399_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody399_0, 399, 2)) (some 395) ([12]) (some (12, sourceBody399_2, 399, 3))

def sourceBody399_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody399_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_3 sourceBody399_4

def sourceBody399_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_5 sourceBody399_0

def sourceBody399_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_1 sourceBody399_6

def sourceBody399_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody399_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 128#64]))

def sourceBody399_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody399_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody399_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody399_0, 399, 4)) (some 79) ([4, 10, 8]) (some (4, sourceBody399_11, 399, 5))

def sourceBody399_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_12 sourceBody399_4

def sourceBody399_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_13 sourceBody399_0

def sourceBody399_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_10 sourceBody399_14

def sourceBody399_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_9 sourceBody399_15

def sourceBody399_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_8 sourceBody399_16

def sourceBody399_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody399_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody399_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody399_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody399_22 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 8) sourceBody399_20 sourceBody399_21

def sourceBody399_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_22 sourceBody399_4

def sourceBody399_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody399_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody399_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody399_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_26 sourceBody399_0

def sourceBody399_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_25 sourceBody399_27

def sourceBody399_29 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody399_28 sourceBody399_0

def sourceBody399_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_29 sourceBody399_4

def sourceBody399_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_30 sourceBody399_0

def sourceBody399_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_24 sourceBody399_31

def sourceBody399_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_23 sourceBody399_32

def sourceBody399_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_19 sourceBody399_33

def sourceBody399_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_18 sourceBody399_34

def sourceBody399_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody399_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_36 sourceBody399_27

def sourceBody399_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_35 sourceBody399_37

def sourceBody399_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_17 sourceBody399_38

def sourceBody399_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_0 sourceBody399_39

def sourceBody399_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_0 sourceBody399_40

def sourceBody399_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_7 sourceBody399_41

def sourceBody399_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_0 sourceBody399_42

def sourceBody399_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody399_0 sourceBody399_43

def source399 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (399, 2, sourceBody399_44)
end InitECandidate.Proofs.WordStages
