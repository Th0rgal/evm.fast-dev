import InitECandidate.Proofs.WordStages.Source432
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody448_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody448_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 216#64]))

def sourceBody448_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody448_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody448_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody448_0, 448, 2)) (some 186) ([20, 10]) (some (20, sourceBody448_3, 448, 3))

def sourceBody448_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody448_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_4 sourceBody448_5

def sourceBody448_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_6 sourceBody448_0

def sourceBody448_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_2 sourceBody448_7

def sourceBody448_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_1 sourceBody448_8

def sourceBody448_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody448_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody448_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody448_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody448_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 16) sourceBody448_12 sourceBody448_13

def sourceBody448_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_14 sourceBody448_5

def sourceBody448_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody448_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody448_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody448_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_18 sourceBody448_0

def sourceBody448_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_17 sourceBody448_19

def sourceBody448_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody448_20 sourceBody448_0

def sourceBody448_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_21 sourceBody448_5

def sourceBody448_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_22 sourceBody448_0

def sourceBody448_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_16 sourceBody448_23

def sourceBody448_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_15 sourceBody448_24

def sourceBody448_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_11 sourceBody448_25

def sourceBody448_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_10 sourceBody448_26

def sourceBody448_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.var 4]))

def sourceBody448_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody448_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody448_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody448_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody448_0, 448, 4)) (some 447) ([10, 16, 12]) (some (10, sourceBody448_31, 448, 5))

def sourceBody448_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_32 sourceBody448_5

def sourceBody448_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_33 sourceBody448_0

def sourceBody448_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_30 sourceBody448_34

def sourceBody448_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_29 sourceBody448_35

def sourceBody448_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_28 sourceBody448_36

def sourceBody448_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_0 sourceBody448_37

def sourceBody448_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_0 sourceBody448_38

def sourceBody448_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_27 sourceBody448_39

def sourceBody448_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_40 sourceBody448_20

def sourceBody448_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_9 sourceBody448_41

def sourceBody448_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_0 sourceBody448_42

def sourceBody448_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_0 sourceBody448_43

def sourceBody448_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_0 sourceBody448_44

def sourceBody448_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody448_0 sourceBody448_45

def source448 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (448, 5, sourceBody448_46)
end InitECandidate.Proofs.WordStages
