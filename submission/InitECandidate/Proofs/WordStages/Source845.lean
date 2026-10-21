import InitECandidate.Proofs.WordStages.Source829
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody845_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody845_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody845_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody845_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody845_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody845_0, 845, 2)) (some 187) ([6, 10]) (some (6, sourceBody845_3, 845, 3))

def sourceBody845_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody845_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_4 sourceBody845_5

def sourceBody845_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_6 sourceBody845_0

def sourceBody845_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_2 sourceBody845_7

def sourceBody845_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_1 sourceBody845_8

def sourceBody845_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody845_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody845_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody845_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody845_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 8) sourceBody845_12 sourceBody845_13

def sourceBody845_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_14 sourceBody845_5

def sourceBody845_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody845_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 128#64]))

def sourceBody845_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody845_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_18 sourceBody845_0

def sourceBody845_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_17 sourceBody845_19

def sourceBody845_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody845_20 sourceBody845_0

def sourceBody845_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_21 sourceBody845_5

def sourceBody845_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_22 sourceBody845_0

def sourceBody845_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_16 sourceBody845_23

def sourceBody845_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_15 sourceBody845_24

def sourceBody845_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_11 sourceBody845_25

def sourceBody845_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_10 sourceBody845_26

def sourceBody845_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody845_29 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody845_0, 845, 4)) (some 395) ([10]) (some (10, sourceBody845_28, 845, 5))

def sourceBody845_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_29 sourceBody845_5

def sourceBody845_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_30 sourceBody845_0

def sourceBody845_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_2 sourceBody845_31

def sourceBody845_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody845_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody845_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_34 sourceBody845_0

def sourceBody845_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_33 sourceBody845_35

def sourceBody845_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_32 sourceBody845_36

def sourceBody845_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_0 sourceBody845_37

def sourceBody845_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_0 sourceBody845_38

def sourceBody845_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_27 sourceBody845_39

def sourceBody845_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_9 sourceBody845_40

def sourceBody845_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_0 sourceBody845_41

def sourceBody845_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody845_0 sourceBody845_42

def source845 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (845, 3, sourceBody845_43)
end InitECandidate.Proofs.WordStages
