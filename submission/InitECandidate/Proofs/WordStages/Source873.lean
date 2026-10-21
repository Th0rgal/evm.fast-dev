import InitECandidate.Proofs.WordStages.Source857
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody873_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody873_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody873_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody873_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody873_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody873_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.lookup (Flapjack.WordStore.temp 0#5))

def sourceBody873_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_5 sourceBody873_0

def sourceBody873_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_6 sourceBody873_0

def sourceBody873_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody873_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_8 sourceBody873_0

def sourceBody873_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_9 sourceBody873_0

def sourceBody873_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 536#64])

def sourceBody873_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody873_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody873_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 14

def sourceBody873_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_14 sourceBody873_0

def sourceBody873_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_13 sourceBody873_15

def sourceBody873_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_16 sourceBody873_0

def sourceBody873_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_12 sourceBody873_17

def sourceBody873_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_0 sourceBody873_18

def sourceBody873_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_11 sourceBody873_19

def sourceBody873_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_0 sourceBody873_20

def sourceBody873_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_10 sourceBody873_21

def sourceBody873_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_7 sourceBody873_22

def sourceBody873_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_4 sourceBody873_23

def sourceBody873_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 9#64) sourceBody873_3 sourceBody873_24

def sourceBody873_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_25 sourceBody873_4

def sourceBody873_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody873_0, 873, 2)) (some 872) ([10]) (some (10, sourceBody873_26, 873, 3))

def sourceBody873_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_27 sourceBody873_4

def sourceBody873_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_28 sourceBody873_0

def sourceBody873_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_2 sourceBody873_29

def sourceBody873_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_0 sourceBody873_30

def sourceBody873_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_0 sourceBody873_31

def sourceBody873_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 12)

def sourceBody873_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody873_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_34 sourceBody873_0

def sourceBody873_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_33 sourceBody873_35

def sourceBody873_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_32 sourceBody873_36

def sourceBody873_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_1 sourceBody873_37

def sourceBody873_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_0 sourceBody873_38

def sourceBody873_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_0 sourceBody873_39

def sourceBody873_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody873_0 sourceBody873_40

def source873 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (873, 2, sourceBody873_41)
end InitECandidate.Proofs.WordStages
