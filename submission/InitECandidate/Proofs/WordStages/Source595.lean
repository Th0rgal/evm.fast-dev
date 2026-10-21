import InitECandidate.Proofs.WordStages.Source579
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody595_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody595_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody595_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody595_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody595_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.lookup (Flapjack.WordStore.temp 0#5))

def sourceBody595_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_4 sourceBody595_0

def sourceBody595_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_5 sourceBody595_0

def sourceBody595_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody595_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody595_9 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody595_0, 595, 3)) (some 593) ([8]) (some (8, sourceBody595_8, 595, 4))

def sourceBody595_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_9 sourceBody595_3

def sourceBody595_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_10 sourceBody595_0

def sourceBody595_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_7 sourceBody595_11

def sourceBody595_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_0 sourceBody595_12

def sourceBody595_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_0 sourceBody595_13

def sourceBody595_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_6 sourceBody595_14

def sourceBody595_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_3 sourceBody595_15

def sourceBody595_17 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.WordRegImm.imm 8#64) sourceBody595_2 sourceBody595_16

def sourceBody595_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_17 sourceBody595_3

def sourceBody595_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody595_0, 595, 2)) (some 594) ([]) (some (2, sourceBody595_18, 595, 5))

def sourceBody595_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_19 sourceBody595_3

def sourceBody595_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_20 sourceBody595_0

def sourceBody595_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody595_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody595_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody595_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody595_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.reg 6) sourceBody595_24 sourceBody595_25

def sourceBody595_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_26 sourceBody595_3

def sourceBody595_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody595_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 288#64]),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody595_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody595_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 2) 6

def sourceBody595_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_31 sourceBody595_0

def sourceBody595_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_30 sourceBody595_32

def sourceBody595_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_33 sourceBody595_0

def sourceBody595_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_24 sourceBody595_34

def sourceBody595_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_0 sourceBody595_35

def sourceBody595_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_29 sourceBody595_36

def sourceBody595_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_0 sourceBody595_37

def sourceBody595_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody595_38 sourceBody595_0

def sourceBody595_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_39 sourceBody595_3

def sourceBody595_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_40 sourceBody595_0

def sourceBody595_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_28 sourceBody595_41

def sourceBody595_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_27 sourceBody595_42

def sourceBody595_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_23 sourceBody595_43

def sourceBody595_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_22 sourceBody595_44

def sourceBody595_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_21 sourceBody595_45

def sourceBody595_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody595_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [2]

def sourceBody595_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_48 sourceBody595_0

def sourceBody595_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_47 sourceBody595_49

def sourceBody595_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_46 sourceBody595_50

def sourceBody595_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_1 sourceBody595_51

def sourceBody595_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_0 sourceBody595_52

def sourceBody595_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_0 sourceBody595_53

def sourceBody595_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody595_0 sourceBody595_54

def source595 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (595, 1, sourceBody595_55)
end InitECandidate.Proofs.WordStages
