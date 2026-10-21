import InitECandidate.Proofs.WordStages.Source311
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody327_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody327_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody327_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody327_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody327_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody327_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody327_6 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.WordRegImm.reg 10) sourceBody327_4 sourceBody327_5

def sourceBody327_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody327_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_6 sourceBody327_7

def sourceBody327_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody327_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody327_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 128#64]))

def sourceBody327_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody327_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody327_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody327_0, 327, 2)) (some 77) ([12, 10, 16]) (some (12, sourceBody327_13, 327, 3))

def sourceBody327_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_14 sourceBody327_7

def sourceBody327_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_15 sourceBody327_0

def sourceBody327_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_12 sourceBody327_16

def sourceBody327_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_11 sourceBody327_17

def sourceBody327_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_10 sourceBody327_18

def sourceBody327_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_0 sourceBody327_19

def sourceBody327_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_0 sourceBody327_20

def sourceBody327_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody327_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody327_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_23 sourceBody327_0

def sourceBody327_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_22 sourceBody327_24

def sourceBody327_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_21 sourceBody327_25

def sourceBody327_27 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody327_26 sourceBody327_0

def sourceBody327_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_27 sourceBody327_7

def sourceBody327_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_28 sourceBody327_0

def sourceBody327_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_9 sourceBody327_29

def sourceBody327_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_8 sourceBody327_30

def sourceBody327_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_3 sourceBody327_31

def sourceBody327_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_2 sourceBody327_32

def sourceBody327_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody327_0, 327, 4)) (some 326) ([12]) (some (12, sourceBody327_13, 327, 5))

def sourceBody327_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_34 sourceBody327_7

def sourceBody327_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_35 sourceBody327_0

def sourceBody327_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_2 sourceBody327_36

def sourceBody327_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody327_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody327_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody327_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody327_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody327_0, 327, 6)) (some 77) ([10, 16, 6]) (some (10, sourceBody327_41, 327, 7))

def sourceBody327_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_42 sourceBody327_7

def sourceBody327_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_43 sourceBody327_0

def sourceBody327_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_40 sourceBody327_44

def sourceBody327_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_39 sourceBody327_45

def sourceBody327_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_38 sourceBody327_46

def sourceBody327_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_0 sourceBody327_47

def sourceBody327_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_0 sourceBody327_48

def sourceBody327_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody327_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_50 sourceBody327_0

def sourceBody327_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_5 sourceBody327_51

def sourceBody327_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_49 sourceBody327_52

def sourceBody327_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_37 sourceBody327_53

def sourceBody327_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_0 sourceBody327_54

def sourceBody327_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_0 sourceBody327_55

def sourceBody327_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_33 sourceBody327_56

def sourceBody327_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_1 sourceBody327_57

def sourceBody327_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody327_0 sourceBody327_58

def source327 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (327, 3, sourceBody327_59)
end InitECandidate.Proofs.WordStages
