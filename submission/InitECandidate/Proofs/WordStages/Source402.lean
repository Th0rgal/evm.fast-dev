import InitECandidate.Proofs.WordStages.Source386
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody402_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody402_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
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
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody402_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody402_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody402_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody402_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody402_0, 402, 2)) (some 192) ([12, 4, 10]) (some (12, sourceBody402_4, 402, 3))

def sourceBody402_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody402_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_5 sourceBody402_6

def sourceBody402_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_7 sourceBody402_0

def sourceBody402_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_3 sourceBody402_8

def sourceBody402_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_2 sourceBody402_9

def sourceBody402_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_1 sourceBody402_10

def sourceBody402_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_0 sourceBody402_11

def sourceBody402_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_0 sourceBody402_12

def sourceBody402_14 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody402_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody402_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody402_17 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 12]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody402_0, 402, 4)) (some 186) ([4, 10]) (some (4, sourceBody402_16, 402, 5))

def sourceBody402_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_17 sourceBody402_6

def sourceBody402_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_18 sourceBody402_0

def sourceBody402_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_15 sourceBody402_19

def sourceBody402_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_14 sourceBody402_20

def sourceBody402_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody402_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody402_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody402_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 8) sourceBody402_3 sourceBody402_24

def sourceBody402_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_25 sourceBody402_6

def sourceBody402_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody402_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 12)

def sourceBody402_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody402_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_29 sourceBody402_0

def sourceBody402_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_28 sourceBody402_30

def sourceBody402_32 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody402_31 sourceBody402_0

def sourceBody402_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_32 sourceBody402_6

def sourceBody402_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_33 sourceBody402_0

def sourceBody402_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_27 sourceBody402_34

def sourceBody402_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_26 sourceBody402_35

def sourceBody402_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_23 sourceBody402_36

def sourceBody402_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_22 sourceBody402_37

def sourceBody402_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody402_40 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody402_0, 402, 6)) (some 400) ([10]) (some (10, sourceBody402_39, 402, 7))

def sourceBody402_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_40 sourceBody402_6

def sourceBody402_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_41 sourceBody402_0

def sourceBody402_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_15 sourceBody402_42

def sourceBody402_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody402_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody402_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_45 sourceBody402_0

def sourceBody402_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_44 sourceBody402_46

def sourceBody402_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_43 sourceBody402_47

def sourceBody402_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_0 sourceBody402_48

def sourceBody402_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_0 sourceBody402_49

def sourceBody402_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_38 sourceBody402_50

def sourceBody402_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_21 sourceBody402_51

def sourceBody402_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_0 sourceBody402_52

def sourceBody402_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_0 sourceBody402_53

def sourceBody402_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_0 sourceBody402_54

def sourceBody402_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_0 sourceBody402_55

def sourceBody402_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody402_13 sourceBody402_56

def source402 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (402, 2, sourceBody402_57)
end InitECandidate.Proofs.WordStages
