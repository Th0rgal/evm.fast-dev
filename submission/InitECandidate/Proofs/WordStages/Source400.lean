import InitECandidate.Proofs.WordStages.Source384
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody400_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody400_1 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody400_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody400_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody400_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody400_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody400_0, 400, 2)) (some 192) ([12, 4, 10]) (some (12, sourceBody400_4, 400, 3))

def sourceBody400_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody400_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_5 sourceBody400_6

def sourceBody400_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_7 sourceBody400_0

def sourceBody400_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_3 sourceBody400_8

def sourceBody400_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_2 sourceBody400_9

def sourceBody400_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_1 sourceBody400_10

def sourceBody400_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_0 sourceBody400_11

def sourceBody400_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_0 sourceBody400_12

def sourceBody400_14 : WordLangProgHOL (BitVec 64) :=
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
              Flapjack.WordLangExpHOL.const 176#64]),
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody400_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody400_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody400_17 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 12]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody400_0, 400, 4)) (some 186) ([4, 10]) (some (4, sourceBody400_16, 400, 5))

def sourceBody400_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_17 sourceBody400_6

def sourceBody400_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_18 sourceBody400_0

def sourceBody400_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_15 sourceBody400_19

def sourceBody400_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_14 sourceBody400_20

def sourceBody400_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody400_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody400_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody400_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 8) sourceBody400_3 sourceBody400_24

def sourceBody400_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_25 sourceBody400_6

def sourceBody400_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody400_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 12)

def sourceBody400_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody400_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_29 sourceBody400_0

def sourceBody400_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_28 sourceBody400_30

def sourceBody400_32 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody400_31 sourceBody400_0

def sourceBody400_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_32 sourceBody400_6

def sourceBody400_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_33 sourceBody400_0

def sourceBody400_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_27 sourceBody400_34

def sourceBody400_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_26 sourceBody400_35

def sourceBody400_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_23 sourceBody400_36

def sourceBody400_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_22 sourceBody400_37

def sourceBody400_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody400_40 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody400_0, 400, 6)) (some 392) ([10]) (some (10, sourceBody400_39, 400, 7))

def sourceBody400_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_40 sourceBody400_6

def sourceBody400_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_41 sourceBody400_0

def sourceBody400_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_15 sourceBody400_42

def sourceBody400_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_0 sourceBody400_43

def sourceBody400_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_0 sourceBody400_44

def sourceBody400_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_38 sourceBody400_45

def sourceBody400_47 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody400_0, 400, 8)) (some 394) ([10]) (some (10, sourceBody400_39, 400, 9))

def sourceBody400_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_47 sourceBody400_6

def sourceBody400_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_48 sourceBody400_0

def sourceBody400_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_15 sourceBody400_49

def sourceBody400_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody400_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody400_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_52 sourceBody400_0

def sourceBody400_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_51 sourceBody400_53

def sourceBody400_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_50 sourceBody400_54

def sourceBody400_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_0 sourceBody400_55

def sourceBody400_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_0 sourceBody400_56

def sourceBody400_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_46 sourceBody400_57

def sourceBody400_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_21 sourceBody400_58

def sourceBody400_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_0 sourceBody400_59

def sourceBody400_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_0 sourceBody400_60

def sourceBody400_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_0 sourceBody400_61

def sourceBody400_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_0 sourceBody400_62

def sourceBody400_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody400_13 sourceBody400_63

def source400 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (400, 2, sourceBody400_64)
end InitECandidate.Proofs.WordStages
