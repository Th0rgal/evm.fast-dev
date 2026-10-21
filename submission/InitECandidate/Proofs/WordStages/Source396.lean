import InitECandidate.Proofs.WordStages.Source380
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody396_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody396_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 168#64]),
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody396_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody396_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody396_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody396_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody396_0, 396, 2)) (some 186) ([14, 10]) (some (14, sourceBody396_4, 396, 3))

def sourceBody396_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody396_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_5 sourceBody396_6

def sourceBody396_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_7 sourceBody396_0

def sourceBody396_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_3 sourceBody396_8

def sourceBody396_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_2 sourceBody396_9

def sourceBody396_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody396_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody396_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody396_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody396_15 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 18) sourceBody396_13 sourceBody396_14

def sourceBody396_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_15 sourceBody396_6

def sourceBody396_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody396_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody396_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody396_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_19 sourceBody396_0

def sourceBody396_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_18 sourceBody396_20

def sourceBody396_22 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody396_21 sourceBody396_0

def sourceBody396_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_22 sourceBody396_6

def sourceBody396_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_23 sourceBody396_0

def sourceBody396_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_17 sourceBody396_24

def sourceBody396_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_16 sourceBody396_25

def sourceBody396_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_12 sourceBody396_26

def sourceBody396_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_11 sourceBody396_27

def sourceBody396_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 168#64]),
        Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody396_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody396_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody396_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody396_0, 396, 4)) (some 301) ([10, 18]) (some (10, sourceBody396_31, 396, 5))

def sourceBody396_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_32 sourceBody396_6

def sourceBody396_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_33 sourceBody396_0

def sourceBody396_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_30 sourceBody396_34

def sourceBody396_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_29 sourceBody396_35

def sourceBody396_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody396_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody396_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody396_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody396_41 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody396_0, 396, 6)) (some 192) ([18, 4, 12]) (some (18, sourceBody396_40, 396, 7))

def sourceBody396_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_41 sourceBody396_6

def sourceBody396_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_42 sourceBody396_0

def sourceBody396_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_39 sourceBody396_43

def sourceBody396_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_38 sourceBody396_44

def sourceBody396_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_37 sourceBody396_45

def sourceBody396_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_0 sourceBody396_46

def sourceBody396_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_0 sourceBody396_47

def sourceBody396_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody396_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody396_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_50 sourceBody396_0

def sourceBody396_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_49 sourceBody396_51

def sourceBody396_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_48 sourceBody396_52

def sourceBody396_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_36 sourceBody396_53

def sourceBody396_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_0 sourceBody396_54

def sourceBody396_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_0 sourceBody396_55

def sourceBody396_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_28 sourceBody396_56

def sourceBody396_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_10 sourceBody396_57

def sourceBody396_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_0 sourceBody396_58

def sourceBody396_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_0 sourceBody396_59

def sourceBody396_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_0 sourceBody396_60

def sourceBody396_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_0 sourceBody396_61

def sourceBody396_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_1 sourceBody396_62

def sourceBody396_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody396_0 sourceBody396_63

def source396 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (396, 2, sourceBody396_64)
end InitECandidate.Proofs.WordStages
