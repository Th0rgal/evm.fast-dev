import InitECandidate.Proofs.WordStages.Source382
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody398_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody398_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody398_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 136#64]))

def sourceBody398_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody398_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody398_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody398_0, 398, 2)) (some 79) ([16, 6, 14]) (some (16, sourceBody398_4, 398, 3))

def sourceBody398_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody398_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_5 sourceBody398_6

def sourceBody398_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_7 sourceBody398_0

def sourceBody398_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_3 sourceBody398_8

def sourceBody398_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_2 sourceBody398_9

def sourceBody398_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_1 sourceBody398_10

def sourceBody398_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody398_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody398_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody398_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody398_16 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.reg 14) sourceBody398_14 sourceBody398_15

def sourceBody398_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_16 sourceBody398_6

def sourceBody398_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody398_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody398_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16, 6]

def sourceBody398_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_20 sourceBody398_0

def sourceBody398_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_15 sourceBody398_21

def sourceBody398_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_19 sourceBody398_22

def sourceBody398_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody398_23 sourceBody398_0

def sourceBody398_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_24 sourceBody398_6

def sourceBody398_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_25 sourceBody398_0

def sourceBody398_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_18 sourceBody398_26

def sourceBody398_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_17 sourceBody398_27

def sourceBody398_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_13 sourceBody398_28

def sourceBody398_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_12 sourceBody398_29

def sourceBody398_31 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody398_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody398_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody398_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 6, 14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody398_0, 398, 4)) (some 290) ([10, 18]) (some (10, sourceBody398_33, 398, 5))

def sourceBody398_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_34 sourceBody398_6

def sourceBody398_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_35 sourceBody398_0

def sourceBody398_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_32 sourceBody398_36

def sourceBody398_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_31 sourceBody398_37

def sourceBody398_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody398_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody398_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody398_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody398_43 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 18 (Flapjack.WordRegImm.reg 4) sourceBody398_41 sourceBody398_42

def sourceBody398_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_43 sourceBody398_6

def sourceBody398_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody398_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody398_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 10)

def sourceBody398_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_47 sourceBody398_0

def sourceBody398_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_48 sourceBody398_0

def sourceBody398_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_46 sourceBody398_49

def sourceBody398_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_0 sourceBody398_50

def sourceBody398_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 7#64)

def sourceBody398_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_52 sourceBody398_33

def sourceBody398_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_51 sourceBody398_53

def sourceBody398_55 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody398_54 sourceBody398_0

def sourceBody398_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_55 sourceBody398_6

def sourceBody398_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_56 sourceBody398_0

def sourceBody398_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_45 sourceBody398_57

def sourceBody398_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_44 sourceBody398_58

def sourceBody398_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_40 sourceBody398_59

def sourceBody398_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_39 sourceBody398_60

def sourceBody398_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody398_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10, 18]

def sourceBody398_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_63 sourceBody398_0

def sourceBody398_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_62 sourceBody398_64

def sourceBody398_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_18 sourceBody398_65

def sourceBody398_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_61 sourceBody398_66

def sourceBody398_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_38 sourceBody398_67

def sourceBody398_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_0 sourceBody398_68

def sourceBody398_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_0 sourceBody398_69

def sourceBody398_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_0 sourceBody398_70

def sourceBody398_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_0 sourceBody398_71

def sourceBody398_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_0 sourceBody398_72

def sourceBody398_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_0 sourceBody398_73

def sourceBody398_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_30 sourceBody398_74

def sourceBody398_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_11 sourceBody398_75

def sourceBody398_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_0 sourceBody398_76

def sourceBody398_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody398_0 sourceBody398_77

def source398 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (398, 2, sourceBody398_78)
end InitECandidate.Proofs.WordStages
