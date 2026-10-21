import InitECandidate.Proofs.WordStages.Source428
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody444_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody444_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
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
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody444_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody444_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody444_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody444_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([20, 8]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody444_0, 444, 2)) (some 405) ([18, 14, 24]) (some (18, sourceBody444_4, 444, 3))

def sourceBody444_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody444_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_5 sourceBody444_6

def sourceBody444_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_7 sourceBody444_0

def sourceBody444_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_3 sourceBody444_8

def sourceBody444_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_2 sourceBody444_9

def sourceBody444_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_1 sourceBody444_10

def sourceBody444_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody444_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody444_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody444_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody444_16 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.reg 24) sourceBody444_14 sourceBody444_15

def sourceBody444_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_16 sourceBody444_6

def sourceBody444_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 14)

def sourceBody444_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 8))

def sourceBody444_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody444_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody444_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody444_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18, 14, 24, 6]

def sourceBody444_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_23 sourceBody444_0

def sourceBody444_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_22 sourceBody444_24

def sourceBody444_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_21 sourceBody444_25

def sourceBody444_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_20 sourceBody444_26

def sourceBody444_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_19 sourceBody444_27

def sourceBody444_29 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody444_28 sourceBody444_0

def sourceBody444_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_29 sourceBody444_6

def sourceBody444_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_30 sourceBody444_0

def sourceBody444_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_18 sourceBody444_31

def sourceBody444_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_17 sourceBody444_32

def sourceBody444_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_13 sourceBody444_33

def sourceBody444_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_12 sourceBody444_34

def sourceBody444_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody444_37 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody444_0, 444, 4)) (some 392) ([14]) (some (14, sourceBody444_36, 444, 5))

def sourceBody444_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_37 sourceBody444_6

def sourceBody444_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_38 sourceBody444_0

def sourceBody444_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_2 sourceBody444_39

def sourceBody444_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_0 sourceBody444_40

def sourceBody444_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_0 sourceBody444_41

def sourceBody444_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_35 sourceBody444_42

def sourceBody444_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody444_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody444_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody444_47 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 14, 24, 6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody444_0, 444, 6)) (some 397) ([16, 12]) (some (16, sourceBody444_46, 444, 7))

def sourceBody444_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_47 sourceBody444_6

def sourceBody444_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_48 sourceBody444_0

def sourceBody444_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_45 sourceBody444_49

def sourceBody444_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_44 sourceBody444_50

def sourceBody444_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody444_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody444_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 24)

def sourceBody444_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody444_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16, 12, 22, 10]

def sourceBody444_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_56 sourceBody444_0

def sourceBody444_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_55 sourceBody444_57

def sourceBody444_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_54 sourceBody444_58

def sourceBody444_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_53 sourceBody444_59

def sourceBody444_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_52 sourceBody444_60

def sourceBody444_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_51 sourceBody444_61

def sourceBody444_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_0 sourceBody444_62

def sourceBody444_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_0 sourceBody444_63

def sourceBody444_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_0 sourceBody444_64

def sourceBody444_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_0 sourceBody444_65

def sourceBody444_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_0 sourceBody444_66

def sourceBody444_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_0 sourceBody444_67

def sourceBody444_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_0 sourceBody444_68

def sourceBody444_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_0 sourceBody444_69

def sourceBody444_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_43 sourceBody444_70

def sourceBody444_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_11 sourceBody444_71

def sourceBody444_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_0 sourceBody444_72

def sourceBody444_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_0 sourceBody444_73

def sourceBody444_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_0 sourceBody444_74

def sourceBody444_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody444_0 sourceBody444_75

def source444 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (444, 3, sourceBody444_76)
end InitECandidate.Proofs.WordStages
