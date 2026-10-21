import InitECandidate.Proofs.WordStages.Source395
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody411_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody411_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody411_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody411_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody411_0, 411, 2)) (some 403) ([14]) (some (14, sourceBody411_2, 411, 3))

def sourceBody411_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody411_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_3 sourceBody411_4

def sourceBody411_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_5 sourceBody411_0

def sourceBody411_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_1 sourceBody411_6

def sourceBody411_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody411_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody411_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody411_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody411_12 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.reg 12) sourceBody411_10 sourceBody411_11

def sourceBody411_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_12 sourceBody411_4

def sourceBody411_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody411_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody411_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody411_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_16 sourceBody411_0

def sourceBody411_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_15 sourceBody411_17

def sourceBody411_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody411_18 sourceBody411_0

def sourceBody411_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_19 sourceBody411_4

def sourceBody411_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_20 sourceBody411_0

def sourceBody411_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_14 sourceBody411_21

def sourceBody411_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_13 sourceBody411_22

def sourceBody411_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_9 sourceBody411_23

def sourceBody411_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_8 sourceBody411_24

def sourceBody411_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody411_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 136#64]))

def sourceBody411_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody411_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody411_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody411_0, 411, 4)) (some 79) ([6, 12, 10]) (some (6, sourceBody411_29, 411, 5))

def sourceBody411_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_30 sourceBody411_4

def sourceBody411_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_31 sourceBody411_0

def sourceBody411_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_28 sourceBody411_32

def sourceBody411_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_27 sourceBody411_33

def sourceBody411_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_26 sourceBody411_34

def sourceBody411_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody411_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody411_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody411_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.WordRegImm.reg 10) sourceBody411_38 sourceBody411_9

def sourceBody411_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_39 sourceBody411_4

def sourceBody411_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody411_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody411_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_42 sourceBody411_0

def sourceBody411_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_11 sourceBody411_43

def sourceBody411_45 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody411_44 sourceBody411_0

def sourceBody411_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_45 sourceBody411_4

def sourceBody411_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_46 sourceBody411_0

def sourceBody411_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_41 sourceBody411_47

def sourceBody411_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_40 sourceBody411_48

def sourceBody411_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_37 sourceBody411_49

def sourceBody411_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_36 sourceBody411_50

def sourceBody411_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody411_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody411_54 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody411_0, 411, 6)) (some 410) ([12]) (some (12, sourceBody411_53, 411, 7))

def sourceBody411_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_54 sourceBody411_4

def sourceBody411_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_55 sourceBody411_0

def sourceBody411_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_52 sourceBody411_56

def sourceBody411_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody411_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody411_60 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 16) sourceBody411_59 sourceBody411_37

def sourceBody411_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_60 sourceBody411_4

def sourceBody411_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody411_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody411_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_63 sourceBody411_0

def sourceBody411_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_9 sourceBody411_64

def sourceBody411_66 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody411_65 sourceBody411_0

def sourceBody411_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_66 sourceBody411_4

def sourceBody411_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_67 sourceBody411_0

def sourceBody411_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_62 sourceBody411_68

def sourceBody411_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_61 sourceBody411_69

def sourceBody411_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_58 sourceBody411_70

def sourceBody411_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_14 sourceBody411_71

def sourceBody411_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_38 sourceBody411_64

def sourceBody411_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_72 sourceBody411_73

def sourceBody411_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_57 sourceBody411_74

def sourceBody411_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_0 sourceBody411_75

def sourceBody411_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_0 sourceBody411_76

def sourceBody411_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_51 sourceBody411_77

def sourceBody411_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_35 sourceBody411_78

def sourceBody411_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_0 sourceBody411_79

def sourceBody411_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_0 sourceBody411_80

def sourceBody411_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_25 sourceBody411_81

def sourceBody411_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_7 sourceBody411_82

def sourceBody411_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_0 sourceBody411_83

def sourceBody411_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody411_0 sourceBody411_84

def source411 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (411, 2, sourceBody411_85)
end InitECandidate.Proofs.WordStages
