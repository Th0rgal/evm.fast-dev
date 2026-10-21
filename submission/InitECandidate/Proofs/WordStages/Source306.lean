import InitECandidate.Proofs.WordStages.Source290
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody306_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody306_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody306_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody306_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody306_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.reg 12) sourceBody306_2 sourceBody306_3

def sourceBody306_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody306_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_4 sourceBody306_5

def sourceBody306_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody306_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody306_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody306_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody306_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 152#64]))

def sourceBody306_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody306_13 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody306_8, 306, 2)) (some 158) ([14, 12, 16]) (some (14, sourceBody306_12, 306, 3))

def sourceBody306_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_13 sourceBody306_5

def sourceBody306_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_14 sourceBody306_8

def sourceBody306_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_11 sourceBody306_15

def sourceBody306_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_10 sourceBody306_16

def sourceBody306_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_9 sourceBody306_17

def sourceBody306_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_8 sourceBody306_18

def sourceBody306_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_8 sourceBody306_19

def sourceBody306_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody306_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody306_8, 306, 4)) (some 68) ([14]) (some (14, sourceBody306_12, 306, 5))

def sourceBody306_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_22 sourceBody306_5

def sourceBody306_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_23 sourceBody306_8

def sourceBody306_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_21 sourceBody306_24

def sourceBody306_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 152#64]))

def sourceBody306_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody306_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody306_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody306_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody306_8, 306, 6)) (some 284) ([12, 16, 8]) (some (12, sourceBody306_29, 306, 7))

def sourceBody306_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_30 sourceBody306_5

def sourceBody306_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_31 sourceBody306_8

def sourceBody306_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_28 sourceBody306_32

def sourceBody306_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_27 sourceBody306_33

def sourceBody306_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_26 sourceBody306_34

def sourceBody306_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_8 sourceBody306_35

def sourceBody306_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_8 sourceBody306_36

def sourceBody306_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody306_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody306_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14, 12]

def sourceBody306_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_40 sourceBody306_8

def sourceBody306_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_39 sourceBody306_41

def sourceBody306_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_38 sourceBody306_42

def sourceBody306_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_37 sourceBody306_43

def sourceBody306_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_25 sourceBody306_44

def sourceBody306_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_8 sourceBody306_45

def sourceBody306_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_8 sourceBody306_46

def sourceBody306_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_20 sourceBody306_47

def sourceBody306_49 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody306_48 sourceBody306_8

def sourceBody306_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_49 sourceBody306_5

def sourceBody306_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_50 sourceBody306_8

def sourceBody306_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_7 sourceBody306_51

def sourceBody306_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_6 sourceBody306_52

def sourceBody306_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_1 sourceBody306_53

def sourceBody306_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_0 sourceBody306_54

def sourceBody306_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 6)
    (Flapjack.WordLangExpHOL.const 1#64))

def sourceBody306_57 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody306_8, 306, 8)) (some 68) ([14]) (some (14, sourceBody306_12, 306, 9))

def sourceBody306_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_57 sourceBody306_5

def sourceBody306_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_58 sourceBody306_8

def sourceBody306_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_56 sourceBody306_59

def sourceBody306_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody306_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody306_63 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody306_8, 306, 10)) (some 284) ([12, 16, 8]) (some (12, sourceBody306_29, 306, 11))

def sourceBody306_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_63 sourceBody306_5

def sourceBody306_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_64 sourceBody306_8

def sourceBody306_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_28 sourceBody306_65

def sourceBody306_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_62 sourceBody306_66

def sourceBody306_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_61 sourceBody306_67

def sourceBody306_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_8 sourceBody306_68

def sourceBody306_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_8 sourceBody306_69

def sourceBody306_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 6)
    (Flapjack.WordLangExpHOL.const 1#64))

def sourceBody306_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_71 sourceBody306_41

def sourceBody306_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_38 sourceBody306_72

def sourceBody306_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_70 sourceBody306_73

def sourceBody306_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_60 sourceBody306_74

def sourceBody306_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_8 sourceBody306_75

def sourceBody306_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_8 sourceBody306_76

def sourceBody306_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody306_55 sourceBody306_77

def source306 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (306, 4, sourceBody306_78)
end InitECandidate.Proofs.WordStages
