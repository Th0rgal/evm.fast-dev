import InitECandidate.Proofs.WordStages.Source312
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody328_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody328_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody328_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody328_0, 328, 2)) (some 69) ([]) (some (20, sourceBody328_1, 328, 3))

def sourceBody328_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody328_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_2 sourceBody328_3

def sourceBody328_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_4 sourceBody328_0

def sourceBody328_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody328_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody328_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody328_9 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody328_0, 328, 4)) (some 304) ([16, 26]) (some (16, sourceBody328_8, 328, 5))

def sourceBody328_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_9 sourceBody328_3

def sourceBody328_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_10 sourceBody328_0

def sourceBody328_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_7 sourceBody328_11

def sourceBody328_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_6 sourceBody328_12

def sourceBody328_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 16)

def sourceBody328_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody328_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody328_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody328_18 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 8 (Flapjack.WordRegImm.reg 18) sourceBody328_16 sourceBody328_17

def sourceBody328_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_18 sourceBody328_3

def sourceBody328_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody328_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody328_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody328_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody328_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody328_0, 328, 6)) (some 177) ([8, 18]) (some (8, sourceBody328_23, 328, 7))

def sourceBody328_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_24 sourceBody328_3

def sourceBody328_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_25 sourceBody328_0

def sourceBody328_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_22 sourceBody328_26

def sourceBody328_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_21 sourceBody328_27

def sourceBody328_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody328_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody328_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody328_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody328_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody328_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody328_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody328_0, 328, 8)) (some 316) ([18, 14, 24, 12, 22]) (some (18, sourceBody328_34, 328, 9))

def sourceBody328_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_35 sourceBody328_3

def sourceBody328_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_36 sourceBody328_0

def sourceBody328_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_33 sourceBody328_37

def sourceBody328_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_32 sourceBody328_38

def sourceBody328_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_31 sourceBody328_39

def sourceBody328_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_30 sourceBody328_40

def sourceBody328_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_29 sourceBody328_41

def sourceBody328_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_0 sourceBody328_42

def sourceBody328_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_0 sourceBody328_43

def sourceBody328_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody328_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody328_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_46 sourceBody328_0

def sourceBody328_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_47 sourceBody328_0

def sourceBody328_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_45 sourceBody328_48

def sourceBody328_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_0 sourceBody328_49

def sourceBody328_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_44 sourceBody328_50

def sourceBody328_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_28 sourceBody328_51

def sourceBody328_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_0 sourceBody328_52

def sourceBody328_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_0 sourceBody328_53

def sourceBody328_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody328_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_54 sourceBody328_55

def sourceBody328_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody328_58 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody328_56 sourceBody328_57

def sourceBody328_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_58 sourceBody328_3

def sourceBody328_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_59 sourceBody328_0

def sourceBody328_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_20 sourceBody328_60

def sourceBody328_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_19 sourceBody328_61

def sourceBody328_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_15 sourceBody328_62

def sourceBody328_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_14 sourceBody328_63

def sourceBody328_65 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody328_64 (Flapjack.Spt.bs
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody328_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_65 sourceBody328_3

def sourceBody328_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_3 sourceBody328_66

def sourceBody328_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 20)

def sourceBody328_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody328_70 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody328_0, 328, 10)) (some 327) ([8, 18]) (some (8, sourceBody328_23, 328, 11))

def sourceBody328_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_70 sourceBody328_3

def sourceBody328_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_71 sourceBody328_0

def sourceBody328_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_69 sourceBody328_72

def sourceBody328_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_68 sourceBody328_73

def sourceBody328_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_0 sourceBody328_74

def sourceBody328_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_0 sourceBody328_75

def sourceBody328_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_67 sourceBody328_76

def sourceBody328_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody328_79 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody328_0, 328, 12)) (some 70) ([8]) (some (8, sourceBody328_23, 328, 13))

def sourceBody328_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_79 sourceBody328_3

def sourceBody328_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_80 sourceBody328_0

def sourceBody328_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_78 sourceBody328_81

def sourceBody328_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_0 sourceBody328_82

def sourceBody328_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_0 sourceBody328_83

def sourceBody328_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_77 sourceBody328_84

def sourceBody328_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody328_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_86 sourceBody328_0

def sourceBody328_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_7 sourceBody328_87

def sourceBody328_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_85 sourceBody328_88

def sourceBody328_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_6 sourceBody328_89

def sourceBody328_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_0 sourceBody328_90

def sourceBody328_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_13 sourceBody328_91

def sourceBody328_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_0 sourceBody328_92

def sourceBody328_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_0 sourceBody328_93

def sourceBody328_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_5 sourceBody328_94

def sourceBody328_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_0 sourceBody328_95

def sourceBody328_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody328_0 sourceBody328_96

def source328 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (328, 4, sourceBody328_97)
end InitECandidate.Proofs.WordStages
