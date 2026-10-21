import InitECandidate.Proofs.WordStages.Source273
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody289_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody289_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody289_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody289_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody289_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.const 2#64])

def sourceBody289_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody289_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody289_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 14 (Flapjack.WordRegImm.reg 10) sourceBody289_5 sourceBody289_6

def sourceBody289_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_7 sourceBody289_2

def sourceBody289_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody289_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
    (Flapjack.WordLangExpHOL.const 1#64))

def sourceBody289_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody289_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_11 sourceBody289_0

def sourceBody289_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_12 sourceBody289_0

def sourceBody289_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_10 sourceBody289_13

def sourceBody289_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_0 sourceBody289_14

def sourceBody289_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody289_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_15 sourceBody289_16

def sourceBody289_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody289_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody289_17 sourceBody289_18

def sourceBody289_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_19 sourceBody289_2

def sourceBody289_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_20 sourceBody289_0

def sourceBody289_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_9 sourceBody289_21

def sourceBody289_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_8 sourceBody289_22

def sourceBody289_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_4 sourceBody289_23

def sourceBody289_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_3 sourceBody289_24

def sourceBody289_26 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody289_25 (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody289_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_26 sourceBody289_2

def sourceBody289_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_2 sourceBody289_27

def sourceBody289_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody289_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody289_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody289_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody289_0, 289, 2)) (some 182) ([14, 10]) (some (14, sourceBody289_31, 289, 3))

def sourceBody289_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_32 sourceBody289_2

def sourceBody289_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_33 sourceBody289_0

def sourceBody289_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_30 sourceBody289_34

def sourceBody289_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_29 sourceBody289_35

def sourceBody289_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody289_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody289_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody289_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 18 (Flapjack.WordRegImm.reg 6) sourceBody289_38 sourceBody289_39

def sourceBody289_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_40 sourceBody289_2

def sourceBody289_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody289_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody289_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody289_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 152#64]))

def sourceBody289_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody289_47 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody289_0, 289, 4)) (some 158) ([18, 6, 12]) (some (18, sourceBody289_46, 289, 5))

def sourceBody289_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_47 sourceBody289_2

def sourceBody289_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_48 sourceBody289_0

def sourceBody289_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_45 sourceBody289_49

def sourceBody289_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_44 sourceBody289_50

def sourceBody289_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_43 sourceBody289_51

def sourceBody289_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_0 sourceBody289_52

def sourceBody289_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_0 sourceBody289_53

def sourceBody289_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody289_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 152#64]))

def sourceBody289_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
        (Flapjack.WordLangExpHOL.const 4#64)])

def sourceBody289_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody289_0, 289, 6)) (some 192) ([18, 6, 12]) (some (18, sourceBody289_46, 289, 7))

def sourceBody289_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_58 sourceBody289_2

def sourceBody289_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_59 sourceBody289_0

def sourceBody289_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_57 sourceBody289_60

def sourceBody289_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_56 sourceBody289_61

def sourceBody289_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_55 sourceBody289_62

def sourceBody289_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_0 sourceBody289_63

def sourceBody289_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_0 sourceBody289_64

def sourceBody289_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_54 sourceBody289_65

def sourceBody289_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody289_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody289_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_68 sourceBody289_0

def sourceBody289_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_69 sourceBody289_0

def sourceBody289_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_67 sourceBody289_70

def sourceBody289_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_0 sourceBody289_71

def sourceBody289_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_66 sourceBody289_72

def sourceBody289_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_73 sourceBody289_16

def sourceBody289_75 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody289_74 sourceBody289_18

def sourceBody289_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_75 sourceBody289_2

def sourceBody289_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_76 sourceBody289_0

def sourceBody289_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_42 sourceBody289_77

def sourceBody289_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_41 sourceBody289_78

def sourceBody289_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_37 sourceBody289_79

def sourceBody289_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_9 sourceBody289_80

def sourceBody289_82 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody289_81 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody289_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_82 sourceBody289_2

def sourceBody289_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_2 sourceBody289_83

def sourceBody289_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody289_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody289_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_86 sourceBody289_0

def sourceBody289_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_85 sourceBody289_87

def sourceBody289_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_84 sourceBody289_88

def sourceBody289_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_6 sourceBody289_89

def sourceBody289_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_0 sourceBody289_90

def sourceBody289_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_36 sourceBody289_91

def sourceBody289_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_0 sourceBody289_92

def sourceBody289_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_0 sourceBody289_93

def sourceBody289_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_28 sourceBody289_94

def sourceBody289_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_1 sourceBody289_95

def sourceBody289_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody289_0 sourceBody289_96

def source289 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (289, 3, sourceBody289_97)
end InitECandidate.Proofs.WordStages
