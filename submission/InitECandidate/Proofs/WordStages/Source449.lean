import InitECandidate.Proofs.WordStages.Source433
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody449_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody449_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 216#64]))

def sourceBody449_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody449_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody449_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 20]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody449_0, 449, 2)) (some 186) ([16, 24]) (some (16, sourceBody449_3, 449, 3))

def sourceBody449_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody449_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_4 sourceBody449_5

def sourceBody449_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_6 sourceBody449_0

def sourceBody449_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_2 sourceBody449_7

def sourceBody449_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_1 sourceBody449_8

def sourceBody449_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody449_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody449_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody449_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody449_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 8) sourceBody449_12 sourceBody449_13

def sourceBody449_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_14 sourceBody449_5

def sourceBody449_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody449_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody449_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody449_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_18 sourceBody449_0

def sourceBody449_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_17 sourceBody449_19

def sourceBody449_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody449_20 sourceBody449_0

def sourceBody449_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_21 sourceBody449_5

def sourceBody449_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_22 sourceBody449_0

def sourceBody449_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_16 sourceBody449_23

def sourceBody449_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_15 sourceBody449_24

def sourceBody449_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_11 sourceBody449_25

def sourceBody449_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_10 sourceBody449_26

def sourceBody449_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody449_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody449_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody449_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody449_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([24, 8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody449_0, 449, 4)) (some 186) ([18, 14]) (some (18, sourceBody449_31, 449, 5))

def sourceBody449_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_32 sourceBody449_5

def sourceBody449_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_33 sourceBody449_0

def sourceBody449_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_30 sourceBody449_34

def sourceBody449_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_29 sourceBody449_35

def sourceBody449_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 24)

def sourceBody449_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody449_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody449_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody449_41 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 22) sourceBody449_39 sourceBody449_40

def sourceBody449_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_41 sourceBody449_5

def sourceBody449_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody449_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody449_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody449_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_45 sourceBody449_0

def sourceBody449_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_44 sourceBody449_46

def sourceBody449_48 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody449_47 sourceBody449_0

def sourceBody449_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_48 sourceBody449_5

def sourceBody449_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_49 sourceBody449_0

def sourceBody449_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_43 sourceBody449_50

def sourceBody449_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_42 sourceBody449_51

def sourceBody449_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_38 sourceBody449_52

def sourceBody449_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_37 sourceBody449_53

def sourceBody449_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody449_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 40#64)

def sourceBody449_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody449_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody449_59 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody449_0, 449, 6)) (some 447) ([14, 22, 12]) (some (14, sourceBody449_58, 449, 7))

def sourceBody449_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_59 sourceBody449_5

def sourceBody449_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_60 sourceBody449_0

def sourceBody449_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_57 sourceBody449_61

def sourceBody449_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_56 sourceBody449_62

def sourceBody449_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_55 sourceBody449_63

def sourceBody449_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_0 sourceBody449_64

def sourceBody449_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_0 sourceBody449_65

def sourceBody449_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_54 sourceBody449_66

def sourceBody449_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody449_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody449_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 4)

def sourceBody449_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody449_0, 449, 8)) (some 193) ([14, 22]) (some (14, sourceBody449_58, 449, 9))

def sourceBody449_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_71 sourceBody449_5

def sourceBody449_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_72 sourceBody449_0

def sourceBody449_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_70 sourceBody449_73

def sourceBody449_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_69 sourceBody449_74

def sourceBody449_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_0 sourceBody449_75

def sourceBody449_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_0 sourceBody449_76

def sourceBody449_78 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody449_77 sourceBody449_0

def sourceBody449_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_78 sourceBody449_5

def sourceBody449_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_79 sourceBody449_0

def sourceBody449_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_43 sourceBody449_80

def sourceBody449_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_42 sourceBody449_81

def sourceBody449_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_38 sourceBody449_82

def sourceBody449_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_68 sourceBody449_83

def sourceBody449_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_67 sourceBody449_84

def sourceBody449_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_85 sourceBody449_47

def sourceBody449_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_36 sourceBody449_86

def sourceBody449_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_0 sourceBody449_87

def sourceBody449_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_0 sourceBody449_88

def sourceBody449_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_0 sourceBody449_89

def sourceBody449_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_0 sourceBody449_90

def sourceBody449_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_28 sourceBody449_91

def sourceBody449_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_0 sourceBody449_92

def sourceBody449_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_27 sourceBody449_93

def sourceBody449_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_9 sourceBody449_94

def sourceBody449_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_0 sourceBody449_95

def sourceBody449_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_0 sourceBody449_96

def sourceBody449_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_0 sourceBody449_97

def sourceBody449_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody449_0 sourceBody449_98

def source449 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (449, 4, sourceBody449_99)
end InitECandidate.Proofs.WordStages
