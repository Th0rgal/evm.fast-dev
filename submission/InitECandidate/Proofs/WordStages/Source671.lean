import InitECandidate.Proofs.WordStages.Source655
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody671_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody671_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody671_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody671_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 28)

def sourceBody671_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody671_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody671_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody671_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 36 (Flapjack.WordRegImm.reg 12) sourceBody671_5 sourceBody671_6

def sourceBody671_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_7 sourceBody671_2

def sourceBody671_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 36)

def sourceBody671_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 28)
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody671_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 6,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 28)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody671_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 6,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 28)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody671_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 6,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 28)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody671_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 20)

def sourceBody671_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 36)

def sourceBody671_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody671_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody671_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody671_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody671_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 34, 14, 30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody671_0, 671, 2)) (some 661) ([22, 38, 10, 24, 16]) (some (22, sourceBody671_19, 671, 3))

def sourceBody671_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_20 sourceBody671_2

def sourceBody671_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_21 sourceBody671_0

def sourceBody671_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_18 sourceBody671_22

def sourceBody671_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_17 sourceBody671_23

def sourceBody671_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_16 sourceBody671_24

def sourceBody671_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_15 sourceBody671_25

def sourceBody671_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_14 sourceBody671_26

def sourceBody671_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 4,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 28)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody671_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 18)

def sourceBody671_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 34)

def sourceBody671_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody671_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 30)

def sourceBody671_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 38)

def sourceBody671_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 22) 32

def sourceBody671_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_34 sourceBody671_0

def sourceBody671_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_33 sourceBody671_35

def sourceBody671_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody671_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 8#64])
  32

def sourceBody671_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_38 sourceBody671_0

def sourceBody671_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_37 sourceBody671_39

def sourceBody671_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 24)

def sourceBody671_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 16#64])
  32

def sourceBody671_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_42 sourceBody671_0

def sourceBody671_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_41 sourceBody671_43

def sourceBody671_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 16)

def sourceBody671_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 24#64])
  32

def sourceBody671_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_46 sourceBody671_0

def sourceBody671_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_45 sourceBody671_47

def sourceBody671_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_48 sourceBody671_0

def sourceBody671_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_44 sourceBody671_49

def sourceBody671_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_40 sourceBody671_50

def sourceBody671_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_36 sourceBody671_51

def sourceBody671_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_32 sourceBody671_52

def sourceBody671_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_53

def sourceBody671_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_31 sourceBody671_54

def sourceBody671_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_55

def sourceBody671_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_30 sourceBody671_56

def sourceBody671_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_57

def sourceBody671_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_29 sourceBody671_58

def sourceBody671_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_59

def sourceBody671_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_28 sourceBody671_60

def sourceBody671_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_61

def sourceBody671_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody671_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 22)

def sourceBody671_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_64 sourceBody671_0

def sourceBody671_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_65 sourceBody671_0

def sourceBody671_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_63 sourceBody671_66

def sourceBody671_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_67

def sourceBody671_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_62 sourceBody671_68

def sourceBody671_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_27 sourceBody671_69

def sourceBody671_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_70

def sourceBody671_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_71

def sourceBody671_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_72

def sourceBody671_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_73

def sourceBody671_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_74

def sourceBody671_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_75

def sourceBody671_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_76

def sourceBody671_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_77

def sourceBody671_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_13 sourceBody671_78

def sourceBody671_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_79

def sourceBody671_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_12 sourceBody671_80

def sourceBody671_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_81

def sourceBody671_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_11 sourceBody671_82

def sourceBody671_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_83

def sourceBody671_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_10 sourceBody671_84

def sourceBody671_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_85

def sourceBody671_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody671_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_86 sourceBody671_87

def sourceBody671_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody671_90 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody671_88 sourceBody671_89

def sourceBody671_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_90 sourceBody671_2

def sourceBody671_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_91 sourceBody671_0

def sourceBody671_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_9 sourceBody671_92

def sourceBody671_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_8 sourceBody671_93

def sourceBody671_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_4 sourceBody671_94

def sourceBody671_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_3 sourceBody671_95

def sourceBody671_97 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln) sourceBody671_96 (Flapjack.Spt.ls PUnit.unit)

def sourceBody671_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_97 sourceBody671_2

def sourceBody671_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_2 sourceBody671_98

def sourceBody671_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody671_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody671_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_101 sourceBody671_0

def sourceBody671_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_100 sourceBody671_102

def sourceBody671_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_99 sourceBody671_103

def sourceBody671_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_1 sourceBody671_104

def sourceBody671_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody671_0 sourceBody671_105

def source671 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (671, 5, sourceBody671_106)
end InitECandidate.Proofs.WordStages
