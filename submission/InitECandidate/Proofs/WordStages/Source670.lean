import InitECandidate.Proofs.WordStages.Source654
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody670_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody670_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody670_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody670_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody670_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 2)

def sourceBody670_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody670_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody670_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 20 (Flapjack.WordRegImm.reg 34) sourceBody670_5 sourceBody670_6

def sourceBody670_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_7 sourceBody670_2

def sourceBody670_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 20)

def sourceBody670_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody670_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 6,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody670_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 6,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody670_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 6,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody670_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 28)

def sourceBody670_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 20)

def sourceBody670_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 34)

def sourceBody670_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody670_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody670_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([26, 18, 32, 14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody670_0, 670, 2)) (some 656) ([30, 22, 36, 8]) (some (30, sourceBody670_18, 670, 3))

def sourceBody670_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_19 sourceBody670_2

def sourceBody670_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_20 sourceBody670_0

def sourceBody670_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_17 sourceBody670_21

def sourceBody670_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_16 sourceBody670_22

def sourceBody670_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_15 sourceBody670_23

def sourceBody670_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_14 sourceBody670_24

def sourceBody670_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 4,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody670_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody670_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 18)

def sourceBody670_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 32)

def sourceBody670_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody670_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody670_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 30) 16

def sourceBody670_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_32 sourceBody670_0

def sourceBody670_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_31 sourceBody670_33

def sourceBody670_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 36)

def sourceBody670_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 8#64])
  16

def sourceBody670_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_36 sourceBody670_0

def sourceBody670_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_35 sourceBody670_37

def sourceBody670_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody670_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 16#64])
  16

def sourceBody670_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_40 sourceBody670_0

def sourceBody670_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_39 sourceBody670_41

def sourceBody670_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody670_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 24#64])
  16

def sourceBody670_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_44 sourceBody670_0

def sourceBody670_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_43 sourceBody670_45

def sourceBody670_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_46 sourceBody670_0

def sourceBody670_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_42 sourceBody670_47

def sourceBody670_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_38 sourceBody670_48

def sourceBody670_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_34 sourceBody670_49

def sourceBody670_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_30 sourceBody670_50

def sourceBody670_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_51

def sourceBody670_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_29 sourceBody670_52

def sourceBody670_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_53

def sourceBody670_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_28 sourceBody670_54

def sourceBody670_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_55

def sourceBody670_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_27 sourceBody670_56

def sourceBody670_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_57

def sourceBody670_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_26 sourceBody670_58

def sourceBody670_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_59

def sourceBody670_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody670_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 30)

def sourceBody670_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_62 sourceBody670_0

def sourceBody670_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_63 sourceBody670_0

def sourceBody670_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_61 sourceBody670_64

def sourceBody670_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_65

def sourceBody670_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_60 sourceBody670_66

def sourceBody670_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_25 sourceBody670_67

def sourceBody670_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_68

def sourceBody670_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_69

def sourceBody670_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_70

def sourceBody670_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_71

def sourceBody670_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_72

def sourceBody670_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_73

def sourceBody670_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_74

def sourceBody670_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_75

def sourceBody670_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_13 sourceBody670_76

def sourceBody670_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_77

def sourceBody670_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_12 sourceBody670_78

def sourceBody670_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_79

def sourceBody670_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_11 sourceBody670_80

def sourceBody670_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_81

def sourceBody670_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_10 sourceBody670_82

def sourceBody670_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_83

def sourceBody670_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody670_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_84 sourceBody670_85

def sourceBody670_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody670_88 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody670_86 sourceBody670_87

def sourceBody670_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_88 sourceBody670_2

def sourceBody670_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_89 sourceBody670_0

def sourceBody670_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_9 sourceBody670_90

def sourceBody670_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_8 sourceBody670_91

def sourceBody670_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_4 sourceBody670_92

def sourceBody670_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_3 sourceBody670_93

def sourceBody670_95 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln) sourceBody670_94 (Flapjack.Spt.ls PUnit.unit)

def sourceBody670_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_95 sourceBody670_2

def sourceBody670_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_2 sourceBody670_96

def sourceBody670_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody670_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [28]

def sourceBody670_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_99 sourceBody670_0

def sourceBody670_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_98 sourceBody670_100

def sourceBody670_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_97 sourceBody670_101

def sourceBody670_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_1 sourceBody670_102

def sourceBody670_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody670_0 sourceBody670_103

def source670 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (670, 4, sourceBody670_104)
end InitECandidate.Proofs.WordStages
