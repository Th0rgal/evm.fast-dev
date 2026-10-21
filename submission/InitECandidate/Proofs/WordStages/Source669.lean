import InitECandidate.Proofs.WordStages.Source653
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody669_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody669_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody669_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody669_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 36)

def sourceBody669_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody669_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody669_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody669_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 46 (Flapjack.WordRegImm.reg 12) sourceBody669_5 sourceBody669_6

def sourceBody669_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_7 sourceBody669_2

def sourceBody669_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 46)

def sourceBody669_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody669_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 6,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody669_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 6,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody669_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 6,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody669_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody669_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 8,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody669_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 8,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody669_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 8,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody669_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody669_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 46)

def sourceBody669_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody669_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 32)

def sourceBody669_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 22)

def sourceBody669_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 44)

def sourceBody669_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody669_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 40)

def sourceBody669_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody669_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([28, 50, 10, 30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody669_0, 669, 2)) (some 655) ([20, 42, 16, 38, 26, 48, 14, 34]) (some (20, sourceBody669_26, 669, 3))

def sourceBody669_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_27 sourceBody669_2

def sourceBody669_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_28 sourceBody669_0

def sourceBody669_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_25 sourceBody669_29

def sourceBody669_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_24 sourceBody669_30

def sourceBody669_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_23 sourceBody669_31

def sourceBody669_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_22 sourceBody669_32

def sourceBody669_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_21 sourceBody669_33

def sourceBody669_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_20 sourceBody669_34

def sourceBody669_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_19 sourceBody669_35

def sourceBody669_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_18 sourceBody669_36

def sourceBody669_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 4,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody669_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 28)

def sourceBody669_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 50)

def sourceBody669_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 10)

def sourceBody669_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody669_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 42)

def sourceBody669_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 20) 48

def sourceBody669_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_44 sourceBody669_0

def sourceBody669_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_43 sourceBody669_45

def sourceBody669_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 16)

def sourceBody669_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 8#64])
  48

def sourceBody669_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_48 sourceBody669_0

def sourceBody669_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_47 sourceBody669_49

def sourceBody669_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 38)

def sourceBody669_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 16#64])
  48

def sourceBody669_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_52 sourceBody669_0

def sourceBody669_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_51 sourceBody669_53

def sourceBody669_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 26)

def sourceBody669_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 24#64])
  48

def sourceBody669_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_56 sourceBody669_0

def sourceBody669_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_55 sourceBody669_57

def sourceBody669_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_58 sourceBody669_0

def sourceBody669_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_54 sourceBody669_59

def sourceBody669_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_50 sourceBody669_60

def sourceBody669_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_46 sourceBody669_61

def sourceBody669_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_42 sourceBody669_62

def sourceBody669_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_63

def sourceBody669_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_41 sourceBody669_64

def sourceBody669_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_65

def sourceBody669_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_40 sourceBody669_66

def sourceBody669_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_67

def sourceBody669_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_39 sourceBody669_68

def sourceBody669_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_69

def sourceBody669_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_38 sourceBody669_70

def sourceBody669_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_71

def sourceBody669_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody669_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 20)

def sourceBody669_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_74 sourceBody669_0

def sourceBody669_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_75 sourceBody669_0

def sourceBody669_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_73 sourceBody669_76

def sourceBody669_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_77

def sourceBody669_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_72 sourceBody669_78

def sourceBody669_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_37 sourceBody669_79

def sourceBody669_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_80

def sourceBody669_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_81

def sourceBody669_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_82

def sourceBody669_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_83

def sourceBody669_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_84

def sourceBody669_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_85

def sourceBody669_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_86

def sourceBody669_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_87

def sourceBody669_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_17 sourceBody669_88

def sourceBody669_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_89

def sourceBody669_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_16 sourceBody669_90

def sourceBody669_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_91

def sourceBody669_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_15 sourceBody669_92

def sourceBody669_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_93

def sourceBody669_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_14 sourceBody669_94

def sourceBody669_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_95

def sourceBody669_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_13 sourceBody669_96

def sourceBody669_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_97

def sourceBody669_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_12 sourceBody669_98

def sourceBody669_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_99

def sourceBody669_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_11 sourceBody669_100

def sourceBody669_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_101

def sourceBody669_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_10 sourceBody669_102

def sourceBody669_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_103

def sourceBody669_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody669_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_104 sourceBody669_105

def sourceBody669_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody669_108 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody669_106 sourceBody669_107

def sourceBody669_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_108 sourceBody669_2

def sourceBody669_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_109 sourceBody669_0

def sourceBody669_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_9 sourceBody669_110

def sourceBody669_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_8 sourceBody669_111

def sourceBody669_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_4 sourceBody669_112

def sourceBody669_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_3 sourceBody669_113

def sourceBody669_115 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln) sourceBody669_114 (Flapjack.Spt.ls PUnit.unit)

def sourceBody669_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_115 sourceBody669_2

def sourceBody669_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_2 sourceBody669_116

def sourceBody669_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody669_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody669_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_119 sourceBody669_0

def sourceBody669_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_118 sourceBody669_120

def sourceBody669_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_117 sourceBody669_121

def sourceBody669_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_1 sourceBody669_122

def sourceBody669_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody669_0 sourceBody669_123

def source669 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (669, 5, sourceBody669_124)
end InitECandidate.Proofs.WordStages
