import InitECandidate.Proofs.WordStages.Source652
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody668_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody668_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody668_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody668_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 36)

def sourceBody668_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody668_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody668_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody668_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 46 (Flapjack.WordRegImm.reg 12) sourceBody668_5 sourceBody668_6

def sourceBody668_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_7 sourceBody668_2

def sourceBody668_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 46)

def sourceBody668_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody668_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 6,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody668_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 6,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody668_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 6,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody668_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody668_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 8,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody668_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 8,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody668_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 8,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody668_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody668_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 46)

def sourceBody668_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody668_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 32)

def sourceBody668_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 22)

def sourceBody668_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 44)

def sourceBody668_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody668_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 40)

def sourceBody668_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody668_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([28, 50, 10, 30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody668_0, 668, 2)) (some 654) ([20, 42, 16, 38, 26, 48, 14, 34]) (some (20, sourceBody668_26, 668, 3))

def sourceBody668_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_27 sourceBody668_2

def sourceBody668_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_28 sourceBody668_0

def sourceBody668_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_25 sourceBody668_29

def sourceBody668_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_24 sourceBody668_30

def sourceBody668_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_23 sourceBody668_31

def sourceBody668_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_22 sourceBody668_32

def sourceBody668_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_21 sourceBody668_33

def sourceBody668_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_20 sourceBody668_34

def sourceBody668_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_19 sourceBody668_35

def sourceBody668_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_18 sourceBody668_36

def sourceBody668_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 4,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody668_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 28)

def sourceBody668_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 50)

def sourceBody668_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 10)

def sourceBody668_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody668_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 42)

def sourceBody668_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 20) 48

def sourceBody668_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_44 sourceBody668_0

def sourceBody668_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_43 sourceBody668_45

def sourceBody668_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 16)

def sourceBody668_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 8#64])
  48

def sourceBody668_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_48 sourceBody668_0

def sourceBody668_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_47 sourceBody668_49

def sourceBody668_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 38)

def sourceBody668_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 16#64])
  48

def sourceBody668_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_52 sourceBody668_0

def sourceBody668_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_51 sourceBody668_53

def sourceBody668_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 26)

def sourceBody668_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 24#64])
  48

def sourceBody668_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_56 sourceBody668_0

def sourceBody668_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_55 sourceBody668_57

def sourceBody668_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_58 sourceBody668_0

def sourceBody668_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_54 sourceBody668_59

def sourceBody668_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_50 sourceBody668_60

def sourceBody668_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_46 sourceBody668_61

def sourceBody668_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_42 sourceBody668_62

def sourceBody668_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_63

def sourceBody668_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_41 sourceBody668_64

def sourceBody668_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_65

def sourceBody668_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_40 sourceBody668_66

def sourceBody668_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_67

def sourceBody668_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_39 sourceBody668_68

def sourceBody668_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_69

def sourceBody668_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_38 sourceBody668_70

def sourceBody668_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_71

def sourceBody668_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody668_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 20)

def sourceBody668_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_74 sourceBody668_0

def sourceBody668_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_75 sourceBody668_0

def sourceBody668_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_73 sourceBody668_76

def sourceBody668_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_77

def sourceBody668_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_72 sourceBody668_78

def sourceBody668_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_37 sourceBody668_79

def sourceBody668_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_80

def sourceBody668_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_81

def sourceBody668_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_82

def sourceBody668_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_83

def sourceBody668_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_84

def sourceBody668_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_85

def sourceBody668_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_86

def sourceBody668_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_87

def sourceBody668_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_17 sourceBody668_88

def sourceBody668_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_89

def sourceBody668_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_16 sourceBody668_90

def sourceBody668_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_91

def sourceBody668_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_15 sourceBody668_92

def sourceBody668_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_93

def sourceBody668_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_14 sourceBody668_94

def sourceBody668_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_95

def sourceBody668_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_13 sourceBody668_96

def sourceBody668_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_97

def sourceBody668_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_12 sourceBody668_98

def sourceBody668_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_99

def sourceBody668_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_11 sourceBody668_100

def sourceBody668_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_101

def sourceBody668_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_10 sourceBody668_102

def sourceBody668_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_103

def sourceBody668_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody668_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_104 sourceBody668_105

def sourceBody668_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody668_108 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody668_106 sourceBody668_107

def sourceBody668_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_108 sourceBody668_2

def sourceBody668_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_109 sourceBody668_0

def sourceBody668_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_9 sourceBody668_110

def sourceBody668_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_8 sourceBody668_111

def sourceBody668_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_4 sourceBody668_112

def sourceBody668_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_3 sourceBody668_113

def sourceBody668_115 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln) sourceBody668_114 (Flapjack.Spt.ls PUnit.unit)

def sourceBody668_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_115 sourceBody668_2

def sourceBody668_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_2 sourceBody668_116

def sourceBody668_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody668_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody668_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_119 sourceBody668_0

def sourceBody668_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_118 sourceBody668_120

def sourceBody668_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_117 sourceBody668_121

def sourceBody668_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_1 sourceBody668_122

def sourceBody668_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody668_0 sourceBody668_123

def source668 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (668, 5, sourceBody668_124)
end InitECandidate.Proofs.WordStages
