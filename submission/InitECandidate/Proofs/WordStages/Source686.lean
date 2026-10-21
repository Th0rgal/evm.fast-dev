import InitECandidate.Proofs.WordStages.Source670
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody686_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody686_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody686_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody686_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 16)

def sourceBody686_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 40)

def sourceBody686_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody686_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody686_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 52 (Flapjack.WordRegImm.reg 24) sourceBody686_5 sourceBody686_6

def sourceBody686_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_7 sourceBody686_2

def sourceBody686_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 52)

def sourceBody686_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody686_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody686_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody686_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody686_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 6)

def sourceBody686_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 8)

def sourceBody686_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody686_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 12)

def sourceBody686_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 30)

def sourceBody686_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 52)

def sourceBody686_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody686_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 46)

def sourceBody686_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody686_23 : WordLangProgHOL (BitVec 64) :=
.call (some (([36, 58, 18, 38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody686_0, 686, 2)) (some 657) ([28, 50, 22, 44, 34, 56, 20, 42]) (some (28, sourceBody686_22, 686, 3))

def sourceBody686_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_23 sourceBody686_2

def sourceBody686_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_24 sourceBody686_0

def sourceBody686_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_21 sourceBody686_25

def sourceBody686_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_20 sourceBody686_26

def sourceBody686_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_19 sourceBody686_27

def sourceBody686_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_18 sourceBody686_28

def sourceBody686_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_17 sourceBody686_29

def sourceBody686_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_16 sourceBody686_30

def sourceBody686_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_15 sourceBody686_31

def sourceBody686_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_14 sourceBody686_32

def sourceBody686_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.var 40])
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody686_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.var 40])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody686_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.var 40])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody686_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.var 40])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody686_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 28)

def sourceBody686_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 50)

def sourceBody686_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 22)

def sourceBody686_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 44)

def sourceBody686_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 36)

def sourceBody686_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 58)

def sourceBody686_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 18)

def sourceBody686_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 38)

def sourceBody686_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody686_47 : WordLangProgHOL (BitVec 64) :=
.call (some (([28, 50, 22, 44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody686_0, 686, 4)) (some 655) ([34, 56, 20, 42, 32, 54, 26, 48]) (some (34, sourceBody686_46, 686, 5))

def sourceBody686_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_47 sourceBody686_2

def sourceBody686_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_48 sourceBody686_0

def sourceBody686_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_45 sourceBody686_49

def sourceBody686_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_44 sourceBody686_50

def sourceBody686_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_43 sourceBody686_51

def sourceBody686_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_42 sourceBody686_52

def sourceBody686_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_41 sourceBody686_53

def sourceBody686_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_40 sourceBody686_54

def sourceBody686_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_39 sourceBody686_55

def sourceBody686_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_38 sourceBody686_56

def sourceBody686_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.var 40])
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody686_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 28)

def sourceBody686_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 50)

def sourceBody686_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 22)

def sourceBody686_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 44)

def sourceBody686_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 56)

def sourceBody686_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 34) 54

def sourceBody686_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_64 sourceBody686_0

def sourceBody686_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_63 sourceBody686_65

def sourceBody686_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 20)

def sourceBody686_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 8#64])
  54

def sourceBody686_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_68 sourceBody686_0

def sourceBody686_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_67 sourceBody686_69

def sourceBody686_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 42)

def sourceBody686_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 16#64])
  54

def sourceBody686_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_72 sourceBody686_0

def sourceBody686_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_71 sourceBody686_73

def sourceBody686_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 32)

def sourceBody686_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 24#64])
  54

def sourceBody686_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_76 sourceBody686_0

def sourceBody686_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_75 sourceBody686_77

def sourceBody686_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_78 sourceBody686_0

def sourceBody686_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_74 sourceBody686_79

def sourceBody686_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_70 sourceBody686_80

def sourceBody686_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_66 sourceBody686_81

def sourceBody686_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_62 sourceBody686_82

def sourceBody686_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_83

def sourceBody686_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_61 sourceBody686_84

def sourceBody686_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_85

def sourceBody686_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_60 sourceBody686_86

def sourceBody686_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_87

def sourceBody686_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_59 sourceBody686_88

def sourceBody686_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_89

def sourceBody686_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_58 sourceBody686_90

def sourceBody686_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_91

def sourceBody686_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_57 sourceBody686_92

def sourceBody686_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody686_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 34)

def sourceBody686_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_95 sourceBody686_0

def sourceBody686_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_96 sourceBody686_0

def sourceBody686_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_94 sourceBody686_97

def sourceBody686_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_98

def sourceBody686_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_93 sourceBody686_99

def sourceBody686_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_37 sourceBody686_100

def sourceBody686_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_101

def sourceBody686_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_36 sourceBody686_102

def sourceBody686_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_103

def sourceBody686_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_35 sourceBody686_104

def sourceBody686_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_105

def sourceBody686_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_34 sourceBody686_106

def sourceBody686_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_107

def sourceBody686_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_33 sourceBody686_108

def sourceBody686_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_109

def sourceBody686_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_110

def sourceBody686_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_111

def sourceBody686_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_112

def sourceBody686_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_113

def sourceBody686_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_114

def sourceBody686_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_115

def sourceBody686_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_116

def sourceBody686_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_13 sourceBody686_117

def sourceBody686_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_118

def sourceBody686_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_12 sourceBody686_119

def sourceBody686_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_120

def sourceBody686_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_11 sourceBody686_121

def sourceBody686_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_122

def sourceBody686_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_10 sourceBody686_123

def sourceBody686_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_124

def sourceBody686_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody686_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_125 sourceBody686_126

def sourceBody686_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody686_129 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 46 (Flapjack.WordRegImm.imm 0#64) sourceBody686_127 sourceBody686_128

def sourceBody686_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_129 sourceBody686_2

def sourceBody686_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_130 sourceBody686_0

def sourceBody686_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_9 sourceBody686_131

def sourceBody686_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_8 sourceBody686_132

def sourceBody686_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_4 sourceBody686_133

def sourceBody686_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_3 sourceBody686_134

def sourceBody686_136 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody686_135 (Flapjack.Spt.ls PUnit.unit)

def sourceBody686_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_136 sourceBody686_2

def sourceBody686_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_2 sourceBody686_137

def sourceBody686_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody686_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30]

def sourceBody686_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_140 sourceBody686_0

def sourceBody686_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_139 sourceBody686_141

def sourceBody686_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_138 sourceBody686_142

def sourceBody686_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_1 sourceBody686_143

def sourceBody686_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody686_0 sourceBody686_144

def source686 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (686, 9, sourceBody686_145)
end InitECandidate.Proofs.WordStages
