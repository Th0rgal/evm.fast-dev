import InitECandidate.Proofs.WordStages.Source592
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody608_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody608_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody608_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody608_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody608_0, 608, 2)) (some 484) ([]) (some (38, sourceBody608_2, 608, 3))

def sourceBody608_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody608_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_3 sourceBody608_4

def sourceBody608_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_5 sourceBody608_0

def sourceBody608_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody608_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody608_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 46)

def sourceBody608_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 38) 42

def sourceBody608_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_10 sourceBody608_0

def sourceBody608_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_9 sourceBody608_11

def sourceBody608_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_12 sourceBody608_0

def sourceBody608_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_8 sourceBody608_13

def sourceBody608_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_14

def sourceBody608_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_7 sourceBody608_15

def sourceBody608_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_16

def sourceBody608_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody608_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody608_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_19 sourceBody608_13

def sourceBody608_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_20

def sourceBody608_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_18 sourceBody608_21

def sourceBody608_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_22

def sourceBody608_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_17 sourceBody608_23

def sourceBody608_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody608_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 2)

def sourceBody608_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_26 sourceBody608_13

def sourceBody608_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_27

def sourceBody608_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_25 sourceBody608_28

def sourceBody608_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_29

def sourceBody608_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_24 sourceBody608_30

def sourceBody608_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody608_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 4)

def sourceBody608_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_33 sourceBody608_13

def sourceBody608_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_34

def sourceBody608_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_32 sourceBody608_35

def sourceBody608_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_36

def sourceBody608_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_31 sourceBody608_37

def sourceBody608_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody608_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 6)

def sourceBody608_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_40 sourceBody608_13

def sourceBody608_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_41

def sourceBody608_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_39 sourceBody608_42

def sourceBody608_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_43

def sourceBody608_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_38 sourceBody608_44

def sourceBody608_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody608_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 8)

def sourceBody608_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_47 sourceBody608_13

def sourceBody608_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_48

def sourceBody608_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_46 sourceBody608_49

def sourceBody608_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_50

def sourceBody608_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_45 sourceBody608_51

def sourceBody608_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody608_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 10)

def sourceBody608_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_54 sourceBody608_13

def sourceBody608_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_55

def sourceBody608_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_53 sourceBody608_56

def sourceBody608_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_57

def sourceBody608_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_52 sourceBody608_58

def sourceBody608_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 56#64])

def sourceBody608_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 12)

def sourceBody608_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 14)

def sourceBody608_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 16)

def sourceBody608_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 18)

def sourceBody608_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 46)

def sourceBody608_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 38) 44

def sourceBody608_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_66 sourceBody608_0

def sourceBody608_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_65 sourceBody608_67

def sourceBody608_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 42)

def sourceBody608_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 8#64])
  44

def sourceBody608_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_70 sourceBody608_0

def sourceBody608_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_69 sourceBody608_71

def sourceBody608_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 50)

def sourceBody608_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 16#64])
  44

def sourceBody608_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_74 sourceBody608_0

def sourceBody608_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_73 sourceBody608_75

def sourceBody608_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 36)

def sourceBody608_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 24#64])
  44

def sourceBody608_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_78 sourceBody608_0

def sourceBody608_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_77 sourceBody608_79

def sourceBody608_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_80 sourceBody608_0

def sourceBody608_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_76 sourceBody608_81

def sourceBody608_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_72 sourceBody608_82

def sourceBody608_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_68 sourceBody608_83

def sourceBody608_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_64 sourceBody608_84

def sourceBody608_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_85

def sourceBody608_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_63 sourceBody608_86

def sourceBody608_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_87

def sourceBody608_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_62 sourceBody608_88

def sourceBody608_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_89

def sourceBody608_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_61 sourceBody608_90

def sourceBody608_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_91

def sourceBody608_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_60 sourceBody608_92

def sourceBody608_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_93

def sourceBody608_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_59 sourceBody608_94

def sourceBody608_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 88#64])

def sourceBody608_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 20)

def sourceBody608_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_97 sourceBody608_13

def sourceBody608_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_98

def sourceBody608_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_96 sourceBody608_99

def sourceBody608_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_100

def sourceBody608_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_95 sourceBody608_101

def sourceBody608_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody608_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 22)

def sourceBody608_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_104 sourceBody608_13

def sourceBody608_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_105

def sourceBody608_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_103 sourceBody608_106

def sourceBody608_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_107

def sourceBody608_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_102 sourceBody608_108

def sourceBody608_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 104#64])

def sourceBody608_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 24)

def sourceBody608_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_111 sourceBody608_13

def sourceBody608_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_112

def sourceBody608_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_110 sourceBody608_113

def sourceBody608_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_114

def sourceBody608_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_109 sourceBody608_115

def sourceBody608_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 112#64])

def sourceBody608_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 26)

def sourceBody608_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_118 sourceBody608_13

def sourceBody608_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_119

def sourceBody608_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_117 sourceBody608_120

def sourceBody608_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_121

def sourceBody608_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_116 sourceBody608_122

def sourceBody608_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 120#64])

def sourceBody608_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 28)

def sourceBody608_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_125 sourceBody608_13

def sourceBody608_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_126

def sourceBody608_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_124 sourceBody608_127

def sourceBody608_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_128

def sourceBody608_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_123 sourceBody608_129

def sourceBody608_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 128#64])

def sourceBody608_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 128#64]),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody608_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_132 sourceBody608_13

def sourceBody608_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_133

def sourceBody608_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_131 sourceBody608_134

def sourceBody608_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_135

def sourceBody608_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_130 sourceBody608_136

def sourceBody608_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 136#64])

def sourceBody608_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 30)

def sourceBody608_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_139 sourceBody608_13

def sourceBody608_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_140

def sourceBody608_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_138 sourceBody608_141

def sourceBody608_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_142

def sourceBody608_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_137 sourceBody608_143

def sourceBody608_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 32)

def sourceBody608_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 144#64]))

def sourceBody608_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody608_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody608_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody608_150 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.reg 50) sourceBody608_148 sourceBody608_149

def sourceBody608_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_150 sourceBody608_4

def sourceBody608_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 42)

def sourceBody608_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody608_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_153 sourceBody608_0

def sourceBody608_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_154 sourceBody608_0

def sourceBody608_156 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody608_155 sourceBody608_0

def sourceBody608_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_156 sourceBody608_4

def sourceBody608_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_157 sourceBody608_0

def sourceBody608_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_152 sourceBody608_158

def sourceBody608_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_151 sourceBody608_159

def sourceBody608_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_147 sourceBody608_160

def sourceBody608_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_146 sourceBody608_161

def sourceBody608_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 144#64])

def sourceBody608_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 38)

def sourceBody608_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 42)

def sourceBody608_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 46) 50

def sourceBody608_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_166 sourceBody608_0

def sourceBody608_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_165 sourceBody608_167

def sourceBody608_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_168 sourceBody608_0

def sourceBody608_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_164 sourceBody608_169

def sourceBody608_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_170

def sourceBody608_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_163 sourceBody608_171

def sourceBody608_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_172

def sourceBody608_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_162 sourceBody608_173

def sourceBody608_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 152#64])

def sourceBody608_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 168#64]))

def sourceBody608_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_176 sourceBody608_169

def sourceBody608_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_177

def sourceBody608_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_175 sourceBody608_178

def sourceBody608_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_179

def sourceBody608_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_174 sourceBody608_180

def sourceBody608_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 160#64])

def sourceBody608_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 176#64]))

def sourceBody608_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_183 sourceBody608_169

def sourceBody608_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_184

def sourceBody608_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_182 sourceBody608_185

def sourceBody608_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_186

def sourceBody608_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_181 sourceBody608_187

def sourceBody608_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 168#64])

def sourceBody608_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 34)

def sourceBody608_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_190 sourceBody608_169

def sourceBody608_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_191

def sourceBody608_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_189 sourceBody608_192

def sourceBody608_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_193

def sourceBody608_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_188 sourceBody608_194

def sourceBody608_196 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 48)

def sourceBody608_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [46]

def sourceBody608_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_197 sourceBody608_0

def sourceBody608_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_196 sourceBody608_198

def sourceBody608_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_195 sourceBody608_199

def sourceBody608_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_145 sourceBody608_200

def sourceBody608_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_201

def sourceBody608_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_144 sourceBody608_202

def sourceBody608_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_6 sourceBody608_203

def sourceBody608_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_204

def sourceBody608_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_205

def sourceBody608_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_1 sourceBody608_206

def sourceBody608_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody608_0 sourceBody608_207

def source608 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (608, 18, sourceBody608_208)
end InitECandidate.Proofs.WordStages
