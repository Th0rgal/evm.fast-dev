import InitECandidate.Proofs.FrontendStages.Loop.Translate526
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody542_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody542_1 : HolLoopProg 64 :=
.mark loopBody542_0

def loopBody542_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody542_3 : HolLoopProg 64 :=
.mark loopBody542_2

def loopBody542_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody542_5 : HolLoopProg 64 :=
.mark loopBody542_4

def loopBody542_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 605) ([2]) (some (2, loopBody542_5, loopBody542_1, (Flapjack.Spt.ls PUnit.unit)))

def loopBody542_7 : HolLoopProg 64 :=
.mark loopBody542_6

def loopBody542_8 : HolLoopProg 64 :=
.seq loopBody542_7 loopBody542_1

def loopBody542_9 : HolLoopProg 64 :=
.mark loopBody542_8

def loopBody542_10 : HolLoopProg 64 :=
.seq loopBody542_3 loopBody542_9

def loopBody542_11 : HolLoopProg 64 :=
.mark loopBody542_10

def loopBody542_12 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_11

def loopBody542_13 : HolLoopProg 64 :=
.mark loopBody542_12

def loopBody542_14 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_13

def loopBody542_15 : HolLoopProg 64 :=
.mark loopBody542_14

def loopBody542_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 192#64])

def loopBody542_17 : HolLoopProg 64 :=
.mark loopBody542_16

def loopBody542_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 192#64]),
      Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 192#64])])

def loopBody542_19 : HolLoopProg 64 :=
.mark loopBody542_18

def loopBody542_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody542_21 : HolLoopProg 64 :=
.mark loopBody542_20

def loopBody542_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 1) 3

def loopBody542_23 : HolLoopProg 64 :=
.mark loopBody542_22

def loopBody542_24 : HolLoopProg 64 :=
.seq loopBody542_23 loopBody542_1

def loopBody542_25 : HolLoopProg 64 :=
.mark loopBody542_24

def loopBody542_26 : HolLoopProg 64 :=
.seq loopBody542_21 loopBody542_25

def loopBody542_27 : HolLoopProg 64 :=
.mark loopBody542_26

def loopBody542_28 : HolLoopProg 64 :=
.seq loopBody542_27 loopBody542_1

def loopBody542_29 : HolLoopProg 64 :=
.mark loopBody542_28

def loopBody542_30 : HolLoopProg 64 :=
.seq loopBody542_19 loopBody542_29

def loopBody542_31 : HolLoopProg 64 :=
.mark loopBody542_30

def loopBody542_32 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_31

def loopBody542_33 : HolLoopProg 64 :=
.mark loopBody542_32

def loopBody542_34 : HolLoopProg 64 :=
.seq loopBody542_17 loopBody542_33

def loopBody542_35 : HolLoopProg 64 :=
.mark loopBody542_34

def loopBody542_36 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_35

def loopBody542_37 : HolLoopProg 64 :=
.mark loopBody542_36

def loopBody542_38 : HolLoopProg 64 :=
.seq loopBody542_15 loopBody542_37

def loopBody542_39 : HolLoopProg 64 :=
.mark loopBody542_38

def loopBody542_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 72#64]))

def loopBody542_41 : HolLoopProg 64 :=
.mark loopBody542_40

def loopBody542_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 192#64]))

def loopBody542_43 : HolLoopProg 64 :=
.mark loopBody542_42

def loopBody542_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody542_45 : HolLoopProg 64 :=
.mark loopBody542_44

def loopBody542_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody542_47 : HolLoopProg 64 :=
.mark loopBody542_46

def loopBody542_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody542_49 : HolLoopProg 64 :=
.mark loopBody542_48

def loopBody542_50 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 3 (Flapjack.RegImm.reg 4) loopBody542_47 loopBody542_49 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody542_51 : HolLoopProg 64 :=
.mark loopBody542_50

def loopBody542_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody542_53 : HolLoopProg 64 :=
.mark loopBody542_52

def loopBody542_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 192#64]))

def loopBody542_55 : HolLoopProg 64 :=
.mark loopBody542_54

def loopBody542_56 : HolLoopProg 64 :=
.seq loopBody542_55 loopBody542_1

def loopBody542_57 : HolLoopProg 64 :=
.mark loopBody542_56

def loopBody542_58 : HolLoopProg 64 :=
.seq loopBody542_57 loopBody542_1

def loopBody542_59 : HolLoopProg 64 :=
.mark loopBody542_58

def loopBody542_60 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody542_59 loopBody542_1 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody542_61 : HolLoopProg 64 :=
.mark loopBody542_60

def loopBody542_62 : HolLoopProg 64 :=
.seq loopBody542_61 loopBody542_1

def loopBody542_63 : HolLoopProg 64 :=
.mark loopBody542_62

def loopBody542_64 : HolLoopProg 64 :=
.seq loopBody542_53 loopBody542_63

def loopBody542_65 : HolLoopProg 64 :=
.mark loopBody542_64

def loopBody542_66 : HolLoopProg 64 :=
.seq loopBody542_51 loopBody542_65

def loopBody542_67 : HolLoopProg 64 :=
.mark loopBody542_66

def loopBody542_68 : HolLoopProg 64 :=
.seq loopBody542_45 loopBody542_67

def loopBody542_69 : HolLoopProg 64 :=
.mark loopBody542_68

def loopBody542_70 : HolLoopProg 64 :=
.seq loopBody542_43 loopBody542_69

def loopBody542_71 : HolLoopProg 64 :=
.mark loopBody542_70

def loopBody542_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 64#64])

def loopBody542_73 : HolLoopProg 64 :=
.mark loopBody542_72

def loopBody542_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 64#64]),
      Flapjack.HolLoopExp.var 1])

def loopBody542_75 : HolLoopProg 64 :=
.mark loopBody542_74

def loopBody542_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody542_77 : HolLoopProg 64 :=
.mark loopBody542_76

def loopBody542_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 2) 4

def loopBody542_79 : HolLoopProg 64 :=
.mark loopBody542_78

def loopBody542_80 : HolLoopProg 64 :=
.seq loopBody542_79 loopBody542_1

def loopBody542_81 : HolLoopProg 64 :=
.mark loopBody542_80

def loopBody542_82 : HolLoopProg 64 :=
.seq loopBody542_77 loopBody542_81

def loopBody542_83 : HolLoopProg 64 :=
.mark loopBody542_82

def loopBody542_84 : HolLoopProg 64 :=
.seq loopBody542_83 loopBody542_1

def loopBody542_85 : HolLoopProg 64 :=
.mark loopBody542_84

def loopBody542_86 : HolLoopProg 64 :=
.seq loopBody542_75 loopBody542_85

def loopBody542_87 : HolLoopProg 64 :=
.mark loopBody542_86

def loopBody542_88 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_87

def loopBody542_89 : HolLoopProg 64 :=
.mark loopBody542_88

def loopBody542_90 : HolLoopProg 64 :=
.seq loopBody542_73 loopBody542_89

def loopBody542_91 : HolLoopProg 64 :=
.mark loopBody542_90

def loopBody542_92 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_91

def loopBody542_93 : HolLoopProg 64 :=
.mark loopBody542_92

def loopBody542_94 : HolLoopProg 64 :=
.seq loopBody542_71 loopBody542_93

def loopBody542_95 : HolLoopProg 64 :=
.mark loopBody542_94

def loopBody542_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 72#64])

def loopBody542_97 : HolLoopProg 64 :=
.mark loopBody542_96

def loopBody542_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 72#64]),
      Flapjack.HolLoopExp.var 1])

def loopBody542_99 : HolLoopProg 64 :=
.mark loopBody542_98

def loopBody542_100 : HolLoopProg 64 :=
.seq loopBody542_99 loopBody542_85

def loopBody542_101 : HolLoopProg 64 :=
.mark loopBody542_100

def loopBody542_102 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_101

def loopBody542_103 : HolLoopProg 64 :=
.mark loopBody542_102

def loopBody542_104 : HolLoopProg 64 :=
.seq loopBody542_97 loopBody542_103

def loopBody542_105 : HolLoopProg 64 :=
.mark loopBody542_104

def loopBody542_106 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_105

def loopBody542_107 : HolLoopProg 64 :=
.mark loopBody542_106

def loopBody542_108 : HolLoopProg 64 :=
.seq loopBody542_95 loopBody542_107

def loopBody542_109 : HolLoopProg 64 :=
.mark loopBody542_108

def loopBody542_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 192#64])

def loopBody542_111 : HolLoopProg 64 :=
.mark loopBody542_110

def loopBody542_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 192#64]),
      Flapjack.HolLoopExp.var 1])

def loopBody542_113 : HolLoopProg 64 :=
.mark loopBody542_112

def loopBody542_114 : HolLoopProg 64 :=
.seq loopBody542_113 loopBody542_85

def loopBody542_115 : HolLoopProg 64 :=
.mark loopBody542_114

def loopBody542_116 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_115

def loopBody542_117 : HolLoopProg 64 :=
.mark loopBody542_116

def loopBody542_118 : HolLoopProg 64 :=
.seq loopBody542_111 loopBody542_117

def loopBody542_119 : HolLoopProg 64 :=
.mark loopBody542_118

def loopBody542_120 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_119

def loopBody542_121 : HolLoopProg 64 :=
.mark loopBody542_120

def loopBody542_122 : HolLoopProg 64 :=
.seq loopBody542_109 loopBody542_121

def loopBody542_123 : HolLoopProg 64 :=
.mark loopBody542_122

def loopBody542_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 88#64]))

def loopBody542_125 : HolLoopProg 64 :=
.mark loopBody542_124

def loopBody542_126 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 8#64]))

def loopBody542_127 : HolLoopProg 64 :=
.mark loopBody542_126

def loopBody542_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 0#64]))

def loopBody542_129 : HolLoopProg 64 :=
.mark loopBody542_128

def loopBody542_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody542_131 : HolLoopProg 64 :=
.mark loopBody542_130

def loopBody542_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody542_133 : HolLoopProg 64 :=
.mark loopBody542_132

def loopBody542_134 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody542_135 : HolLoopProg 64 :=
.mark loopBody542_134

def loopBody542_136 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody542_137 : HolLoopProg 64 :=
.mark loopBody542_136

def loopBody542_138 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody542_139 : HolLoopProg 64 :=
.mark loopBody542_138

def loopBody542_140 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 7 (Flapjack.RegImm.reg 8) loopBody542_137 loopBody542_139 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody542_141 : HolLoopProg 64 :=
.mark loopBody542_140

def loopBody542_142 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody542_143 : HolLoopProg 64 :=
.mark loopBody542_142

def loopBody542_144 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]))

def loopBody542_145 : HolLoopProg 64 :=
.mark loopBody542_144

def loopBody542_146 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 4,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.const 3#64)]))

def loopBody542_147 : HolLoopProg 64 :=
.mark loopBody542_146

def loopBody542_148 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody542_149 : HolLoopProg 64 :=
.mark loopBody542_148

def loopBody542_150 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 541) ([7, 8]) (some (7, loopBody542_149, loopBody542_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody542_151 : HolLoopProg 64 :=
.mark loopBody542_150

def loopBody542_152 : HolLoopProg 64 :=
.seq loopBody542_151 loopBody542_1

def loopBody542_153 : HolLoopProg 64 :=
.mark loopBody542_152

def loopBody542_154 : HolLoopProg 64 :=
.seq loopBody542_147 loopBody542_153

def loopBody542_155 : HolLoopProg 64 :=
.mark loopBody542_154

def loopBody542_156 : HolLoopProg 64 :=
.seq loopBody542_145 loopBody542_155

def loopBody542_157 : HolLoopProg 64 :=
.mark loopBody542_156

def loopBody542_158 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_157

def loopBody542_159 : HolLoopProg 64 :=
.mark loopBody542_158

def loopBody542_160 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_159

def loopBody542_161 : HolLoopProg 64 :=
.mark loopBody542_160

def loopBody542_162 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 1#64])

def loopBody542_163 : HolLoopProg 64 :=
.mark loopBody542_162

def loopBody542_164 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 6)

def loopBody542_165 : HolLoopProg 64 :=
.mark loopBody542_164

def loopBody542_166 : HolLoopProg 64 :=
.seq loopBody542_165 loopBody542_1

def loopBody542_167 : HolLoopProg 64 :=
.mark loopBody542_166

def loopBody542_168 : HolLoopProg 64 :=
.seq loopBody542_167 loopBody542_1

def loopBody542_169 : HolLoopProg 64 :=
.mark loopBody542_168

def loopBody542_170 : HolLoopProg 64 :=
.seq loopBody542_163 loopBody542_169

def loopBody542_171 : HolLoopProg 64 :=
.mark loopBody542_170

def loopBody542_172 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_171

def loopBody542_173 : HolLoopProg 64 :=
.mark loopBody542_172

def loopBody542_174 : HolLoopProg 64 :=
.seq loopBody542_161 loopBody542_173

def loopBody542_175 : HolLoopProg 64 :=
.mark loopBody542_174

def loopBody542_176 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody542_177 : HolLoopProg 64 :=
.mark loopBody542_176

def loopBody542_178 : HolLoopProg 64 :=
.seq loopBody542_175 loopBody542_177

def loopBody542_179 : HolLoopProg 64 :=
.mark loopBody542_178

def loopBody542_180 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody542_181 : HolLoopProg 64 :=
.mark loopBody542_180

def loopBody542_182 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody542_179 loopBody542_181 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody542_183 : HolLoopProg 64 :=
.mark loopBody542_182

def loopBody542_184 : HolLoopProg 64 :=
.seq loopBody542_183 loopBody542_1

def loopBody542_185 : HolLoopProg 64 :=
.mark loopBody542_184

def loopBody542_186 : HolLoopProg 64 :=
.seq loopBody542_143 loopBody542_185

def loopBody542_187 : HolLoopProg 64 :=
.mark loopBody542_186

def loopBody542_188 : HolLoopProg 64 :=
.seq loopBody542_141 loopBody542_187

def loopBody542_189 : HolLoopProg 64 :=
.mark loopBody542_188

def loopBody542_190 : HolLoopProg 64 :=
.seq loopBody542_135 loopBody542_189

def loopBody542_191 : HolLoopProg 64 :=
.mark loopBody542_190

def loopBody542_192 : HolLoopProg 64 :=
.seq loopBody542_133 loopBody542_191

def loopBody542_193 : HolLoopProg 64 :=
.mark loopBody542_192

def loopBody542_194 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody542_193 (Flapjack.Spt.ls PUnit.unit)

def loopBody542_195 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 96#64])

def loopBody542_196 : HolLoopProg 64 :=
.mark loopBody542_195

def loopBody542_197 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 96#64]),
      Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 96#64])])

def loopBody542_198 : HolLoopProg 64 :=
.mark loopBody542_197

def loopBody542_199 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 7)

def loopBody542_200 : HolLoopProg 64 :=
.mark loopBody542_199

def loopBody542_201 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 6) 8

def loopBody542_202 : HolLoopProg 64 :=
.mark loopBody542_201

def loopBody542_203 : HolLoopProg 64 :=
.seq loopBody542_202 loopBody542_1

def loopBody542_204 : HolLoopProg 64 :=
.mark loopBody542_203

def loopBody542_205 : HolLoopProg 64 :=
.seq loopBody542_200 loopBody542_204

def loopBody542_206 : HolLoopProg 64 :=
.mark loopBody542_205

def loopBody542_207 : HolLoopProg 64 :=
.seq loopBody542_206 loopBody542_1

def loopBody542_208 : HolLoopProg 64 :=
.mark loopBody542_207

def loopBody542_209 : HolLoopProg 64 :=
.seq loopBody542_198 loopBody542_208

def loopBody542_210 : HolLoopProg 64 :=
.mark loopBody542_209

def loopBody542_211 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_210

def loopBody542_212 : HolLoopProg 64 :=
.mark loopBody542_211

def loopBody542_213 : HolLoopProg 64 :=
.seq loopBody542_196 loopBody542_212

def loopBody542_214 : HolLoopProg 64 :=
.mark loopBody542_213

def loopBody542_215 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_214

def loopBody542_216 : HolLoopProg 64 :=
.mark loopBody542_215

def loopBody542_217 : HolLoopProg 64 :=
.seq loopBody542_194 loopBody542_216

def loopBody542_218 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 136#64]))

def loopBody542_219 : HolLoopProg 64 :=
.mark loopBody542_218

def loopBody542_220 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 136#64]))

def loopBody542_221 : HolLoopProg 64 :=
.mark loopBody542_220

def loopBody542_222 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 428) ([7, 8]) (some (7, loopBody542_149, loopBody542_1, (Flapjack.Spt.ln)))

def loopBody542_223 : HolLoopProg 64 :=
.mark loopBody542_222

def loopBody542_224 : HolLoopProg 64 :=
.seq loopBody542_223 loopBody542_1

def loopBody542_225 : HolLoopProg 64 :=
.mark loopBody542_224

def loopBody542_226 : HolLoopProg 64 :=
.seq loopBody542_221 loopBody542_225

def loopBody542_227 : HolLoopProg 64 :=
.mark loopBody542_226

def loopBody542_228 : HolLoopProg 64 :=
.seq loopBody542_219 loopBody542_227

def loopBody542_229 : HolLoopProg 64 :=
.mark loopBody542_228

def loopBody542_230 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_229

def loopBody542_231 : HolLoopProg 64 :=
.mark loopBody542_230

def loopBody542_232 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_231

def loopBody542_233 : HolLoopProg 64 :=
.mark loopBody542_232

def loopBody542_234 : HolLoopProg 64 :=
.seq loopBody542_217 loopBody542_233

def loopBody542_235 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody542_236 : HolLoopProg 64 :=
.mark loopBody542_235

def loopBody542_237 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody542_238 : HolLoopProg 64 :=
.mark loopBody542_237

def loopBody542_239 : HolLoopProg 64 :=
.seq loopBody542_238 loopBody542_1

def loopBody542_240 : HolLoopProg 64 :=
.mark loopBody542_239

def loopBody542_241 : HolLoopProg 64 :=
.seq loopBody542_236 loopBody542_240

def loopBody542_242 : HolLoopProg 64 :=
.mark loopBody542_241

def loopBody542_243 : HolLoopProg 64 :=
.seq loopBody542_234 loopBody542_242

def loopBody542_244 : HolLoopProg 64 :=
.seq loopBody542_131 loopBody542_243

def loopBody542_245 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_244

def loopBody542_246 : HolLoopProg 64 :=
.seq loopBody542_129 loopBody542_245

def loopBody542_247 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_246

def loopBody542_248 : HolLoopProg 64 :=
.seq loopBody542_127 loopBody542_247

def loopBody542_249 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_248

def loopBody542_250 : HolLoopProg 64 :=
.seq loopBody542_125 loopBody542_249

def loopBody542_251 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_250

def loopBody542_252 : HolLoopProg 64 :=
.seq loopBody542_123 loopBody542_251

def loopBody542_253 : HolLoopProg 64 :=
.seq loopBody542_41 loopBody542_252

def loopBody542_254 : HolLoopProg 64 :=
.seq loopBody542_1 loopBody542_253

def loopBody542_255 : HolLoopProg 64 :=
.seq loopBody542_39 loopBody542_254

def output542 : Nat × List Nat × HolLoopProg 64 :=
  (606, [0], loopBody542_255)
end InitECandidate.Proofs.FrontendStages.Loop
