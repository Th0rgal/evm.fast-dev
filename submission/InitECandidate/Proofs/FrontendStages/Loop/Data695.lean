import InitECandidate.Proofs.FrontendStages.Loop.Translate679
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody695_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody695_1 : HolLoopProg 64 :=
.mark loopBody695_0

def loopBody695_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody695_3 : HolLoopProg 64 :=
.mark loopBody695_2

def loopBody695_4 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (3, loopBody695_3, loopBody695_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody695_5 : HolLoopProg 64 :=
.mark loopBody695_4

def loopBody695_6 : HolLoopProg 64 :=
.seq loopBody695_5 loopBody695_1

def loopBody695_7 : HolLoopProg 64 :=
.mark loopBody695_6

def loopBody695_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 576#64)

def loopBody695_9 : HolLoopProg 64 :=
.mark loopBody695_8

def loopBody695_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody695_11 : HolLoopProg 64 :=
.mark loopBody695_10

def loopBody695_12 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody695_11, loopBody695_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody695_13 : HolLoopProg 64 :=
.mark loopBody695_12

def loopBody695_14 : HolLoopProg 64 :=
.seq loopBody695_13 loopBody695_1

def loopBody695_15 : HolLoopProg 64 :=
.mark loopBody695_14

def loopBody695_16 : HolLoopProg 64 :=
.seq loopBody695_9 loopBody695_15

def loopBody695_17 : HolLoopProg 64 :=
.mark loopBody695_16

def loopBody695_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 576#64)

def loopBody695_19 : HolLoopProg 64 :=
.mark loopBody695_18

def loopBody695_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody695_21 : HolLoopProg 64 :=
.mark loopBody695_20

def loopBody695_22 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([5]) (some (5, loopBody695_21, loopBody695_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody695_23 : HolLoopProg 64 :=
.mark loopBody695_22

def loopBody695_24 : HolLoopProg 64 :=
.seq loopBody695_23 loopBody695_1

def loopBody695_25 : HolLoopProg 64 :=
.mark loopBody695_24

def loopBody695_26 : HolLoopProg 64 :=
.seq loopBody695_19 loopBody695_25

def loopBody695_27 : HolLoopProg 64 :=
.mark loopBody695_26

def loopBody695_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody695_29 : HolLoopProg 64 :=
.mark loopBody695_28

def loopBody695_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody695_31 : HolLoopProg 64 :=
.mark loopBody695_30

def loopBody695_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody695_33 : HolLoopProg 64 :=
.mark loopBody695_32

def loopBody695_34 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 751) ([6, 7]) (some (6, loopBody695_33, loopBody695_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody695_35 : HolLoopProg 64 :=
.mark loopBody695_34

def loopBody695_36 : HolLoopProg 64 :=
.seq loopBody695_35 loopBody695_1

def loopBody695_37 : HolLoopProg 64 :=
.mark loopBody695_36

def loopBody695_38 : HolLoopProg 64 :=
.seq loopBody695_31 loopBody695_37

def loopBody695_39 : HolLoopProg 64 :=
.mark loopBody695_38

def loopBody695_40 : HolLoopProg 64 :=
.seq loopBody695_29 loopBody695_39

def loopBody695_41 : HolLoopProg 64 :=
.mark loopBody695_40

def loopBody695_42 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_41

def loopBody695_43 : HolLoopProg 64 :=
.mark loopBody695_42

def loopBody695_44 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_43

def loopBody695_45 : HolLoopProg 64 :=
.mark loopBody695_44

def loopBody695_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody695_47 : HolLoopProg 64 :=
.mark loopBody695_46

def loopBody695_48 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 752) ([6]) (some (6, loopBody695_33, loopBody695_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody695_49 : HolLoopProg 64 :=
.mark loopBody695_48

def loopBody695_50 : HolLoopProg 64 :=
.seq loopBody695_49 loopBody695_1

def loopBody695_51 : HolLoopProg 64 :=
.mark loopBody695_50

def loopBody695_52 : HolLoopProg 64 :=
.seq loopBody695_47 loopBody695_51

def loopBody695_53 : HolLoopProg 64 :=
.mark loopBody695_52

def loopBody695_54 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_53

def loopBody695_55 : HolLoopProg 64 :=
.mark loopBody695_54

def loopBody695_56 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_55

def loopBody695_57 : HolLoopProg 64 :=
.mark loopBody695_56

def loopBody695_58 : HolLoopProg 64 :=
.seq loopBody695_45 loopBody695_57

def loopBody695_59 : HolLoopProg 64 :=
.mark loopBody695_58

def loopBody695_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 392#64]),
        Flapjack.HolLoopExp.const 1376#64]))

def loopBody695_61 : HolLoopProg 64 :=
.mark loopBody695_60

def loopBody695_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody695_63 : HolLoopProg 64 :=
.mark loopBody695_62

def loopBody695_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 64#64)

def loopBody695_65 : HolLoopProg 64 :=
.mark loopBody695_64

def loopBody695_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody695_67 : HolLoopProg 64 :=
.mark loopBody695_66

def loopBody695_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 7)

def loopBody695_69 : HolLoopProg 64 :=
.mark loopBody695_68

def loopBody695_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 1#64)

def loopBody695_71 : HolLoopProg 64 :=
.mark loopBody695_70

def loopBody695_72 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 9 (Flapjack.RegImm.reg 10) loopBody695_71 loopBody695_67 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody695_73 : HolLoopProg 64 :=
.mark loopBody695_72

def loopBody695_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody695_75 : HolLoopProg 64 :=
.mark loopBody695_74

def loopBody695_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 1#64])

def loopBody695_77 : HolLoopProg 64 :=
.mark loopBody695_76

def loopBody695_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 8)

def loopBody695_79 : HolLoopProg 64 :=
.mark loopBody695_78

def loopBody695_80 : HolLoopProg 64 :=
.seq loopBody695_79 loopBody695_1

def loopBody695_81 : HolLoopProg 64 :=
.mark loopBody695_80

def loopBody695_82 : HolLoopProg 64 :=
.seq loopBody695_81 loopBody695_1

def loopBody695_83 : HolLoopProg 64 :=
.mark loopBody695_82

def loopBody695_84 : HolLoopProg 64 :=
.seq loopBody695_77 loopBody695_83

def loopBody695_85 : HolLoopProg 64 :=
.mark loopBody695_84

def loopBody695_86 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_85

def loopBody695_87 : HolLoopProg 64 :=
.mark loopBody695_86

def loopBody695_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 6)

def loopBody695_89 : HolLoopProg 64 :=
.mark loopBody695_88

def loopBody695_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 1#64)

def loopBody695_91 : HolLoopProg 64 :=
.mark loopBody695_90

def loopBody695_92 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 9 (Flapjack.RegImm.reg 10) loopBody695_71 loopBody695_67 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody695_93 : HolLoopProg 64 :=
.mark loopBody695_92

def loopBody695_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody695_95 : HolLoopProg 64 :=
.mark loopBody695_94

def loopBody695_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 4)

def loopBody695_97 : HolLoopProg 64 :=
.mark loopBody695_96

def loopBody695_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 4)

def loopBody695_99 : HolLoopProg 64 :=
.mark loopBody695_98

def loopBody695_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody695_101 : HolLoopProg 64 :=
.mark loopBody695_100

def loopBody695_102 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 754) ([9, 10, 11]) (some (9, loopBody695_101, loopBody695_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody695_103 : HolLoopProg 64 :=
.mark loopBody695_102

def loopBody695_104 : HolLoopProg 64 :=
.seq loopBody695_103 loopBody695_1

def loopBody695_105 : HolLoopProg 64 :=
.mark loopBody695_104

def loopBody695_106 : HolLoopProg 64 :=
.seq loopBody695_99 loopBody695_105

def loopBody695_107 : HolLoopProg 64 :=
.mark loopBody695_106

def loopBody695_108 : HolLoopProg 64 :=
.seq loopBody695_97 loopBody695_107

def loopBody695_109 : HolLoopProg 64 :=
.mark loopBody695_108

def loopBody695_110 : HolLoopProg 64 :=
.seq loopBody695_95 loopBody695_109

def loopBody695_111 : HolLoopProg 64 :=
.mark loopBody695_110

def loopBody695_112 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_111

def loopBody695_113 : HolLoopProg 64 :=
.mark loopBody695_112

def loopBody695_114 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_113

def loopBody695_115 : HolLoopProg 64 :=
.mark loopBody695_114

def loopBody695_116 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody695_115 loopBody695_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody695_117 : HolLoopProg 64 :=
.mark loopBody695_116

def loopBody695_118 : HolLoopProg 64 :=
.seq loopBody695_117 loopBody695_1

def loopBody695_119 : HolLoopProg 64 :=
.mark loopBody695_118

def loopBody695_120 : HolLoopProg 64 :=
.seq loopBody695_75 loopBody695_119

def loopBody695_121 : HolLoopProg 64 :=
.mark loopBody695_120

def loopBody695_122 : HolLoopProg 64 :=
.seq loopBody695_93 loopBody695_121

def loopBody695_123 : HolLoopProg 64 :=
.mark loopBody695_122

def loopBody695_124 : HolLoopProg 64 :=
.seq loopBody695_91 loopBody695_123

def loopBody695_125 : HolLoopProg 64 :=
.mark loopBody695_124

def loopBody695_126 : HolLoopProg 64 :=
.seq loopBody695_89 loopBody695_125

def loopBody695_127 : HolLoopProg 64 :=
.mark loopBody695_126

def loopBody695_128 : HolLoopProg 64 :=
.seq loopBody695_87 loopBody695_127

def loopBody695_129 : HolLoopProg 64 :=
.mark loopBody695_128

def loopBody695_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.var 7),
      Flapjack.HolLoopExp.const 1#64])

def loopBody695_131 : HolLoopProg 64 :=
.mark loopBody695_130

def loopBody695_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 3)

def loopBody695_133 : HolLoopProg 64 :=
.mark loopBody695_132

def loopBody695_134 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 754) ([9, 10, 11]) (some (9, loopBody695_101, loopBody695_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody695_135 : HolLoopProg 64 :=
.mark loopBody695_134

def loopBody695_136 : HolLoopProg 64 :=
.seq loopBody695_135 loopBody695_1

def loopBody695_137 : HolLoopProg 64 :=
.mark loopBody695_136

def loopBody695_138 : HolLoopProg 64 :=
.seq loopBody695_133 loopBody695_137

def loopBody695_139 : HolLoopProg 64 :=
.mark loopBody695_138

def loopBody695_140 : HolLoopProg 64 :=
.seq loopBody695_97 loopBody695_139

def loopBody695_141 : HolLoopProg 64 :=
.mark loopBody695_140

def loopBody695_142 : HolLoopProg 64 :=
.seq loopBody695_95 loopBody695_141

def loopBody695_143 : HolLoopProg 64 :=
.mark loopBody695_142

def loopBody695_144 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_143

def loopBody695_145 : HolLoopProg 64 :=
.mark loopBody695_144

def loopBody695_146 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_145

def loopBody695_147 : HolLoopProg 64 :=
.mark loopBody695_146

def loopBody695_148 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody695_149 : HolLoopProg 64 :=
.mark loopBody695_148

def loopBody695_150 : HolLoopProg 64 :=
.seq loopBody695_149 loopBody695_1

def loopBody695_151 : HolLoopProg 64 :=
.mark loopBody695_150

def loopBody695_152 : HolLoopProg 64 :=
.seq loopBody695_151 loopBody695_1

def loopBody695_153 : HolLoopProg 64 :=
.mark loopBody695_152

def loopBody695_154 : HolLoopProg 64 :=
.seq loopBody695_147 loopBody695_153

def loopBody695_155 : HolLoopProg 64 :=
.mark loopBody695_154

def loopBody695_156 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody695_155 loopBody695_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody695_157 : HolLoopProg 64 :=
.mark loopBody695_156

def loopBody695_158 : HolLoopProg 64 :=
.seq loopBody695_157 loopBody695_1

def loopBody695_159 : HolLoopProg 64 :=
.mark loopBody695_158

def loopBody695_160 : HolLoopProg 64 :=
.seq loopBody695_75 loopBody695_159

def loopBody695_161 : HolLoopProg 64 :=
.mark loopBody695_160

def loopBody695_162 : HolLoopProg 64 :=
.seq loopBody695_93 loopBody695_161

def loopBody695_163 : HolLoopProg 64 :=
.mark loopBody695_162

def loopBody695_164 : HolLoopProg 64 :=
.seq loopBody695_91 loopBody695_163

def loopBody695_165 : HolLoopProg 64 :=
.mark loopBody695_164

def loopBody695_166 : HolLoopProg 64 :=
.seq loopBody695_131 loopBody695_165

def loopBody695_167 : HolLoopProg 64 :=
.mark loopBody695_166

def loopBody695_168 : HolLoopProg 64 :=
.seq loopBody695_129 loopBody695_167

def loopBody695_169 : HolLoopProg 64 :=
.mark loopBody695_168

def loopBody695_170 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody695_171 : HolLoopProg 64 :=
.mark loopBody695_170

def loopBody695_172 : HolLoopProg 64 :=
.seq loopBody695_169 loopBody695_171

def loopBody695_173 : HolLoopProg 64 :=
.mark loopBody695_172

def loopBody695_174 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody695_175 : HolLoopProg 64 :=
.mark loopBody695_174

def loopBody695_176 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody695_173 loopBody695_175 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody695_177 : HolLoopProg 64 :=
.mark loopBody695_176

def loopBody695_178 : HolLoopProg 64 :=
.seq loopBody695_177 loopBody695_1

def loopBody695_179 : HolLoopProg 64 :=
.mark loopBody695_178

def loopBody695_180 : HolLoopProg 64 :=
.seq loopBody695_75 loopBody695_179

def loopBody695_181 : HolLoopProg 64 :=
.mark loopBody695_180

def loopBody695_182 : HolLoopProg 64 :=
.seq loopBody695_73 loopBody695_181

def loopBody695_183 : HolLoopProg 64 :=
.mark loopBody695_182

def loopBody695_184 : HolLoopProg 64 :=
.seq loopBody695_69 loopBody695_183

def loopBody695_185 : HolLoopProg 64 :=
.mark loopBody695_184

def loopBody695_186 : HolLoopProg 64 :=
.seq loopBody695_67 loopBody695_185

def loopBody695_187 : HolLoopProg 64 :=
.mark loopBody695_186

def loopBody695_188 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) loopBody695_187 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)

def loopBody695_189 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 0)

def loopBody695_190 : HolLoopProg 64 :=
.mark loopBody695_189

def loopBody695_191 : HolLoopProg 64 :=
.call (some ([8], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 751) ([9, 10]) (some (9, loopBody695_101, loopBody695_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody695_192 : HolLoopProg 64 :=
.mark loopBody695_191

def loopBody695_193 : HolLoopProg 64 :=
.seq loopBody695_192 loopBody695_1

def loopBody695_194 : HolLoopProg 64 :=
.mark loopBody695_193

def loopBody695_195 : HolLoopProg 64 :=
.seq loopBody695_97 loopBody695_194

def loopBody695_196 : HolLoopProg 64 :=
.mark loopBody695_195

def loopBody695_197 : HolLoopProg 64 :=
.seq loopBody695_190 loopBody695_196

def loopBody695_198 : HolLoopProg 64 :=
.mark loopBody695_197

def loopBody695_199 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_198

def loopBody695_200 : HolLoopProg 64 :=
.mark loopBody695_199

def loopBody695_201 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_200

def loopBody695_202 : HolLoopProg 64 :=
.mark loopBody695_201

def loopBody695_203 : HolLoopProg 64 :=
.seq loopBody695_188 loopBody695_202

def loopBody695_204 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 2)

def loopBody695_205 : HolLoopProg 64 :=
.mark loopBody695_204

def loopBody695_206 : HolLoopProg 64 :=
.call (some ([8], Flapjack.Spt.ln)) (some 70) ([9]) (some (9, loopBody695_101, loopBody695_1, (Flapjack.Spt.ln)))

def loopBody695_207 : HolLoopProg 64 :=
.mark loopBody695_206

def loopBody695_208 : HolLoopProg 64 :=
.seq loopBody695_207 loopBody695_1

def loopBody695_209 : HolLoopProg 64 :=
.mark loopBody695_208

def loopBody695_210 : HolLoopProg 64 :=
.seq loopBody695_205 loopBody695_209

def loopBody695_211 : HolLoopProg 64 :=
.mark loopBody695_210

def loopBody695_212 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_211

def loopBody695_213 : HolLoopProg 64 :=
.mark loopBody695_212

def loopBody695_214 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_213

def loopBody695_215 : HolLoopProg 64 :=
.mark loopBody695_214

def loopBody695_216 : HolLoopProg 64 :=
.seq loopBody695_203 loopBody695_215

def loopBody695_217 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody695_218 : HolLoopProg 64 :=
.mark loopBody695_217

def loopBody695_219 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [8]

def loopBody695_220 : HolLoopProg 64 :=
.mark loopBody695_219

def loopBody695_221 : HolLoopProg 64 :=
.seq loopBody695_220 loopBody695_1

def loopBody695_222 : HolLoopProg 64 :=
.mark loopBody695_221

def loopBody695_223 : HolLoopProg 64 :=
.seq loopBody695_218 loopBody695_222

def loopBody695_224 : HolLoopProg 64 :=
.mark loopBody695_223

def loopBody695_225 : HolLoopProg 64 :=
.seq loopBody695_216 loopBody695_224

def loopBody695_226 : HolLoopProg 64 :=
.seq loopBody695_65 loopBody695_225

def loopBody695_227 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_226

def loopBody695_228 : HolLoopProg 64 :=
.seq loopBody695_63 loopBody695_227

def loopBody695_229 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_228

def loopBody695_230 : HolLoopProg 64 :=
.seq loopBody695_61 loopBody695_229

def loopBody695_231 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_230

def loopBody695_232 : HolLoopProg 64 :=
.seq loopBody695_59 loopBody695_231

def loopBody695_233 : HolLoopProg 64 :=
.seq loopBody695_27 loopBody695_232

def loopBody695_234 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_233

def loopBody695_235 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_234

def loopBody695_236 : HolLoopProg 64 :=
.seq loopBody695_17 loopBody695_235

def loopBody695_237 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_236

def loopBody695_238 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_237

def loopBody695_239 : HolLoopProg 64 :=
.seq loopBody695_7 loopBody695_238

def loopBody695_240 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_239

def loopBody695_241 : HolLoopProg 64 :=
.seq loopBody695_1 loopBody695_240

def output695 : Nat × List Nat × HolLoopProg 64 :=
  (759, [0, 1], loopBody695_241)
end InitECandidate.Proofs.FrontendStages.Loop
