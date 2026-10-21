import InitECandidate.Proofs.FrontendStages.Loop.Translate295
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody311_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody311_1 : HolLoopProg 64 :=
.mark loopBody311_0

def loopBody311_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody311_3 : HolLoopProg 64 :=
.mark loopBody311_2

def loopBody311_4 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (4, loopBody311_3, loopBody311_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody311_5 : HolLoopProg 64 :=
.mark loopBody311_4

def loopBody311_6 : HolLoopProg 64 :=
.seq loopBody311_5 loopBody311_1

def loopBody311_7 : HolLoopProg 64 :=
.mark loopBody311_6

def loopBody311_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 32#64)

def loopBody311_9 : HolLoopProg 64 :=
.mark loopBody311_8

def loopBody311_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody311_11 : HolLoopProg 64 :=
.mark loopBody311_10

def loopBody311_12 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([5]) (some (5, loopBody311_11, loopBody311_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody311_13 : HolLoopProg 64 :=
.mark loopBody311_12

def loopBody311_14 : HolLoopProg 64 :=
.seq loopBody311_13 loopBody311_1

def loopBody311_15 : HolLoopProg 64 :=
.mark loopBody311_14

def loopBody311_16 : HolLoopProg 64 :=
.seq loopBody311_9 loopBody311_15

def loopBody311_17 : HolLoopProg 64 :=
.mark loopBody311_16

def loopBody311_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody311_19 : HolLoopProg 64 :=
.mark loopBody311_18

def loopBody311_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody311_21 : HolLoopProg 64 :=
.mark loopBody311_20

def loopBody311_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 4)

def loopBody311_23 : HolLoopProg 64 :=
.mark loopBody311_22

def loopBody311_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody311_25 : HolLoopProg 64 :=
.mark loopBody311_24

def loopBody311_26 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 374) ([6, 7, 8]) (some (6, loopBody311_25, loopBody311_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))

def loopBody311_27 : HolLoopProg 64 :=
.mark loopBody311_26

def loopBody311_28 : HolLoopProg 64 :=
.seq loopBody311_27 loopBody311_1

def loopBody311_29 : HolLoopProg 64 :=
.mark loopBody311_28

def loopBody311_30 : HolLoopProg 64 :=
.seq loopBody311_23 loopBody311_29

def loopBody311_31 : HolLoopProg 64 :=
.mark loopBody311_30

def loopBody311_32 : HolLoopProg 64 :=
.seq loopBody311_21 loopBody311_31

def loopBody311_33 : HolLoopProg 64 :=
.mark loopBody311_32

def loopBody311_34 : HolLoopProg 64 :=
.seq loopBody311_19 loopBody311_33

def loopBody311_35 : HolLoopProg 64 :=
.mark loopBody311_34

def loopBody311_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody311_37 : HolLoopProg 64 :=
.mark loopBody311_36

def loopBody311_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 320#64]))

def loopBody311_39 : HolLoopProg 64 :=
.mark loopBody311_38

def loopBody311_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 320#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody311_41 : HolLoopProg 64 :=
.mark loopBody311_40

def loopBody311_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 320#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody311_43 : HolLoopProg 64 :=
.mark loopBody311_42

def loopBody311_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 320#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody311_45 : HolLoopProg 64 :=
.mark loopBody311_44

def loopBody311_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 352#64]))

def loopBody311_47 : HolLoopProg 64 :=
.mark loopBody311_46

def loopBody311_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 352#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody311_49 : HolLoopProg 64 :=
.mark loopBody311_48

def loopBody311_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 352#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody311_51 : HolLoopProg 64 :=
.mark loopBody311_50

def loopBody311_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 352#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody311_53 : HolLoopProg 64 :=
.mark loopBody311_52

def loopBody311_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 5)

def loopBody311_55 : HolLoopProg 64 :=
.mark loopBody311_54

def loopBody311_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 2)

def loopBody311_57 : HolLoopProg 64 :=
.mark loopBody311_56

def loopBody311_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody311_59 : HolLoopProg 64 :=
.mark loopBody311_58

def loopBody311_60 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 231) ([7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]) (some (7, loopBody311_59, loopBody311_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody311_61 : HolLoopProg 64 :=
.mark loopBody311_60

def loopBody311_62 : HolLoopProg 64 :=
.seq loopBody311_61 loopBody311_1

def loopBody311_63 : HolLoopProg 64 :=
.mark loopBody311_62

def loopBody311_64 : HolLoopProg 64 :=
.seq loopBody311_57 loopBody311_63

def loopBody311_65 : HolLoopProg 64 :=
.mark loopBody311_64

def loopBody311_66 : HolLoopProg 64 :=
.seq loopBody311_55 loopBody311_65

def loopBody311_67 : HolLoopProg 64 :=
.mark loopBody311_66

def loopBody311_68 : HolLoopProg 64 :=
.seq loopBody311_53 loopBody311_67

def loopBody311_69 : HolLoopProg 64 :=
.mark loopBody311_68

def loopBody311_70 : HolLoopProg 64 :=
.seq loopBody311_51 loopBody311_69

def loopBody311_71 : HolLoopProg 64 :=
.mark loopBody311_70

def loopBody311_72 : HolLoopProg 64 :=
.seq loopBody311_49 loopBody311_71

def loopBody311_73 : HolLoopProg 64 :=
.mark loopBody311_72

def loopBody311_74 : HolLoopProg 64 :=
.seq loopBody311_47 loopBody311_73

def loopBody311_75 : HolLoopProg 64 :=
.mark loopBody311_74

def loopBody311_76 : HolLoopProg 64 :=
.seq loopBody311_45 loopBody311_75

def loopBody311_77 : HolLoopProg 64 :=
.mark loopBody311_76

def loopBody311_78 : HolLoopProg 64 :=
.seq loopBody311_43 loopBody311_77

def loopBody311_79 : HolLoopProg 64 :=
.mark loopBody311_78

def loopBody311_80 : HolLoopProg 64 :=
.seq loopBody311_41 loopBody311_79

def loopBody311_81 : HolLoopProg 64 :=
.mark loopBody311_80

def loopBody311_82 : HolLoopProg 64 :=
.seq loopBody311_39 loopBody311_81

def loopBody311_83 : HolLoopProg 64 :=
.mark loopBody311_82

def loopBody311_84 : HolLoopProg 64 :=
.seq loopBody311_37 loopBody311_83

def loopBody311_85 : HolLoopProg 64 :=
.mark loopBody311_84

def loopBody311_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody311_87 : HolLoopProg 64 :=
.mark loopBody311_86

def loopBody311_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody311_89 : HolLoopProg 64 :=
.mark loopBody311_88

def loopBody311_90 : HolLoopProg 64 :=
.call (some ([7], Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)) (some 70) ([8]) (some (8, loopBody311_89, loopBody311_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))

def loopBody311_91 : HolLoopProg 64 :=
.mark loopBody311_90

def loopBody311_92 : HolLoopProg 64 :=
.seq loopBody311_91 loopBody311_1

def loopBody311_93 : HolLoopProg 64 :=
.mark loopBody311_92

def loopBody311_94 : HolLoopProg 64 :=
.seq loopBody311_87 loopBody311_93

def loopBody311_95 : HolLoopProg 64 :=
.mark loopBody311_94

def loopBody311_96 : HolLoopProg 64 :=
.seq loopBody311_1 loopBody311_95

def loopBody311_97 : HolLoopProg 64 :=
.mark loopBody311_96

def loopBody311_98 : HolLoopProg 64 :=
.seq loopBody311_1 loopBody311_97

def loopBody311_99 : HolLoopProg 64 :=
.mark loopBody311_98

def loopBody311_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody311_101 : HolLoopProg 64 :=
.mark loopBody311_100

def loopBody311_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody311_103 : HolLoopProg 64 :=
.mark loopBody311_102

def loopBody311_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody311_105 : HolLoopProg 64 :=
.mark loopBody311_104

def loopBody311_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody311_107 : HolLoopProg 64 :=
.mark loopBody311_106

def loopBody311_108 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 8 (Flapjack.RegImm.reg 9) loopBody311_105 loopBody311_107 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  Flapjack.Spt.ln)

def loopBody311_109 : HolLoopProg 64 :=
.mark loopBody311_108

def loopBody311_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody311_111 : HolLoopProg 64 :=
.mark loopBody311_110

def loopBody311_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 46#64)

def loopBody311_113 : HolLoopProg 64 :=
.mark loopBody311_112

def loopBody311_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 7)

def loopBody311_115 : HolLoopProg 64 :=
.mark loopBody311_114

def loopBody311_116 : HolLoopProg 64 :=
.seq loopBody311_115 loopBody311_1

def loopBody311_117 : HolLoopProg 64 :=
.mark loopBody311_116

def loopBody311_118 : HolLoopProg 64 :=
.seq loopBody311_117 loopBody311_1

def loopBody311_119 : HolLoopProg 64 :=
.mark loopBody311_118

def loopBody311_120 : HolLoopProg 64 :=
.seq loopBody311_113 loopBody311_119

def loopBody311_121 : HolLoopProg 64 :=
.mark loopBody311_120

def loopBody311_122 : HolLoopProg 64 :=
.seq loopBody311_1 loopBody311_121

def loopBody311_123 : HolLoopProg 64 :=
.mark loopBody311_122

def loopBody311_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 6#64)

def loopBody311_125 : HolLoopProg 64 :=
.mark loopBody311_124

def loopBody311_126 : HolLoopProg 64 :=
.seq loopBody311_125 loopBody311_59

def loopBody311_127 : HolLoopProg 64 :=
.mark loopBody311_126

def loopBody311_128 : HolLoopProg 64 :=
.seq loopBody311_123 loopBody311_127

def loopBody311_129 : HolLoopProg 64 :=
.mark loopBody311_128

def loopBody311_130 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody311_129 loopBody311_1 (Flapjack.Spt.ln)

def loopBody311_131 : HolLoopProg 64 :=
.mark loopBody311_130

def loopBody311_132 : HolLoopProg 64 :=
.seq loopBody311_131 loopBody311_1

def loopBody311_133 : HolLoopProg 64 :=
.mark loopBody311_132

def loopBody311_134 : HolLoopProg 64 :=
.seq loopBody311_111 loopBody311_133

def loopBody311_135 : HolLoopProg 64 :=
.mark loopBody311_134

def loopBody311_136 : HolLoopProg 64 :=
.seq loopBody311_109 loopBody311_135

def loopBody311_137 : HolLoopProg 64 :=
.mark loopBody311_136

def loopBody311_138 : HolLoopProg 64 :=
.seq loopBody311_103 loopBody311_137

def loopBody311_139 : HolLoopProg 64 :=
.mark loopBody311_138

def loopBody311_140 : HolLoopProg 64 :=
.seq loopBody311_101 loopBody311_139

def loopBody311_141 : HolLoopProg 64 :=
.mark loopBody311_140

def loopBody311_142 : HolLoopProg 64 :=
.seq loopBody311_99 loopBody311_141

def loopBody311_143 : HolLoopProg 64 :=
.mark loopBody311_142

def loopBody311_144 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody311_145 : HolLoopProg 64 :=
.mark loopBody311_144

def loopBody311_146 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [7]

def loopBody311_147 : HolLoopProg 64 :=
.mark loopBody311_146

def loopBody311_148 : HolLoopProg 64 :=
.seq loopBody311_147 loopBody311_1

def loopBody311_149 : HolLoopProg 64 :=
.mark loopBody311_148

def loopBody311_150 : HolLoopProg 64 :=
.seq loopBody311_145 loopBody311_149

def loopBody311_151 : HolLoopProg 64 :=
.mark loopBody311_150

def loopBody311_152 : HolLoopProg 64 :=
.seq loopBody311_143 loopBody311_151

def loopBody311_153 : HolLoopProg 64 :=
.mark loopBody311_152

def loopBody311_154 : HolLoopProg 64 :=
.seq loopBody311_85 loopBody311_153

def loopBody311_155 : HolLoopProg 64 :=
.mark loopBody311_154

def loopBody311_156 : HolLoopProg 64 :=
.seq loopBody311_1 loopBody311_155

def loopBody311_157 : HolLoopProg 64 :=
.mark loopBody311_156

def loopBody311_158 : HolLoopProg 64 :=
.seq loopBody311_1 loopBody311_157

def loopBody311_159 : HolLoopProg 64 :=
.mark loopBody311_158

def loopBody311_160 : HolLoopProg 64 :=
.seq loopBody311_35 loopBody311_159

def loopBody311_161 : HolLoopProg 64 :=
.mark loopBody311_160

def loopBody311_162 : HolLoopProg 64 :=
.seq loopBody311_1 loopBody311_161

def loopBody311_163 : HolLoopProg 64 :=
.mark loopBody311_162

def loopBody311_164 : HolLoopProg 64 :=
.seq loopBody311_1 loopBody311_163

def loopBody311_165 : HolLoopProg 64 :=
.mark loopBody311_164

def loopBody311_166 : HolLoopProg 64 :=
.seq loopBody311_17 loopBody311_165

def loopBody311_167 : HolLoopProg 64 :=
.mark loopBody311_166

def loopBody311_168 : HolLoopProg 64 :=
.seq loopBody311_1 loopBody311_167

def loopBody311_169 : HolLoopProg 64 :=
.mark loopBody311_168

def loopBody311_170 : HolLoopProg 64 :=
.seq loopBody311_1 loopBody311_169

def loopBody311_171 : HolLoopProg 64 :=
.mark loopBody311_170

def loopBody311_172 : HolLoopProg 64 :=
.seq loopBody311_7 loopBody311_171

def loopBody311_173 : HolLoopProg 64 :=
.mark loopBody311_172

def loopBody311_174 : HolLoopProg 64 :=
.seq loopBody311_1 loopBody311_173

def loopBody311_175 : HolLoopProg 64 :=
.mark loopBody311_174

def loopBody311_176 : HolLoopProg 64 :=
.seq loopBody311_1 loopBody311_175

def loopBody311_177 : HolLoopProg 64 :=
.mark loopBody311_176

def output311 : Nat × List Nat × HolLoopProg 64 :=
  (375, [0, 1, 2], loopBody311_177)
end InitECandidate.Proofs.FrontendStages.Loop
