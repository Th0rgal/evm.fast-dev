import InitECandidate.Proofs.FrontendStages.Loop.Translate777
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody793_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody793_1 : HolLoopProg 64 :=
.mark loopBody793_0

def loopBody793_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody793_3 : HolLoopProg 64 :=
.mark loopBody793_2

def loopBody793_4 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 383) ([]) (some (2, loopBody793_3, loopBody793_1, (Flapjack.Spt.ls PUnit.unit)))

def loopBody793_5 : HolLoopProg 64 :=
.mark loopBody793_4

def loopBody793_6 : HolLoopProg 64 :=
.seq loopBody793_5 loopBody793_1

def loopBody793_7 : HolLoopProg 64 :=
.mark loopBody793_6

def loopBody793_8 : HolLoopProg 64 :=
.seq loopBody793_1 loopBody793_7

def loopBody793_9 : HolLoopProg 64 :=
.mark loopBody793_8

def loopBody793_10 : HolLoopProg 64 :=
.seq loopBody793_1 loopBody793_9

def loopBody793_11 : HolLoopProg 64 :=
.mark loopBody793_10

def loopBody793_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody793_13 : HolLoopProg 64 :=
.mark loopBody793_12

def loopBody793_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody793_15 : HolLoopProg 64 :=
.mark loopBody793_14

def loopBody793_16 : HolLoopProg 64 :=
.call (some ([1, 2], Flapjack.Spt.ls PUnit.unit)) (some 561) ([3]) (some (3, loopBody793_15, loopBody793_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))

def loopBody793_17 : HolLoopProg 64 :=
.mark loopBody793_16

def loopBody793_18 : HolLoopProg 64 :=
.seq loopBody793_17 loopBody793_1

def loopBody793_19 : HolLoopProg 64 :=
.mark loopBody793_18

def loopBody793_20 : HolLoopProg 64 :=
.seq loopBody793_13 loopBody793_19

def loopBody793_21 : HolLoopProg 64 :=
.mark loopBody793_20

def loopBody793_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody793_23 : HolLoopProg 64 :=
.mark loopBody793_22

def loopBody793_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody793_25 : HolLoopProg 64 :=
.mark loopBody793_24

def loopBody793_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody793_27 : HolLoopProg 64 :=
.mark loopBody793_26

def loopBody793_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody793_29 : HolLoopProg 64 :=
.mark loopBody793_28

def loopBody793_30 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.RegImm.reg 5) loopBody793_27 loopBody793_29 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)

def loopBody793_31 : HolLoopProg 64 :=
.mark loopBody793_30

def loopBody793_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody793_33 : HolLoopProg 64 :=
.mark loopBody793_32

def loopBody793_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 70#64)

def loopBody793_35 : HolLoopProg 64 :=
.mark loopBody793_34

def loopBody793_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 3)

def loopBody793_37 : HolLoopProg 64 :=
.mark loopBody793_36

def loopBody793_38 : HolLoopProg 64 :=
.seq loopBody793_37 loopBody793_1

def loopBody793_39 : HolLoopProg 64 :=
.mark loopBody793_38

def loopBody793_40 : HolLoopProg 64 :=
.seq loopBody793_39 loopBody793_1

def loopBody793_41 : HolLoopProg 64 :=
.mark loopBody793_40

def loopBody793_42 : HolLoopProg 64 :=
.seq loopBody793_35 loopBody793_41

def loopBody793_43 : HolLoopProg 64 :=
.mark loopBody793_42

def loopBody793_44 : HolLoopProg 64 :=
.seq loopBody793_1 loopBody793_43

def loopBody793_45 : HolLoopProg 64 :=
.mark loopBody793_44

def loopBody793_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 4#64)

def loopBody793_47 : HolLoopProg 64 :=
.mark loopBody793_46

def loopBody793_48 : HolLoopProg 64 :=
.seq loopBody793_47 loopBody793_15

def loopBody793_49 : HolLoopProg 64 :=
.mark loopBody793_48

def loopBody793_50 : HolLoopProg 64 :=
.seq loopBody793_45 loopBody793_49

def loopBody793_51 : HolLoopProg 64 :=
.mark loopBody793_50

def loopBody793_52 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody793_51 loopBody793_1 (Flapjack.Spt.ls PUnit.unit)

def loopBody793_53 : HolLoopProg 64 :=
.mark loopBody793_52

def loopBody793_54 : HolLoopProg 64 :=
.seq loopBody793_53 loopBody793_1

def loopBody793_55 : HolLoopProg 64 :=
.mark loopBody793_54

def loopBody793_56 : HolLoopProg 64 :=
.seq loopBody793_33 loopBody793_55

def loopBody793_57 : HolLoopProg 64 :=
.mark loopBody793_56

def loopBody793_58 : HolLoopProg 64 :=
.seq loopBody793_31 loopBody793_57

def loopBody793_59 : HolLoopProg 64 :=
.mark loopBody793_58

def loopBody793_60 : HolLoopProg 64 :=
.seq loopBody793_25 loopBody793_59

def loopBody793_61 : HolLoopProg 64 :=
.mark loopBody793_60

def loopBody793_62 : HolLoopProg 64 :=
.seq loopBody793_23 loopBody793_61

def loopBody793_63 : HolLoopProg 64 :=
.mark loopBody793_62

def loopBody793_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 8#64)

def loopBody793_65 : HolLoopProg 64 :=
.mark loopBody793_64

def loopBody793_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody793_67 : HolLoopProg 64 :=
.mark loopBody793_66

def loopBody793_68 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.ls PUnit.unit)) (some 68) ([4]) (some (4, loopBody793_67, loopBody793_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody793_69 : HolLoopProg 64 :=
.mark loopBody793_68

def loopBody793_70 : HolLoopProg 64 :=
.seq loopBody793_69 loopBody793_1

def loopBody793_71 : HolLoopProg 64 :=
.mark loopBody793_70

def loopBody793_72 : HolLoopProg 64 :=
.seq loopBody793_65 loopBody793_71

def loopBody793_73 : HolLoopProg 64 :=
.mark loopBody793_72

def loopBody793_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody793_75 : HolLoopProg 64 :=
.mark loopBody793_74

def loopBody793_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody793_77 : HolLoopProg 64 :=
.mark loopBody793_76

def loopBody793_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody793_79 : HolLoopProg 64 :=
.mark loopBody793_78

def loopBody793_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody793_81 : HolLoopProg 64 :=
.mark loopBody793_80

def loopBody793_82 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ln)) (some 856) ([5, 6, 7]) (some (5, loopBody793_81, loopBody793_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))

def loopBody793_83 : HolLoopProg 64 :=
.mark loopBody793_82

def loopBody793_84 : HolLoopProg 64 :=
.seq loopBody793_83 loopBody793_1

def loopBody793_85 : HolLoopProg 64 :=
.mark loopBody793_84

def loopBody793_86 : HolLoopProg 64 :=
.seq loopBody793_79 loopBody793_85

def loopBody793_87 : HolLoopProg 64 :=
.mark loopBody793_86

def loopBody793_88 : HolLoopProg 64 :=
.seq loopBody793_77 loopBody793_87

def loopBody793_89 : HolLoopProg 64 :=
.mark loopBody793_88

def loopBody793_90 : HolLoopProg 64 :=
.seq loopBody793_75 loopBody793_89

def loopBody793_91 : HolLoopProg 64 :=
.mark loopBody793_90

def loopBody793_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 32#64]))

def loopBody793_93 : HolLoopProg 64 :=
.mark loopBody793_92

def loopBody793_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody793_95 : HolLoopProg 64 :=
.mark loopBody793_94

def loopBody793_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody793_97 : HolLoopProg 64 :=
.mark loopBody793_96

def loopBody793_98 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.reg 7) loopBody793_95 loopBody793_97 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody793_99 : HolLoopProg 64 :=
.mark loopBody793_98

def loopBody793_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody793_101 : HolLoopProg 64 :=
.mark loopBody793_100

def loopBody793_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 71#64)

def loopBody793_103 : HolLoopProg 64 :=
.mark loopBody793_102

def loopBody793_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 5)

def loopBody793_105 : HolLoopProg 64 :=
.mark loopBody793_104

def loopBody793_106 : HolLoopProg 64 :=
.seq loopBody793_105 loopBody793_1

def loopBody793_107 : HolLoopProg 64 :=
.mark loopBody793_106

def loopBody793_108 : HolLoopProg 64 :=
.seq loopBody793_107 loopBody793_1

def loopBody793_109 : HolLoopProg 64 :=
.mark loopBody793_108

def loopBody793_110 : HolLoopProg 64 :=
.seq loopBody793_103 loopBody793_109

def loopBody793_111 : HolLoopProg 64 :=
.mark loopBody793_110

def loopBody793_112 : HolLoopProg 64 :=
.seq loopBody793_1 loopBody793_111

def loopBody793_113 : HolLoopProg 64 :=
.mark loopBody793_112

def loopBody793_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 4#64)

def loopBody793_115 : HolLoopProg 64 :=
.mark loopBody793_114

def loopBody793_116 : HolLoopProg 64 :=
.seq loopBody793_115 loopBody793_81

def loopBody793_117 : HolLoopProg 64 :=
.mark loopBody793_116

def loopBody793_118 : HolLoopProg 64 :=
.seq loopBody793_113 loopBody793_117

def loopBody793_119 : HolLoopProg 64 :=
.mark loopBody793_118

def loopBody793_120 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody793_119 loopBody793_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody793_121 : HolLoopProg 64 :=
.mark loopBody793_120

def loopBody793_122 : HolLoopProg 64 :=
.seq loopBody793_121 loopBody793_1

def loopBody793_123 : HolLoopProg 64 :=
.mark loopBody793_122

def loopBody793_124 : HolLoopProg 64 :=
.seq loopBody793_101 loopBody793_123

def loopBody793_125 : HolLoopProg 64 :=
.mark loopBody793_124

def loopBody793_126 : HolLoopProg 64 :=
.seq loopBody793_99 loopBody793_125

def loopBody793_127 : HolLoopProg 64 :=
.mark loopBody793_126

def loopBody793_128 : HolLoopProg 64 :=
.seq loopBody793_79 loopBody793_127

def loopBody793_129 : HolLoopProg 64 :=
.mark loopBody793_128

def loopBody793_130 : HolLoopProg 64 :=
.seq loopBody793_93 loopBody793_129

def loopBody793_131 : HolLoopProg 64 :=
.mark loopBody793_130

def loopBody793_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 4)

def loopBody793_133 : HolLoopProg 64 :=
.mark loopBody793_132

def loopBody793_134 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody793_135 : HolLoopProg 64 :=
.mark loopBody793_134

def loopBody793_136 : HolLoopProg 64 :=
.seq loopBody793_135 loopBody793_1

def loopBody793_137 : HolLoopProg 64 :=
.mark loopBody793_136

def loopBody793_138 : HolLoopProg 64 :=
.seq loopBody793_133 loopBody793_137

def loopBody793_139 : HolLoopProg 64 :=
.mark loopBody793_138

def loopBody793_140 : HolLoopProg 64 :=
.seq loopBody793_131 loopBody793_139

def loopBody793_141 : HolLoopProg 64 :=
.mark loopBody793_140

def loopBody793_142 : HolLoopProg 64 :=
.seq loopBody793_91 loopBody793_141

def loopBody793_143 : HolLoopProg 64 :=
.mark loopBody793_142

def loopBody793_144 : HolLoopProg 64 :=
.seq loopBody793_1 loopBody793_143

def loopBody793_145 : HolLoopProg 64 :=
.mark loopBody793_144

def loopBody793_146 : HolLoopProg 64 :=
.seq loopBody793_1 loopBody793_145

def loopBody793_147 : HolLoopProg 64 :=
.mark loopBody793_146

def loopBody793_148 : HolLoopProg 64 :=
.seq loopBody793_73 loopBody793_147

def loopBody793_149 : HolLoopProg 64 :=
.mark loopBody793_148

def loopBody793_150 : HolLoopProg 64 :=
.seq loopBody793_1 loopBody793_149

def loopBody793_151 : HolLoopProg 64 :=
.mark loopBody793_150

def loopBody793_152 : HolLoopProg 64 :=
.seq loopBody793_1 loopBody793_151

def loopBody793_153 : HolLoopProg 64 :=
.mark loopBody793_152

def loopBody793_154 : HolLoopProg 64 :=
.seq loopBody793_63 loopBody793_153

def loopBody793_155 : HolLoopProg 64 :=
.mark loopBody793_154

def loopBody793_156 : HolLoopProg 64 :=
.seq loopBody793_21 loopBody793_155

def loopBody793_157 : HolLoopProg 64 :=
.mark loopBody793_156

def loopBody793_158 : HolLoopProg 64 :=
.seq loopBody793_1 loopBody793_157

def loopBody793_159 : HolLoopProg 64 :=
.mark loopBody793_158

def loopBody793_160 : HolLoopProg 64 :=
.seq loopBody793_1 loopBody793_159

def loopBody793_161 : HolLoopProg 64 :=
.mark loopBody793_160

def loopBody793_162 : HolLoopProg 64 :=
.seq loopBody793_1 loopBody793_161

def loopBody793_163 : HolLoopProg 64 :=
.mark loopBody793_162

def loopBody793_164 : HolLoopProg 64 :=
.seq loopBody793_1 loopBody793_163

def loopBody793_165 : HolLoopProg 64 :=
.mark loopBody793_164

def loopBody793_166 : HolLoopProg 64 :=
.seq loopBody793_11 loopBody793_165

def loopBody793_167 : HolLoopProg 64 :=
.mark loopBody793_166

def output793 : Nat × List Nat × HolLoopProg 64 :=
  (857, [0], loopBody793_167)
end InitECandidate.Proofs.FrontendStages.Loop
