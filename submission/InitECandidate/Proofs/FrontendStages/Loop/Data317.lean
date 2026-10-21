import InitECandidate.Proofs.FrontendStages.Loop.Translate301
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody317_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody317_1 : HolLoopProg 64 :=
.mark loopBody317_0

def loopBody317_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody317_3 : HolLoopProg 64 :=
.mark loopBody317_2

def loopBody317_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody317_5 : HolLoopProg 64 :=
.mark loopBody317_4

def loopBody317_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody317_7 : HolLoopProg 64 :=
.mark loopBody317_6

def loopBody317_8 : HolLoopProg 64 :=
.call (some ([2, 3, 4], Flapjack.Spt.ls PUnit.unit)) (some 380) ([5, 6]) (some (5, loopBody317_7, loopBody317_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody317_9 : HolLoopProg 64 :=
.mark loopBody317_8

def loopBody317_10 : HolLoopProg 64 :=
.seq loopBody317_9 loopBody317_1

def loopBody317_11 : HolLoopProg 64 :=
.mark loopBody317_10

def loopBody317_12 : HolLoopProg 64 :=
.seq loopBody317_5 loopBody317_11

def loopBody317_13 : HolLoopProg 64 :=
.mark loopBody317_12

def loopBody317_14 : HolLoopProg 64 :=
.seq loopBody317_3 loopBody317_13

def loopBody317_15 : HolLoopProg 64 :=
.mark loopBody317_14

def loopBody317_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 144#64]))

def loopBody317_17 : HolLoopProg 64 :=
.mark loopBody317_16

def loopBody317_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 4294967295#64)

def loopBody317_19 : HolLoopProg 64 :=
.mark loopBody317_18

def loopBody317_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody317_21 : HolLoopProg 64 :=
.mark loopBody317_20

def loopBody317_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody317_23 : HolLoopProg 64 :=
.mark loopBody317_22

def loopBody317_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody317_25 : HolLoopProg 64 :=
.mark loopBody317_24

def loopBody317_26 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 7 (Flapjack.RegImm.reg 8) loopBody317_23 loopBody317_25 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody317_27 : HolLoopProg 64 :=
.mark loopBody317_26

def loopBody317_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody317_29 : HolLoopProg 64 :=
.mark loopBody317_28

def loopBody317_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 66#64)

def loopBody317_31 : HolLoopProg 64 :=
.mark loopBody317_30

def loopBody317_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 6)

def loopBody317_33 : HolLoopProg 64 :=
.mark loopBody317_32

def loopBody317_34 : HolLoopProg 64 :=
.seq loopBody317_33 loopBody317_1

def loopBody317_35 : HolLoopProg 64 :=
.mark loopBody317_34

def loopBody317_36 : HolLoopProg 64 :=
.seq loopBody317_35 loopBody317_1

def loopBody317_37 : HolLoopProg 64 :=
.mark loopBody317_36

def loopBody317_38 : HolLoopProg 64 :=
.seq loopBody317_31 loopBody317_37

def loopBody317_39 : HolLoopProg 64 :=
.mark loopBody317_38

def loopBody317_40 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_39

def loopBody317_41 : HolLoopProg 64 :=
.mark loopBody317_40

def loopBody317_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 6#64)

def loopBody317_43 : HolLoopProg 64 :=
.mark loopBody317_42

def loopBody317_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody317_45 : HolLoopProg 64 :=
.mark loopBody317_44

def loopBody317_46 : HolLoopProg 64 :=
.seq loopBody317_43 loopBody317_45

def loopBody317_47 : HolLoopProg 64 :=
.mark loopBody317_46

def loopBody317_48 : HolLoopProg 64 :=
.seq loopBody317_41 loopBody317_47

def loopBody317_49 : HolLoopProg 64 :=
.mark loopBody317_48

def loopBody317_50 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody317_49 loopBody317_1 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))

def loopBody317_51 : HolLoopProg 64 :=
.mark loopBody317_50

def loopBody317_52 : HolLoopProg 64 :=
.seq loopBody317_51 loopBody317_1

def loopBody317_53 : HolLoopProg 64 :=
.mark loopBody317_52

def loopBody317_54 : HolLoopProg 64 :=
.seq loopBody317_29 loopBody317_53

def loopBody317_55 : HolLoopProg 64 :=
.mark loopBody317_54

def loopBody317_56 : HolLoopProg 64 :=
.seq loopBody317_27 loopBody317_55

def loopBody317_57 : HolLoopProg 64 :=
.mark loopBody317_56

def loopBody317_58 : HolLoopProg 64 :=
.seq loopBody317_21 loopBody317_57

def loopBody317_59 : HolLoopProg 64 :=
.mark loopBody317_58

def loopBody317_60 : HolLoopProg 64 :=
.seq loopBody317_19 loopBody317_59

def loopBody317_61 : HolLoopProg 64 :=
.mark loopBody317_60

def loopBody317_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody317_63 : HolLoopProg 64 :=
.mark loopBody317_62

def loopBody317_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 3])

def loopBody317_65 : HolLoopProg 64 :=
.mark loopBody317_64

def loopBody317_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 60#64)

def loopBody317_67 : HolLoopProg 64 :=
.mark loopBody317_66

def loopBody317_68 : HolLoopProg 64 :=
.seq loopBody317_67 loopBody317_37

def loopBody317_69 : HolLoopProg 64 :=
.mark loopBody317_68

def loopBody317_70 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_69

def loopBody317_71 : HolLoopProg 64 :=
.mark loopBody317_70

def loopBody317_72 : HolLoopProg 64 :=
.seq loopBody317_71 loopBody317_47

def loopBody317_73 : HolLoopProg 64 :=
.mark loopBody317_72

def loopBody317_74 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody317_73 loopBody317_1 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))

def loopBody317_75 : HolLoopProg 64 :=
.mark loopBody317_74

def loopBody317_76 : HolLoopProg 64 :=
.seq loopBody317_75 loopBody317_1

def loopBody317_77 : HolLoopProg 64 :=
.mark loopBody317_76

def loopBody317_78 : HolLoopProg 64 :=
.seq loopBody317_29 loopBody317_77

def loopBody317_79 : HolLoopProg 64 :=
.mark loopBody317_78

def loopBody317_80 : HolLoopProg 64 :=
.seq loopBody317_27 loopBody317_79

def loopBody317_81 : HolLoopProg 64 :=
.mark loopBody317_80

def loopBody317_82 : HolLoopProg 64 :=
.seq loopBody317_65 loopBody317_81

def loopBody317_83 : HolLoopProg 64 :=
.mark loopBody317_82

def loopBody317_84 : HolLoopProg 64 :=
.seq loopBody317_63 loopBody317_83

def loopBody317_85 : HolLoopProg 64 :=
.mark loopBody317_84

def loopBody317_86 : HolLoopProg 64 :=
.seq loopBody317_61 loopBody317_85

def loopBody317_87 : HolLoopProg 64 :=
.mark loopBody317_86

def loopBody317_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 4)

def loopBody317_89 : HolLoopProg 64 :=
.mark loopBody317_88

def loopBody317_90 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 7 (Flapjack.RegImm.reg 8) loopBody317_23 loopBody317_25 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody317_91 : HolLoopProg 64 :=
.mark loopBody317_90

def loopBody317_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 61#64)

def loopBody317_93 : HolLoopProg 64 :=
.mark loopBody317_92

def loopBody317_94 : HolLoopProg 64 :=
.seq loopBody317_93 loopBody317_37

def loopBody317_95 : HolLoopProg 64 :=
.mark loopBody317_94

def loopBody317_96 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_95

def loopBody317_97 : HolLoopProg 64 :=
.mark loopBody317_96

def loopBody317_98 : HolLoopProg 64 :=
.seq loopBody317_97 loopBody317_47

def loopBody317_99 : HolLoopProg 64 :=
.mark loopBody317_98

def loopBody317_100 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody317_99 loopBody317_1 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody317_101 : HolLoopProg 64 :=
.mark loopBody317_100

def loopBody317_102 : HolLoopProg 64 :=
.seq loopBody317_101 loopBody317_1

def loopBody317_103 : HolLoopProg 64 :=
.mark loopBody317_102

def loopBody317_104 : HolLoopProg 64 :=
.seq loopBody317_29 loopBody317_103

def loopBody317_105 : HolLoopProg 64 :=
.mark loopBody317_104

def loopBody317_106 : HolLoopProg 64 :=
.seq loopBody317_91 loopBody317_105

def loopBody317_107 : HolLoopProg 64 :=
.mark loopBody317_106

def loopBody317_108 : HolLoopProg 64 :=
.seq loopBody317_89 loopBody317_107

def loopBody317_109 : HolLoopProg 64 :=
.mark loopBody317_108

def loopBody317_110 : HolLoopProg 64 :=
.seq loopBody317_63 loopBody317_109

def loopBody317_111 : HolLoopProg 64 :=
.mark loopBody317_110

def loopBody317_112 : HolLoopProg 64 :=
.seq loopBody317_87 loopBody317_111

def loopBody317_113 : HolLoopProg 64 :=
.mark loopBody317_112

def loopBody317_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 152#64]))

def loopBody317_115 : HolLoopProg 64 :=
.mark loopBody317_114

def loopBody317_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody317_117 : HolLoopProg 64 :=
.mark loopBody317_116

def loopBody317_118 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 7 (Flapjack.RegImm.reg 8) loopBody317_23 loopBody317_25 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody317_119 : HolLoopProg 64 :=
.mark loopBody317_118

def loopBody317_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 131072#64)

def loopBody317_121 : HolLoopProg 64 :=
.mark loopBody317_120

def loopBody317_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 200#64]))

def loopBody317_123 : HolLoopProg 64 :=
.mark loopBody317_122

def loopBody317_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 62#64)

def loopBody317_125 : HolLoopProg 64 :=
.mark loopBody317_124

def loopBody317_126 : HolLoopProg 64 :=
.seq loopBody317_125 loopBody317_37

def loopBody317_127 : HolLoopProg 64 :=
.mark loopBody317_126

def loopBody317_128 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_127

def loopBody317_129 : HolLoopProg 64 :=
.mark loopBody317_128

def loopBody317_130 : HolLoopProg 64 :=
.seq loopBody317_129 loopBody317_47

def loopBody317_131 : HolLoopProg 64 :=
.mark loopBody317_130

def loopBody317_132 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody317_131 loopBody317_1 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody317_133 : HolLoopProg 64 :=
.mark loopBody317_132

def loopBody317_134 : HolLoopProg 64 :=
.seq loopBody317_133 loopBody317_1

def loopBody317_135 : HolLoopProg 64 :=
.mark loopBody317_134

def loopBody317_136 : HolLoopProg 64 :=
.seq loopBody317_29 loopBody317_135

def loopBody317_137 : HolLoopProg 64 :=
.mark loopBody317_136

def loopBody317_138 : HolLoopProg 64 :=
.seq loopBody317_91 loopBody317_137

def loopBody317_139 : HolLoopProg 64 :=
.mark loopBody317_138

def loopBody317_140 : HolLoopProg 64 :=
.seq loopBody317_123 loopBody317_139

def loopBody317_141 : HolLoopProg 64 :=
.mark loopBody317_140

def loopBody317_142 : HolLoopProg 64 :=
.seq loopBody317_121 loopBody317_141

def loopBody317_143 : HolLoopProg 64 :=
.mark loopBody317_142

def loopBody317_144 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody317_143 loopBody317_1 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody317_145 : HolLoopProg 64 :=
.mark loopBody317_144

def loopBody317_146 : HolLoopProg 64 :=
.seq loopBody317_145 loopBody317_1

def loopBody317_147 : HolLoopProg 64 :=
.mark loopBody317_146

def loopBody317_148 : HolLoopProg 64 :=
.seq loopBody317_29 loopBody317_147

def loopBody317_149 : HolLoopProg 64 :=
.mark loopBody317_148

def loopBody317_150 : HolLoopProg 64 :=
.seq loopBody317_119 loopBody317_149

def loopBody317_151 : HolLoopProg 64 :=
.mark loopBody317_150

def loopBody317_152 : HolLoopProg 64 :=
.seq loopBody317_117 loopBody317_151

def loopBody317_153 : HolLoopProg 64 :=
.mark loopBody317_152

def loopBody317_154 : HolLoopProg 64 :=
.seq loopBody317_115 loopBody317_153

def loopBody317_155 : HolLoopProg 64 :=
.mark loopBody317_154

def loopBody317_156 : HolLoopProg 64 :=
.seq loopBody317_113 loopBody317_155

def loopBody317_157 : HolLoopProg 64 :=
.mark loopBody317_156

def loopBody317_158 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 16777216#64)

def loopBody317_159 : HolLoopProg 64 :=
.mark loopBody317_158

def loopBody317_160 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody317_161 : HolLoopProg 64 :=
.mark loopBody317_160

def loopBody317_162 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 63#64)

def loopBody317_163 : HolLoopProg 64 :=
.mark loopBody317_162

def loopBody317_164 : HolLoopProg 64 :=
.seq loopBody317_163 loopBody317_37

def loopBody317_165 : HolLoopProg 64 :=
.mark loopBody317_164

def loopBody317_166 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_165

def loopBody317_167 : HolLoopProg 64 :=
.mark loopBody317_166

def loopBody317_168 : HolLoopProg 64 :=
.seq loopBody317_167 loopBody317_47

def loopBody317_169 : HolLoopProg 64 :=
.mark loopBody317_168

def loopBody317_170 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody317_169 loopBody317_1 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody317_171 : HolLoopProg 64 :=
.mark loopBody317_170

def loopBody317_172 : HolLoopProg 64 :=
.seq loopBody317_171 loopBody317_1

def loopBody317_173 : HolLoopProg 64 :=
.mark loopBody317_172

def loopBody317_174 : HolLoopProg 64 :=
.seq loopBody317_29 loopBody317_173

def loopBody317_175 : HolLoopProg 64 :=
.mark loopBody317_174

def loopBody317_176 : HolLoopProg 64 :=
.seq loopBody317_91 loopBody317_175

def loopBody317_177 : HolLoopProg 64 :=
.mark loopBody317_176

def loopBody317_178 : HolLoopProg 64 :=
.seq loopBody317_161 loopBody317_177

def loopBody317_179 : HolLoopProg 64 :=
.mark loopBody317_178

def loopBody317_180 : HolLoopProg 64 :=
.seq loopBody317_159 loopBody317_179

def loopBody317_181 : HolLoopProg 64 :=
.mark loopBody317_180

def loopBody317_182 : HolLoopProg 64 :=
.seq loopBody317_157 loopBody317_181

def loopBody317_183 : HolLoopProg 64 :=
.mark loopBody317_182

def loopBody317_184 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 64#64)

def loopBody317_185 : HolLoopProg 64 :=
.mark loopBody317_184

def loopBody317_186 : HolLoopProg 64 :=
.seq loopBody317_185 loopBody317_37

def loopBody317_187 : HolLoopProg 64 :=
.mark loopBody317_186

def loopBody317_188 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_187

def loopBody317_189 : HolLoopProg 64 :=
.mark loopBody317_188

def loopBody317_190 : HolLoopProg 64 :=
.seq loopBody317_189 loopBody317_47

def loopBody317_191 : HolLoopProg 64 :=
.mark loopBody317_190

def loopBody317_192 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody317_191 loopBody317_1 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody317_193 : HolLoopProg 64 :=
.mark loopBody317_192

def loopBody317_194 : HolLoopProg 64 :=
.seq loopBody317_193 loopBody317_1

def loopBody317_195 : HolLoopProg 64 :=
.mark loopBody317_194

def loopBody317_196 : HolLoopProg 64 :=
.seq loopBody317_29 loopBody317_195

def loopBody317_197 : HolLoopProg 64 :=
.mark loopBody317_196

def loopBody317_198 : HolLoopProg 64 :=
.seq loopBody317_91 loopBody317_197

def loopBody317_199 : HolLoopProg 64 :=
.mark loopBody317_198

def loopBody317_200 : HolLoopProg 64 :=
.seq loopBody317_89 loopBody317_199

def loopBody317_201 : HolLoopProg 64 :=
.mark loopBody317_200

def loopBody317_202 : HolLoopProg 64 :=
.seq loopBody317_159 loopBody317_201

def loopBody317_203 : HolLoopProg 64 :=
.mark loopBody317_202

def loopBody317_204 : HolLoopProg 64 :=
.seq loopBody317_183 loopBody317_203

def loopBody317_205 : HolLoopProg 64 :=
.mark loopBody317_204

def loopBody317_206 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64]))

def loopBody317_207 : HolLoopProg 64 :=
.mark loopBody317_206

def loopBody317_208 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody317_209 : HolLoopProg 64 :=
.mark loopBody317_208

def loopBody317_210 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody317_211 : HolLoopProg 64 :=
.mark loopBody317_210

def loopBody317_212 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody317_213 : HolLoopProg 64 :=
.mark loopBody317_212

def loopBody317_214 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 6)

def loopBody317_215 : HolLoopProg 64 :=
.mark loopBody317_214

def loopBody317_216 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 7)

def loopBody317_217 : HolLoopProg 64 :=
.mark loopBody317_216

def loopBody317_218 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 8)

def loopBody317_219 : HolLoopProg 64 :=
.mark loopBody317_218

def loopBody317_220 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 9)

def loopBody317_221 : HolLoopProg 64 :=
.mark loopBody317_220

def loopBody317_222 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 11

def loopBody317_223 : HolLoopProg 64 :=
.mark loopBody317_222

def loopBody317_224 : HolLoopProg 64 :=
.call (some
  ([10],
    Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 101) ([11, 12, 13, 14]) (some (11, loopBody317_223, loopBody317_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody317_225 : HolLoopProg 64 :=
.mark loopBody317_224

def loopBody317_226 : HolLoopProg 64 :=
.seq loopBody317_225 loopBody317_1

def loopBody317_227 : HolLoopProg 64 :=
.mark loopBody317_226

def loopBody317_228 : HolLoopProg 64 :=
.seq loopBody317_221 loopBody317_227

def loopBody317_229 : HolLoopProg 64 :=
.mark loopBody317_228

def loopBody317_230 : HolLoopProg 64 :=
.seq loopBody317_219 loopBody317_229

def loopBody317_231 : HolLoopProg 64 :=
.mark loopBody317_230

def loopBody317_232 : HolLoopProg 64 :=
.seq loopBody317_217 loopBody317_231

def loopBody317_233 : HolLoopProg 64 :=
.mark loopBody317_232

def loopBody317_234 : HolLoopProg 64 :=
.seq loopBody317_215 loopBody317_233

def loopBody317_235 : HolLoopProg 64 :=
.mark loopBody317_234

def loopBody317_236 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 10)

def loopBody317_237 : HolLoopProg 64 :=
.mark loopBody317_236

def loopBody317_238 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 0#64)

def loopBody317_239 : HolLoopProg 64 :=
.mark loopBody317_238

def loopBody317_240 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody317_241 : HolLoopProg 64 :=
.mark loopBody317_240

def loopBody317_242 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 0#64)

def loopBody317_243 : HolLoopProg 64 :=
.mark loopBody317_242

def loopBody317_244 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.RegImm.reg 13) loopBody317_241 loopBody317_243 (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody317_245 : HolLoopProg 64 :=
.mark loopBody317_244

def loopBody317_246 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 12)

def loopBody317_247 : HolLoopProg 64 :=
.mark loopBody317_246

def loopBody317_248 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 65#64)

def loopBody317_249 : HolLoopProg 64 :=
.mark loopBody317_248

def loopBody317_250 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 11)

def loopBody317_251 : HolLoopProg 64 :=
.mark loopBody317_250

def loopBody317_252 : HolLoopProg 64 :=
.seq loopBody317_251 loopBody317_1

def loopBody317_253 : HolLoopProg 64 :=
.mark loopBody317_252

def loopBody317_254 : HolLoopProg 64 :=
.seq loopBody317_253 loopBody317_1

def loopBody317_255 : HolLoopProg 64 :=
.mark loopBody317_254

def loopBody317_256 : HolLoopProg 64 :=
.seq loopBody317_249 loopBody317_255

def loopBody317_257 : HolLoopProg 64 :=
.mark loopBody317_256

def loopBody317_258 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_257

def loopBody317_259 : HolLoopProg 64 :=
.mark loopBody317_258

def loopBody317_260 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 6#64)

def loopBody317_261 : HolLoopProg 64 :=
.mark loopBody317_260

def loopBody317_262 : HolLoopProg 64 :=
.seq loopBody317_261 loopBody317_223

def loopBody317_263 : HolLoopProg 64 :=
.mark loopBody317_262

def loopBody317_264 : HolLoopProg 64 :=
.seq loopBody317_259 loopBody317_263

def loopBody317_265 : HolLoopProg 64 :=
.mark loopBody317_264

def loopBody317_266 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.RegImm.imm 0#64) loopBody317_265 loopBody317_1 (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody317_267 : HolLoopProg 64 :=
.mark loopBody317_266

def loopBody317_268 : HolLoopProg 64 :=
.seq loopBody317_267 loopBody317_1

def loopBody317_269 : HolLoopProg 64 :=
.mark loopBody317_268

def loopBody317_270 : HolLoopProg 64 :=
.seq loopBody317_247 loopBody317_269

def loopBody317_271 : HolLoopProg 64 :=
.mark loopBody317_270

def loopBody317_272 : HolLoopProg 64 :=
.seq loopBody317_245 loopBody317_271

def loopBody317_273 : HolLoopProg 64 :=
.mark loopBody317_272

def loopBody317_274 : HolLoopProg 64 :=
.seq loopBody317_239 loopBody317_273

def loopBody317_275 : HolLoopProg 64 :=
.mark loopBody317_274

def loopBody317_276 : HolLoopProg 64 :=
.seq loopBody317_237 loopBody317_275

def loopBody317_277 : HolLoopProg 64 :=
.mark loopBody317_276

def loopBody317_278 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 6)

def loopBody317_279 : HolLoopProg 64 :=
.mark loopBody317_278

def loopBody317_280 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.const 0#64, Flapjack.HolLoopExp.const 1#64])

def loopBody317_281 : HolLoopProg 64 :=
.mark loopBody317_280

def loopBody317_282 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.RegImm.reg 13) loopBody317_241 loopBody317_243 (Flapjack.Spt.bn
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody317_283 : HolLoopProg 64 :=
.mark loopBody317_282

def loopBody317_284 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.RegImm.imm 0#64) loopBody317_265 loopBody317_1 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody317_285 : HolLoopProg 64 :=
.mark loopBody317_284

def loopBody317_286 : HolLoopProg 64 :=
.seq loopBody317_285 loopBody317_1

def loopBody317_287 : HolLoopProg 64 :=
.mark loopBody317_286

def loopBody317_288 : HolLoopProg 64 :=
.seq loopBody317_247 loopBody317_287

def loopBody317_289 : HolLoopProg 64 :=
.mark loopBody317_288

def loopBody317_290 : HolLoopProg 64 :=
.seq loopBody317_283 loopBody317_289

def loopBody317_291 : HolLoopProg 64 :=
.mark loopBody317_290

def loopBody317_292 : HolLoopProg 64 :=
.seq loopBody317_281 loopBody317_291

def loopBody317_293 : HolLoopProg 64 :=
.mark loopBody317_292

def loopBody317_294 : HolLoopProg 64 :=
.seq loopBody317_279 loopBody317_293

def loopBody317_295 : HolLoopProg 64 :=
.mark loopBody317_294

def loopBody317_296 : HolLoopProg 64 :=
.seq loopBody317_277 loopBody317_295

def loopBody317_297 : HolLoopProg 64 :=
.mark loopBody317_296

def loopBody317_298 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 2)

def loopBody317_299 : HolLoopProg 64 :=
.mark loopBody317_298

def loopBody317_300 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 3)

def loopBody317_301 : HolLoopProg 64 :=
.mark loopBody317_300

def loopBody317_302 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 4)

def loopBody317_303 : HolLoopProg 64 :=
.mark loopBody317_302

def loopBody317_304 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [11, 12, 13]

def loopBody317_305 : HolLoopProg 64 :=
.mark loopBody317_304

def loopBody317_306 : HolLoopProg 64 :=
.seq loopBody317_305 loopBody317_1

def loopBody317_307 : HolLoopProg 64 :=
.mark loopBody317_306

def loopBody317_308 : HolLoopProg 64 :=
.seq loopBody317_303 loopBody317_307

def loopBody317_309 : HolLoopProg 64 :=
.mark loopBody317_308

def loopBody317_310 : HolLoopProg 64 :=
.seq loopBody317_301 loopBody317_309

def loopBody317_311 : HolLoopProg 64 :=
.mark loopBody317_310

def loopBody317_312 : HolLoopProg 64 :=
.seq loopBody317_299 loopBody317_311

def loopBody317_313 : HolLoopProg 64 :=
.mark loopBody317_312

def loopBody317_314 : HolLoopProg 64 :=
.seq loopBody317_297 loopBody317_313

def loopBody317_315 : HolLoopProg 64 :=
.mark loopBody317_314

def loopBody317_316 : HolLoopProg 64 :=
.seq loopBody317_235 loopBody317_315

def loopBody317_317 : HolLoopProg 64 :=
.mark loopBody317_316

def loopBody317_318 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_317

def loopBody317_319 : HolLoopProg 64 :=
.mark loopBody317_318

def loopBody317_320 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_319

def loopBody317_321 : HolLoopProg 64 :=
.mark loopBody317_320

def loopBody317_322 : HolLoopProg 64 :=
.seq loopBody317_213 loopBody317_321

def loopBody317_323 : HolLoopProg 64 :=
.mark loopBody317_322

def loopBody317_324 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_323

def loopBody317_325 : HolLoopProg 64 :=
.mark loopBody317_324

def loopBody317_326 : HolLoopProg 64 :=
.seq loopBody317_211 loopBody317_325

def loopBody317_327 : HolLoopProg 64 :=
.mark loopBody317_326

def loopBody317_328 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_327

def loopBody317_329 : HolLoopProg 64 :=
.mark loopBody317_328

def loopBody317_330 : HolLoopProg 64 :=
.seq loopBody317_209 loopBody317_329

def loopBody317_331 : HolLoopProg 64 :=
.mark loopBody317_330

def loopBody317_332 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_331

def loopBody317_333 : HolLoopProg 64 :=
.mark loopBody317_332

def loopBody317_334 : HolLoopProg 64 :=
.seq loopBody317_207 loopBody317_333

def loopBody317_335 : HolLoopProg 64 :=
.mark loopBody317_334

def loopBody317_336 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_335

def loopBody317_337 : HolLoopProg 64 :=
.mark loopBody317_336

def loopBody317_338 : HolLoopProg 64 :=
.seq loopBody317_205 loopBody317_337

def loopBody317_339 : HolLoopProg 64 :=
.mark loopBody317_338

def loopBody317_340 : HolLoopProg 64 :=
.seq loopBody317_17 loopBody317_339

def loopBody317_341 : HolLoopProg 64 :=
.mark loopBody317_340

def loopBody317_342 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_341

def loopBody317_343 : HolLoopProg 64 :=
.mark loopBody317_342

def loopBody317_344 : HolLoopProg 64 :=
.seq loopBody317_15 loopBody317_343

def loopBody317_345 : HolLoopProg 64 :=
.mark loopBody317_344

def loopBody317_346 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_345

def loopBody317_347 : HolLoopProg 64 :=
.mark loopBody317_346

def loopBody317_348 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_347

def loopBody317_349 : HolLoopProg 64 :=
.mark loopBody317_348

def loopBody317_350 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_349

def loopBody317_351 : HolLoopProg 64 :=
.mark loopBody317_350

def loopBody317_352 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_351

def loopBody317_353 : HolLoopProg 64 :=
.mark loopBody317_352

def loopBody317_354 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_353

def loopBody317_355 : HolLoopProg 64 :=
.mark loopBody317_354

def loopBody317_356 : HolLoopProg 64 :=
.seq loopBody317_1 loopBody317_355

def loopBody317_357 : HolLoopProg 64 :=
.mark loopBody317_356

def output317 : Nat × List Nat × HolLoopProg 64 :=
  (381, [0, 1], loopBody317_357)
end InitECandidate.Proofs.FrontendStages.Loop
