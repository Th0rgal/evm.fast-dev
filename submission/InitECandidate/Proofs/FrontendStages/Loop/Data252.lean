import InitECandidate.Proofs.FrontendStages.Loop.Translate236
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody252_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody252_1 : HolLoopProg 64 :=
.mark loopBody252_0

def loopBody252_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 0)

def loopBody252_3 : HolLoopProg 64 :=
.mark loopBody252_2

def loopBody252_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody252_5 : HolLoopProg 64 :=
.mark loopBody252_4

def loopBody252_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 2)

def loopBody252_7 : HolLoopProg 64 :=
.mark loopBody252_6

def loopBody252_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody252_9 : HolLoopProg 64 :=
.mark loopBody252_8

def loopBody252_10 : HolLoopProg 64 :=
.call (some
  ([5, 6],
    Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 306) ([7, 8, 9]) (some (7, loopBody252_9, loopBody252_1, (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))

def loopBody252_11 : HolLoopProg 64 :=
.mark loopBody252_10

def loopBody252_12 : HolLoopProg 64 :=
.seq loopBody252_11 loopBody252_1

def loopBody252_13 : HolLoopProg 64 :=
.mark loopBody252_12

def loopBody252_14 : HolLoopProg 64 :=
.seq loopBody252_7 loopBody252_13

def loopBody252_15 : HolLoopProg 64 :=
.mark loopBody252_14

def loopBody252_16 : HolLoopProg 64 :=
.seq loopBody252_5 loopBody252_15

def loopBody252_17 : HolLoopProg 64 :=
.mark loopBody252_16

def loopBody252_18 : HolLoopProg 64 :=
.seq loopBody252_3 loopBody252_17

def loopBody252_19 : HolLoopProg 64 :=
.mark loopBody252_18

def loopBody252_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64]))

def loopBody252_21 : HolLoopProg 64 :=
.mark loopBody252_20

def loopBody252_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 3)

def loopBody252_23 : HolLoopProg 64 :=
.mark loopBody252_22

def loopBody252_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody252_25 : HolLoopProg 64 :=
.mark loopBody252_24

def loopBody252_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 1#64)

def loopBody252_27 : HolLoopProg 64 :=
.mark loopBody252_26

def loopBody252_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody252_29 : HolLoopProg 64 :=
.mark loopBody252_28

def loopBody252_30 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 9 (Flapjack.RegImm.reg 10) loopBody252_27 loopBody252_29 (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody252_31 : HolLoopProg 64 :=
.mark loopBody252_30

def loopBody252_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 4)

def loopBody252_33 : HolLoopProg 64 :=
.mark loopBody252_32

def loopBody252_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 0#64)

def loopBody252_35 : HolLoopProg 64 :=
.mark loopBody252_34

def loopBody252_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody252_37 : HolLoopProg 64 :=
.mark loopBody252_36

def loopBody252_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 0#64)

def loopBody252_39 : HolLoopProg 64 :=
.mark loopBody252_38

def loopBody252_40 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.RegImm.reg 13) loopBody252_37 loopBody252_39 (Flapjack.Spt.bs
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
  PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody252_41 : HolLoopProg 64 :=
.mark loopBody252_40

def loopBody252_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 0#64)

def loopBody252_43 : HolLoopProg 64 :=
.mark loopBody252_42

def loopBody252_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or [Flapjack.HolLoopExp.var 9, Flapjack.HolLoopExp.var 12])

def loopBody252_45 : HolLoopProg 64 :=
.mark loopBody252_44

def loopBody252_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 1#64)

def loopBody252_47 : HolLoopProg 64 :=
.mark loopBody252_46

def loopBody252_48 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 15 (Flapjack.RegImm.reg 16) loopBody252_47 loopBody252_43 (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody252_49 : HolLoopProg 64 :=
.mark loopBody252_48

def loopBody252_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 15)

def loopBody252_51 : HolLoopProg 64 :=
.mark loopBody252_50

def loopBody252_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 7)

def loopBody252_53 : HolLoopProg 64 :=
.mark loopBody252_52

def loopBody252_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody252_55 : HolLoopProg 64 :=
.mark loopBody252_54

def loopBody252_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 6)

def loopBody252_57 : HolLoopProg 64 :=
.mark loopBody252_56

def loopBody252_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody252_59 : HolLoopProg 64 :=
.mark loopBody252_58

def loopBody252_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody252_61 : HolLoopProg 64 :=
.mark loopBody252_60

def loopBody252_62 : HolLoopProg 64 :=
.call (some ([7], Flapjack.Spt.ls PUnit.unit)) (some 315) ([8, 9, 10, 11]) (some (8, loopBody252_61, loopBody252_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody252_63 : HolLoopProg 64 :=
.mark loopBody252_62

def loopBody252_64 : HolLoopProg 64 :=
.seq loopBody252_63 loopBody252_1

def loopBody252_65 : HolLoopProg 64 :=
.mark loopBody252_64

def loopBody252_66 : HolLoopProg 64 :=
.seq loopBody252_59 loopBody252_65

def loopBody252_67 : HolLoopProg 64 :=
.mark loopBody252_66

def loopBody252_68 : HolLoopProg 64 :=
.seq loopBody252_57 loopBody252_67

def loopBody252_69 : HolLoopProg 64 :=
.mark loopBody252_68

def loopBody252_70 : HolLoopProg 64 :=
.seq loopBody252_55 loopBody252_69

def loopBody252_71 : HolLoopProg 64 :=
.mark loopBody252_70

def loopBody252_72 : HolLoopProg 64 :=
.seq loopBody252_53 loopBody252_71

def loopBody252_73 : HolLoopProg 64 :=
.mark loopBody252_72

def loopBody252_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 3)

def loopBody252_75 : HolLoopProg 64 :=
.mark loopBody252_74

def loopBody252_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 4)

def loopBody252_77 : HolLoopProg 64 :=
.mark loopBody252_76

def loopBody252_78 : HolLoopProg 64 :=
.call (some ([7], Flapjack.Spt.ls PUnit.unit)) (some 311) ([8, 9, 10, 11, 12, 13]) (some (8, loopBody252_61, loopBody252_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody252_79 : HolLoopProg 64 :=
.mark loopBody252_78

def loopBody252_80 : HolLoopProg 64 :=
.seq loopBody252_79 loopBody252_1

def loopBody252_81 : HolLoopProg 64 :=
.mark loopBody252_80

def loopBody252_82 : HolLoopProg 64 :=
.seq loopBody252_77 loopBody252_81

def loopBody252_83 : HolLoopProg 64 :=
.mark loopBody252_82

def loopBody252_84 : HolLoopProg 64 :=
.seq loopBody252_75 loopBody252_83

def loopBody252_85 : HolLoopProg 64 :=
.mark loopBody252_84

def loopBody252_86 : HolLoopProg 64 :=
.seq loopBody252_59 loopBody252_85

def loopBody252_87 : HolLoopProg 64 :=
.mark loopBody252_86

def loopBody252_88 : HolLoopProg 64 :=
.seq loopBody252_57 loopBody252_87

def loopBody252_89 : HolLoopProg 64 :=
.mark loopBody252_88

def loopBody252_90 : HolLoopProg 64 :=
.seq loopBody252_55 loopBody252_89

def loopBody252_91 : HolLoopProg 64 :=
.mark loopBody252_90

def loopBody252_92 : HolLoopProg 64 :=
.seq loopBody252_53 loopBody252_91

def loopBody252_93 : HolLoopProg 64 :=
.mark loopBody252_92

def loopBody252_94 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 17 (Flapjack.RegImm.imm 0#64) loopBody252_73 loopBody252_93 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody252_95 : HolLoopProg 64 :=
.mark loopBody252_94

def loopBody252_96 : HolLoopProg 64 :=
.seq loopBody252_95 loopBody252_1

def loopBody252_97 : HolLoopProg 64 :=
.mark loopBody252_96

def loopBody252_98 : HolLoopProg 64 :=
.seq loopBody252_51 loopBody252_97

def loopBody252_99 : HolLoopProg 64 :=
.mark loopBody252_98

def loopBody252_100 : HolLoopProg 64 :=
.seq loopBody252_49 loopBody252_99

def loopBody252_101 : HolLoopProg 64 :=
.mark loopBody252_100

def loopBody252_102 : HolLoopProg 64 :=
.seq loopBody252_45 loopBody252_101

def loopBody252_103 : HolLoopProg 64 :=
.mark loopBody252_102

def loopBody252_104 : HolLoopProg 64 :=
.seq loopBody252_43 loopBody252_103

def loopBody252_105 : HolLoopProg 64 :=
.mark loopBody252_104

def loopBody252_106 : HolLoopProg 64 :=
.seq loopBody252_41 loopBody252_105

def loopBody252_107 : HolLoopProg 64 :=
.mark loopBody252_106

def loopBody252_108 : HolLoopProg 64 :=
.seq loopBody252_35 loopBody252_107

def loopBody252_109 : HolLoopProg 64 :=
.mark loopBody252_108

def loopBody252_110 : HolLoopProg 64 :=
.seq loopBody252_33 loopBody252_109

def loopBody252_111 : HolLoopProg 64 :=
.mark loopBody252_110

def loopBody252_112 : HolLoopProg 64 :=
.seq loopBody252_31 loopBody252_111

def loopBody252_113 : HolLoopProg 64 :=
.mark loopBody252_112

def loopBody252_114 : HolLoopProg 64 :=
.seq loopBody252_25 loopBody252_113

def loopBody252_115 : HolLoopProg 64 :=
.mark loopBody252_114

def loopBody252_116 : HolLoopProg 64 :=
.seq loopBody252_23 loopBody252_115

def loopBody252_117 : HolLoopProg 64 :=
.mark loopBody252_116

def loopBody252_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64])

def loopBody252_119 : HolLoopProg 64 :=
.mark loopBody252_118

def loopBody252_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody252_121 : HolLoopProg 64 :=
.mark loopBody252_120

def loopBody252_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 9)

def loopBody252_123 : HolLoopProg 64 :=
.mark loopBody252_122

def loopBody252_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 8) 10

def loopBody252_125 : HolLoopProg 64 :=
.mark loopBody252_124

def loopBody252_126 : HolLoopProg 64 :=
.seq loopBody252_125 loopBody252_1

def loopBody252_127 : HolLoopProg 64 :=
.mark loopBody252_126

def loopBody252_128 : HolLoopProg 64 :=
.seq loopBody252_123 loopBody252_127

def loopBody252_129 : HolLoopProg 64 :=
.mark loopBody252_128

def loopBody252_130 : HolLoopProg 64 :=
.seq loopBody252_129 loopBody252_1

def loopBody252_131 : HolLoopProg 64 :=
.mark loopBody252_130

def loopBody252_132 : HolLoopProg 64 :=
.seq loopBody252_121 loopBody252_131

def loopBody252_133 : HolLoopProg 64 :=
.mark loopBody252_132

def loopBody252_134 : HolLoopProg 64 :=
.seq loopBody252_1 loopBody252_133

def loopBody252_135 : HolLoopProg 64 :=
.mark loopBody252_134

def loopBody252_136 : HolLoopProg 64 :=
.seq loopBody252_119 loopBody252_135

def loopBody252_137 : HolLoopProg 64 :=
.mark loopBody252_136

def loopBody252_138 : HolLoopProg 64 :=
.seq loopBody252_1 loopBody252_137

def loopBody252_139 : HolLoopProg 64 :=
.mark loopBody252_138

def loopBody252_140 : HolLoopProg 64 :=
.seq loopBody252_117 loopBody252_139

def loopBody252_141 : HolLoopProg 64 :=
.mark loopBody252_140

def loopBody252_142 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody252_143 : HolLoopProg 64 :=
.mark loopBody252_142

def loopBody252_144 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [8]

def loopBody252_145 : HolLoopProg 64 :=
.mark loopBody252_144

def loopBody252_146 : HolLoopProg 64 :=
.seq loopBody252_145 loopBody252_1

def loopBody252_147 : HolLoopProg 64 :=
.mark loopBody252_146

def loopBody252_148 : HolLoopProg 64 :=
.seq loopBody252_143 loopBody252_147

def loopBody252_149 : HolLoopProg 64 :=
.mark loopBody252_148

def loopBody252_150 : HolLoopProg 64 :=
.seq loopBody252_141 loopBody252_149

def loopBody252_151 : HolLoopProg 64 :=
.mark loopBody252_150

def loopBody252_152 : HolLoopProg 64 :=
.seq loopBody252_21 loopBody252_151

def loopBody252_153 : HolLoopProg 64 :=
.mark loopBody252_152

def loopBody252_154 : HolLoopProg 64 :=
.seq loopBody252_1 loopBody252_153

def loopBody252_155 : HolLoopProg 64 :=
.mark loopBody252_154

def loopBody252_156 : HolLoopProg 64 :=
.seq loopBody252_19 loopBody252_155

def loopBody252_157 : HolLoopProg 64 :=
.mark loopBody252_156

def loopBody252_158 : HolLoopProg 64 :=
.seq loopBody252_1 loopBody252_157

def loopBody252_159 : HolLoopProg 64 :=
.mark loopBody252_158

def loopBody252_160 : HolLoopProg 64 :=
.seq loopBody252_1 loopBody252_159

def loopBody252_161 : HolLoopProg 64 :=
.mark loopBody252_160

def loopBody252_162 : HolLoopProg 64 :=
.seq loopBody252_1 loopBody252_161

def loopBody252_163 : HolLoopProg 64 :=
.mark loopBody252_162

def loopBody252_164 : HolLoopProg 64 :=
.seq loopBody252_1 loopBody252_163

def loopBody252_165 : HolLoopProg 64 :=
.mark loopBody252_164

def output252 : Nat × List Nat × HolLoopProg 64 :=
  (316, [0, 1, 2, 3, 4], loopBody252_165)
end InitECandidate.Proofs.FrontendStages.Loop
