import InitECandidate.Proofs.FrontendStages.Loop.Translate384
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody400_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody400_1 : HolLoopProg 64 :=
.mark loopBody400_0

def loopBody400_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 23#64)

def loopBody400_3 : HolLoopProg 64 :=
.mark loopBody400_2

def loopBody400_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody400_5 : HolLoopProg 64 :=
.mark loopBody400_4

def loopBody400_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody400_7 : HolLoopProg 64 :=
.mark loopBody400_6

def loopBody400_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 3 (Flapjack.RegImm.reg 4) loopBody400_5 loopBody400_7 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody400_9 : HolLoopProg 64 :=
.mark loopBody400_8

def loopBody400_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody400_11 : HolLoopProg 64 :=
.mark loopBody400_10

def loopBody400_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody400_13 : HolLoopProg 64 :=
.mark loopBody400_12

def loopBody400_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody400_15 : HolLoopProg 64 :=
.mark loopBody400_14

def loopBody400_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody400_17 : HolLoopProg 64 :=
.mark loopBody400_16

def loopBody400_18 : HolLoopProg 64 :=
.seq loopBody400_15 loopBody400_17

def loopBody400_19 : HolLoopProg 64 :=
.mark loopBody400_18

def loopBody400_20 : HolLoopProg 64 :=
.seq loopBody400_13 loopBody400_19

def loopBody400_21 : HolLoopProg 64 :=
.mark loopBody400_20

def loopBody400_22 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody400_21 loopBody400_17 (Flapjack.Spt.ls PUnit.unit)

def loopBody400_23 : HolLoopProg 64 :=
.mark loopBody400_22

def loopBody400_24 : HolLoopProg 64 :=
.seq loopBody400_23 loopBody400_17

def loopBody400_25 : HolLoopProg 64 :=
.mark loopBody400_24

def loopBody400_26 : HolLoopProg 64 :=
.seq loopBody400_11 loopBody400_25

def loopBody400_27 : HolLoopProg 64 :=
.mark loopBody400_26

def loopBody400_28 : HolLoopProg 64 :=
.seq loopBody400_9 loopBody400_27

def loopBody400_29 : HolLoopProg 64 :=
.mark loopBody400_28

def loopBody400_30 : HolLoopProg 64 :=
.seq loopBody400_3 loopBody400_29

def loopBody400_31 : HolLoopProg 64 :=
.mark loopBody400_30

def loopBody400_32 : HolLoopProg 64 :=
.seq loopBody400_1 loopBody400_31

def loopBody400_33 : HolLoopProg 64 :=
.mark loopBody400_32

def loopBody400_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody400_35 : HolLoopProg 64 :=
.mark loopBody400_34

def loopBody400_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 2 2

def loopBody400_37 : HolLoopProg 64 :=
.mark loopBody400_36

def loopBody400_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody400_39 : HolLoopProg 64 :=
.mark loopBody400_38

def loopBody400_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 239#64)

def loopBody400_41 : HolLoopProg 64 :=
.mark loopBody400_40

def loopBody400_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody400_43 : HolLoopProg 64 :=
.mark loopBody400_42

def loopBody400_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody400_45 : HolLoopProg 64 :=
.mark loopBody400_44

def loopBody400_46 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.RegImm.reg 5) loopBody400_43 loopBody400_45 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)

def loopBody400_47 : HolLoopProg 64 :=
.mark loopBody400_46

def loopBody400_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody400_49 : HolLoopProg 64 :=
.mark loopBody400_48

def loopBody400_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 4)

def loopBody400_51 : HolLoopProg 64 :=
.mark loopBody400_50

def loopBody400_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody400_53 : HolLoopProg 64 :=
.mark loopBody400_52

def loopBody400_54 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.reg 8) loopBody400_53 loopBody400_49 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody400_55 : HolLoopProg 64 :=
.mark loopBody400_54

def loopBody400_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 1#64])

def loopBody400_57 : HolLoopProg 64 :=
.mark loopBody400_56

def loopBody400_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 9 9

def loopBody400_59 : HolLoopProg 64 :=
.mark loopBody400_58

def loopBody400_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody400_61 : HolLoopProg 64 :=
.mark loopBody400_60

def loopBody400_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody400_63 : HolLoopProg 64 :=
.mark loopBody400_62

def loopBody400_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 1#64)

def loopBody400_65 : HolLoopProg 64 :=
.mark loopBody400_64

def loopBody400_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody400_67 : HolLoopProg 64 :=
.mark loopBody400_66

def loopBody400_68 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 11 (Flapjack.RegImm.reg 12) loopBody400_65 loopBody400_67 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))

def loopBody400_69 : HolLoopProg 64 :=
.mark loopBody400_68

def loopBody400_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 0#64)

def loopBody400_71 : HolLoopProg 64 :=
.mark loopBody400_70

def loopBody400_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 11)

def loopBody400_73 : HolLoopProg 64 :=
.mark loopBody400_72

def loopBody400_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 1#64)

def loopBody400_75 : HolLoopProg 64 :=
.mark loopBody400_74

def loopBody400_76 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.RegImm.reg 15) loopBody400_75 loopBody400_71 (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
  PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody400_77 : HolLoopProg 64 :=
.mark loopBody400_76

def loopBody400_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 2#64])

def loopBody400_79 : HolLoopProg 64 :=
.mark loopBody400_78

def loopBody400_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 16 16

def loopBody400_81 : HolLoopProg 64 :=
.mark loopBody400_80

def loopBody400_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 16)

def loopBody400_83 : HolLoopProg 64 :=
.mark loopBody400_82

def loopBody400_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.const 0#64)

def loopBody400_85 : HolLoopProg 64 :=
.mark loopBody400_84

def loopBody400_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.const 1#64)

def loopBody400_87 : HolLoopProg 64 :=
.mark loopBody400_86

def loopBody400_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.const 0#64)

def loopBody400_89 : HolLoopProg 64 :=
.mark loopBody400_88

def loopBody400_90 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 18 (Flapjack.RegImm.reg 19) loopBody400_87 loopBody400_89 (Flapjack.Spt.bn
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    Flapjack.Spt.ln)
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody400_91 : HolLoopProg 64 :=
.mark loopBody400_90

def loopBody400_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 21 (Flapjack.HolLoopExp.const 0#64)

def loopBody400_93 : HolLoopProg 64 :=
.mark loopBody400_92

def loopBody400_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22 (Flapjack.HolLoopExp.var 18)

def loopBody400_95 : HolLoopProg 64 :=
.mark loopBody400_94

def loopBody400_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 21 (Flapjack.HolLoopExp.const 1#64)

def loopBody400_97 : HolLoopProg 64 :=
.mark loopBody400_96

def loopBody400_98 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 21 (Flapjack.RegImm.reg 22) loopBody400_97 loopBody400_93 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody400_99 : HolLoopProg 64 :=
.mark loopBody400_98

def loopBody400_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 23
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and
    [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.var 14, Flapjack.HolLoopExp.var 21])

def loopBody400_101 : HolLoopProg 64 :=
.mark loopBody400_100

def loopBody400_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody400_103 : HolLoopProg 64 :=
.mark loopBody400_102

def loopBody400_104 : HolLoopProg 64 :=
.seq loopBody400_103 loopBody400_19

def loopBody400_105 : HolLoopProg 64 :=
.mark loopBody400_104

def loopBody400_106 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 23 (Flapjack.RegImm.imm 0#64) loopBody400_105 loopBody400_17 (Flapjack.Spt.ln)

def loopBody400_107 : HolLoopProg 64 :=
.mark loopBody400_106

def loopBody400_108 : HolLoopProg 64 :=
.seq loopBody400_107 loopBody400_17

def loopBody400_109 : HolLoopProg 64 :=
.mark loopBody400_108

def loopBody400_110 : HolLoopProg 64 :=
.seq loopBody400_101 loopBody400_109

def loopBody400_111 : HolLoopProg 64 :=
.mark loopBody400_110

def loopBody400_112 : HolLoopProg 64 :=
.seq loopBody400_99 loopBody400_111

def loopBody400_113 : HolLoopProg 64 :=
.mark loopBody400_112

def loopBody400_114 : HolLoopProg 64 :=
.seq loopBody400_95 loopBody400_113

def loopBody400_115 : HolLoopProg 64 :=
.mark loopBody400_114

def loopBody400_116 : HolLoopProg 64 :=
.seq loopBody400_93 loopBody400_115

def loopBody400_117 : HolLoopProg 64 :=
.mark loopBody400_116

def loopBody400_118 : HolLoopProg 64 :=
.seq loopBody400_91 loopBody400_117

def loopBody400_119 : HolLoopProg 64 :=
.mark loopBody400_118

def loopBody400_120 : HolLoopProg 64 :=
.seq loopBody400_85 loopBody400_119

def loopBody400_121 : HolLoopProg 64 :=
.mark loopBody400_120

def loopBody400_122 : HolLoopProg 64 :=
.seq loopBody400_83 loopBody400_121

def loopBody400_123 : HolLoopProg 64 :=
.mark loopBody400_122

def loopBody400_124 : HolLoopProg 64 :=
.seq loopBody400_81 loopBody400_123

def loopBody400_125 : HolLoopProg 64 :=
.mark loopBody400_124

def loopBody400_126 : HolLoopProg 64 :=
.seq loopBody400_79 loopBody400_125

def loopBody400_127 : HolLoopProg 64 :=
.mark loopBody400_126

def loopBody400_128 : HolLoopProg 64 :=
.seq loopBody400_77 loopBody400_127

def loopBody400_129 : HolLoopProg 64 :=
.mark loopBody400_128

def loopBody400_130 : HolLoopProg 64 :=
.seq loopBody400_73 loopBody400_129

def loopBody400_131 : HolLoopProg 64 :=
.mark loopBody400_130

def loopBody400_132 : HolLoopProg 64 :=
.seq loopBody400_71 loopBody400_131

def loopBody400_133 : HolLoopProg 64 :=
.mark loopBody400_132

def loopBody400_134 : HolLoopProg 64 :=
.seq loopBody400_69 loopBody400_133

def loopBody400_135 : HolLoopProg 64 :=
.mark loopBody400_134

def loopBody400_136 : HolLoopProg 64 :=
.seq loopBody400_63 loopBody400_135

def loopBody400_137 : HolLoopProg 64 :=
.mark loopBody400_136

def loopBody400_138 : HolLoopProg 64 :=
.seq loopBody400_61 loopBody400_137

def loopBody400_139 : HolLoopProg 64 :=
.mark loopBody400_138

def loopBody400_140 : HolLoopProg 64 :=
.seq loopBody400_59 loopBody400_139

def loopBody400_141 : HolLoopProg 64 :=
.mark loopBody400_140

def loopBody400_142 : HolLoopProg 64 :=
.seq loopBody400_57 loopBody400_141

def loopBody400_143 : HolLoopProg 64 :=
.mark loopBody400_142

def loopBody400_144 : HolLoopProg 64 :=
.seq loopBody400_55 loopBody400_143

def loopBody400_145 : HolLoopProg 64 :=
.mark loopBody400_144

def loopBody400_146 : HolLoopProg 64 :=
.seq loopBody400_51 loopBody400_145

def loopBody400_147 : HolLoopProg 64 :=
.mark loopBody400_146

def loopBody400_148 : HolLoopProg 64 :=
.seq loopBody400_49 loopBody400_147

def loopBody400_149 : HolLoopProg 64 :=
.mark loopBody400_148

def loopBody400_150 : HolLoopProg 64 :=
.seq loopBody400_47 loopBody400_149

def loopBody400_151 : HolLoopProg 64 :=
.mark loopBody400_150

def loopBody400_152 : HolLoopProg 64 :=
.seq loopBody400_41 loopBody400_151

def loopBody400_153 : HolLoopProg 64 :=
.mark loopBody400_152

def loopBody400_154 : HolLoopProg 64 :=
.seq loopBody400_39 loopBody400_153

def loopBody400_155 : HolLoopProg 64 :=
.mark loopBody400_154

def loopBody400_156 : HolLoopProg 64 :=
.seq loopBody400_37 loopBody400_155

def loopBody400_157 : HolLoopProg 64 :=
.mark loopBody400_156

def loopBody400_158 : HolLoopProg 64 :=
.seq loopBody400_35 loopBody400_157

def loopBody400_159 : HolLoopProg 64 :=
.mark loopBody400_158

def loopBody400_160 : HolLoopProg 64 :=
.seq loopBody400_33 loopBody400_159

def loopBody400_161 : HolLoopProg 64 :=
.mark loopBody400_160

def loopBody400_162 : HolLoopProg 64 :=
.seq loopBody400_161 loopBody400_21

def loopBody400_163 : HolLoopProg 64 :=
.mark loopBody400_162

def output400 : Nat × List Nat × HolLoopProg 64 :=
  (464, [0, 1], loopBody400_163)
end InitECandidate.Proofs.FrontendStages.Loop
