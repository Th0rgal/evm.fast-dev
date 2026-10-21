import InitECandidate.Proofs.FrontendStages.Loop.Translate635
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody651_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 1#64])

def loopBody651_1 : HolLoopProg 64 :=
.mark loopBody651_0

def loopBody651_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody651_3 : HolLoopProg 64 :=
.mark loopBody651_2

def loopBody651_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody651_5 : HolLoopProg 64 :=
.mark loopBody651_4

def loopBody651_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody651_7 : HolLoopProg 64 :=
.mark loopBody651_6

def loopBody651_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 7 (Flapjack.RegImm.reg 8) loopBody651_5 loopBody651_7 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody651_9 : HolLoopProg 64 :=
.mark loopBody651_8

def loopBody651_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody651_11 : HolLoopProg 64 :=
.mark loopBody651_10

def loopBody651_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody651_13 : HolLoopProg 64 :=
.mark loopBody651_12

def loopBody651_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody651_15 : HolLoopProg 64 :=
.mark loopBody651_14

def loopBody651_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody651_17 : HolLoopProg 64 :=
.mark loopBody651_16

def loopBody651_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 3)

def loopBody651_19 : HolLoopProg 64 :=
.mark loopBody651_18

def loopBody651_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 4)

def loopBody651_21 : HolLoopProg 64 :=
.mark loopBody651_20

def loopBody651_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 5)

def loopBody651_23 : HolLoopProg 64 :=
.mark loopBody651_22

def loopBody651_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 714) [6, 7, 8, 9, 10, 11] none

def loopBody651_25 : HolLoopProg 64 :=
.mark loopBody651_24

def loopBody651_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody651_27 : HolLoopProg 64 :=
.mark loopBody651_26

def loopBody651_28 : HolLoopProg 64 :=
.seq loopBody651_25 loopBody651_27

def loopBody651_29 : HolLoopProg 64 :=
.mark loopBody651_28

def loopBody651_30 : HolLoopProg 64 :=
.seq loopBody651_23 loopBody651_29

def loopBody651_31 : HolLoopProg 64 :=
.mark loopBody651_30

def loopBody651_32 : HolLoopProg 64 :=
.seq loopBody651_21 loopBody651_31

def loopBody651_33 : HolLoopProg 64 :=
.mark loopBody651_32

def loopBody651_34 : HolLoopProg 64 :=
.seq loopBody651_19 loopBody651_33

def loopBody651_35 : HolLoopProg 64 :=
.mark loopBody651_34

def loopBody651_36 : HolLoopProg 64 :=
.seq loopBody651_17 loopBody651_35

def loopBody651_37 : HolLoopProg 64 :=
.mark loopBody651_36

def loopBody651_38 : HolLoopProg 64 :=
.seq loopBody651_15 loopBody651_37

def loopBody651_39 : HolLoopProg 64 :=
.mark loopBody651_38

def loopBody651_40 : HolLoopProg 64 :=
.seq loopBody651_13 loopBody651_39

def loopBody651_41 : HolLoopProg 64 :=
.mark loopBody651_40

def loopBody651_42 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody651_41 loopBody651_27 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody651_43 : HolLoopProg 64 :=
.mark loopBody651_42

def loopBody651_44 : HolLoopProg 64 :=
.seq loopBody651_43 loopBody651_27

def loopBody651_45 : HolLoopProg 64 :=
.mark loopBody651_44

def loopBody651_46 : HolLoopProg 64 :=
.seq loopBody651_11 loopBody651_45

def loopBody651_47 : HolLoopProg 64 :=
.mark loopBody651_46

def loopBody651_48 : HolLoopProg 64 :=
.seq loopBody651_9 loopBody651_47

def loopBody651_49 : HolLoopProg 64 :=
.mark loopBody651_48

def loopBody651_50 : HolLoopProg 64 :=
.seq loopBody651_3 loopBody651_49

def loopBody651_51 : HolLoopProg 64 :=
.mark loopBody651_50

def loopBody651_52 : HolLoopProg 64 :=
.seq loopBody651_1 loopBody651_51

def loopBody651_53 : HolLoopProg 64 :=
.mark loopBody651_52

def loopBody651_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 0)

def loopBody651_55 : HolLoopProg 64 :=
.mark loopBody651_54

def loopBody651_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 1)

def loopBody651_57 : HolLoopProg 64 :=
.mark loopBody651_56

def loopBody651_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 2)

def loopBody651_59 : HolLoopProg 64 :=
.mark loopBody651_58

def loopBody651_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 3)

def loopBody651_61 : HolLoopProg 64 :=
.mark loopBody651_60

def loopBody651_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 4)

def loopBody651_63 : HolLoopProg 64 :=
.mark loopBody651_62

def loopBody651_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 5)

def loopBody651_65 : HolLoopProg 64 :=
.mark loopBody651_64

def loopBody651_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.const 13402431016077863595#64)

def loopBody651_67 : HolLoopProg 64 :=
.mark loopBody651_66

def loopBody651_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.const 2210141511517208575#64)

def loopBody651_69 : HolLoopProg 64 :=
.mark loopBody651_68

def loopBody651_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 21 (Flapjack.HolLoopExp.const 7435674573564081700#64)

def loopBody651_71 : HolLoopProg 64 :=
.mark loopBody651_70

def loopBody651_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22 (Flapjack.HolLoopExp.const 7239337960414712511#64)

def loopBody651_73 : HolLoopProg 64 :=
.mark loopBody651_72

def loopBody651_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 23 (Flapjack.HolLoopExp.const 5412103778470702295#64)

def loopBody651_75 : HolLoopProg 64 :=
.mark loopBody651_74

def loopBody651_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 24 (Flapjack.HolLoopExp.const 1873798617647539866#64)

def loopBody651_77 : HolLoopProg 64 :=
.mark loopBody651_76

def loopBody651_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 13

def loopBody651_79 : HolLoopProg 64 :=
.mark loopBody651_78

def loopBody651_80 : HolLoopProg 64 :=
.call (some ([6, 7, 8, 9, 10, 11, 12], Flapjack.Spt.ln)) (some 704) ([13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]) (some (13, loopBody651_79, loopBody651_27, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))))

def loopBody651_81 : HolLoopProg 64 :=
.mark loopBody651_80

def loopBody651_82 : HolLoopProg 64 :=
.seq loopBody651_81 loopBody651_27

def loopBody651_83 : HolLoopProg 64 :=
.mark loopBody651_82

def loopBody651_84 : HolLoopProg 64 :=
.seq loopBody651_77 loopBody651_83

def loopBody651_85 : HolLoopProg 64 :=
.mark loopBody651_84

def loopBody651_86 : HolLoopProg 64 :=
.seq loopBody651_75 loopBody651_85

def loopBody651_87 : HolLoopProg 64 :=
.mark loopBody651_86

def loopBody651_88 : HolLoopProg 64 :=
.seq loopBody651_73 loopBody651_87

def loopBody651_89 : HolLoopProg 64 :=
.mark loopBody651_88

def loopBody651_90 : HolLoopProg 64 :=
.seq loopBody651_71 loopBody651_89

def loopBody651_91 : HolLoopProg 64 :=
.mark loopBody651_90

def loopBody651_92 : HolLoopProg 64 :=
.seq loopBody651_69 loopBody651_91

def loopBody651_93 : HolLoopProg 64 :=
.mark loopBody651_92

def loopBody651_94 : HolLoopProg 64 :=
.seq loopBody651_67 loopBody651_93

def loopBody651_95 : HolLoopProg 64 :=
.mark loopBody651_94

def loopBody651_96 : HolLoopProg 64 :=
.seq loopBody651_65 loopBody651_95

def loopBody651_97 : HolLoopProg 64 :=
.mark loopBody651_96

def loopBody651_98 : HolLoopProg 64 :=
.seq loopBody651_63 loopBody651_97

def loopBody651_99 : HolLoopProg 64 :=
.mark loopBody651_98

def loopBody651_100 : HolLoopProg 64 :=
.seq loopBody651_61 loopBody651_99

def loopBody651_101 : HolLoopProg 64 :=
.mark loopBody651_100

def loopBody651_102 : HolLoopProg 64 :=
.seq loopBody651_59 loopBody651_101

def loopBody651_103 : HolLoopProg 64 :=
.mark loopBody651_102

def loopBody651_104 : HolLoopProg 64 :=
.seq loopBody651_57 loopBody651_103

def loopBody651_105 : HolLoopProg 64 :=
.mark loopBody651_104

def loopBody651_106 : HolLoopProg 64 :=
.seq loopBody651_55 loopBody651_105

def loopBody651_107 : HolLoopProg 64 :=
.mark loopBody651_106

def loopBody651_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 6) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 7) (Flapjack.HolLoopExp.const 63#64)])

def loopBody651_109 : HolLoopProg 64 :=
.mark loopBody651_108

def loopBody651_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 7) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 8) (Flapjack.HolLoopExp.const 63#64)])

def loopBody651_111 : HolLoopProg 64 :=
.mark loopBody651_110

def loopBody651_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 8) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 9) (Flapjack.HolLoopExp.const 63#64)])

def loopBody651_113 : HolLoopProg 64 :=
.mark loopBody651_112

def loopBody651_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 9) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 10) (Flapjack.HolLoopExp.const 63#64)])

def loopBody651_115 : HolLoopProg 64 :=
.mark loopBody651_114

def loopBody651_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 10) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 11) (Flapjack.HolLoopExp.const 63#64)])

def loopBody651_117 : HolLoopProg 64 :=
.mark loopBody651_116

def loopBody651_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 11) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 12) (Flapjack.HolLoopExp.const 63#64)])

def loopBody651_119 : HolLoopProg 64 :=
.mark loopBody651_118

def loopBody651_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [13, 14, 15, 16, 17, 18]

def loopBody651_121 : HolLoopProg 64 :=
.mark loopBody651_120

def loopBody651_122 : HolLoopProg 64 :=
.seq loopBody651_121 loopBody651_27

def loopBody651_123 : HolLoopProg 64 :=
.mark loopBody651_122

def loopBody651_124 : HolLoopProg 64 :=
.seq loopBody651_119 loopBody651_123

def loopBody651_125 : HolLoopProg 64 :=
.mark loopBody651_124

def loopBody651_126 : HolLoopProg 64 :=
.seq loopBody651_117 loopBody651_125

def loopBody651_127 : HolLoopProg 64 :=
.mark loopBody651_126

def loopBody651_128 : HolLoopProg 64 :=
.seq loopBody651_115 loopBody651_127

def loopBody651_129 : HolLoopProg 64 :=
.mark loopBody651_128

def loopBody651_130 : HolLoopProg 64 :=
.seq loopBody651_113 loopBody651_129

def loopBody651_131 : HolLoopProg 64 :=
.mark loopBody651_130

def loopBody651_132 : HolLoopProg 64 :=
.seq loopBody651_111 loopBody651_131

def loopBody651_133 : HolLoopProg 64 :=
.mark loopBody651_132

def loopBody651_134 : HolLoopProg 64 :=
.seq loopBody651_109 loopBody651_133

def loopBody651_135 : HolLoopProg 64 :=
.mark loopBody651_134

def loopBody651_136 : HolLoopProg 64 :=
.seq loopBody651_107 loopBody651_135

def loopBody651_137 : HolLoopProg 64 :=
.mark loopBody651_136

def loopBody651_138 : HolLoopProg 64 :=
.seq loopBody651_27 loopBody651_137

def loopBody651_139 : HolLoopProg 64 :=
.mark loopBody651_138

def loopBody651_140 : HolLoopProg 64 :=
.seq loopBody651_27 loopBody651_139

def loopBody651_141 : HolLoopProg 64 :=
.mark loopBody651_140

def loopBody651_142 : HolLoopProg 64 :=
.seq loopBody651_27 loopBody651_141

def loopBody651_143 : HolLoopProg 64 :=
.mark loopBody651_142

def loopBody651_144 : HolLoopProg 64 :=
.seq loopBody651_27 loopBody651_143

def loopBody651_145 : HolLoopProg 64 :=
.mark loopBody651_144

def loopBody651_146 : HolLoopProg 64 :=
.seq loopBody651_27 loopBody651_145

def loopBody651_147 : HolLoopProg 64 :=
.mark loopBody651_146

def loopBody651_148 : HolLoopProg 64 :=
.seq loopBody651_27 loopBody651_147

def loopBody651_149 : HolLoopProg 64 :=
.mark loopBody651_148

def loopBody651_150 : HolLoopProg 64 :=
.seq loopBody651_27 loopBody651_149

def loopBody651_151 : HolLoopProg 64 :=
.mark loopBody651_150

def loopBody651_152 : HolLoopProg 64 :=
.seq loopBody651_27 loopBody651_151

def loopBody651_153 : HolLoopProg 64 :=
.mark loopBody651_152

def loopBody651_154 : HolLoopProg 64 :=
.seq loopBody651_27 loopBody651_153

def loopBody651_155 : HolLoopProg 64 :=
.mark loopBody651_154

def loopBody651_156 : HolLoopProg 64 :=
.seq loopBody651_27 loopBody651_155

def loopBody651_157 : HolLoopProg 64 :=
.mark loopBody651_156

def loopBody651_158 : HolLoopProg 64 :=
.seq loopBody651_27 loopBody651_157

def loopBody651_159 : HolLoopProg 64 :=
.mark loopBody651_158

def loopBody651_160 : HolLoopProg 64 :=
.seq loopBody651_27 loopBody651_159

def loopBody651_161 : HolLoopProg 64 :=
.mark loopBody651_160

def loopBody651_162 : HolLoopProg 64 :=
.seq loopBody651_27 loopBody651_161

def loopBody651_163 : HolLoopProg 64 :=
.mark loopBody651_162

def loopBody651_164 : HolLoopProg 64 :=
.seq loopBody651_27 loopBody651_163

def loopBody651_165 : HolLoopProg 64 :=
.mark loopBody651_164

def loopBody651_166 : HolLoopProg 64 :=
.seq loopBody651_53 loopBody651_165

def loopBody651_167 : HolLoopProg 64 :=
.mark loopBody651_166

def output651 : Nat × List Nat × HolLoopProg 64 :=
  (715, [0, 1, 2, 3, 4, 5], loopBody651_167)
end InitECandidate.Proofs.FrontendStages.Loop
