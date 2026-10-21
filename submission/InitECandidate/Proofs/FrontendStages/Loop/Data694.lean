import InitECandidate.Proofs.FrontendStages.Loop.Translate678
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody694_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody694_1 : HolLoopProg 64 :=
.mark loopBody694_0

def loopBody694_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody694_3 : HolLoopProg 64 :=
.mark loopBody694_2

def loopBody694_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody694_5 : HolLoopProg 64 :=
.mark loopBody694_4

def loopBody694_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody694_7 : HolLoopProg 64 :=
.mark loopBody694_6

def loopBody694_8 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 734) ([3, 4]) (some (3, loopBody694_7, loopBody694_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody694_9 : HolLoopProg 64 :=
.mark loopBody694_8

def loopBody694_10 : HolLoopProg 64 :=
.seq loopBody694_9 loopBody694_1

def loopBody694_11 : HolLoopProg 64 :=
.mark loopBody694_10

def loopBody694_12 : HolLoopProg 64 :=
.seq loopBody694_5 loopBody694_11

def loopBody694_13 : HolLoopProg 64 :=
.mark loopBody694_12

def loopBody694_14 : HolLoopProg 64 :=
.seq loopBody694_3 loopBody694_13

def loopBody694_15 : HolLoopProg 64 :=
.mark loopBody694_14

def loopBody694_16 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_15

def loopBody694_17 : HolLoopProg 64 :=
.mark loopBody694_16

def loopBody694_18 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_17

def loopBody694_19 : HolLoopProg 64 :=
.mark loopBody694_18

def loopBody694_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 96#64])

def loopBody694_21 : HolLoopProg 64 :=
.mark loopBody694_20

def loopBody694_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 96#64])

def loopBody694_23 : HolLoopProg 64 :=
.mark loopBody694_22

def loopBody694_24 : HolLoopProg 64 :=
.seq loopBody694_23 loopBody694_11

def loopBody694_25 : HolLoopProg 64 :=
.mark loopBody694_24

def loopBody694_26 : HolLoopProg 64 :=
.seq loopBody694_21 loopBody694_25

def loopBody694_27 : HolLoopProg 64 :=
.mark loopBody694_26

def loopBody694_28 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_27

def loopBody694_29 : HolLoopProg 64 :=
.mark loopBody694_28

def loopBody694_30 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_29

def loopBody694_31 : HolLoopProg 64 :=
.mark loopBody694_30

def loopBody694_32 : HolLoopProg 64 :=
.seq loopBody694_19 loopBody694_31

def loopBody694_33 : HolLoopProg 64 :=
.mark loopBody694_32

def loopBody694_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 96#64])

def loopBody694_35 : HolLoopProg 64 :=
.mark loopBody694_34

def loopBody694_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 392#64]),
      Flapjack.HolLoopExp.const 960#64])

def loopBody694_37 : HolLoopProg 64 :=
.mark loopBody694_36

def loopBody694_38 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 735) ([3, 4, 5]) (some (3, loopBody694_7, loopBody694_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody694_39 : HolLoopProg 64 :=
.mark loopBody694_38

def loopBody694_40 : HolLoopProg 64 :=
.seq loopBody694_39 loopBody694_1

def loopBody694_41 : HolLoopProg 64 :=
.mark loopBody694_40

def loopBody694_42 : HolLoopProg 64 :=
.seq loopBody694_37 loopBody694_41

def loopBody694_43 : HolLoopProg 64 :=
.mark loopBody694_42

def loopBody694_44 : HolLoopProg 64 :=
.seq loopBody694_35 loopBody694_43

def loopBody694_45 : HolLoopProg 64 :=
.mark loopBody694_44

def loopBody694_46 : HolLoopProg 64 :=
.seq loopBody694_21 loopBody694_45

def loopBody694_47 : HolLoopProg 64 :=
.mark loopBody694_46

def loopBody694_48 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_47

def loopBody694_49 : HolLoopProg 64 :=
.mark loopBody694_48

def loopBody694_50 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_49

def loopBody694_51 : HolLoopProg 64 :=
.mark loopBody694_50

def loopBody694_52 : HolLoopProg 64 :=
.seq loopBody694_33 loopBody694_51

def loopBody694_53 : HolLoopProg 64 :=
.mark loopBody694_52

def loopBody694_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 192#64])

def loopBody694_55 : HolLoopProg 64 :=
.mark loopBody694_54

def loopBody694_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 192#64])

def loopBody694_57 : HolLoopProg 64 :=
.mark loopBody694_56

def loopBody694_58 : HolLoopProg 64 :=
.seq loopBody694_57 loopBody694_11

def loopBody694_59 : HolLoopProg 64 :=
.mark loopBody694_58

def loopBody694_60 : HolLoopProg 64 :=
.seq loopBody694_55 loopBody694_59

def loopBody694_61 : HolLoopProg 64 :=
.mark loopBody694_60

def loopBody694_62 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_61

def loopBody694_63 : HolLoopProg 64 :=
.mark loopBody694_62

def loopBody694_64 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_63

def loopBody694_65 : HolLoopProg 64 :=
.mark loopBody694_64

def loopBody694_66 : HolLoopProg 64 :=
.seq loopBody694_53 loopBody694_65

def loopBody694_67 : HolLoopProg 64 :=
.mark loopBody694_66

def loopBody694_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 192#64])

def loopBody694_69 : HolLoopProg 64 :=
.mark loopBody694_68

def loopBody694_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 392#64]),
      Flapjack.HolLoopExp.const 1152#64])

def loopBody694_71 : HolLoopProg 64 :=
.mark loopBody694_70

def loopBody694_72 : HolLoopProg 64 :=
.seq loopBody694_71 loopBody694_41

def loopBody694_73 : HolLoopProg 64 :=
.mark loopBody694_72

def loopBody694_74 : HolLoopProg 64 :=
.seq loopBody694_69 loopBody694_73

def loopBody694_75 : HolLoopProg 64 :=
.mark loopBody694_74

def loopBody694_76 : HolLoopProg 64 :=
.seq loopBody694_55 loopBody694_75

def loopBody694_77 : HolLoopProg 64 :=
.mark loopBody694_76

def loopBody694_78 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_77

def loopBody694_79 : HolLoopProg 64 :=
.mark loopBody694_78

def loopBody694_80 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_79

def loopBody694_81 : HolLoopProg 64 :=
.mark loopBody694_80

def loopBody694_82 : HolLoopProg 64 :=
.seq loopBody694_67 loopBody694_81

def loopBody694_83 : HolLoopProg 64 :=
.mark loopBody694_82

def loopBody694_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 288#64])

def loopBody694_85 : HolLoopProg 64 :=
.mark loopBody694_84

def loopBody694_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 288#64])

def loopBody694_87 : HolLoopProg 64 :=
.mark loopBody694_86

def loopBody694_88 : HolLoopProg 64 :=
.seq loopBody694_87 loopBody694_11

def loopBody694_89 : HolLoopProg 64 :=
.mark loopBody694_88

def loopBody694_90 : HolLoopProg 64 :=
.seq loopBody694_85 loopBody694_89

def loopBody694_91 : HolLoopProg 64 :=
.mark loopBody694_90

def loopBody694_92 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_91

def loopBody694_93 : HolLoopProg 64 :=
.mark loopBody694_92

def loopBody694_94 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_93

def loopBody694_95 : HolLoopProg 64 :=
.mark loopBody694_94

def loopBody694_96 : HolLoopProg 64 :=
.seq loopBody694_83 loopBody694_95

def loopBody694_97 : HolLoopProg 64 :=
.mark loopBody694_96

def loopBody694_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 288#64])

def loopBody694_99 : HolLoopProg 64 :=
.mark loopBody694_98

def loopBody694_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 392#64]),
      Flapjack.HolLoopExp.const 864#64])

def loopBody694_101 : HolLoopProg 64 :=
.mark loopBody694_100

def loopBody694_102 : HolLoopProg 64 :=
.seq loopBody694_101 loopBody694_41

def loopBody694_103 : HolLoopProg 64 :=
.mark loopBody694_102

def loopBody694_104 : HolLoopProg 64 :=
.seq loopBody694_99 loopBody694_103

def loopBody694_105 : HolLoopProg 64 :=
.mark loopBody694_104

def loopBody694_106 : HolLoopProg 64 :=
.seq loopBody694_85 loopBody694_105

def loopBody694_107 : HolLoopProg 64 :=
.mark loopBody694_106

def loopBody694_108 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_107

def loopBody694_109 : HolLoopProg 64 :=
.mark loopBody694_108

def loopBody694_110 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_109

def loopBody694_111 : HolLoopProg 64 :=
.mark loopBody694_110

def loopBody694_112 : HolLoopProg 64 :=
.seq loopBody694_97 loopBody694_111

def loopBody694_113 : HolLoopProg 64 :=
.mark loopBody694_112

def loopBody694_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 384#64])

def loopBody694_115 : HolLoopProg 64 :=
.mark loopBody694_114

def loopBody694_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 384#64])

def loopBody694_117 : HolLoopProg 64 :=
.mark loopBody694_116

def loopBody694_118 : HolLoopProg 64 :=
.seq loopBody694_117 loopBody694_11

def loopBody694_119 : HolLoopProg 64 :=
.mark loopBody694_118

def loopBody694_120 : HolLoopProg 64 :=
.seq loopBody694_115 loopBody694_119

def loopBody694_121 : HolLoopProg 64 :=
.mark loopBody694_120

def loopBody694_122 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_121

def loopBody694_123 : HolLoopProg 64 :=
.mark loopBody694_122

def loopBody694_124 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_123

def loopBody694_125 : HolLoopProg 64 :=
.mark loopBody694_124

def loopBody694_126 : HolLoopProg 64 :=
.seq loopBody694_113 loopBody694_125

def loopBody694_127 : HolLoopProg 64 :=
.mark loopBody694_126

def loopBody694_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 384#64])

def loopBody694_129 : HolLoopProg 64 :=
.mark loopBody694_128

def loopBody694_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 392#64]),
      Flapjack.HolLoopExp.const 1056#64])

def loopBody694_131 : HolLoopProg 64 :=
.mark loopBody694_130

def loopBody694_132 : HolLoopProg 64 :=
.seq loopBody694_131 loopBody694_41

def loopBody694_133 : HolLoopProg 64 :=
.mark loopBody694_132

def loopBody694_134 : HolLoopProg 64 :=
.seq loopBody694_129 loopBody694_133

def loopBody694_135 : HolLoopProg 64 :=
.mark loopBody694_134

def loopBody694_136 : HolLoopProg 64 :=
.seq loopBody694_115 loopBody694_135

def loopBody694_137 : HolLoopProg 64 :=
.mark loopBody694_136

def loopBody694_138 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_137

def loopBody694_139 : HolLoopProg 64 :=
.mark loopBody694_138

def loopBody694_140 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_139

def loopBody694_141 : HolLoopProg 64 :=
.mark loopBody694_140

def loopBody694_142 : HolLoopProg 64 :=
.seq loopBody694_127 loopBody694_141

def loopBody694_143 : HolLoopProg 64 :=
.mark loopBody694_142

def loopBody694_144 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 480#64])

def loopBody694_145 : HolLoopProg 64 :=
.mark loopBody694_144

def loopBody694_146 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 480#64])

def loopBody694_147 : HolLoopProg 64 :=
.mark loopBody694_146

def loopBody694_148 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ls PUnit.unit)) (some 734) ([3, 4]) (some (3, loopBody694_7, loopBody694_1, (Flapjack.Spt.ls PUnit.unit)))

def loopBody694_149 : HolLoopProg 64 :=
.mark loopBody694_148

def loopBody694_150 : HolLoopProg 64 :=
.seq loopBody694_149 loopBody694_1

def loopBody694_151 : HolLoopProg 64 :=
.mark loopBody694_150

def loopBody694_152 : HolLoopProg 64 :=
.seq loopBody694_147 loopBody694_151

def loopBody694_153 : HolLoopProg 64 :=
.mark loopBody694_152

def loopBody694_154 : HolLoopProg 64 :=
.seq loopBody694_145 loopBody694_153

def loopBody694_155 : HolLoopProg 64 :=
.mark loopBody694_154

def loopBody694_156 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_155

def loopBody694_157 : HolLoopProg 64 :=
.mark loopBody694_156

def loopBody694_158 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_157

def loopBody694_159 : HolLoopProg 64 :=
.mark loopBody694_158

def loopBody694_160 : HolLoopProg 64 :=
.seq loopBody694_143 loopBody694_159

def loopBody694_161 : HolLoopProg 64 :=
.mark loopBody694_160

def loopBody694_162 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 480#64])

def loopBody694_163 : HolLoopProg 64 :=
.mark loopBody694_162

def loopBody694_164 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 392#64]),
      Flapjack.HolLoopExp.const 1248#64])

def loopBody694_165 : HolLoopProg 64 :=
.mark loopBody694_164

def loopBody694_166 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 735) ([3, 4, 5]) (some (3, loopBody694_7, loopBody694_1, (Flapjack.Spt.ln)))

def loopBody694_167 : HolLoopProg 64 :=
.mark loopBody694_166

def loopBody694_168 : HolLoopProg 64 :=
.seq loopBody694_167 loopBody694_1

def loopBody694_169 : HolLoopProg 64 :=
.mark loopBody694_168

def loopBody694_170 : HolLoopProg 64 :=
.seq loopBody694_165 loopBody694_169

def loopBody694_171 : HolLoopProg 64 :=
.mark loopBody694_170

def loopBody694_172 : HolLoopProg 64 :=
.seq loopBody694_163 loopBody694_171

def loopBody694_173 : HolLoopProg 64 :=
.mark loopBody694_172

def loopBody694_174 : HolLoopProg 64 :=
.seq loopBody694_145 loopBody694_173

def loopBody694_175 : HolLoopProg 64 :=
.mark loopBody694_174

def loopBody694_176 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_175

def loopBody694_177 : HolLoopProg 64 :=
.mark loopBody694_176

def loopBody694_178 : HolLoopProg 64 :=
.seq loopBody694_1 loopBody694_177

def loopBody694_179 : HolLoopProg 64 :=
.mark loopBody694_178

def loopBody694_180 : HolLoopProg 64 :=
.seq loopBody694_161 loopBody694_179

def loopBody694_181 : HolLoopProg 64 :=
.mark loopBody694_180

def loopBody694_182 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody694_183 : HolLoopProg 64 :=
.mark loopBody694_182

def loopBody694_184 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody694_185 : HolLoopProg 64 :=
.mark loopBody694_184

def loopBody694_186 : HolLoopProg 64 :=
.seq loopBody694_185 loopBody694_1

def loopBody694_187 : HolLoopProg 64 :=
.mark loopBody694_186

def loopBody694_188 : HolLoopProg 64 :=
.seq loopBody694_183 loopBody694_187

def loopBody694_189 : HolLoopProg 64 :=
.mark loopBody694_188

def loopBody694_190 : HolLoopProg 64 :=
.seq loopBody694_181 loopBody694_189

def loopBody694_191 : HolLoopProg 64 :=
.mark loopBody694_190

def output694 : Nat × List Nat × HolLoopProg 64 :=
  (758, [0, 1], loopBody694_191)
end InitECandidate.Proofs.FrontendStages.Loop
