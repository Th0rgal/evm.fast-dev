import InitECandidate.Proofs.FrontendStages.Loop.Translate454
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody470_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody470_1 : HolLoopProg 64 :=
.mark loopBody470_0

def loopBody470_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 16#64]))

def loopBody470_3 : HolLoopProg 64 :=
.mark loopBody470_2

def loopBody470_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody470_5 : HolLoopProg 64 :=
.mark loopBody470_4

def loopBody470_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 3,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
          [Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 1#64],
            Flapjack.HolLoopExp.var 0])
        (Flapjack.HolLoopExp.const 5#64)])

def loopBody470_7 : HolLoopProg 64 :=
.mark loopBody470_6

def loopBody470_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 3,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
          [Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 1#64],
            Flapjack.HolLoopExp.var 1])
        (Flapjack.HolLoopExp.const 5#64)])

def loopBody470_9 : HolLoopProg 64 :=
.mark loopBody470_8

def loopBody470_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.var 4))

def loopBody470_11 : HolLoopProg 64 :=
.mark loopBody470_10

def loopBody470_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 8#64]))

def loopBody470_13 : HolLoopProg 64 :=
.mark loopBody470_12

def loopBody470_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 16#64]))

def loopBody470_15 : HolLoopProg 64 :=
.mark loopBody470_14

def loopBody470_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 24#64]))

def loopBody470_17 : HolLoopProg 64 :=
.mark loopBody470_16

def loopBody470_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.var 5))

def loopBody470_19 : HolLoopProg 64 :=
.mark loopBody470_18

def loopBody470_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 8#64]))

def loopBody470_21 : HolLoopProg 64 :=
.mark loopBody470_20

def loopBody470_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 16#64]))

def loopBody470_23 : HolLoopProg 64 :=
.mark loopBody470_22

def loopBody470_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 24#64]))

def loopBody470_25 : HolLoopProg 64 :=
.mark loopBody470_24

def loopBody470_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 4)

def loopBody470_27 : HolLoopProg 64 :=
.mark loopBody470_26

def loopBody470_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 10)

def loopBody470_29 : HolLoopProg 64 :=
.mark loopBody470_28

def loopBody470_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 11)

def loopBody470_31 : HolLoopProg 64 :=
.mark loopBody470_30

def loopBody470_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 12)

def loopBody470_33 : HolLoopProg 64 :=
.mark loopBody470_32

def loopBody470_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 13)

def loopBody470_35 : HolLoopProg 64 :=
.mark loopBody470_34

def loopBody470_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 15)

def loopBody470_37 : HolLoopProg 64 :=
.mark loopBody470_36

def loopBody470_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 14) 19

def loopBody470_39 : HolLoopProg 64 :=
.mark loopBody470_38

def loopBody470_40 : HolLoopProg 64 :=
.seq loopBody470_39 loopBody470_1

def loopBody470_41 : HolLoopProg 64 :=
.mark loopBody470_40

def loopBody470_42 : HolLoopProg 64 :=
.seq loopBody470_37 loopBody470_41

def loopBody470_43 : HolLoopProg 64 :=
.mark loopBody470_42

def loopBody470_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 16)

def loopBody470_45 : HolLoopProg 64 :=
.mark loopBody470_44

def loopBody470_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 14, Flapjack.HolLoopExp.const 8#64]) 19

def loopBody470_47 : HolLoopProg 64 :=
.mark loopBody470_46

def loopBody470_48 : HolLoopProg 64 :=
.seq loopBody470_47 loopBody470_1

def loopBody470_49 : HolLoopProg 64 :=
.mark loopBody470_48

def loopBody470_50 : HolLoopProg 64 :=
.seq loopBody470_45 loopBody470_49

def loopBody470_51 : HolLoopProg 64 :=
.mark loopBody470_50

def loopBody470_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 17)

def loopBody470_53 : HolLoopProg 64 :=
.mark loopBody470_52

def loopBody470_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 14, Flapjack.HolLoopExp.const 16#64]) 19

def loopBody470_55 : HolLoopProg 64 :=
.mark loopBody470_54

def loopBody470_56 : HolLoopProg 64 :=
.seq loopBody470_55 loopBody470_1

def loopBody470_57 : HolLoopProg 64 :=
.mark loopBody470_56

def loopBody470_58 : HolLoopProg 64 :=
.seq loopBody470_53 loopBody470_57

def loopBody470_59 : HolLoopProg 64 :=
.mark loopBody470_58

def loopBody470_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 18)

def loopBody470_61 : HolLoopProg 64 :=
.mark loopBody470_60

def loopBody470_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 14, Flapjack.HolLoopExp.const 24#64]) 19

def loopBody470_63 : HolLoopProg 64 :=
.mark loopBody470_62

def loopBody470_64 : HolLoopProg 64 :=
.seq loopBody470_63 loopBody470_1

def loopBody470_65 : HolLoopProg 64 :=
.mark loopBody470_64

def loopBody470_66 : HolLoopProg 64 :=
.seq loopBody470_61 loopBody470_65

def loopBody470_67 : HolLoopProg 64 :=
.mark loopBody470_66

def loopBody470_68 : HolLoopProg 64 :=
.seq loopBody470_67 loopBody470_1

def loopBody470_69 : HolLoopProg 64 :=
.mark loopBody470_68

def loopBody470_70 : HolLoopProg 64 :=
.seq loopBody470_59 loopBody470_69

def loopBody470_71 : HolLoopProg 64 :=
.mark loopBody470_70

def loopBody470_72 : HolLoopProg 64 :=
.seq loopBody470_51 loopBody470_71

def loopBody470_73 : HolLoopProg 64 :=
.mark loopBody470_72

def loopBody470_74 : HolLoopProg 64 :=
.seq loopBody470_43 loopBody470_73

def loopBody470_75 : HolLoopProg 64 :=
.mark loopBody470_74

def loopBody470_76 : HolLoopProg 64 :=
.seq loopBody470_35 loopBody470_75

def loopBody470_77 : HolLoopProg 64 :=
.mark loopBody470_76

def loopBody470_78 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_77

def loopBody470_79 : HolLoopProg 64 :=
.mark loopBody470_78

def loopBody470_80 : HolLoopProg 64 :=
.seq loopBody470_33 loopBody470_79

def loopBody470_81 : HolLoopProg 64 :=
.mark loopBody470_80

def loopBody470_82 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_81

def loopBody470_83 : HolLoopProg 64 :=
.mark loopBody470_82

def loopBody470_84 : HolLoopProg 64 :=
.seq loopBody470_31 loopBody470_83

def loopBody470_85 : HolLoopProg 64 :=
.mark loopBody470_84

def loopBody470_86 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_85

def loopBody470_87 : HolLoopProg 64 :=
.mark loopBody470_86

def loopBody470_88 : HolLoopProg 64 :=
.seq loopBody470_29 loopBody470_87

def loopBody470_89 : HolLoopProg 64 :=
.mark loopBody470_88

def loopBody470_90 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_89

def loopBody470_91 : HolLoopProg 64 :=
.mark loopBody470_90

def loopBody470_92 : HolLoopProg 64 :=
.seq loopBody470_27 loopBody470_91

def loopBody470_93 : HolLoopProg 64 :=
.mark loopBody470_92

def loopBody470_94 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_93

def loopBody470_95 : HolLoopProg 64 :=
.mark loopBody470_94

def loopBody470_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 5)

def loopBody470_97 : HolLoopProg 64 :=
.mark loopBody470_96

def loopBody470_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 6)

def loopBody470_99 : HolLoopProg 64 :=
.mark loopBody470_98

def loopBody470_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 7)

def loopBody470_101 : HolLoopProg 64 :=
.mark loopBody470_100

def loopBody470_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 8)

def loopBody470_103 : HolLoopProg 64 :=
.mark loopBody470_102

def loopBody470_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 9)

def loopBody470_105 : HolLoopProg 64 :=
.mark loopBody470_104

def loopBody470_106 : HolLoopProg 64 :=
.seq loopBody470_105 loopBody470_75

def loopBody470_107 : HolLoopProg 64 :=
.mark loopBody470_106

def loopBody470_108 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_107

def loopBody470_109 : HolLoopProg 64 :=
.mark loopBody470_108

def loopBody470_110 : HolLoopProg 64 :=
.seq loopBody470_103 loopBody470_109

def loopBody470_111 : HolLoopProg 64 :=
.mark loopBody470_110

def loopBody470_112 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_111

def loopBody470_113 : HolLoopProg 64 :=
.mark loopBody470_112

def loopBody470_114 : HolLoopProg 64 :=
.seq loopBody470_101 loopBody470_113

def loopBody470_115 : HolLoopProg 64 :=
.mark loopBody470_114

def loopBody470_116 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_115

def loopBody470_117 : HolLoopProg 64 :=
.mark loopBody470_116

def loopBody470_118 : HolLoopProg 64 :=
.seq loopBody470_99 loopBody470_117

def loopBody470_119 : HolLoopProg 64 :=
.mark loopBody470_118

def loopBody470_120 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_119

def loopBody470_121 : HolLoopProg 64 :=
.mark loopBody470_120

def loopBody470_122 : HolLoopProg 64 :=
.seq loopBody470_97 loopBody470_121

def loopBody470_123 : HolLoopProg 64 :=
.mark loopBody470_122

def loopBody470_124 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_123

def loopBody470_125 : HolLoopProg 64 :=
.mark loopBody470_124

def loopBody470_126 : HolLoopProg 64 :=
.seq loopBody470_95 loopBody470_125

def loopBody470_127 : HolLoopProg 64 :=
.mark loopBody470_126

def loopBody470_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 0#64)

def loopBody470_129 : HolLoopProg 64 :=
.mark loopBody470_128

def loopBody470_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [14]

def loopBody470_131 : HolLoopProg 64 :=
.mark loopBody470_130

def loopBody470_132 : HolLoopProg 64 :=
.seq loopBody470_131 loopBody470_1

def loopBody470_133 : HolLoopProg 64 :=
.mark loopBody470_132

def loopBody470_134 : HolLoopProg 64 :=
.seq loopBody470_129 loopBody470_133

def loopBody470_135 : HolLoopProg 64 :=
.mark loopBody470_134

def loopBody470_136 : HolLoopProg 64 :=
.seq loopBody470_127 loopBody470_135

def loopBody470_137 : HolLoopProg 64 :=
.mark loopBody470_136

def loopBody470_138 : HolLoopProg 64 :=
.seq loopBody470_25 loopBody470_137

def loopBody470_139 : HolLoopProg 64 :=
.mark loopBody470_138

def loopBody470_140 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_139

def loopBody470_141 : HolLoopProg 64 :=
.mark loopBody470_140

def loopBody470_142 : HolLoopProg 64 :=
.seq loopBody470_23 loopBody470_141

def loopBody470_143 : HolLoopProg 64 :=
.mark loopBody470_142

def loopBody470_144 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_143

def loopBody470_145 : HolLoopProg 64 :=
.mark loopBody470_144

def loopBody470_146 : HolLoopProg 64 :=
.seq loopBody470_21 loopBody470_145

def loopBody470_147 : HolLoopProg 64 :=
.mark loopBody470_146

def loopBody470_148 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_147

def loopBody470_149 : HolLoopProg 64 :=
.mark loopBody470_148

def loopBody470_150 : HolLoopProg 64 :=
.seq loopBody470_19 loopBody470_149

def loopBody470_151 : HolLoopProg 64 :=
.mark loopBody470_150

def loopBody470_152 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_151

def loopBody470_153 : HolLoopProg 64 :=
.mark loopBody470_152

def loopBody470_154 : HolLoopProg 64 :=
.seq loopBody470_17 loopBody470_153

def loopBody470_155 : HolLoopProg 64 :=
.mark loopBody470_154

def loopBody470_156 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_155

def loopBody470_157 : HolLoopProg 64 :=
.mark loopBody470_156

def loopBody470_158 : HolLoopProg 64 :=
.seq loopBody470_15 loopBody470_157

def loopBody470_159 : HolLoopProg 64 :=
.mark loopBody470_158

def loopBody470_160 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_159

def loopBody470_161 : HolLoopProg 64 :=
.mark loopBody470_160

def loopBody470_162 : HolLoopProg 64 :=
.seq loopBody470_13 loopBody470_161

def loopBody470_163 : HolLoopProg 64 :=
.mark loopBody470_162

def loopBody470_164 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_163

def loopBody470_165 : HolLoopProg 64 :=
.mark loopBody470_164

def loopBody470_166 : HolLoopProg 64 :=
.seq loopBody470_11 loopBody470_165

def loopBody470_167 : HolLoopProg 64 :=
.mark loopBody470_166

def loopBody470_168 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_167

def loopBody470_169 : HolLoopProg 64 :=
.mark loopBody470_168

def loopBody470_170 : HolLoopProg 64 :=
.seq loopBody470_9 loopBody470_169

def loopBody470_171 : HolLoopProg 64 :=
.mark loopBody470_170

def loopBody470_172 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_171

def loopBody470_173 : HolLoopProg 64 :=
.mark loopBody470_172

def loopBody470_174 : HolLoopProg 64 :=
.seq loopBody470_7 loopBody470_173

def loopBody470_175 : HolLoopProg 64 :=
.mark loopBody470_174

def loopBody470_176 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_175

def loopBody470_177 : HolLoopProg 64 :=
.mark loopBody470_176

def loopBody470_178 : HolLoopProg 64 :=
.seq loopBody470_5 loopBody470_177

def loopBody470_179 : HolLoopProg 64 :=
.mark loopBody470_178

def loopBody470_180 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_179

def loopBody470_181 : HolLoopProg 64 :=
.mark loopBody470_180

def loopBody470_182 : HolLoopProg 64 :=
.seq loopBody470_3 loopBody470_181

def loopBody470_183 : HolLoopProg 64 :=
.mark loopBody470_182

def loopBody470_184 : HolLoopProg 64 :=
.seq loopBody470_1 loopBody470_183

def loopBody470_185 : HolLoopProg 64 :=
.mark loopBody470_184

def output470 : Nat × List Nat × HolLoopProg 64 :=
  (534, [0, 1], loopBody470_185)
end InitECandidate.Proofs.FrontendStages.Loop
