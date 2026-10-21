import InitECandidate.Proofs.FrontendStages.Loop.Translate468
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody484_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody484_1 : HolLoopProg 64 :=
.mark loopBody484_0

def loopBody484_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody484_3 : HolLoopProg 64 :=
.mark loopBody484_2

def loopBody484_4 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 488) ([]) (some (2, loopBody484_3, loopBody484_1, (Flapjack.Spt.ln)))

def loopBody484_5 : HolLoopProg 64 :=
.mark loopBody484_4

def loopBody484_6 : HolLoopProg 64 :=
.seq loopBody484_5 loopBody484_1

def loopBody484_7 : HolLoopProg 64 :=
.mark loopBody484_6

def loopBody484_8 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_7

def loopBody484_9 : HolLoopProg 64 :=
.mark loopBody484_8

def loopBody484_10 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_9

def loopBody484_11 : HolLoopProg 64 :=
.mark loopBody484_10

def loopBody484_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody484_13 : HolLoopProg 64 :=
.mark loopBody484_12

def loopBody484_14 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody484_13, loopBody484_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody484_15 : HolLoopProg 64 :=
.mark loopBody484_14

def loopBody484_16 : HolLoopProg 64 :=
.seq loopBody484_15 loopBody484_1

def loopBody484_17 : HolLoopProg 64 :=
.mark loopBody484_16

def loopBody484_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody484_19 : HolLoopProg 64 :=
.mark loopBody484_18

def loopBody484_20 : HolLoopProg 64 :=
.call (some
  ([5, 6, 7, 8],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 471) ([]) (some (9, loopBody484_19, loopBody484_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody484_21 : HolLoopProg 64 :=
.mark loopBody484_20

def loopBody484_22 : HolLoopProg 64 :=
.seq loopBody484_21 loopBody484_1

def loopBody484_23 : HolLoopProg 64 :=
.mark loopBody484_22

def loopBody484_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 100#64)

def loopBody484_25 : HolLoopProg 64 :=
.mark loopBody484_24

def loopBody484_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody484_27 : HolLoopProg 64 :=
.mark loopBody484_26

def loopBody484_28 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 466) ([10]) (some (10, loopBody484_27, loopBody484_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody484_29 : HolLoopProg 64 :=
.mark loopBody484_28

def loopBody484_30 : HolLoopProg 64 :=
.seq loopBody484_29 loopBody484_1

def loopBody484_31 : HolLoopProg 64 :=
.mark loopBody484_30

def loopBody484_32 : HolLoopProg 64 :=
.seq loopBody484_25 loopBody484_31

def loopBody484_33 : HolLoopProg 64 :=
.mark loopBody484_32

def loopBody484_34 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_33

def loopBody484_35 : HolLoopProg 64 :=
.mark loopBody484_34

def loopBody484_36 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_35

def loopBody484_37 : HolLoopProg 64 :=
.mark loopBody484_36

def loopBody484_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 280#64]))

def loopBody484_39 : HolLoopProg 64 :=
.mark loopBody484_38

def loopBody484_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 1)

def loopBody484_41 : HolLoopProg 64 :=
.mark loopBody484_40

def loopBody484_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 2)

def loopBody484_43 : HolLoopProg 64 :=
.mark loopBody484_42

def loopBody484_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 3)

def loopBody484_45 : HolLoopProg 64 :=
.mark loopBody484_44

def loopBody484_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 4)

def loopBody484_47 : HolLoopProg 64 :=
.mark loopBody484_46

def loopBody484_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 9)

def loopBody484_49 : HolLoopProg 64 :=
.mark loopBody484_48

def loopBody484_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 11

def loopBody484_51 : HolLoopProg 64 :=
.mark loopBody484_50

def loopBody484_52 : HolLoopProg 64 :=
.call (some
  ([10],
    Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))) (some 147) ([11, 12, 13, 14, 15]) (some (11, loopBody484_51, loopBody484_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody484_53 : HolLoopProg 64 :=
.mark loopBody484_52

def loopBody484_54 : HolLoopProg 64 :=
.seq loopBody484_53 loopBody484_1

def loopBody484_55 : HolLoopProg 64 :=
.mark loopBody484_54

def loopBody484_56 : HolLoopProg 64 :=
.seq loopBody484_49 loopBody484_55

def loopBody484_57 : HolLoopProg 64 :=
.mark loopBody484_56

def loopBody484_58 : HolLoopProg 64 :=
.seq loopBody484_47 loopBody484_57

def loopBody484_59 : HolLoopProg 64 :=
.mark loopBody484_58

def loopBody484_60 : HolLoopProg 64 :=
.seq loopBody484_45 loopBody484_59

def loopBody484_61 : HolLoopProg 64 :=
.mark loopBody484_60

def loopBody484_62 : HolLoopProg 64 :=
.seq loopBody484_43 loopBody484_61

def loopBody484_63 : HolLoopProg 64 :=
.mark loopBody484_62

def loopBody484_64 : HolLoopProg 64 :=
.seq loopBody484_41 loopBody484_63

def loopBody484_65 : HolLoopProg 64 :=
.mark loopBody484_64

def loopBody484_66 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_65

def loopBody484_67 : HolLoopProg 64 :=
.mark loopBody484_66

def loopBody484_68 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_67

def loopBody484_69 : HolLoopProg 64 :=
.mark loopBody484_68

def loopBody484_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.add
            [Flapjack.HolLoopExp.load
                (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                  [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
              Flapjack.HolLoopExp.const 112#64]),
        Flapjack.HolLoopExp.const 32#64]))

def loopBody484_71 : HolLoopProg 64 :=
.mark loopBody484_70

def loopBody484_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 10)

def loopBody484_73 : HolLoopProg 64 :=
.mark loopBody484_72

def loopBody484_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 9)

def loopBody484_75 : HolLoopProg 64 :=
.mark loopBody484_74

def loopBody484_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 5)

def loopBody484_77 : HolLoopProg 64 :=
.mark loopBody484_76

def loopBody484_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 6)

def loopBody484_79 : HolLoopProg 64 :=
.mark loopBody484_78

def loopBody484_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 7)

def loopBody484_81 : HolLoopProg 64 :=
.mark loopBody484_80

def loopBody484_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 8)

def loopBody484_83 : HolLoopProg 64 :=
.mark loopBody484_82

def loopBody484_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 12

def loopBody484_85 : HolLoopProg 64 :=
.mark loopBody484_84

def loopBody484_86 : HolLoopProg 64 :=
.call (some ([11], Flapjack.Spt.ln)) (some 422) ([12, 13, 14, 15, 16, 17]) (some (12, loopBody484_85, loopBody484_1, (Flapjack.Spt.ln)))

def loopBody484_87 : HolLoopProg 64 :=
.mark loopBody484_86

def loopBody484_88 : HolLoopProg 64 :=
.seq loopBody484_87 loopBody484_1

def loopBody484_89 : HolLoopProg 64 :=
.mark loopBody484_88

def loopBody484_90 : HolLoopProg 64 :=
.seq loopBody484_83 loopBody484_89

def loopBody484_91 : HolLoopProg 64 :=
.mark loopBody484_90

def loopBody484_92 : HolLoopProg 64 :=
.seq loopBody484_81 loopBody484_91

def loopBody484_93 : HolLoopProg 64 :=
.mark loopBody484_92

def loopBody484_94 : HolLoopProg 64 :=
.seq loopBody484_79 loopBody484_93

def loopBody484_95 : HolLoopProg 64 :=
.mark loopBody484_94

def loopBody484_96 : HolLoopProg 64 :=
.seq loopBody484_77 loopBody484_95

def loopBody484_97 : HolLoopProg 64 :=
.mark loopBody484_96

def loopBody484_98 : HolLoopProg 64 :=
.seq loopBody484_75 loopBody484_97

def loopBody484_99 : HolLoopProg 64 :=
.mark loopBody484_98

def loopBody484_100 : HolLoopProg 64 :=
.seq loopBody484_73 loopBody484_99

def loopBody484_101 : HolLoopProg 64 :=
.mark loopBody484_100

def loopBody484_102 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_101

def loopBody484_103 : HolLoopProg 64 :=
.mark loopBody484_102

def loopBody484_104 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_103

def loopBody484_105 : HolLoopProg 64 :=
.mark loopBody484_104

def loopBody484_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody484_107 : HolLoopProg 64 :=
.mark loopBody484_106

def loopBody484_108 : HolLoopProg 64 :=
.call (some ([11], Flapjack.Spt.ln)) (some 486) ([12]) (some (12, loopBody484_85, loopBody484_1, (Flapjack.Spt.ln)))

def loopBody484_109 : HolLoopProg 64 :=
.mark loopBody484_108

def loopBody484_110 : HolLoopProg 64 :=
.seq loopBody484_109 loopBody484_1

def loopBody484_111 : HolLoopProg 64 :=
.mark loopBody484_110

def loopBody484_112 : HolLoopProg 64 :=
.seq loopBody484_107 loopBody484_111

def loopBody484_113 : HolLoopProg 64 :=
.mark loopBody484_112

def loopBody484_114 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_113

def loopBody484_115 : HolLoopProg 64 :=
.mark loopBody484_114

def loopBody484_116 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_115

def loopBody484_117 : HolLoopProg 64 :=
.mark loopBody484_116

def loopBody484_118 : HolLoopProg 64 :=
.seq loopBody484_105 loopBody484_117

def loopBody484_119 : HolLoopProg 64 :=
.mark loopBody484_118

def loopBody484_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody484_121 : HolLoopProg 64 :=
.mark loopBody484_120

def loopBody484_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [11]

def loopBody484_123 : HolLoopProg 64 :=
.mark loopBody484_122

def loopBody484_124 : HolLoopProg 64 :=
.seq loopBody484_123 loopBody484_1

def loopBody484_125 : HolLoopProg 64 :=
.mark loopBody484_124

def loopBody484_126 : HolLoopProg 64 :=
.seq loopBody484_121 loopBody484_125

def loopBody484_127 : HolLoopProg 64 :=
.mark loopBody484_126

def loopBody484_128 : HolLoopProg 64 :=
.seq loopBody484_119 loopBody484_127

def loopBody484_129 : HolLoopProg 64 :=
.mark loopBody484_128

def loopBody484_130 : HolLoopProg 64 :=
.seq loopBody484_71 loopBody484_129

def loopBody484_131 : HolLoopProg 64 :=
.mark loopBody484_130

def loopBody484_132 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_131

def loopBody484_133 : HolLoopProg 64 :=
.mark loopBody484_132

def loopBody484_134 : HolLoopProg 64 :=
.seq loopBody484_69 loopBody484_133

def loopBody484_135 : HolLoopProg 64 :=
.mark loopBody484_134

def loopBody484_136 : HolLoopProg 64 :=
.seq loopBody484_39 loopBody484_135

def loopBody484_137 : HolLoopProg 64 :=
.mark loopBody484_136

def loopBody484_138 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_137

def loopBody484_139 : HolLoopProg 64 :=
.mark loopBody484_138

def loopBody484_140 : HolLoopProg 64 :=
.seq loopBody484_37 loopBody484_139

def loopBody484_141 : HolLoopProg 64 :=
.mark loopBody484_140

def loopBody484_142 : HolLoopProg 64 :=
.seq loopBody484_23 loopBody484_141

def loopBody484_143 : HolLoopProg 64 :=
.mark loopBody484_142

def loopBody484_144 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_143

def loopBody484_145 : HolLoopProg 64 :=
.mark loopBody484_144

def loopBody484_146 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_145

def loopBody484_147 : HolLoopProg 64 :=
.mark loopBody484_146

def loopBody484_148 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_147

def loopBody484_149 : HolLoopProg 64 :=
.mark loopBody484_148

def loopBody484_150 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_149

def loopBody484_151 : HolLoopProg 64 :=
.mark loopBody484_150

def loopBody484_152 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_151

def loopBody484_153 : HolLoopProg 64 :=
.mark loopBody484_152

def loopBody484_154 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_153

def loopBody484_155 : HolLoopProg 64 :=
.mark loopBody484_154

def loopBody484_156 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_155

def loopBody484_157 : HolLoopProg 64 :=
.mark loopBody484_156

def loopBody484_158 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_157

def loopBody484_159 : HolLoopProg 64 :=
.mark loopBody484_158

def loopBody484_160 : HolLoopProg 64 :=
.seq loopBody484_17 loopBody484_159

def loopBody484_161 : HolLoopProg 64 :=
.mark loopBody484_160

def loopBody484_162 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_161

def loopBody484_163 : HolLoopProg 64 :=
.mark loopBody484_162

def loopBody484_164 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_163

def loopBody484_165 : HolLoopProg 64 :=
.mark loopBody484_164

def loopBody484_166 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_165

def loopBody484_167 : HolLoopProg 64 :=
.mark loopBody484_166

def loopBody484_168 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_167

def loopBody484_169 : HolLoopProg 64 :=
.mark loopBody484_168

def loopBody484_170 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_169

def loopBody484_171 : HolLoopProg 64 :=
.mark loopBody484_170

def loopBody484_172 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_171

def loopBody484_173 : HolLoopProg 64 :=
.mark loopBody484_172

def loopBody484_174 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_173

def loopBody484_175 : HolLoopProg 64 :=
.mark loopBody484_174

def loopBody484_176 : HolLoopProg 64 :=
.seq loopBody484_1 loopBody484_175

def loopBody484_177 : HolLoopProg 64 :=
.mark loopBody484_176

def loopBody484_178 : HolLoopProg 64 :=
.seq loopBody484_11 loopBody484_177

def loopBody484_179 : HolLoopProg 64 :=
.mark loopBody484_178

def output484 : Nat × List Nat × HolLoopProg 64 :=
  (548, [], loopBody484_179)
end InitECandidate.Proofs.FrontendStages.Loop
