import InitECandidate.Proofs.FrontendStages.Loop.Translate448
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody464_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody464_1 : HolLoopProg 64 :=
.mark loopBody464_0

def loopBody464_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody464_3 : HolLoopProg 64 :=
.mark loopBody464_2

def loopBody464_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody464_3, loopBody464_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody464_5 : HolLoopProg 64 :=
.mark loopBody464_4

def loopBody464_6 : HolLoopProg 64 :=
.seq loopBody464_5 loopBody464_1

def loopBody464_7 : HolLoopProg 64 :=
.mark loopBody464_6

def loopBody464_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 3#64)

def loopBody464_9 : HolLoopProg 64 :=
.mark loopBody464_8

def loopBody464_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody464_11 : HolLoopProg 64 :=
.mark loopBody464_10

def loopBody464_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody464_13 : HolLoopProg 64 :=
.mark loopBody464_12

def loopBody464_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 3)

def loopBody464_15 : HolLoopProg 64 :=
.mark loopBody464_14

def loopBody464_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 4)

def loopBody464_17 : HolLoopProg 64 :=
.mark loopBody464_16

def loopBody464_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 32#64)

def loopBody464_19 : HolLoopProg 64 :=
.mark loopBody464_18

def loopBody464_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 0#64)

def loopBody464_21 : HolLoopProg 64 :=
.mark loopBody464_20

def loopBody464_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 0#64)

def loopBody464_23 : HolLoopProg 64 :=
.mark loopBody464_22

def loopBody464_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 0#64)

def loopBody464_25 : HolLoopProg 64 :=
.mark loopBody464_24

def loopBody464_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody464_27 : HolLoopProg 64 :=
.mark loopBody464_26

def loopBody464_28 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 479) ([6, 7, 8, 9, 10, 11, 12, 13, 14]) (some (6, loopBody464_27, loopBody464_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody464_29 : HolLoopProg 64 :=
.mark loopBody464_28

def loopBody464_30 : HolLoopProg 64 :=
.seq loopBody464_29 loopBody464_1

def loopBody464_31 : HolLoopProg 64 :=
.mark loopBody464_30

def loopBody464_32 : HolLoopProg 64 :=
.seq loopBody464_25 loopBody464_31

def loopBody464_33 : HolLoopProg 64 :=
.mark loopBody464_32

def loopBody464_34 : HolLoopProg 64 :=
.seq loopBody464_23 loopBody464_33

def loopBody464_35 : HolLoopProg 64 :=
.mark loopBody464_34

def loopBody464_36 : HolLoopProg 64 :=
.seq loopBody464_21 loopBody464_35

def loopBody464_37 : HolLoopProg 64 :=
.mark loopBody464_36

def loopBody464_38 : HolLoopProg 64 :=
.seq loopBody464_19 loopBody464_37

def loopBody464_39 : HolLoopProg 64 :=
.mark loopBody464_38

def loopBody464_40 : HolLoopProg 64 :=
.seq loopBody464_17 loopBody464_39

def loopBody464_41 : HolLoopProg 64 :=
.mark loopBody464_40

def loopBody464_42 : HolLoopProg 64 :=
.seq loopBody464_15 loopBody464_41

def loopBody464_43 : HolLoopProg 64 :=
.mark loopBody464_42

def loopBody464_44 : HolLoopProg 64 :=
.seq loopBody464_13 loopBody464_43

def loopBody464_45 : HolLoopProg 64 :=
.mark loopBody464_44

def loopBody464_46 : HolLoopProg 64 :=
.seq loopBody464_11 loopBody464_45

def loopBody464_47 : HolLoopProg 64 :=
.mark loopBody464_46

def loopBody464_48 : HolLoopProg 64 :=
.seq loopBody464_9 loopBody464_47

def loopBody464_49 : HolLoopProg 64 :=
.mark loopBody464_48

def loopBody464_50 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_49

def loopBody464_51 : HolLoopProg 64 :=
.mark loopBody464_50

def loopBody464_52 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_51

def loopBody464_53 : HolLoopProg 64 :=
.mark loopBody464_52

def loopBody464_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody464_55 : HolLoopProg 64 :=
.mark loopBody464_54

def loopBody464_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody464_57 : HolLoopProg 64 :=
.mark loopBody464_56

def loopBody464_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody464_59 : HolLoopProg 64 :=
.mark loopBody464_58

def loopBody464_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody464_61 : HolLoopProg 64 :=
.mark loopBody464_60

def loopBody464_62 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 458) ([6, 7, 8, 9]) (some (6, loopBody464_27, loopBody464_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody464_63 : HolLoopProg 64 :=
.mark loopBody464_62

def loopBody464_64 : HolLoopProg 64 :=
.seq loopBody464_63 loopBody464_1

def loopBody464_65 : HolLoopProg 64 :=
.mark loopBody464_64

def loopBody464_66 : HolLoopProg 64 :=
.seq loopBody464_61 loopBody464_65

def loopBody464_67 : HolLoopProg 64 :=
.mark loopBody464_66

def loopBody464_68 : HolLoopProg 64 :=
.seq loopBody464_59 loopBody464_67

def loopBody464_69 : HolLoopProg 64 :=
.mark loopBody464_68

def loopBody464_70 : HolLoopProg 64 :=
.seq loopBody464_57 loopBody464_69

def loopBody464_71 : HolLoopProg 64 :=
.mark loopBody464_70

def loopBody464_72 : HolLoopProg 64 :=
.seq loopBody464_55 loopBody464_71

def loopBody464_73 : HolLoopProg 64 :=
.mark loopBody464_72

def loopBody464_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 24#64]),
      Flapjack.HolLoopExp.var 5])

def loopBody464_75 : HolLoopProg 64 :=
.mark loopBody464_74

def loopBody464_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody464_77 : HolLoopProg 64 :=
.mark loopBody464_76

def loopBody464_78 : HolLoopProg 64 :=
.call (some ([6, 7, 8, 9], Flapjack.Spt.ln)) (some 146) ([10, 11]) (some (10, loopBody464_77, loopBody464_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody464_79 : HolLoopProg 64 :=
.mark loopBody464_78

def loopBody464_80 : HolLoopProg 64 :=
.seq loopBody464_79 loopBody464_1

def loopBody464_81 : HolLoopProg 64 :=
.mark loopBody464_80

def loopBody464_82 : HolLoopProg 64 :=
.seq loopBody464_19 loopBody464_81

def loopBody464_83 : HolLoopProg 64 :=
.mark loopBody464_82

def loopBody464_84 : HolLoopProg 64 :=
.seq loopBody464_75 loopBody464_83

def loopBody464_85 : HolLoopProg 64 :=
.mark loopBody464_84

def loopBody464_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 6)

def loopBody464_87 : HolLoopProg 64 :=
.mark loopBody464_86

def loopBody464_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 7)

def loopBody464_89 : HolLoopProg 64 :=
.mark loopBody464_88

def loopBody464_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 8)

def loopBody464_91 : HolLoopProg 64 :=
.mark loopBody464_90

def loopBody464_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 9)

def loopBody464_93 : HolLoopProg 64 :=
.mark loopBody464_92

def loopBody464_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 11

def loopBody464_95 : HolLoopProg 64 :=
.mark loopBody464_94

def loopBody464_96 : HolLoopProg 64 :=
.call (some ([10], Flapjack.Spt.ln)) (some 472) ([11, 12, 13, 14]) (some (11, loopBody464_95, loopBody464_1, (Flapjack.Spt.ln)))

def loopBody464_97 : HolLoopProg 64 :=
.mark loopBody464_96

def loopBody464_98 : HolLoopProg 64 :=
.seq loopBody464_97 loopBody464_1

def loopBody464_99 : HolLoopProg 64 :=
.mark loopBody464_98

def loopBody464_100 : HolLoopProg 64 :=
.seq loopBody464_93 loopBody464_99

def loopBody464_101 : HolLoopProg 64 :=
.mark loopBody464_100

def loopBody464_102 : HolLoopProg 64 :=
.seq loopBody464_91 loopBody464_101

def loopBody464_103 : HolLoopProg 64 :=
.mark loopBody464_102

def loopBody464_104 : HolLoopProg 64 :=
.seq loopBody464_89 loopBody464_103

def loopBody464_105 : HolLoopProg 64 :=
.mark loopBody464_104

def loopBody464_106 : HolLoopProg 64 :=
.seq loopBody464_87 loopBody464_105

def loopBody464_107 : HolLoopProg 64 :=
.mark loopBody464_106

def loopBody464_108 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_107

def loopBody464_109 : HolLoopProg 64 :=
.mark loopBody464_108

def loopBody464_110 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_109

def loopBody464_111 : HolLoopProg 64 :=
.mark loopBody464_110

def loopBody464_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 1#64)

def loopBody464_113 : HolLoopProg 64 :=
.mark loopBody464_112

def loopBody464_114 : HolLoopProg 64 :=
.call (some ([10], Flapjack.Spt.ln)) (some 486) ([11]) (some (11, loopBody464_95, loopBody464_1, (Flapjack.Spt.ln)))

def loopBody464_115 : HolLoopProg 64 :=
.mark loopBody464_114

def loopBody464_116 : HolLoopProg 64 :=
.seq loopBody464_115 loopBody464_1

def loopBody464_117 : HolLoopProg 64 :=
.mark loopBody464_116

def loopBody464_118 : HolLoopProg 64 :=
.seq loopBody464_113 loopBody464_117

def loopBody464_119 : HolLoopProg 64 :=
.mark loopBody464_118

def loopBody464_120 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_119

def loopBody464_121 : HolLoopProg 64 :=
.mark loopBody464_120

def loopBody464_122 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_121

def loopBody464_123 : HolLoopProg 64 :=
.mark loopBody464_122

def loopBody464_124 : HolLoopProg 64 :=
.seq loopBody464_111 loopBody464_123

def loopBody464_125 : HolLoopProg 64 :=
.mark loopBody464_124

def loopBody464_126 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody464_127 : HolLoopProg 64 :=
.mark loopBody464_126

def loopBody464_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [10]

def loopBody464_129 : HolLoopProg 64 :=
.mark loopBody464_128

def loopBody464_130 : HolLoopProg 64 :=
.seq loopBody464_129 loopBody464_1

def loopBody464_131 : HolLoopProg 64 :=
.mark loopBody464_130

def loopBody464_132 : HolLoopProg 64 :=
.seq loopBody464_127 loopBody464_131

def loopBody464_133 : HolLoopProg 64 :=
.mark loopBody464_132

def loopBody464_134 : HolLoopProg 64 :=
.seq loopBody464_125 loopBody464_133

def loopBody464_135 : HolLoopProg 64 :=
.mark loopBody464_134

def loopBody464_136 : HolLoopProg 64 :=
.seq loopBody464_85 loopBody464_135

def loopBody464_137 : HolLoopProg 64 :=
.mark loopBody464_136

def loopBody464_138 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_137

def loopBody464_139 : HolLoopProg 64 :=
.mark loopBody464_138

def loopBody464_140 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_139

def loopBody464_141 : HolLoopProg 64 :=
.mark loopBody464_140

def loopBody464_142 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_141

def loopBody464_143 : HolLoopProg 64 :=
.mark loopBody464_142

def loopBody464_144 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_143

def loopBody464_145 : HolLoopProg 64 :=
.mark loopBody464_144

def loopBody464_146 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_145

def loopBody464_147 : HolLoopProg 64 :=
.mark loopBody464_146

def loopBody464_148 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_147

def loopBody464_149 : HolLoopProg 64 :=
.mark loopBody464_148

def loopBody464_150 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_149

def loopBody464_151 : HolLoopProg 64 :=
.mark loopBody464_150

def loopBody464_152 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_151

def loopBody464_153 : HolLoopProg 64 :=
.mark loopBody464_152

def loopBody464_154 : HolLoopProg 64 :=
.seq loopBody464_73 loopBody464_153

def loopBody464_155 : HolLoopProg 64 :=
.mark loopBody464_154

def loopBody464_156 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_155

def loopBody464_157 : HolLoopProg 64 :=
.mark loopBody464_156

def loopBody464_158 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_157

def loopBody464_159 : HolLoopProg 64 :=
.mark loopBody464_158

def loopBody464_160 : HolLoopProg 64 :=
.seq loopBody464_53 loopBody464_159

def loopBody464_161 : HolLoopProg 64 :=
.mark loopBody464_160

def loopBody464_162 : HolLoopProg 64 :=
.seq loopBody464_7 loopBody464_161

def loopBody464_163 : HolLoopProg 64 :=
.mark loopBody464_162

def loopBody464_164 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_163

def loopBody464_165 : HolLoopProg 64 :=
.mark loopBody464_164

def loopBody464_166 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_165

def loopBody464_167 : HolLoopProg 64 :=
.mark loopBody464_166

def loopBody464_168 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_167

def loopBody464_169 : HolLoopProg 64 :=
.mark loopBody464_168

def loopBody464_170 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_169

def loopBody464_171 : HolLoopProg 64 :=
.mark loopBody464_170

def loopBody464_172 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_171

def loopBody464_173 : HolLoopProg 64 :=
.mark loopBody464_172

def loopBody464_174 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_173

def loopBody464_175 : HolLoopProg 64 :=
.mark loopBody464_174

def loopBody464_176 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_175

def loopBody464_177 : HolLoopProg 64 :=
.mark loopBody464_176

def loopBody464_178 : HolLoopProg 64 :=
.seq loopBody464_1 loopBody464_177

def loopBody464_179 : HolLoopProg 64 :=
.mark loopBody464_178

def output464 : Nat × List Nat × HolLoopProg 64 :=
  (528, [], loopBody464_179)
end InitECandidate.Proofs.FrontendStages.Loop
