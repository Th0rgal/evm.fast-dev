import InitECandidate.Proofs.FrontendStages.Loop.Translate446
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody462_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody462_1 : HolLoopProg 64 :=
.mark loopBody462_0

def loopBody462_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody462_3 : HolLoopProg 64 :=
.mark loopBody462_2

def loopBody462_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody462_3, loopBody462_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody462_5 : HolLoopProg 64 :=
.mark loopBody462_4

def loopBody462_6 : HolLoopProg 64 :=
.seq loopBody462_5 loopBody462_1

def loopBody462_7 : HolLoopProg 64 :=
.mark loopBody462_6

def loopBody462_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody462_9 : HolLoopProg 64 :=
.mark loopBody462_8

def loopBody462_10 : HolLoopProg 64 :=
.call (some
  ([5, 6, 7, 8],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 471) ([]) (some (9, loopBody462_9, loopBody462_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody462_11 : HolLoopProg 64 :=
.mark loopBody462_10

def loopBody462_12 : HolLoopProg 64 :=
.seq loopBody462_11 loopBody462_1

def loopBody462_13 : HolLoopProg 64 :=
.mark loopBody462_12

def loopBody462_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 3#64)

def loopBody462_15 : HolLoopProg 64 :=
.mark loopBody462_14

def loopBody462_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 1)

def loopBody462_17 : HolLoopProg 64 :=
.mark loopBody462_16

def loopBody462_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 2)

def loopBody462_19 : HolLoopProg 64 :=
.mark loopBody462_18

def loopBody462_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 3)

def loopBody462_21 : HolLoopProg 64 :=
.mark loopBody462_20

def loopBody462_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 4)

def loopBody462_23 : HolLoopProg 64 :=
.mark loopBody462_22

def loopBody462_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 32#64)

def loopBody462_25 : HolLoopProg 64 :=
.mark loopBody462_24

def loopBody462_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.const 0#64)

def loopBody462_27 : HolLoopProg 64 :=
.mark loopBody462_26

def loopBody462_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.const 0#64)

def loopBody462_29 : HolLoopProg 64 :=
.mark loopBody462_28

def loopBody462_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.const 0#64)

def loopBody462_31 : HolLoopProg 64 :=
.mark loopBody462_30

def loopBody462_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody462_33 : HolLoopProg 64 :=
.mark loopBody462_32

def loopBody462_34 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 479) ([10, 11, 12, 13, 14, 15, 16, 17, 18]) (some (10, loopBody462_33, loopBody462_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody462_35 : HolLoopProg 64 :=
.mark loopBody462_34

def loopBody462_36 : HolLoopProg 64 :=
.seq loopBody462_35 loopBody462_1

def loopBody462_37 : HolLoopProg 64 :=
.mark loopBody462_36

def loopBody462_38 : HolLoopProg 64 :=
.seq loopBody462_31 loopBody462_37

def loopBody462_39 : HolLoopProg 64 :=
.mark loopBody462_38

def loopBody462_40 : HolLoopProg 64 :=
.seq loopBody462_29 loopBody462_39

def loopBody462_41 : HolLoopProg 64 :=
.mark loopBody462_40

def loopBody462_42 : HolLoopProg 64 :=
.seq loopBody462_27 loopBody462_41

def loopBody462_43 : HolLoopProg 64 :=
.mark loopBody462_42

def loopBody462_44 : HolLoopProg 64 :=
.seq loopBody462_25 loopBody462_43

def loopBody462_45 : HolLoopProg 64 :=
.mark loopBody462_44

def loopBody462_46 : HolLoopProg 64 :=
.seq loopBody462_23 loopBody462_45

def loopBody462_47 : HolLoopProg 64 :=
.mark loopBody462_46

def loopBody462_48 : HolLoopProg 64 :=
.seq loopBody462_21 loopBody462_47

def loopBody462_49 : HolLoopProg 64 :=
.mark loopBody462_48

def loopBody462_50 : HolLoopProg 64 :=
.seq loopBody462_19 loopBody462_49

def loopBody462_51 : HolLoopProg 64 :=
.mark loopBody462_50

def loopBody462_52 : HolLoopProg 64 :=
.seq loopBody462_17 loopBody462_51

def loopBody462_53 : HolLoopProg 64 :=
.mark loopBody462_52

def loopBody462_54 : HolLoopProg 64 :=
.seq loopBody462_15 loopBody462_53

def loopBody462_55 : HolLoopProg 64 :=
.mark loopBody462_54

def loopBody462_56 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_55

def loopBody462_57 : HolLoopProg 64 :=
.mark loopBody462_56

def loopBody462_58 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_57

def loopBody462_59 : HolLoopProg 64 :=
.mark loopBody462_58

def loopBody462_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 1)

def loopBody462_61 : HolLoopProg 64 :=
.mark loopBody462_60

def loopBody462_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 2)

def loopBody462_63 : HolLoopProg 64 :=
.mark loopBody462_62

def loopBody462_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 3)

def loopBody462_65 : HolLoopProg 64 :=
.mark loopBody462_64

def loopBody462_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 4)

def loopBody462_67 : HolLoopProg 64 :=
.mark loopBody462_66

def loopBody462_68 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))) (some 458) ([10, 11, 12, 13]) (some (10, loopBody462_33, loopBody462_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody462_69 : HolLoopProg 64 :=
.mark loopBody462_68

def loopBody462_70 : HolLoopProg 64 :=
.seq loopBody462_69 loopBody462_1

def loopBody462_71 : HolLoopProg 64 :=
.mark loopBody462_70

def loopBody462_72 : HolLoopProg 64 :=
.seq loopBody462_67 loopBody462_71

def loopBody462_73 : HolLoopProg 64 :=
.mark loopBody462_72

def loopBody462_74 : HolLoopProg 64 :=
.seq loopBody462_65 loopBody462_73

def loopBody462_75 : HolLoopProg 64 :=
.mark loopBody462_74

def loopBody462_76 : HolLoopProg 64 :=
.seq loopBody462_63 loopBody462_75

def loopBody462_77 : HolLoopProg 64 :=
.mark loopBody462_76

def loopBody462_78 : HolLoopProg 64 :=
.seq loopBody462_61 loopBody462_77

def loopBody462_79 : HolLoopProg 64 :=
.mark loopBody462_78

def loopBody462_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 5)

def loopBody462_81 : HolLoopProg 64 :=
.mark loopBody462_80

def loopBody462_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 6)

def loopBody462_83 : HolLoopProg 64 :=
.mark loopBody462_82

def loopBody462_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 7)

def loopBody462_85 : HolLoopProg 64 :=
.mark loopBody462_84

def loopBody462_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 8)

def loopBody462_87 : HolLoopProg 64 :=
.mark loopBody462_86

def loopBody462_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 24#64]),
      Flapjack.HolLoopExp.var 9])

def loopBody462_89 : HolLoopProg 64 :=
.mark loopBody462_88

def loopBody462_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 11

def loopBody462_91 : HolLoopProg 64 :=
.mark loopBody462_90

def loopBody462_92 : HolLoopProg 64 :=
.call (some ([10], Flapjack.Spt.ln)) (some 147) ([11, 12, 13, 14, 15]) (some (11, loopBody462_91, loopBody462_1, (Flapjack.Spt.ln)))

def loopBody462_93 : HolLoopProg 64 :=
.mark loopBody462_92

def loopBody462_94 : HolLoopProg 64 :=
.seq loopBody462_93 loopBody462_1

def loopBody462_95 : HolLoopProg 64 :=
.mark loopBody462_94

def loopBody462_96 : HolLoopProg 64 :=
.seq loopBody462_89 loopBody462_95

def loopBody462_97 : HolLoopProg 64 :=
.mark loopBody462_96

def loopBody462_98 : HolLoopProg 64 :=
.seq loopBody462_87 loopBody462_97

def loopBody462_99 : HolLoopProg 64 :=
.mark loopBody462_98

def loopBody462_100 : HolLoopProg 64 :=
.seq loopBody462_85 loopBody462_99

def loopBody462_101 : HolLoopProg 64 :=
.mark loopBody462_100

def loopBody462_102 : HolLoopProg 64 :=
.seq loopBody462_83 loopBody462_101

def loopBody462_103 : HolLoopProg 64 :=
.mark loopBody462_102

def loopBody462_104 : HolLoopProg 64 :=
.seq loopBody462_81 loopBody462_103

def loopBody462_105 : HolLoopProg 64 :=
.mark loopBody462_104

def loopBody462_106 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_105

def loopBody462_107 : HolLoopProg 64 :=
.mark loopBody462_106

def loopBody462_108 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_107

def loopBody462_109 : HolLoopProg 64 :=
.mark loopBody462_108

def loopBody462_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 1#64)

def loopBody462_111 : HolLoopProg 64 :=
.mark loopBody462_110

def loopBody462_112 : HolLoopProg 64 :=
.call (some ([10], Flapjack.Spt.ln)) (some 486) ([11]) (some (11, loopBody462_91, loopBody462_1, (Flapjack.Spt.ln)))

def loopBody462_113 : HolLoopProg 64 :=
.mark loopBody462_112

def loopBody462_114 : HolLoopProg 64 :=
.seq loopBody462_113 loopBody462_1

def loopBody462_115 : HolLoopProg 64 :=
.mark loopBody462_114

def loopBody462_116 : HolLoopProg 64 :=
.seq loopBody462_111 loopBody462_115

def loopBody462_117 : HolLoopProg 64 :=
.mark loopBody462_116

def loopBody462_118 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_117

def loopBody462_119 : HolLoopProg 64 :=
.mark loopBody462_118

def loopBody462_120 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_119

def loopBody462_121 : HolLoopProg 64 :=
.mark loopBody462_120

def loopBody462_122 : HolLoopProg 64 :=
.seq loopBody462_109 loopBody462_121

def loopBody462_123 : HolLoopProg 64 :=
.mark loopBody462_122

def loopBody462_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody462_125 : HolLoopProg 64 :=
.mark loopBody462_124

def loopBody462_126 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [10]

def loopBody462_127 : HolLoopProg 64 :=
.mark loopBody462_126

def loopBody462_128 : HolLoopProg 64 :=
.seq loopBody462_127 loopBody462_1

def loopBody462_129 : HolLoopProg 64 :=
.mark loopBody462_128

def loopBody462_130 : HolLoopProg 64 :=
.seq loopBody462_125 loopBody462_129

def loopBody462_131 : HolLoopProg 64 :=
.mark loopBody462_130

def loopBody462_132 : HolLoopProg 64 :=
.seq loopBody462_123 loopBody462_131

def loopBody462_133 : HolLoopProg 64 :=
.mark loopBody462_132

def loopBody462_134 : HolLoopProg 64 :=
.seq loopBody462_79 loopBody462_133

def loopBody462_135 : HolLoopProg 64 :=
.mark loopBody462_134

def loopBody462_136 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_135

def loopBody462_137 : HolLoopProg 64 :=
.mark loopBody462_136

def loopBody462_138 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_137

def loopBody462_139 : HolLoopProg 64 :=
.mark loopBody462_138

def loopBody462_140 : HolLoopProg 64 :=
.seq loopBody462_59 loopBody462_139

def loopBody462_141 : HolLoopProg 64 :=
.mark loopBody462_140

def loopBody462_142 : HolLoopProg 64 :=
.seq loopBody462_13 loopBody462_141

def loopBody462_143 : HolLoopProg 64 :=
.mark loopBody462_142

def loopBody462_144 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_143

def loopBody462_145 : HolLoopProg 64 :=
.mark loopBody462_144

def loopBody462_146 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_145

def loopBody462_147 : HolLoopProg 64 :=
.mark loopBody462_146

def loopBody462_148 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_147

def loopBody462_149 : HolLoopProg 64 :=
.mark loopBody462_148

def loopBody462_150 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_149

def loopBody462_151 : HolLoopProg 64 :=
.mark loopBody462_150

def loopBody462_152 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_151

def loopBody462_153 : HolLoopProg 64 :=
.mark loopBody462_152

def loopBody462_154 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_153

def loopBody462_155 : HolLoopProg 64 :=
.mark loopBody462_154

def loopBody462_156 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_155

def loopBody462_157 : HolLoopProg 64 :=
.mark loopBody462_156

def loopBody462_158 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_157

def loopBody462_159 : HolLoopProg 64 :=
.mark loopBody462_158

def loopBody462_160 : HolLoopProg 64 :=
.seq loopBody462_7 loopBody462_159

def loopBody462_161 : HolLoopProg 64 :=
.mark loopBody462_160

def loopBody462_162 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_161

def loopBody462_163 : HolLoopProg 64 :=
.mark loopBody462_162

def loopBody462_164 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_163

def loopBody462_165 : HolLoopProg 64 :=
.mark loopBody462_164

def loopBody462_166 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_165

def loopBody462_167 : HolLoopProg 64 :=
.mark loopBody462_166

def loopBody462_168 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_167

def loopBody462_169 : HolLoopProg 64 :=
.mark loopBody462_168

def loopBody462_170 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_169

def loopBody462_171 : HolLoopProg 64 :=
.mark loopBody462_170

def loopBody462_172 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_171

def loopBody462_173 : HolLoopProg 64 :=
.mark loopBody462_172

def loopBody462_174 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_173

def loopBody462_175 : HolLoopProg 64 :=
.mark loopBody462_174

def loopBody462_176 : HolLoopProg 64 :=
.seq loopBody462_1 loopBody462_175

def loopBody462_177 : HolLoopProg 64 :=
.mark loopBody462_176

def output462 : Nat × List Nat × HolLoopProg 64 :=
  (526, [], loopBody462_177)
end InitECandidate.Proofs.FrontendStages.Loop
