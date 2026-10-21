import InitECandidate.Proofs.FrontendStages.Loop.Translate467
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody483_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody483_1 : HolLoopProg 64 :=
.mark loopBody483_0

def loopBody483_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody483_3 : HolLoopProg 64 :=
.mark loopBody483_2

def loopBody483_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody483_3, loopBody483_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody483_5 : HolLoopProg 64 :=
.mark loopBody483_4

def loopBody483_6 : HolLoopProg 64 :=
.seq loopBody483_5 loopBody483_1

def loopBody483_7 : HolLoopProg 64 :=
.mark loopBody483_6

def loopBody483_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 100#64)

def loopBody483_9 : HolLoopProg 64 :=
.mark loopBody483_8

def loopBody483_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody483_11 : HolLoopProg 64 :=
.mark loopBody483_10

def loopBody483_12 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 466) ([6]) (some (6, loopBody483_11, loopBody483_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody483_13 : HolLoopProg 64 :=
.mark loopBody483_12

def loopBody483_14 : HolLoopProg 64 :=
.seq loopBody483_13 loopBody483_1

def loopBody483_15 : HolLoopProg 64 :=
.mark loopBody483_14

def loopBody483_16 : HolLoopProg 64 :=
.seq loopBody483_9 loopBody483_15

def loopBody483_17 : HolLoopProg 64 :=
.mark loopBody483_16

def loopBody483_18 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_17

def loopBody483_19 : HolLoopProg 64 :=
.mark loopBody483_18

def loopBody483_20 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_19

def loopBody483_21 : HolLoopProg 64 :=
.mark loopBody483_20

def loopBody483_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 280#64]))

def loopBody483_23 : HolLoopProg 64 :=
.mark loopBody483_22

def loopBody483_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody483_25 : HolLoopProg 64 :=
.mark loopBody483_24

def loopBody483_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody483_27 : HolLoopProg 64 :=
.mark loopBody483_26

def loopBody483_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 3)

def loopBody483_29 : HolLoopProg 64 :=
.mark loopBody483_28

def loopBody483_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 4)

def loopBody483_31 : HolLoopProg 64 :=
.mark loopBody483_30

def loopBody483_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 5)

def loopBody483_33 : HolLoopProg 64 :=
.mark loopBody483_32

def loopBody483_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody483_35 : HolLoopProg 64 :=
.mark loopBody483_34

def loopBody483_36 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))) (some 147) ([7, 8, 9, 10, 11]) (some (7, loopBody483_35, loopBody483_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody483_37 : HolLoopProg 64 :=
.mark loopBody483_36

def loopBody483_38 : HolLoopProg 64 :=
.seq loopBody483_37 loopBody483_1

def loopBody483_39 : HolLoopProg 64 :=
.mark loopBody483_38

def loopBody483_40 : HolLoopProg 64 :=
.seq loopBody483_33 loopBody483_39

def loopBody483_41 : HolLoopProg 64 :=
.mark loopBody483_40

def loopBody483_42 : HolLoopProg 64 :=
.seq loopBody483_31 loopBody483_41

def loopBody483_43 : HolLoopProg 64 :=
.mark loopBody483_42

def loopBody483_44 : HolLoopProg 64 :=
.seq loopBody483_29 loopBody483_43

def loopBody483_45 : HolLoopProg 64 :=
.mark loopBody483_44

def loopBody483_46 : HolLoopProg 64 :=
.seq loopBody483_27 loopBody483_45

def loopBody483_47 : HolLoopProg 64 :=
.mark loopBody483_46

def loopBody483_48 : HolLoopProg 64 :=
.seq loopBody483_25 loopBody483_47

def loopBody483_49 : HolLoopProg 64 :=
.mark loopBody483_48

def loopBody483_50 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_49

def loopBody483_51 : HolLoopProg 64 :=
.mark loopBody483_50

def loopBody483_52 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_51

def loopBody483_53 : HolLoopProg 64 :=
.mark loopBody483_52

def loopBody483_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.add
            [Flapjack.HolLoopExp.load
                (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                  [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
              Flapjack.HolLoopExp.const 112#64]),
        Flapjack.HolLoopExp.const 32#64]))

def loopBody483_55 : HolLoopProg 64 :=
.mark loopBody483_54

def loopBody483_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 6)

def loopBody483_57 : HolLoopProg 64 :=
.mark loopBody483_56

def loopBody483_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 5)

def loopBody483_59 : HolLoopProg 64 :=
.mark loopBody483_58

def loopBody483_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 11

def loopBody483_61 : HolLoopProg 64 :=
.mark loopBody483_60

def loopBody483_62 : HolLoopProg 64 :=
.call (some ([7, 8, 9, 10], Flapjack.Spt.ln)) (some 408) ([11, 12]) (some (11, loopBody483_61, loopBody483_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody483_63 : HolLoopProg 64 :=
.mark loopBody483_62

def loopBody483_64 : HolLoopProg 64 :=
.seq loopBody483_63 loopBody483_1

def loopBody483_65 : HolLoopProg 64 :=
.mark loopBody483_64

def loopBody483_66 : HolLoopProg 64 :=
.seq loopBody483_59 loopBody483_65

def loopBody483_67 : HolLoopProg 64 :=
.mark loopBody483_66

def loopBody483_68 : HolLoopProg 64 :=
.seq loopBody483_57 loopBody483_67

def loopBody483_69 : HolLoopProg 64 :=
.mark loopBody483_68

def loopBody483_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 7)

def loopBody483_71 : HolLoopProg 64 :=
.mark loopBody483_70

def loopBody483_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 8)

def loopBody483_73 : HolLoopProg 64 :=
.mark loopBody483_72

def loopBody483_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 9)

def loopBody483_75 : HolLoopProg 64 :=
.mark loopBody483_74

def loopBody483_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 10)

def loopBody483_77 : HolLoopProg 64 :=
.mark loopBody483_76

def loopBody483_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 12

def loopBody483_79 : HolLoopProg 64 :=
.mark loopBody483_78

def loopBody483_80 : HolLoopProg 64 :=
.call (some ([11], Flapjack.Spt.ln)) (some 472) ([12, 13, 14, 15]) (some (12, loopBody483_79, loopBody483_1, (Flapjack.Spt.ln)))

def loopBody483_81 : HolLoopProg 64 :=
.mark loopBody483_80

def loopBody483_82 : HolLoopProg 64 :=
.seq loopBody483_81 loopBody483_1

def loopBody483_83 : HolLoopProg 64 :=
.mark loopBody483_82

def loopBody483_84 : HolLoopProg 64 :=
.seq loopBody483_77 loopBody483_83

def loopBody483_85 : HolLoopProg 64 :=
.mark loopBody483_84

def loopBody483_86 : HolLoopProg 64 :=
.seq loopBody483_75 loopBody483_85

def loopBody483_87 : HolLoopProg 64 :=
.mark loopBody483_86

def loopBody483_88 : HolLoopProg 64 :=
.seq loopBody483_73 loopBody483_87

def loopBody483_89 : HolLoopProg 64 :=
.mark loopBody483_88

def loopBody483_90 : HolLoopProg 64 :=
.seq loopBody483_71 loopBody483_89

def loopBody483_91 : HolLoopProg 64 :=
.mark loopBody483_90

def loopBody483_92 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_91

def loopBody483_93 : HolLoopProg 64 :=
.mark loopBody483_92

def loopBody483_94 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_93

def loopBody483_95 : HolLoopProg 64 :=
.mark loopBody483_94

def loopBody483_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody483_97 : HolLoopProg 64 :=
.mark loopBody483_96

def loopBody483_98 : HolLoopProg 64 :=
.call (some ([11], Flapjack.Spt.ln)) (some 486) ([12]) (some (12, loopBody483_79, loopBody483_1, (Flapjack.Spt.ln)))

def loopBody483_99 : HolLoopProg 64 :=
.mark loopBody483_98

def loopBody483_100 : HolLoopProg 64 :=
.seq loopBody483_99 loopBody483_1

def loopBody483_101 : HolLoopProg 64 :=
.mark loopBody483_100

def loopBody483_102 : HolLoopProg 64 :=
.seq loopBody483_97 loopBody483_101

def loopBody483_103 : HolLoopProg 64 :=
.mark loopBody483_102

def loopBody483_104 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_103

def loopBody483_105 : HolLoopProg 64 :=
.mark loopBody483_104

def loopBody483_106 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_105

def loopBody483_107 : HolLoopProg 64 :=
.mark loopBody483_106

def loopBody483_108 : HolLoopProg 64 :=
.seq loopBody483_95 loopBody483_107

def loopBody483_109 : HolLoopProg 64 :=
.mark loopBody483_108

def loopBody483_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody483_111 : HolLoopProg 64 :=
.mark loopBody483_110

def loopBody483_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [11]

def loopBody483_113 : HolLoopProg 64 :=
.mark loopBody483_112

def loopBody483_114 : HolLoopProg 64 :=
.seq loopBody483_113 loopBody483_1

def loopBody483_115 : HolLoopProg 64 :=
.mark loopBody483_114

def loopBody483_116 : HolLoopProg 64 :=
.seq loopBody483_111 loopBody483_115

def loopBody483_117 : HolLoopProg 64 :=
.mark loopBody483_116

def loopBody483_118 : HolLoopProg 64 :=
.seq loopBody483_109 loopBody483_117

def loopBody483_119 : HolLoopProg 64 :=
.mark loopBody483_118

def loopBody483_120 : HolLoopProg 64 :=
.seq loopBody483_69 loopBody483_119

def loopBody483_121 : HolLoopProg 64 :=
.mark loopBody483_120

def loopBody483_122 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_121

def loopBody483_123 : HolLoopProg 64 :=
.mark loopBody483_122

def loopBody483_124 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_123

def loopBody483_125 : HolLoopProg 64 :=
.mark loopBody483_124

def loopBody483_126 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_125

def loopBody483_127 : HolLoopProg 64 :=
.mark loopBody483_126

def loopBody483_128 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_127

def loopBody483_129 : HolLoopProg 64 :=
.mark loopBody483_128

def loopBody483_130 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_129

def loopBody483_131 : HolLoopProg 64 :=
.mark loopBody483_130

def loopBody483_132 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_131

def loopBody483_133 : HolLoopProg 64 :=
.mark loopBody483_132

def loopBody483_134 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_133

def loopBody483_135 : HolLoopProg 64 :=
.mark loopBody483_134

def loopBody483_136 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_135

def loopBody483_137 : HolLoopProg 64 :=
.mark loopBody483_136

def loopBody483_138 : HolLoopProg 64 :=
.seq loopBody483_55 loopBody483_137

def loopBody483_139 : HolLoopProg 64 :=
.mark loopBody483_138

def loopBody483_140 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_139

def loopBody483_141 : HolLoopProg 64 :=
.mark loopBody483_140

def loopBody483_142 : HolLoopProg 64 :=
.seq loopBody483_53 loopBody483_141

def loopBody483_143 : HolLoopProg 64 :=
.mark loopBody483_142

def loopBody483_144 : HolLoopProg 64 :=
.seq loopBody483_23 loopBody483_143

def loopBody483_145 : HolLoopProg 64 :=
.mark loopBody483_144

def loopBody483_146 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_145

def loopBody483_147 : HolLoopProg 64 :=
.mark loopBody483_146

def loopBody483_148 : HolLoopProg 64 :=
.seq loopBody483_21 loopBody483_147

def loopBody483_149 : HolLoopProg 64 :=
.mark loopBody483_148

def loopBody483_150 : HolLoopProg 64 :=
.seq loopBody483_7 loopBody483_149

def loopBody483_151 : HolLoopProg 64 :=
.mark loopBody483_150

def loopBody483_152 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_151

def loopBody483_153 : HolLoopProg 64 :=
.mark loopBody483_152

def loopBody483_154 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_153

def loopBody483_155 : HolLoopProg 64 :=
.mark loopBody483_154

def loopBody483_156 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_155

def loopBody483_157 : HolLoopProg 64 :=
.mark loopBody483_156

def loopBody483_158 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_157

def loopBody483_159 : HolLoopProg 64 :=
.mark loopBody483_158

def loopBody483_160 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_159

def loopBody483_161 : HolLoopProg 64 :=
.mark loopBody483_160

def loopBody483_162 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_161

def loopBody483_163 : HolLoopProg 64 :=
.mark loopBody483_162

def loopBody483_164 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_163

def loopBody483_165 : HolLoopProg 64 :=
.mark loopBody483_164

def loopBody483_166 : HolLoopProg 64 :=
.seq loopBody483_1 loopBody483_165

def loopBody483_167 : HolLoopProg 64 :=
.mark loopBody483_166

def output483 : Nat × List Nat × HolLoopProg 64 :=
  (547, [], loopBody483_167)
end InitECandidate.Proofs.FrontendStages.Loop
