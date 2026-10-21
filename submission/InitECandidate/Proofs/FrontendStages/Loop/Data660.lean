import InitECandidate.Proofs.FrontendStages.Loop.Translate644
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody660_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody660_1 : HolLoopProg 64 :=
.mark loopBody660_0

def loopBody660_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.var 0))

def loopBody660_3 : HolLoopProg 64 :=
.mark loopBody660_2

def loopBody660_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64]))

def loopBody660_5 : HolLoopProg 64 :=
.mark loopBody660_4

def loopBody660_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64]))

def loopBody660_7 : HolLoopProg 64 :=
.mark loopBody660_6

def loopBody660_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 24#64]))

def loopBody660_9 : HolLoopProg 64 :=
.mark loopBody660_8

def loopBody660_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 32#64]))

def loopBody660_11 : HolLoopProg 64 :=
.mark loopBody660_10

def loopBody660_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 40#64]))

def loopBody660_13 : HolLoopProg 64 :=
.mark loopBody660_12

def loopBody660_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 2)

def loopBody660_15 : HolLoopProg 64 :=
.mark loopBody660_14

def loopBody660_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 3)

def loopBody660_17 : HolLoopProg 64 :=
.mark loopBody660_16

def loopBody660_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 4)

def loopBody660_19 : HolLoopProg 64 :=
.mark loopBody660_18

def loopBody660_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 5)

def loopBody660_21 : HolLoopProg 64 :=
.mark loopBody660_20

def loopBody660_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 6)

def loopBody660_23 : HolLoopProg 64 :=
.mark loopBody660_22

def loopBody660_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 7)

def loopBody660_25 : HolLoopProg 64 :=
.mark loopBody660_24

def loopBody660_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 14

def loopBody660_27 : HolLoopProg 64 :=
.mark loopBody660_26

def loopBody660_28 : HolLoopProg 64 :=
.call (some ([8, 9, 10, 11, 12, 13], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 713) ([14, 15, 16, 17, 18, 19]) (some (14, loopBody660_27, loopBody660_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))

def loopBody660_29 : HolLoopProg 64 :=
.mark loopBody660_28

def loopBody660_30 : HolLoopProg 64 :=
.seq loopBody660_29 loopBody660_1

def loopBody660_31 : HolLoopProg 64 :=
.mark loopBody660_30

def loopBody660_32 : HolLoopProg 64 :=
.seq loopBody660_25 loopBody660_31

def loopBody660_33 : HolLoopProg 64 :=
.mark loopBody660_32

def loopBody660_34 : HolLoopProg 64 :=
.seq loopBody660_23 loopBody660_33

def loopBody660_35 : HolLoopProg 64 :=
.mark loopBody660_34

def loopBody660_36 : HolLoopProg 64 :=
.seq loopBody660_21 loopBody660_35

def loopBody660_37 : HolLoopProg 64 :=
.mark loopBody660_36

def loopBody660_38 : HolLoopProg 64 :=
.seq loopBody660_19 loopBody660_37

def loopBody660_39 : HolLoopProg 64 :=
.mark loopBody660_38

def loopBody660_40 : HolLoopProg 64 :=
.seq loopBody660_17 loopBody660_39

def loopBody660_41 : HolLoopProg 64 :=
.mark loopBody660_40

def loopBody660_42 : HolLoopProg 64 :=
.seq loopBody660_15 loopBody660_41

def loopBody660_43 : HolLoopProg 64 :=
.mark loopBody660_42

def loopBody660_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 1)

def loopBody660_45 : HolLoopProg 64 :=
.mark loopBody660_44

def loopBody660_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.const 16#64)

def loopBody660_47 : HolLoopProg 64 :=
.mark loopBody660_46

def loopBody660_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 15

def loopBody660_49 : HolLoopProg 64 :=
.mark loopBody660_48

def loopBody660_50 : HolLoopProg 64 :=
.call (some
  ([14],
    Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))) (some 78) ([15, 16]) (some (15, loopBody660_49, loopBody660_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))

def loopBody660_51 : HolLoopProg 64 :=
.mark loopBody660_50

def loopBody660_52 : HolLoopProg 64 :=
.seq loopBody660_51 loopBody660_1

def loopBody660_53 : HolLoopProg 64 :=
.mark loopBody660_52

def loopBody660_54 : HolLoopProg 64 :=
.seq loopBody660_47 loopBody660_53

def loopBody660_55 : HolLoopProg 64 :=
.mark loopBody660_54

def loopBody660_56 : HolLoopProg 64 :=
.seq loopBody660_45 loopBody660_55

def loopBody660_57 : HolLoopProg 64 :=
.mark loopBody660_56

def loopBody660_58 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_57

def loopBody660_59 : HolLoopProg 64 :=
.mark loopBody660_58

def loopBody660_60 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_59

def loopBody660_61 : HolLoopProg 64 :=
.mark loopBody660_60

def loopBody660_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 8)

def loopBody660_63 : HolLoopProg 64 :=
.mark loopBody660_62

def loopBody660_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 9)

def loopBody660_65 : HolLoopProg 64 :=
.mark loopBody660_64

def loopBody660_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 10)

def loopBody660_67 : HolLoopProg 64 :=
.mark loopBody660_66

def loopBody660_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 11)

def loopBody660_69 : HolLoopProg 64 :=
.mark loopBody660_68

def loopBody660_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 12)

def loopBody660_71 : HolLoopProg 64 :=
.mark loopBody660_70

def loopBody660_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.var 13)

def loopBody660_73 : HolLoopProg 64 :=
.mark loopBody660_72

def loopBody660_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 21
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 16#64])

def loopBody660_75 : HolLoopProg 64 :=
.mark loopBody660_74

def loopBody660_76 : HolLoopProg 64 :=
.call (some ([14], Flapjack.Spt.ln)) (some 722) ([15, 16, 17, 18, 19, 20, 21]) (some (15, loopBody660_49, loopBody660_1, (Flapjack.Spt.ln)))

def loopBody660_77 : HolLoopProg 64 :=
.mark loopBody660_76

def loopBody660_78 : HolLoopProg 64 :=
.seq loopBody660_77 loopBody660_1

def loopBody660_79 : HolLoopProg 64 :=
.mark loopBody660_78

def loopBody660_80 : HolLoopProg 64 :=
.seq loopBody660_75 loopBody660_79

def loopBody660_81 : HolLoopProg 64 :=
.mark loopBody660_80

def loopBody660_82 : HolLoopProg 64 :=
.seq loopBody660_73 loopBody660_81

def loopBody660_83 : HolLoopProg 64 :=
.mark loopBody660_82

def loopBody660_84 : HolLoopProg 64 :=
.seq loopBody660_71 loopBody660_83

def loopBody660_85 : HolLoopProg 64 :=
.mark loopBody660_84

def loopBody660_86 : HolLoopProg 64 :=
.seq loopBody660_69 loopBody660_85

def loopBody660_87 : HolLoopProg 64 :=
.mark loopBody660_86

def loopBody660_88 : HolLoopProg 64 :=
.seq loopBody660_67 loopBody660_87

def loopBody660_89 : HolLoopProg 64 :=
.mark loopBody660_88

def loopBody660_90 : HolLoopProg 64 :=
.seq loopBody660_65 loopBody660_89

def loopBody660_91 : HolLoopProg 64 :=
.mark loopBody660_90

def loopBody660_92 : HolLoopProg 64 :=
.seq loopBody660_63 loopBody660_91

def loopBody660_93 : HolLoopProg 64 :=
.mark loopBody660_92

def loopBody660_94 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_93

def loopBody660_95 : HolLoopProg 64 :=
.mark loopBody660_94

def loopBody660_96 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_95

def loopBody660_97 : HolLoopProg 64 :=
.mark loopBody660_96

def loopBody660_98 : HolLoopProg 64 :=
.seq loopBody660_61 loopBody660_97

def loopBody660_99 : HolLoopProg 64 :=
.mark loopBody660_98

def loopBody660_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 0#64)

def loopBody660_101 : HolLoopProg 64 :=
.mark loopBody660_100

def loopBody660_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [14]

def loopBody660_103 : HolLoopProg 64 :=
.mark loopBody660_102

def loopBody660_104 : HolLoopProg 64 :=
.seq loopBody660_103 loopBody660_1

def loopBody660_105 : HolLoopProg 64 :=
.mark loopBody660_104

def loopBody660_106 : HolLoopProg 64 :=
.seq loopBody660_101 loopBody660_105

def loopBody660_107 : HolLoopProg 64 :=
.mark loopBody660_106

def loopBody660_108 : HolLoopProg 64 :=
.seq loopBody660_99 loopBody660_107

def loopBody660_109 : HolLoopProg 64 :=
.mark loopBody660_108

def loopBody660_110 : HolLoopProg 64 :=
.seq loopBody660_43 loopBody660_109

def loopBody660_111 : HolLoopProg 64 :=
.mark loopBody660_110

def loopBody660_112 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_111

def loopBody660_113 : HolLoopProg 64 :=
.mark loopBody660_112

def loopBody660_114 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_113

def loopBody660_115 : HolLoopProg 64 :=
.mark loopBody660_114

def loopBody660_116 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_115

def loopBody660_117 : HolLoopProg 64 :=
.mark loopBody660_116

def loopBody660_118 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_117

def loopBody660_119 : HolLoopProg 64 :=
.mark loopBody660_118

def loopBody660_120 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_119

def loopBody660_121 : HolLoopProg 64 :=
.mark loopBody660_120

def loopBody660_122 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_121

def loopBody660_123 : HolLoopProg 64 :=
.mark loopBody660_122

def loopBody660_124 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_123

def loopBody660_125 : HolLoopProg 64 :=
.mark loopBody660_124

def loopBody660_126 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_125

def loopBody660_127 : HolLoopProg 64 :=
.mark loopBody660_126

def loopBody660_128 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_127

def loopBody660_129 : HolLoopProg 64 :=
.mark loopBody660_128

def loopBody660_130 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_129

def loopBody660_131 : HolLoopProg 64 :=
.mark loopBody660_130

def loopBody660_132 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_131

def loopBody660_133 : HolLoopProg 64 :=
.mark loopBody660_132

def loopBody660_134 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_133

def loopBody660_135 : HolLoopProg 64 :=
.mark loopBody660_134

def loopBody660_136 : HolLoopProg 64 :=
.seq loopBody660_13 loopBody660_135

def loopBody660_137 : HolLoopProg 64 :=
.mark loopBody660_136

def loopBody660_138 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_137

def loopBody660_139 : HolLoopProg 64 :=
.mark loopBody660_138

def loopBody660_140 : HolLoopProg 64 :=
.seq loopBody660_11 loopBody660_139

def loopBody660_141 : HolLoopProg 64 :=
.mark loopBody660_140

def loopBody660_142 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_141

def loopBody660_143 : HolLoopProg 64 :=
.mark loopBody660_142

def loopBody660_144 : HolLoopProg 64 :=
.seq loopBody660_9 loopBody660_143

def loopBody660_145 : HolLoopProg 64 :=
.mark loopBody660_144

def loopBody660_146 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_145

def loopBody660_147 : HolLoopProg 64 :=
.mark loopBody660_146

def loopBody660_148 : HolLoopProg 64 :=
.seq loopBody660_7 loopBody660_147

def loopBody660_149 : HolLoopProg 64 :=
.mark loopBody660_148

def loopBody660_150 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_149

def loopBody660_151 : HolLoopProg 64 :=
.mark loopBody660_150

def loopBody660_152 : HolLoopProg 64 :=
.seq loopBody660_5 loopBody660_151

def loopBody660_153 : HolLoopProg 64 :=
.mark loopBody660_152

def loopBody660_154 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_153

def loopBody660_155 : HolLoopProg 64 :=
.mark loopBody660_154

def loopBody660_156 : HolLoopProg 64 :=
.seq loopBody660_3 loopBody660_155

def loopBody660_157 : HolLoopProg 64 :=
.mark loopBody660_156

def loopBody660_158 : HolLoopProg 64 :=
.seq loopBody660_1 loopBody660_157

def loopBody660_159 : HolLoopProg 64 :=
.mark loopBody660_158

def output660 : Nat × List Nat × HolLoopProg 64 :=
  (724, [0, 1], loopBody660_159)
end InitECandidate.Proofs.FrontendStages.Loop
