import InitECandidate.Proofs.FrontendStages.Loop.Translate470
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody486_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody486_1 : HolLoopProg 64 :=
.mark loopBody486_0

def loopBody486_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody486_3 : HolLoopProg 64 :=
.mark loopBody486_2

def loopBody486_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody486_3, loopBody486_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody486_5 : HolLoopProg 64 :=
.mark loopBody486_4

def loopBody486_6 : HolLoopProg 64 :=
.seq loopBody486_5 loopBody486_1

def loopBody486_7 : HolLoopProg 64 :=
.mark loopBody486_6

def loopBody486_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody486_9 : HolLoopProg 64 :=
.mark loopBody486_8

def loopBody486_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody486_11 : HolLoopProg 64 :=
.mark loopBody486_10

def loopBody486_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody486_13 : HolLoopProg 64 :=
.mark loopBody486_12

def loopBody486_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody486_15 : HolLoopProg 64 :=
.mark loopBody486_14

def loopBody486_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody486_17 : HolLoopProg 64 :=
.mark loopBody486_16

def loopBody486_18 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 462) ([6, 7, 8, 9]) (some (6, loopBody486_17, loopBody486_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody486_19 : HolLoopProg 64 :=
.mark loopBody486_18

def loopBody486_20 : HolLoopProg 64 :=
.seq loopBody486_19 loopBody486_1

def loopBody486_21 : HolLoopProg 64 :=
.mark loopBody486_20

def loopBody486_22 : HolLoopProg 64 :=
.seq loopBody486_15 loopBody486_21

def loopBody486_23 : HolLoopProg 64 :=
.mark loopBody486_22

def loopBody486_24 : HolLoopProg 64 :=
.seq loopBody486_13 loopBody486_23

def loopBody486_25 : HolLoopProg 64 :=
.mark loopBody486_24

def loopBody486_26 : HolLoopProg 64 :=
.seq loopBody486_11 loopBody486_25

def loopBody486_27 : HolLoopProg 64 :=
.mark loopBody486_26

def loopBody486_28 : HolLoopProg 64 :=
.seq loopBody486_9 loopBody486_27

def loopBody486_29 : HolLoopProg 64 :=
.mark loopBody486_28

def loopBody486_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody486_31 : HolLoopProg 64 :=
.mark loopBody486_30

def loopBody486_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody486_33 : HolLoopProg 64 :=
.mark loopBody486_32

def loopBody486_34 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))) (some 491) ([7]) (some (7, loopBody486_33, loopBody486_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody486_35 : HolLoopProg 64 :=
.mark loopBody486_34

def loopBody486_36 : HolLoopProg 64 :=
.seq loopBody486_35 loopBody486_1

def loopBody486_37 : HolLoopProg 64 :=
.mark loopBody486_36

def loopBody486_38 : HolLoopProg 64 :=
.seq loopBody486_31 loopBody486_37

def loopBody486_39 : HolLoopProg 64 :=
.mark loopBody486_38

def loopBody486_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody486_41 : HolLoopProg 64 :=
.mark loopBody486_40

def loopBody486_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody486_43 : HolLoopProg 64 :=
.mark loopBody486_42

def loopBody486_44 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))) (some 466) ([8]) (some (8, loopBody486_43, loopBody486_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody486_45 : HolLoopProg 64 :=
.mark loopBody486_44

def loopBody486_46 : HolLoopProg 64 :=
.seq loopBody486_45 loopBody486_1

def loopBody486_47 : HolLoopProg 64 :=
.mark loopBody486_46

def loopBody486_48 : HolLoopProg 64 :=
.seq loopBody486_41 loopBody486_47

def loopBody486_49 : HolLoopProg 64 :=
.mark loopBody486_48

def loopBody486_50 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_49

def loopBody486_51 : HolLoopProg 64 :=
.mark loopBody486_50

def loopBody486_52 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_51

def loopBody486_53 : HolLoopProg 64 :=
.mark loopBody486_52

def loopBody486_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody486_55 : HolLoopProg 64 :=
.mark loopBody486_54

def loopBody486_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 6)

def loopBody486_57 : HolLoopProg 64 :=
.mark loopBody486_56

def loopBody486_58 : HolLoopProg 64 :=
.call (some ([7], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))) (some 492) ([8, 9]) (some (8, loopBody486_43, loopBody486_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody486_59 : HolLoopProg 64 :=
.mark loopBody486_58

def loopBody486_60 : HolLoopProg 64 :=
.seq loopBody486_59 loopBody486_1

def loopBody486_61 : HolLoopProg 64 :=
.mark loopBody486_60

def loopBody486_62 : HolLoopProg 64 :=
.seq loopBody486_57 loopBody486_61

def loopBody486_63 : HolLoopProg 64 :=
.mark loopBody486_62

def loopBody486_64 : HolLoopProg 64 :=
.seq loopBody486_55 loopBody486_63

def loopBody486_65 : HolLoopProg 64 :=
.mark loopBody486_64

def loopBody486_66 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_65

def loopBody486_67 : HolLoopProg 64 :=
.mark loopBody486_66

def loopBody486_68 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_67

def loopBody486_69 : HolLoopProg 64 :=
.mark loopBody486_68

def loopBody486_70 : HolLoopProg 64 :=
.seq loopBody486_53 loopBody486_69

def loopBody486_71 : HolLoopProg 64 :=
.mark loopBody486_70

def loopBody486_72 : HolLoopProg 64 :=
.call (some ([7], Flapjack.Spt.ln)) (some 403) ([8]) (some (8, loopBody486_43, loopBody486_1, (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody486_73 : HolLoopProg 64 :=
.mark loopBody486_72

def loopBody486_74 : HolLoopProg 64 :=
.seq loopBody486_73 loopBody486_1

def loopBody486_75 : HolLoopProg 64 :=
.mark loopBody486_74

def loopBody486_76 : HolLoopProg 64 :=
.seq loopBody486_55 loopBody486_75

def loopBody486_77 : HolLoopProg 64 :=
.mark loopBody486_76

def loopBody486_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 8#64]))

def loopBody486_79 : HolLoopProg 64 :=
.mark loopBody486_78

def loopBody486_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 8#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody486_81 : HolLoopProg 64 :=
.mark loopBody486_80

def loopBody486_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 8#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody486_83 : HolLoopProg 64 :=
.mark loopBody486_82

def loopBody486_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 8#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody486_85 : HolLoopProg 64 :=
.mark loopBody486_84

def loopBody486_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody486_87 : HolLoopProg 64 :=
.mark loopBody486_86

def loopBody486_88 : HolLoopProg 64 :=
.call (some ([8], Flapjack.Spt.ln)) (some 472) ([9, 10, 11, 12]) (some (9, loopBody486_87, loopBody486_1, (Flapjack.Spt.ln)))

def loopBody486_89 : HolLoopProg 64 :=
.mark loopBody486_88

def loopBody486_90 : HolLoopProg 64 :=
.seq loopBody486_89 loopBody486_1

def loopBody486_91 : HolLoopProg 64 :=
.mark loopBody486_90

def loopBody486_92 : HolLoopProg 64 :=
.seq loopBody486_85 loopBody486_91

def loopBody486_93 : HolLoopProg 64 :=
.mark loopBody486_92

def loopBody486_94 : HolLoopProg 64 :=
.seq loopBody486_83 loopBody486_93

def loopBody486_95 : HolLoopProg 64 :=
.mark loopBody486_94

def loopBody486_96 : HolLoopProg 64 :=
.seq loopBody486_81 loopBody486_95

def loopBody486_97 : HolLoopProg 64 :=
.mark loopBody486_96

def loopBody486_98 : HolLoopProg 64 :=
.seq loopBody486_79 loopBody486_97

def loopBody486_99 : HolLoopProg 64 :=
.mark loopBody486_98

def loopBody486_100 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_99

def loopBody486_101 : HolLoopProg 64 :=
.mark loopBody486_100

def loopBody486_102 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_101

def loopBody486_103 : HolLoopProg 64 :=
.mark loopBody486_102

def loopBody486_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 1#64)

def loopBody486_105 : HolLoopProg 64 :=
.mark loopBody486_104

def loopBody486_106 : HolLoopProg 64 :=
.call (some ([8], Flapjack.Spt.ln)) (some 486) ([9]) (some (9, loopBody486_87, loopBody486_1, (Flapjack.Spt.ln)))

def loopBody486_107 : HolLoopProg 64 :=
.mark loopBody486_106

def loopBody486_108 : HolLoopProg 64 :=
.seq loopBody486_107 loopBody486_1

def loopBody486_109 : HolLoopProg 64 :=
.mark loopBody486_108

def loopBody486_110 : HolLoopProg 64 :=
.seq loopBody486_105 loopBody486_109

def loopBody486_111 : HolLoopProg 64 :=
.mark loopBody486_110

def loopBody486_112 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_111

def loopBody486_113 : HolLoopProg 64 :=
.mark loopBody486_112

def loopBody486_114 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_113

def loopBody486_115 : HolLoopProg 64 :=
.mark loopBody486_114

def loopBody486_116 : HolLoopProg 64 :=
.seq loopBody486_103 loopBody486_115

def loopBody486_117 : HolLoopProg 64 :=
.mark loopBody486_116

def loopBody486_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody486_119 : HolLoopProg 64 :=
.mark loopBody486_118

def loopBody486_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [8]

def loopBody486_121 : HolLoopProg 64 :=
.mark loopBody486_120

def loopBody486_122 : HolLoopProg 64 :=
.seq loopBody486_121 loopBody486_1

def loopBody486_123 : HolLoopProg 64 :=
.mark loopBody486_122

def loopBody486_124 : HolLoopProg 64 :=
.seq loopBody486_119 loopBody486_123

def loopBody486_125 : HolLoopProg 64 :=
.mark loopBody486_124

def loopBody486_126 : HolLoopProg 64 :=
.seq loopBody486_117 loopBody486_125

def loopBody486_127 : HolLoopProg 64 :=
.mark loopBody486_126

def loopBody486_128 : HolLoopProg 64 :=
.seq loopBody486_77 loopBody486_127

def loopBody486_129 : HolLoopProg 64 :=
.mark loopBody486_128

def loopBody486_130 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_129

def loopBody486_131 : HolLoopProg 64 :=
.mark loopBody486_130

def loopBody486_132 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_131

def loopBody486_133 : HolLoopProg 64 :=
.mark loopBody486_132

def loopBody486_134 : HolLoopProg 64 :=
.seq loopBody486_71 loopBody486_133

def loopBody486_135 : HolLoopProg 64 :=
.mark loopBody486_134

def loopBody486_136 : HolLoopProg 64 :=
.seq loopBody486_39 loopBody486_135

def loopBody486_137 : HolLoopProg 64 :=
.mark loopBody486_136

def loopBody486_138 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_137

def loopBody486_139 : HolLoopProg 64 :=
.mark loopBody486_138

def loopBody486_140 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_139

def loopBody486_141 : HolLoopProg 64 :=
.mark loopBody486_140

def loopBody486_142 : HolLoopProg 64 :=
.seq loopBody486_29 loopBody486_141

def loopBody486_143 : HolLoopProg 64 :=
.mark loopBody486_142

def loopBody486_144 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_143

def loopBody486_145 : HolLoopProg 64 :=
.mark loopBody486_144

def loopBody486_146 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_145

def loopBody486_147 : HolLoopProg 64 :=
.mark loopBody486_146

def loopBody486_148 : HolLoopProg 64 :=
.seq loopBody486_7 loopBody486_147

def loopBody486_149 : HolLoopProg 64 :=
.mark loopBody486_148

def loopBody486_150 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_149

def loopBody486_151 : HolLoopProg 64 :=
.mark loopBody486_150

def loopBody486_152 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_151

def loopBody486_153 : HolLoopProg 64 :=
.mark loopBody486_152

def loopBody486_154 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_153

def loopBody486_155 : HolLoopProg 64 :=
.mark loopBody486_154

def loopBody486_156 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_155

def loopBody486_157 : HolLoopProg 64 :=
.mark loopBody486_156

def loopBody486_158 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_157

def loopBody486_159 : HolLoopProg 64 :=
.mark loopBody486_158

def loopBody486_160 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_159

def loopBody486_161 : HolLoopProg 64 :=
.mark loopBody486_160

def loopBody486_162 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_161

def loopBody486_163 : HolLoopProg 64 :=
.mark loopBody486_162

def loopBody486_164 : HolLoopProg 64 :=
.seq loopBody486_1 loopBody486_163

def loopBody486_165 : HolLoopProg 64 :=
.mark loopBody486_164

def output486 : Nat × List Nat × HolLoopProg 64 :=
  (550, [], loopBody486_165)
end InitECandidate.Proofs.FrontendStages.Loop
