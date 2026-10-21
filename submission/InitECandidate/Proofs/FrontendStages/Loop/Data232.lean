import InitECandidate.Proofs.FrontendStages.Loop.Translate216
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody232_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody232_1 : HolLoopProg 64 :=
.mark loopBody232_0

def loopBody232_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody232_3 : HolLoopProg 64 :=
.mark loopBody232_2

def loopBody232_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody232_5 : HolLoopProg 64 :=
.mark loopBody232_4

def loopBody232_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody232_7 : HolLoopProg 64 :=
.mark loopBody232_6

def loopBody232_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody232_9 : HolLoopProg 64 :=
.mark loopBody232_8

def loopBody232_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 2)

def loopBody232_11 : HolLoopProg 64 :=
.mark loopBody232_10

def loopBody232_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody232_13 : HolLoopProg 64 :=
.mark loopBody232_12

def loopBody232_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.tick

def loopBody232_15 : HolLoopProg 64 :=
.mark loopBody232_14

def loopBody232_16 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_1

def loopBody232_17 : HolLoopProg 64 :=
.mark loopBody232_16

def loopBody232_18 : HolLoopProg 64 :=
.seq loopBody232_17 loopBody232_1

def loopBody232_19 : HolLoopProg 64 :=
.mark loopBody232_18

def loopBody232_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 3#64)

def loopBody232_21 : HolLoopProg 64 :=
.mark loopBody232_20

def loopBody232_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody232_23 : HolLoopProg 64 :=
.mark loopBody232_22

def loopBody232_24 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 282) ([9]) (some (9, loopBody232_23, loopBody232_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody232_25 : HolLoopProg 64 :=
.mark loopBody232_24

def loopBody232_26 : HolLoopProg 64 :=
.seq loopBody232_25 loopBody232_1

def loopBody232_27 : HolLoopProg 64 :=
.mark loopBody232_26

def loopBody232_28 : HolLoopProg 64 :=
.seq loopBody232_21 loopBody232_27

def loopBody232_29 : HolLoopProg 64 :=
.mark loopBody232_28

def loopBody232_30 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_29

def loopBody232_31 : HolLoopProg 64 :=
.mark loopBody232_30

def loopBody232_32 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_31

def loopBody232_33 : HolLoopProg 64 :=
.mark loopBody232_32

def loopBody232_34 : HolLoopProg 64 :=
.seq loopBody232_19 loopBody232_33

def loopBody232_35 : HolLoopProg 64 :=
.mark loopBody232_34

def loopBody232_36 : HolLoopProg 64 :=
.seq loopBody232_15 loopBody232_35

def loopBody232_37 : HolLoopProg 64 :=
.mark loopBody232_36

def loopBody232_38 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 1#64) loopBody232_13 loopBody232_37 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody232_39 : HolLoopProg 64 :=
.mark loopBody232_38

def loopBody232_40 : HolLoopProg 64 :=
.call (some
  ([3, 4, 5, 6],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 161) ([8, 9]) (some (8, loopBody232_39, loopBody232_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody232_41 : HolLoopProg 64 :=
.mark loopBody232_40

def loopBody232_42 : HolLoopProg 64 :=
.seq loopBody232_41 loopBody232_1

def loopBody232_43 : HolLoopProg 64 :=
.mark loopBody232_42

def loopBody232_44 : HolLoopProg 64 :=
.seq loopBody232_11 loopBody232_43

def loopBody232_45 : HolLoopProg 64 :=
.mark loopBody232_44

def loopBody232_46 : HolLoopProg 64 :=
.seq loopBody232_9 loopBody232_45

def loopBody232_47 : HolLoopProg 64 :=
.mark loopBody232_46

def loopBody232_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 3)

def loopBody232_49 : HolLoopProg 64 :=
.mark loopBody232_48

def loopBody232_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody232_51 : HolLoopProg 64 :=
.mark loopBody232_50

def loopBody232_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 1#64)

def loopBody232_53 : HolLoopProg 64 :=
.mark loopBody232_52

def loopBody232_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody232_55 : HolLoopProg 64 :=
.mark loopBody232_54

def loopBody232_56 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 9 (Flapjack.RegImm.reg 10) loopBody232_53 loopBody232_55 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))

def loopBody232_57 : HolLoopProg 64 :=
.mark loopBody232_56

def loopBody232_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody232_59 : HolLoopProg 64 :=
.mark loopBody232_58

def loopBody232_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody232_61 : HolLoopProg 64 :=
.mark loopBody232_60

def loopBody232_62 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 9 (Flapjack.RegImm.reg 10) loopBody232_53 loopBody232_55 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))

def loopBody232_63 : HolLoopProg 64 :=
.mark loopBody232_62

def loopBody232_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody232_65 : HolLoopProg 64 :=
.mark loopBody232_64

def loopBody232_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody232_67 : HolLoopProg 64 :=
.mark loopBody232_66

def loopBody232_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [8, 9, 10, 11]

def loopBody232_69 : HolLoopProg 64 :=
.mark loopBody232_68

def loopBody232_70 : HolLoopProg 64 :=
.seq loopBody232_69 loopBody232_1

def loopBody232_71 : HolLoopProg 64 :=
.mark loopBody232_70

def loopBody232_72 : HolLoopProg 64 :=
.seq loopBody232_67 loopBody232_71

def loopBody232_73 : HolLoopProg 64 :=
.mark loopBody232_72

def loopBody232_74 : HolLoopProg 64 :=
.seq loopBody232_51 loopBody232_73

def loopBody232_75 : HolLoopProg 64 :=
.mark loopBody232_74

def loopBody232_76 : HolLoopProg 64 :=
.seq loopBody232_55 loopBody232_75

def loopBody232_77 : HolLoopProg 64 :=
.mark loopBody232_76

def loopBody232_78 : HolLoopProg 64 :=
.seq loopBody232_65 loopBody232_77

def loopBody232_79 : HolLoopProg 64 :=
.mark loopBody232_78

def loopBody232_80 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody232_79 loopBody232_1 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody232_81 : HolLoopProg 64 :=
.mark loopBody232_80

def loopBody232_82 : HolLoopProg 64 :=
.seq loopBody232_81 loopBody232_1

def loopBody232_83 : HolLoopProg 64 :=
.mark loopBody232_82

def loopBody232_84 : HolLoopProg 64 :=
.seq loopBody232_59 loopBody232_83

def loopBody232_85 : HolLoopProg 64 :=
.mark loopBody232_84

def loopBody232_86 : HolLoopProg 64 :=
.seq loopBody232_63 loopBody232_85

def loopBody232_87 : HolLoopProg 64 :=
.mark loopBody232_86

def loopBody232_88 : HolLoopProg 64 :=
.seq loopBody232_51 loopBody232_87

def loopBody232_89 : HolLoopProg 64 :=
.mark loopBody232_88

def loopBody232_90 : HolLoopProg 64 :=
.seq loopBody232_61 loopBody232_89

def loopBody232_91 : HolLoopProg 64 :=
.mark loopBody232_90

def loopBody232_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 32#64)

def loopBody232_93 : HolLoopProg 64 :=
.mark loopBody232_92

def loopBody232_94 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.reg 10) loopBody232_53 loopBody232_55 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))

def loopBody232_95 : HolLoopProg 64 :=
.mark loopBody232_94

def loopBody232_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 10#64)

def loopBody232_97 : HolLoopProg 64 :=
.mark loopBody232_96

def loopBody232_98 : HolLoopProg 64 :=
.call (some ([8], Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)) (some 282) ([9]) (some (9, loopBody232_23, loopBody232_1, (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))

def loopBody232_99 : HolLoopProg 64 :=
.mark loopBody232_98

def loopBody232_100 : HolLoopProg 64 :=
.seq loopBody232_99 loopBody232_1

def loopBody232_101 : HolLoopProg 64 :=
.mark loopBody232_100

def loopBody232_102 : HolLoopProg 64 :=
.seq loopBody232_97 loopBody232_101

def loopBody232_103 : HolLoopProg 64 :=
.mark loopBody232_102

def loopBody232_104 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_103

def loopBody232_105 : HolLoopProg 64 :=
.mark loopBody232_104

def loopBody232_106 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_105

def loopBody232_107 : HolLoopProg 64 :=
.mark loopBody232_106

def loopBody232_108 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody232_107 loopBody232_1 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)

def loopBody232_109 : HolLoopProg 64 :=
.mark loopBody232_108

def loopBody232_110 : HolLoopProg 64 :=
.seq loopBody232_109 loopBody232_1

def loopBody232_111 : HolLoopProg 64 :=
.mark loopBody232_110

def loopBody232_112 : HolLoopProg 64 :=
.seq loopBody232_59 loopBody232_111

def loopBody232_113 : HolLoopProg 64 :=
.mark loopBody232_112

def loopBody232_114 : HolLoopProg 64 :=
.seq loopBody232_95 loopBody232_113

def loopBody232_115 : HolLoopProg 64 :=
.mark loopBody232_114

def loopBody232_116 : HolLoopProg 64 :=
.seq loopBody232_93 loopBody232_115

def loopBody232_117 : HolLoopProg 64 :=
.mark loopBody232_116

def loopBody232_118 : HolLoopProg 64 :=
.seq loopBody232_61 loopBody232_117

def loopBody232_119 : HolLoopProg 64 :=
.mark loopBody232_118

def loopBody232_120 : HolLoopProg 64 :=
.seq loopBody232_91 loopBody232_119

def loopBody232_121 : HolLoopProg 64 :=
.mark loopBody232_120

def loopBody232_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 0)

def loopBody232_123 : HolLoopProg 64 :=
.mark loopBody232_122

def loopBody232_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 4)

def loopBody232_125 : HolLoopProg 64 :=
.mark loopBody232_124

def loopBody232_126 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 11

def loopBody232_127 : HolLoopProg 64 :=
.mark loopBody232_126

def loopBody232_128 : HolLoopProg 64 :=
.call (some ([8, 9, 10], Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)) (some 290) ([11, 12]) (some (11, loopBody232_127, loopBody232_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))

def loopBody232_129 : HolLoopProg 64 :=
.mark loopBody232_128

def loopBody232_130 : HolLoopProg 64 :=
.seq loopBody232_129 loopBody232_1

def loopBody232_131 : HolLoopProg 64 :=
.mark loopBody232_130

def loopBody232_132 : HolLoopProg 64 :=
.seq loopBody232_125 loopBody232_131

def loopBody232_133 : HolLoopProg 64 :=
.mark loopBody232_132

def loopBody232_134 : HolLoopProg 64 :=
.seq loopBody232_123 loopBody232_133

def loopBody232_135 : HolLoopProg 64 :=
.mark loopBody232_134

def loopBody232_136 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 8)

def loopBody232_137 : HolLoopProg 64 :=
.mark loopBody232_136

def loopBody232_138 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 0#64)

def loopBody232_139 : HolLoopProg 64 :=
.mark loopBody232_138

def loopBody232_140 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody232_141 : HolLoopProg 64 :=
.mark loopBody232_140

def loopBody232_142 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 0#64)

def loopBody232_143 : HolLoopProg 64 :=
.mark loopBody232_142

def loopBody232_144 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.RegImm.reg 13) loopBody232_141 loopBody232_143 (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))

def loopBody232_145 : HolLoopProg 64 :=
.mark loopBody232_144

def loopBody232_146 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 12)

def loopBody232_147 : HolLoopProg 64 :=
.mark loopBody232_146

def loopBody232_148 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 12

def loopBody232_149 : HolLoopProg 64 :=
.mark loopBody232_148

def loopBody232_150 : HolLoopProg 64 :=
.call (some ([11], Flapjack.Spt.ln)) (some 291) ([12]) (some (12, loopBody232_149, loopBody232_1, (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))

def loopBody232_151 : HolLoopProg 64 :=
.mark loopBody232_150

def loopBody232_152 : HolLoopProg 64 :=
.seq loopBody232_151 loopBody232_1

def loopBody232_153 : HolLoopProg 64 :=
.mark loopBody232_152

def loopBody232_154 : HolLoopProg 64 :=
.seq loopBody232_125 loopBody232_153

def loopBody232_155 : HolLoopProg 64 :=
.mark loopBody232_154

def loopBody232_156 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 11)

def loopBody232_157 : HolLoopProg 64 :=
.mark loopBody232_156

def loopBody232_158 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 0#64)

def loopBody232_159 : HolLoopProg 64 :=
.mark loopBody232_158

def loopBody232_160 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 0#64)

def loopBody232_161 : HolLoopProg 64 :=
.mark loopBody232_160

def loopBody232_162 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [12, 13, 14, 15]

def loopBody232_163 : HolLoopProg 64 :=
.mark loopBody232_162

def loopBody232_164 : HolLoopProg 64 :=
.seq loopBody232_163 loopBody232_1

def loopBody232_165 : HolLoopProg 64 :=
.mark loopBody232_164

def loopBody232_166 : HolLoopProg 64 :=
.seq loopBody232_161 loopBody232_165

def loopBody232_167 : HolLoopProg 64 :=
.mark loopBody232_166

def loopBody232_168 : HolLoopProg 64 :=
.seq loopBody232_159 loopBody232_167

def loopBody232_169 : HolLoopProg 64 :=
.mark loopBody232_168

def loopBody232_170 : HolLoopProg 64 :=
.seq loopBody232_157 loopBody232_169

def loopBody232_171 : HolLoopProg 64 :=
.mark loopBody232_170

def loopBody232_172 : HolLoopProg 64 :=
.seq loopBody232_143 loopBody232_171

def loopBody232_173 : HolLoopProg 64 :=
.mark loopBody232_172

def loopBody232_174 : HolLoopProg 64 :=
.seq loopBody232_155 loopBody232_173

def loopBody232_175 : HolLoopProg 64 :=
.mark loopBody232_174

def loopBody232_176 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_175

def loopBody232_177 : HolLoopProg 64 :=
.mark loopBody232_176

def loopBody232_178 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_177

def loopBody232_179 : HolLoopProg 64 :=
.mark loopBody232_178

def loopBody232_180 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.RegImm.imm 0#64) loopBody232_179 loopBody232_1 (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))

def loopBody232_181 : HolLoopProg 64 :=
.mark loopBody232_180

def loopBody232_182 : HolLoopProg 64 :=
.seq loopBody232_181 loopBody232_1

def loopBody232_183 : HolLoopProg 64 :=
.mark loopBody232_182

def loopBody232_184 : HolLoopProg 64 :=
.seq loopBody232_147 loopBody232_183

def loopBody232_185 : HolLoopProg 64 :=
.mark loopBody232_184

def loopBody232_186 : HolLoopProg 64 :=
.seq loopBody232_145 loopBody232_185

def loopBody232_187 : HolLoopProg 64 :=
.mark loopBody232_186

def loopBody232_188 : HolLoopProg 64 :=
.seq loopBody232_139 loopBody232_187

def loopBody232_189 : HolLoopProg 64 :=
.mark loopBody232_188

def loopBody232_190 : HolLoopProg 64 :=
.seq loopBody232_137 loopBody232_189

def loopBody232_191 : HolLoopProg 64 :=
.mark loopBody232_190

def loopBody232_192 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 1#64)

def loopBody232_193 : HolLoopProg 64 :=
.mark loopBody232_192

def loopBody232_194 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 9)

def loopBody232_195 : HolLoopProg 64 :=
.mark loopBody232_194

def loopBody232_196 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 10)

def loopBody232_197 : HolLoopProg 64 :=
.mark loopBody232_196

def loopBody232_198 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 4)

def loopBody232_199 : HolLoopProg 64 :=
.mark loopBody232_198

def loopBody232_200 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [11, 12, 13, 14]

def loopBody232_201 : HolLoopProg 64 :=
.mark loopBody232_200

def loopBody232_202 : HolLoopProg 64 :=
.seq loopBody232_201 loopBody232_1

def loopBody232_203 : HolLoopProg 64 :=
.mark loopBody232_202

def loopBody232_204 : HolLoopProg 64 :=
.seq loopBody232_199 loopBody232_203

def loopBody232_205 : HolLoopProg 64 :=
.mark loopBody232_204

def loopBody232_206 : HolLoopProg 64 :=
.seq loopBody232_197 loopBody232_205

def loopBody232_207 : HolLoopProg 64 :=
.mark loopBody232_206

def loopBody232_208 : HolLoopProg 64 :=
.seq loopBody232_195 loopBody232_207

def loopBody232_209 : HolLoopProg 64 :=
.mark loopBody232_208

def loopBody232_210 : HolLoopProg 64 :=
.seq loopBody232_193 loopBody232_209

def loopBody232_211 : HolLoopProg 64 :=
.mark loopBody232_210

def loopBody232_212 : HolLoopProg 64 :=
.seq loopBody232_191 loopBody232_211

def loopBody232_213 : HolLoopProg 64 :=
.mark loopBody232_212

def loopBody232_214 : HolLoopProg 64 :=
.seq loopBody232_135 loopBody232_213

def loopBody232_215 : HolLoopProg 64 :=
.mark loopBody232_214

def loopBody232_216 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_215

def loopBody232_217 : HolLoopProg 64 :=
.mark loopBody232_216

def loopBody232_218 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_217

def loopBody232_219 : HolLoopProg 64 :=
.mark loopBody232_218

def loopBody232_220 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_219

def loopBody232_221 : HolLoopProg 64 :=
.mark loopBody232_220

def loopBody232_222 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_221

def loopBody232_223 : HolLoopProg 64 :=
.mark loopBody232_222

def loopBody232_224 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_223

def loopBody232_225 : HolLoopProg 64 :=
.mark loopBody232_224

def loopBody232_226 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_225

def loopBody232_227 : HolLoopProg 64 :=
.mark loopBody232_226

def loopBody232_228 : HolLoopProg 64 :=
.seq loopBody232_121 loopBody232_227

def loopBody232_229 : HolLoopProg 64 :=
.mark loopBody232_228

def loopBody232_230 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody232_229 loopBody232_1 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))

def loopBody232_231 : HolLoopProg 64 :=
.mark loopBody232_230

def loopBody232_232 : HolLoopProg 64 :=
.seq loopBody232_231 loopBody232_1

def loopBody232_233 : HolLoopProg 64 :=
.mark loopBody232_232

def loopBody232_234 : HolLoopProg 64 :=
.seq loopBody232_59 loopBody232_233

def loopBody232_235 : HolLoopProg 64 :=
.mark loopBody232_234

def loopBody232_236 : HolLoopProg 64 :=
.seq loopBody232_57 loopBody232_235

def loopBody232_237 : HolLoopProg 64 :=
.mark loopBody232_236

def loopBody232_238 : HolLoopProg 64 :=
.seq loopBody232_51 loopBody232_237

def loopBody232_239 : HolLoopProg 64 :=
.mark loopBody232_238

def loopBody232_240 : HolLoopProg 64 :=
.seq loopBody232_49 loopBody232_239

def loopBody232_241 : HolLoopProg 64 :=
.mark loopBody232_240

def loopBody232_242 : HolLoopProg 64 :=
.seq loopBody232_47 loopBody232_241

def loopBody232_243 : HolLoopProg 64 :=
.mark loopBody232_242

def loopBody232_244 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody232_245 : HolLoopProg 64 :=
.mark loopBody232_244

def loopBody232_246 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 1)

def loopBody232_247 : HolLoopProg 64 :=
.mark loopBody232_246

def loopBody232_248 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 2)

def loopBody232_249 : HolLoopProg 64 :=
.mark loopBody232_248

def loopBody232_250 : HolLoopProg 64 :=
.seq loopBody232_249 loopBody232_73

def loopBody232_251 : HolLoopProg 64 :=
.mark loopBody232_250

def loopBody232_252 : HolLoopProg 64 :=
.seq loopBody232_247 loopBody232_251

def loopBody232_253 : HolLoopProg 64 :=
.mark loopBody232_252

def loopBody232_254 : HolLoopProg 64 :=
.seq loopBody232_245 loopBody232_253

def loopBody232_255 : HolLoopProg 64 :=
.mark loopBody232_254

def loopBody232_256 : HolLoopProg 64 :=
.seq loopBody232_243 loopBody232_255

def loopBody232_257 : HolLoopProg 64 :=
.mark loopBody232_256

def loopBody232_258 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_257

def loopBody232_259 : HolLoopProg 64 :=
.mark loopBody232_258

def loopBody232_260 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_259

def loopBody232_261 : HolLoopProg 64 :=
.mark loopBody232_260

def loopBody232_262 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_261

def loopBody232_263 : HolLoopProg 64 :=
.mark loopBody232_262

def loopBody232_264 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_263

def loopBody232_265 : HolLoopProg 64 :=
.mark loopBody232_264

def loopBody232_266 : HolLoopProg 64 :=
.seq loopBody232_7 loopBody232_265

def loopBody232_267 : HolLoopProg 64 :=
.mark loopBody232_266

def loopBody232_268 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_267

def loopBody232_269 : HolLoopProg 64 :=
.mark loopBody232_268

def loopBody232_270 : HolLoopProg 64 :=
.seq loopBody232_5 loopBody232_269

def loopBody232_271 : HolLoopProg 64 :=
.mark loopBody232_270

def loopBody232_272 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_271

def loopBody232_273 : HolLoopProg 64 :=
.mark loopBody232_272

def loopBody232_274 : HolLoopProg 64 :=
.seq loopBody232_3 loopBody232_273

def loopBody232_275 : HolLoopProg 64 :=
.mark loopBody232_274

def loopBody232_276 : HolLoopProg 64 :=
.seq loopBody232_1 loopBody232_275

def loopBody232_277 : HolLoopProg 64 :=
.mark loopBody232_276

def output232 : Nat × List Nat × HolLoopProg 64 :=
  (296, [0, 1, 2], loopBody232_277)
end InitECandidate.Proofs.FrontendStages.Loop
