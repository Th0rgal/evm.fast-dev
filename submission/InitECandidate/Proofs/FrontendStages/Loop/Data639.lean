import InitECandidate.Proofs.FrontendStages.Loop.Translate623
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody639_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 5)

def loopBody639_1 : HolLoopProg 64 :=
.mark loopBody639_0

def loopBody639_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 11)

def loopBody639_3 : HolLoopProg 64 :=
.mark loopBody639_2

def loopBody639_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 1#64)

def loopBody639_5 : HolLoopProg 64 :=
.mark loopBody639_4

def loopBody639_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 0#64)

def loopBody639_7 : HolLoopProg 64 :=
.mark loopBody639_6

def loopBody639_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 13 (Flapjack.RegImm.reg 14) loopBody639_5 loopBody639_7 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody639_9 : HolLoopProg 64 :=
.mark loopBody639_8

def loopBody639_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 13)

def loopBody639_11 : HolLoopProg 64 :=
.mark loopBody639_10

def loopBody639_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 13 (Flapjack.RegImm.reg 14) loopBody639_5 loopBody639_7 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))

def loopBody639_13 : HolLoopProg 64 :=
.mark loopBody639_12

def loopBody639_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody639_15 : HolLoopProg 64 :=
.mark loopBody639_14

def loopBody639_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [12]

def loopBody639_17 : HolLoopProg 64 :=
.mark loopBody639_16

def loopBody639_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody639_19 : HolLoopProg 64 :=
.mark loopBody639_18

def loopBody639_20 : HolLoopProg 64 :=
.seq loopBody639_17 loopBody639_19

def loopBody639_21 : HolLoopProg 64 :=
.mark loopBody639_20

def loopBody639_22 : HolLoopProg 64 :=
.seq loopBody639_15 loopBody639_21

def loopBody639_23 : HolLoopProg 64 :=
.mark loopBody639_22

def loopBody639_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 15 (Flapjack.RegImm.imm 0#64) loopBody639_23 loopBody639_19 (Flapjack.Spt.ln)

def loopBody639_25 : HolLoopProg 64 :=
.mark loopBody639_24

def loopBody639_26 : HolLoopProg 64 :=
.seq loopBody639_25 loopBody639_19

def loopBody639_27 : HolLoopProg 64 :=
.mark loopBody639_26

def loopBody639_28 : HolLoopProg 64 :=
.seq loopBody639_11 loopBody639_27

def loopBody639_29 : HolLoopProg 64 :=
.mark loopBody639_28

def loopBody639_30 : HolLoopProg 64 :=
.seq loopBody639_13 loopBody639_29

def loopBody639_31 : HolLoopProg 64 :=
.mark loopBody639_30

def loopBody639_32 : HolLoopProg 64 :=
.seq loopBody639_3 loopBody639_31

def loopBody639_33 : HolLoopProg 64 :=
.mark loopBody639_32

def loopBody639_34 : HolLoopProg 64 :=
.seq loopBody639_1 loopBody639_33

def loopBody639_35 : HolLoopProg 64 :=
.mark loopBody639_34

def loopBody639_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 0#64)

def loopBody639_37 : HolLoopProg 64 :=
.mark loopBody639_36

def loopBody639_38 : HolLoopProg 64 :=
.seq loopBody639_37 loopBody639_21

def loopBody639_39 : HolLoopProg 64 :=
.mark loopBody639_38

def loopBody639_40 : HolLoopProg 64 :=
.seq loopBody639_35 loopBody639_39

def loopBody639_41 : HolLoopProg 64 :=
.mark loopBody639_40

def loopBody639_42 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 15 (Flapjack.RegImm.imm 0#64) loopBody639_41 loopBody639_19 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody639_43 : HolLoopProg 64 :=
.mark loopBody639_42

def loopBody639_44 : HolLoopProg 64 :=
.seq loopBody639_43 loopBody639_19

def loopBody639_45 : HolLoopProg 64 :=
.mark loopBody639_44

def loopBody639_46 : HolLoopProg 64 :=
.seq loopBody639_11 loopBody639_45

def loopBody639_47 : HolLoopProg 64 :=
.mark loopBody639_46

def loopBody639_48 : HolLoopProg 64 :=
.seq loopBody639_9 loopBody639_47

def loopBody639_49 : HolLoopProg 64 :=
.mark loopBody639_48

def loopBody639_50 : HolLoopProg 64 :=
.seq loopBody639_3 loopBody639_49

def loopBody639_51 : HolLoopProg 64 :=
.mark loopBody639_50

def loopBody639_52 : HolLoopProg 64 :=
.seq loopBody639_1 loopBody639_51

def loopBody639_53 : HolLoopProg 64 :=
.mark loopBody639_52

def loopBody639_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 4)

def loopBody639_55 : HolLoopProg 64 :=
.mark loopBody639_54

def loopBody639_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 10)

def loopBody639_57 : HolLoopProg 64 :=
.mark loopBody639_56

def loopBody639_58 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 13 (Flapjack.RegImm.reg 14) loopBody639_5 loopBody639_7 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody639_59 : HolLoopProg 64 :=
.mark loopBody639_58

def loopBody639_60 : HolLoopProg 64 :=
.seq loopBody639_57 loopBody639_31

def loopBody639_61 : HolLoopProg 64 :=
.mark loopBody639_60

def loopBody639_62 : HolLoopProg 64 :=
.seq loopBody639_55 loopBody639_61

def loopBody639_63 : HolLoopProg 64 :=
.mark loopBody639_62

def loopBody639_64 : HolLoopProg 64 :=
.seq loopBody639_63 loopBody639_39

def loopBody639_65 : HolLoopProg 64 :=
.mark loopBody639_64

def loopBody639_66 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 15 (Flapjack.RegImm.imm 0#64) loopBody639_65 loopBody639_19 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody639_67 : HolLoopProg 64 :=
.mark loopBody639_66

def loopBody639_68 : HolLoopProg 64 :=
.seq loopBody639_67 loopBody639_19

def loopBody639_69 : HolLoopProg 64 :=
.mark loopBody639_68

def loopBody639_70 : HolLoopProg 64 :=
.seq loopBody639_11 loopBody639_69

def loopBody639_71 : HolLoopProg 64 :=
.mark loopBody639_70

def loopBody639_72 : HolLoopProg 64 :=
.seq loopBody639_59 loopBody639_71

def loopBody639_73 : HolLoopProg 64 :=
.mark loopBody639_72

def loopBody639_74 : HolLoopProg 64 :=
.seq loopBody639_57 loopBody639_73

def loopBody639_75 : HolLoopProg 64 :=
.mark loopBody639_74

def loopBody639_76 : HolLoopProg 64 :=
.seq loopBody639_55 loopBody639_75

def loopBody639_77 : HolLoopProg 64 :=
.mark loopBody639_76

def loopBody639_78 : HolLoopProg 64 :=
.seq loopBody639_53 loopBody639_77

def loopBody639_79 : HolLoopProg 64 :=
.mark loopBody639_78

def loopBody639_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 3)

def loopBody639_81 : HolLoopProg 64 :=
.mark loopBody639_80

def loopBody639_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 9)

def loopBody639_83 : HolLoopProg 64 :=
.mark loopBody639_82

def loopBody639_84 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 13 (Flapjack.RegImm.reg 14) loopBody639_5 loopBody639_7 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody639_85 : HolLoopProg 64 :=
.mark loopBody639_84

def loopBody639_86 : HolLoopProg 64 :=
.seq loopBody639_83 loopBody639_31

def loopBody639_87 : HolLoopProg 64 :=
.mark loopBody639_86

def loopBody639_88 : HolLoopProg 64 :=
.seq loopBody639_81 loopBody639_87

def loopBody639_89 : HolLoopProg 64 :=
.mark loopBody639_88

def loopBody639_90 : HolLoopProg 64 :=
.seq loopBody639_89 loopBody639_39

def loopBody639_91 : HolLoopProg 64 :=
.mark loopBody639_90

def loopBody639_92 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 15 (Flapjack.RegImm.imm 0#64) loopBody639_91 loopBody639_19 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody639_93 : HolLoopProg 64 :=
.mark loopBody639_92

def loopBody639_94 : HolLoopProg 64 :=
.seq loopBody639_93 loopBody639_19

def loopBody639_95 : HolLoopProg 64 :=
.mark loopBody639_94

def loopBody639_96 : HolLoopProg 64 :=
.seq loopBody639_11 loopBody639_95

def loopBody639_97 : HolLoopProg 64 :=
.mark loopBody639_96

def loopBody639_98 : HolLoopProg 64 :=
.seq loopBody639_85 loopBody639_97

def loopBody639_99 : HolLoopProg 64 :=
.mark loopBody639_98

def loopBody639_100 : HolLoopProg 64 :=
.seq loopBody639_83 loopBody639_99

def loopBody639_101 : HolLoopProg 64 :=
.mark loopBody639_100

def loopBody639_102 : HolLoopProg 64 :=
.seq loopBody639_81 loopBody639_101

def loopBody639_103 : HolLoopProg 64 :=
.mark loopBody639_102

def loopBody639_104 : HolLoopProg 64 :=
.seq loopBody639_79 loopBody639_103

def loopBody639_105 : HolLoopProg 64 :=
.mark loopBody639_104

def loopBody639_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 2)

def loopBody639_107 : HolLoopProg 64 :=
.mark loopBody639_106

def loopBody639_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 8)

def loopBody639_109 : HolLoopProg 64 :=
.mark loopBody639_108

def loopBody639_110 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 13 (Flapjack.RegImm.reg 14) loopBody639_5 loopBody639_7 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody639_111 : HolLoopProg 64 :=
.mark loopBody639_110

def loopBody639_112 : HolLoopProg 64 :=
.seq loopBody639_109 loopBody639_31

def loopBody639_113 : HolLoopProg 64 :=
.mark loopBody639_112

def loopBody639_114 : HolLoopProg 64 :=
.seq loopBody639_107 loopBody639_113

def loopBody639_115 : HolLoopProg 64 :=
.mark loopBody639_114

def loopBody639_116 : HolLoopProg 64 :=
.seq loopBody639_115 loopBody639_39

def loopBody639_117 : HolLoopProg 64 :=
.mark loopBody639_116

def loopBody639_118 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 15 (Flapjack.RegImm.imm 0#64) loopBody639_117 loopBody639_19 (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody639_119 : HolLoopProg 64 :=
.mark loopBody639_118

def loopBody639_120 : HolLoopProg 64 :=
.seq loopBody639_119 loopBody639_19

def loopBody639_121 : HolLoopProg 64 :=
.mark loopBody639_120

def loopBody639_122 : HolLoopProg 64 :=
.seq loopBody639_11 loopBody639_121

def loopBody639_123 : HolLoopProg 64 :=
.mark loopBody639_122

def loopBody639_124 : HolLoopProg 64 :=
.seq loopBody639_111 loopBody639_123

def loopBody639_125 : HolLoopProg 64 :=
.mark loopBody639_124

def loopBody639_126 : HolLoopProg 64 :=
.seq loopBody639_109 loopBody639_125

def loopBody639_127 : HolLoopProg 64 :=
.mark loopBody639_126

def loopBody639_128 : HolLoopProg 64 :=
.seq loopBody639_107 loopBody639_127

def loopBody639_129 : HolLoopProg 64 :=
.mark loopBody639_128

def loopBody639_130 : HolLoopProg 64 :=
.seq loopBody639_105 loopBody639_129

def loopBody639_131 : HolLoopProg 64 :=
.mark loopBody639_130

def loopBody639_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 1)

def loopBody639_133 : HolLoopProg 64 :=
.mark loopBody639_132

def loopBody639_134 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 7)

def loopBody639_135 : HolLoopProg 64 :=
.mark loopBody639_134

def loopBody639_136 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 13 (Flapjack.RegImm.reg 14) loopBody639_5 loopBody639_7 (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody639_137 : HolLoopProg 64 :=
.mark loopBody639_136

def loopBody639_138 : HolLoopProg 64 :=
.seq loopBody639_135 loopBody639_31

def loopBody639_139 : HolLoopProg 64 :=
.mark loopBody639_138

def loopBody639_140 : HolLoopProg 64 :=
.seq loopBody639_133 loopBody639_139

def loopBody639_141 : HolLoopProg 64 :=
.mark loopBody639_140

def loopBody639_142 : HolLoopProg 64 :=
.seq loopBody639_141 loopBody639_39

def loopBody639_143 : HolLoopProg 64 :=
.mark loopBody639_142

def loopBody639_144 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 15 (Flapjack.RegImm.imm 0#64) loopBody639_143 loopBody639_19 (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)

def loopBody639_145 : HolLoopProg 64 :=
.mark loopBody639_144

def loopBody639_146 : HolLoopProg 64 :=
.seq loopBody639_145 loopBody639_19

def loopBody639_147 : HolLoopProg 64 :=
.mark loopBody639_146

def loopBody639_148 : HolLoopProg 64 :=
.seq loopBody639_11 loopBody639_147

def loopBody639_149 : HolLoopProg 64 :=
.mark loopBody639_148

def loopBody639_150 : HolLoopProg 64 :=
.seq loopBody639_137 loopBody639_149

def loopBody639_151 : HolLoopProg 64 :=
.mark loopBody639_150

def loopBody639_152 : HolLoopProg 64 :=
.seq loopBody639_135 loopBody639_151

def loopBody639_153 : HolLoopProg 64 :=
.mark loopBody639_152

def loopBody639_154 : HolLoopProg 64 :=
.seq loopBody639_133 loopBody639_153

def loopBody639_155 : HolLoopProg 64 :=
.mark loopBody639_154

def loopBody639_156 : HolLoopProg 64 :=
.seq loopBody639_131 loopBody639_155

def loopBody639_157 : HolLoopProg 64 :=
.mark loopBody639_156

def loopBody639_158 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 0)

def loopBody639_159 : HolLoopProg 64 :=
.mark loopBody639_158

def loopBody639_160 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 6)

def loopBody639_161 : HolLoopProg 64 :=
.mark loopBody639_160

def loopBody639_162 : HolLoopProg 64 :=
.seq loopBody639_161 loopBody639_31

def loopBody639_163 : HolLoopProg 64 :=
.mark loopBody639_162

def loopBody639_164 : HolLoopProg 64 :=
.seq loopBody639_159 loopBody639_163

def loopBody639_165 : HolLoopProg 64 :=
.mark loopBody639_164

def loopBody639_166 : HolLoopProg 64 :=
.seq loopBody639_157 loopBody639_165

def loopBody639_167 : HolLoopProg 64 :=
.mark loopBody639_166

def loopBody639_168 : HolLoopProg 64 :=
.seq loopBody639_167 loopBody639_39

def loopBody639_169 : HolLoopProg 64 :=
.mark loopBody639_168

def output639 : Nat × List Nat × HolLoopProg 64 :=
  (703, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], loopBody639_169)
end InitECandidate.Proofs.FrontendStages.Loop
