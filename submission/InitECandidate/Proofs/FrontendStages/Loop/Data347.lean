import InitECandidate.Proofs.FrontendStages.Loop.Translate331
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody347_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody347_1 : HolLoopProg 64 :=
.mark loopBody347_0

def loopBody347_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody347_3 : HolLoopProg 64 :=
.mark loopBody347_2

def loopBody347_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody347_5 : HolLoopProg 64 :=
.mark loopBody347_4

def loopBody347_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 403) ([2]) (some (2, loopBody347_5, loopBody347_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody347_7 : HolLoopProg 64 :=
.mark loopBody347_6

def loopBody347_8 : HolLoopProg 64 :=
.seq loopBody347_7 loopBody347_1

def loopBody347_9 : HolLoopProg 64 :=
.mark loopBody347_8

def loopBody347_10 : HolLoopProg 64 :=
.seq loopBody347_3 loopBody347_9

def loopBody347_11 : HolLoopProg 64 :=
.mark loopBody347_10

def loopBody347_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 0#64]))

def loopBody347_13 : HolLoopProg 64 :=
.mark loopBody347_12

def loopBody347_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody347_15 : HolLoopProg 64 :=
.mark loopBody347_14

def loopBody347_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody347_17 : HolLoopProg 64 :=
.mark loopBody347_16

def loopBody347_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody347_19 : HolLoopProg 64 :=
.mark loopBody347_18

def loopBody347_20 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 3 (Flapjack.RegImm.reg 4) loopBody347_17 loopBody347_19 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody347_21 : HolLoopProg 64 :=
.mark loopBody347_20

def loopBody347_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody347_23 : HolLoopProg 64 :=
.mark loopBody347_22

def loopBody347_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody347_25 : HolLoopProg 64 :=
.mark loopBody347_24

def loopBody347_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody347_27 : HolLoopProg 64 :=
.mark loopBody347_26

def loopBody347_28 : HolLoopProg 64 :=
.seq loopBody347_27 loopBody347_1

def loopBody347_29 : HolLoopProg 64 :=
.mark loopBody347_28

def loopBody347_30 : HolLoopProg 64 :=
.seq loopBody347_25 loopBody347_29

def loopBody347_31 : HolLoopProg 64 :=
.mark loopBody347_30

def loopBody347_32 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody347_31 loopBody347_1 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody347_33 : HolLoopProg 64 :=
.mark loopBody347_32

def loopBody347_34 : HolLoopProg 64 :=
.seq loopBody347_33 loopBody347_1

def loopBody347_35 : HolLoopProg 64 :=
.mark loopBody347_34

def loopBody347_36 : HolLoopProg 64 :=
.seq loopBody347_23 loopBody347_35

def loopBody347_37 : HolLoopProg 64 :=
.mark loopBody347_36

def loopBody347_38 : HolLoopProg 64 :=
.seq loopBody347_21 loopBody347_37

def loopBody347_39 : HolLoopProg 64 :=
.mark loopBody347_38

def loopBody347_40 : HolLoopProg 64 :=
.seq loopBody347_15 loopBody347_39

def loopBody347_41 : HolLoopProg 64 :=
.mark loopBody347_40

def loopBody347_42 : HolLoopProg 64 :=
.seq loopBody347_13 loopBody347_41

def loopBody347_43 : HolLoopProg 64 :=
.mark loopBody347_42

def loopBody347_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 48#64]))

def loopBody347_45 : HolLoopProg 64 :=
.mark loopBody347_44

def loopBody347_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 136#64]))

def loopBody347_47 : HolLoopProg 64 :=
.mark loopBody347_46

def loopBody347_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 32#64)

def loopBody347_49 : HolLoopProg 64 :=
.mark loopBody347_48

def loopBody347_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody347_51 : HolLoopProg 64 :=
.mark loopBody347_50

def loopBody347_52 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ls PUnit.unit)) (some 79) ([3, 4, 5]) (some (3, loopBody347_51, loopBody347_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))

def loopBody347_53 : HolLoopProg 64 :=
.mark loopBody347_52

def loopBody347_54 : HolLoopProg 64 :=
.seq loopBody347_53 loopBody347_1

def loopBody347_55 : HolLoopProg 64 :=
.mark loopBody347_54

def loopBody347_56 : HolLoopProg 64 :=
.seq loopBody347_49 loopBody347_55

def loopBody347_57 : HolLoopProg 64 :=
.mark loopBody347_56

def loopBody347_58 : HolLoopProg 64 :=
.seq loopBody347_47 loopBody347_57

def loopBody347_59 : HolLoopProg 64 :=
.mark loopBody347_58

def loopBody347_60 : HolLoopProg 64 :=
.seq loopBody347_45 loopBody347_59

def loopBody347_61 : HolLoopProg 64 :=
.mark loopBody347_60

def loopBody347_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody347_63 : HolLoopProg 64 :=
.mark loopBody347_62

def loopBody347_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody347_65 : HolLoopProg 64 :=
.mark loopBody347_64

def loopBody347_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody347_67 : HolLoopProg 64 :=
.mark loopBody347_66

def loopBody347_68 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.RegImm.reg 5) loopBody347_67 loopBody347_15 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)

def loopBody347_69 : HolLoopProg 64 :=
.mark loopBody347_68

def loopBody347_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody347_71 : HolLoopProg 64 :=
.mark loopBody347_70

def loopBody347_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody347_73 : HolLoopProg 64 :=
.mark loopBody347_72

def loopBody347_74 : HolLoopProg 64 :=
.seq loopBody347_73 loopBody347_1

def loopBody347_75 : HolLoopProg 64 :=
.mark loopBody347_74

def loopBody347_76 : HolLoopProg 64 :=
.seq loopBody347_19 loopBody347_75

def loopBody347_77 : HolLoopProg 64 :=
.mark loopBody347_76

def loopBody347_78 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody347_77 loopBody347_1 (Flapjack.Spt.ls PUnit.unit)

def loopBody347_79 : HolLoopProg 64 :=
.mark loopBody347_78

def loopBody347_80 : HolLoopProg 64 :=
.seq loopBody347_79 loopBody347_1

def loopBody347_81 : HolLoopProg 64 :=
.mark loopBody347_80

def loopBody347_82 : HolLoopProg 64 :=
.seq loopBody347_71 loopBody347_81

def loopBody347_83 : HolLoopProg 64 :=
.mark loopBody347_82

def loopBody347_84 : HolLoopProg 64 :=
.seq loopBody347_69 loopBody347_83

def loopBody347_85 : HolLoopProg 64 :=
.mark loopBody347_84

def loopBody347_86 : HolLoopProg 64 :=
.seq loopBody347_65 loopBody347_85

def loopBody347_87 : HolLoopProg 64 :=
.mark loopBody347_86

def loopBody347_88 : HolLoopProg 64 :=
.seq loopBody347_63 loopBody347_87

def loopBody347_89 : HolLoopProg 64 :=
.mark loopBody347_88

def loopBody347_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody347_91 : HolLoopProg 64 :=
.mark loopBody347_90

def loopBody347_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody347_93 : HolLoopProg 64 :=
.mark loopBody347_92

def loopBody347_94 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.ln)) (some 410) ([4]) (some (4, loopBody347_93, loopBody347_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody347_95 : HolLoopProg 64 :=
.mark loopBody347_94

def loopBody347_96 : HolLoopProg 64 :=
.seq loopBody347_95 loopBody347_1

def loopBody347_97 : HolLoopProg 64 :=
.mark loopBody347_96

def loopBody347_98 : HolLoopProg 64 :=
.seq loopBody347_91 loopBody347_97

def loopBody347_99 : HolLoopProg 64 :=
.mark loopBody347_98

def loopBody347_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody347_101 : HolLoopProg 64 :=
.mark loopBody347_100

def loopBody347_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody347_103 : HolLoopProg 64 :=
.mark loopBody347_102

def loopBody347_104 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.reg 6) loopBody347_103 loopBody347_65 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody347_105 : HolLoopProg 64 :=
.mark loopBody347_104

def loopBody347_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody347_107 : HolLoopProg 64 :=
.mark loopBody347_106

def loopBody347_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody347_109 : HolLoopProg 64 :=
.mark loopBody347_108

def loopBody347_110 : HolLoopProg 64 :=
.seq loopBody347_109 loopBody347_1

def loopBody347_111 : HolLoopProg 64 :=
.mark loopBody347_110

def loopBody347_112 : HolLoopProg 64 :=
.seq loopBody347_15 loopBody347_111

def loopBody347_113 : HolLoopProg 64 :=
.mark loopBody347_112

def loopBody347_114 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody347_113 loopBody347_1 (Flapjack.Spt.ln)

def loopBody347_115 : HolLoopProg 64 :=
.mark loopBody347_114

def loopBody347_116 : HolLoopProg 64 :=
.seq loopBody347_115 loopBody347_1

def loopBody347_117 : HolLoopProg 64 :=
.mark loopBody347_116

def loopBody347_118 : HolLoopProg 64 :=
.seq loopBody347_107 loopBody347_117

def loopBody347_119 : HolLoopProg 64 :=
.mark loopBody347_118

def loopBody347_120 : HolLoopProg 64 :=
.seq loopBody347_105 loopBody347_119

def loopBody347_121 : HolLoopProg 64 :=
.mark loopBody347_120

def loopBody347_122 : HolLoopProg 64 :=
.seq loopBody347_101 loopBody347_121

def loopBody347_123 : HolLoopProg 64 :=
.mark loopBody347_122

def loopBody347_124 : HolLoopProg 64 :=
.seq loopBody347_23 loopBody347_123

def loopBody347_125 : HolLoopProg 64 :=
.mark loopBody347_124

def loopBody347_126 : HolLoopProg 64 :=
.seq loopBody347_67 loopBody347_111

def loopBody347_127 : HolLoopProg 64 :=
.mark loopBody347_126

def loopBody347_128 : HolLoopProg 64 :=
.seq loopBody347_125 loopBody347_127

def loopBody347_129 : HolLoopProg 64 :=
.mark loopBody347_128

def loopBody347_130 : HolLoopProg 64 :=
.seq loopBody347_99 loopBody347_129

def loopBody347_131 : HolLoopProg 64 :=
.mark loopBody347_130

def loopBody347_132 : HolLoopProg 64 :=
.seq loopBody347_1 loopBody347_131

def loopBody347_133 : HolLoopProg 64 :=
.mark loopBody347_132

def loopBody347_134 : HolLoopProg 64 :=
.seq loopBody347_1 loopBody347_133

def loopBody347_135 : HolLoopProg 64 :=
.mark loopBody347_134

def loopBody347_136 : HolLoopProg 64 :=
.seq loopBody347_89 loopBody347_135

def loopBody347_137 : HolLoopProg 64 :=
.mark loopBody347_136

def loopBody347_138 : HolLoopProg 64 :=
.seq loopBody347_61 loopBody347_137

def loopBody347_139 : HolLoopProg 64 :=
.mark loopBody347_138

def loopBody347_140 : HolLoopProg 64 :=
.seq loopBody347_1 loopBody347_139

def loopBody347_141 : HolLoopProg 64 :=
.mark loopBody347_140

def loopBody347_142 : HolLoopProg 64 :=
.seq loopBody347_1 loopBody347_141

def loopBody347_143 : HolLoopProg 64 :=
.mark loopBody347_142

def loopBody347_144 : HolLoopProg 64 :=
.seq loopBody347_43 loopBody347_143

def loopBody347_145 : HolLoopProg 64 :=
.mark loopBody347_144

def loopBody347_146 : HolLoopProg 64 :=
.seq loopBody347_11 loopBody347_145

def loopBody347_147 : HolLoopProg 64 :=
.mark loopBody347_146

def loopBody347_148 : HolLoopProg 64 :=
.seq loopBody347_1 loopBody347_147

def loopBody347_149 : HolLoopProg 64 :=
.mark loopBody347_148

def loopBody347_150 : HolLoopProg 64 :=
.seq loopBody347_1 loopBody347_149

def loopBody347_151 : HolLoopProg 64 :=
.mark loopBody347_150

def output347 : Nat × List Nat × HolLoopProg 64 :=
  (411, [0], loopBody347_151)
end InitECandidate.Proofs.FrontendStages.Loop
