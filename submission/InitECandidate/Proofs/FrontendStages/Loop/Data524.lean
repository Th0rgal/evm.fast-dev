import InitECandidate.Proofs.FrontendStages.Loop.Translate508
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody524_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody524_1 : HolLoopProg 64 :=
.mark loopBody524_0

def loopBody524_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody524_3 : HolLoopProg 64 :=
.mark loopBody524_2

def loopBody524_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody524_5 : HolLoopProg 64 :=
.mark loopBody524_4

def loopBody524_6 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 403) ([3]) (some (3, loopBody524_5, loopBody524_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody524_7 : HolLoopProg 64 :=
.mark loopBody524_6

def loopBody524_8 : HolLoopProg 64 :=
.seq loopBody524_7 loopBody524_1

def loopBody524_9 : HolLoopProg 64 :=
.mark loopBody524_8

def loopBody524_10 : HolLoopProg 64 :=
.seq loopBody524_3 loopBody524_9

def loopBody524_11 : HolLoopProg 64 :=
.mark loopBody524_10

def loopBody524_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 48#64]))

def loopBody524_13 : HolLoopProg 64 :=
.mark loopBody524_12

def loopBody524_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody524_15 : HolLoopProg 64 :=
.mark loopBody524_14

def loopBody524_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody524_17 : HolLoopProg 64 :=
.mark loopBody524_16

def loopBody524_18 : HolLoopProg 64 :=
.call (some ([3, 4], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)) (some 404) ([5, 6]) (some (5, loopBody524_17, loopBody524_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody524_19 : HolLoopProg 64 :=
.mark loopBody524_18

def loopBody524_20 : HolLoopProg 64 :=
.seq loopBody524_19 loopBody524_1

def loopBody524_21 : HolLoopProg 64 :=
.mark loopBody524_20

def loopBody524_22 : HolLoopProg 64 :=
.seq loopBody524_15 loopBody524_21

def loopBody524_23 : HolLoopProg 64 :=
.mark loopBody524_22

def loopBody524_24 : HolLoopProg 64 :=
.seq loopBody524_13 loopBody524_23

def loopBody524_25 : HolLoopProg 64 :=
.mark loopBody524_24

def loopBody524_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody524_27 : HolLoopProg 64 :=
.mark loopBody524_26

def loopBody524_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody524_29 : HolLoopProg 64 :=
.mark loopBody524_28

def loopBody524_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody524_31 : HolLoopProg 64 :=
.mark loopBody524_30

def loopBody524_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody524_33 : HolLoopProg 64 :=
.mark loopBody524_32

def loopBody524_34 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.reg 7) loopBody524_31 loopBody524_33 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody524_35 : HolLoopProg 64 :=
.mark loopBody524_34

def loopBody524_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody524_37 : HolLoopProg 64 :=
.mark loopBody524_36

def loopBody524_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody524_39 : HolLoopProg 64 :=
.mark loopBody524_38

def loopBody524_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody524_41 : HolLoopProg 64 :=
.mark loopBody524_40

def loopBody524_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody524_43 : HolLoopProg 64 :=
.mark loopBody524_42

def loopBody524_44 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)) (some 464) ([6, 7]) (some (6, loopBody524_43, loopBody524_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody524_45 : HolLoopProg 64 :=
.mark loopBody524_44

def loopBody524_46 : HolLoopProg 64 :=
.seq loopBody524_45 loopBody524_1

def loopBody524_47 : HolLoopProg 64 :=
.mark loopBody524_46

def loopBody524_48 : HolLoopProg 64 :=
.seq loopBody524_41 loopBody524_47

def loopBody524_49 : HolLoopProg 64 :=
.mark loopBody524_48

def loopBody524_50 : HolLoopProg 64 :=
.seq loopBody524_39 loopBody524_49

def loopBody524_51 : HolLoopProg 64 :=
.mark loopBody524_50

def loopBody524_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody524_53 : HolLoopProg 64 :=
.mark loopBody524_52

def loopBody524_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody524_55 : HolLoopProg 64 :=
.mark loopBody524_54

def loopBody524_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody524_57 : HolLoopProg 64 :=
.mark loopBody524_56

def loopBody524_58 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 7 (Flapjack.RegImm.reg 8) loopBody524_57 loopBody524_29 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody524_59 : HolLoopProg 64 :=
.mark loopBody524_58

def loopBody524_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody524_61 : HolLoopProg 64 :=
.mark loopBody524_60

def loopBody524_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody524_63 : HolLoopProg 64 :=
.mark loopBody524_62

def loopBody524_64 : HolLoopProg 64 :=
.seq loopBody524_63 loopBody524_1

def loopBody524_65 : HolLoopProg 64 :=
.mark loopBody524_64

def loopBody524_66 : HolLoopProg 64 :=
.seq loopBody524_33 loopBody524_65

def loopBody524_67 : HolLoopProg 64 :=
.mark loopBody524_66

def loopBody524_68 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody524_67 loopBody524_1 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)

def loopBody524_69 : HolLoopProg 64 :=
.mark loopBody524_68

def loopBody524_70 : HolLoopProg 64 :=
.seq loopBody524_69 loopBody524_1

def loopBody524_71 : HolLoopProg 64 :=
.mark loopBody524_70

def loopBody524_72 : HolLoopProg 64 :=
.seq loopBody524_61 loopBody524_71

def loopBody524_73 : HolLoopProg 64 :=
.mark loopBody524_72

def loopBody524_74 : HolLoopProg 64 :=
.seq loopBody524_59 loopBody524_73

def loopBody524_75 : HolLoopProg 64 :=
.mark loopBody524_74

def loopBody524_76 : HolLoopProg 64 :=
.seq loopBody524_55 loopBody524_75

def loopBody524_77 : HolLoopProg 64 :=
.mark loopBody524_76

def loopBody524_78 : HolLoopProg 64 :=
.seq loopBody524_53 loopBody524_77

def loopBody524_79 : HolLoopProg 64 :=
.mark loopBody524_78

def loopBody524_80 : HolLoopProg 64 :=
.seq loopBody524_51 loopBody524_79

def loopBody524_81 : HolLoopProg 64 :=
.mark loopBody524_80

def loopBody524_82 : HolLoopProg 64 :=
.seq loopBody524_1 loopBody524_81

def loopBody524_83 : HolLoopProg 64 :=
.mark loopBody524_82

def loopBody524_84 : HolLoopProg 64 :=
.seq loopBody524_1 loopBody524_83

def loopBody524_85 : HolLoopProg 64 :=
.mark loopBody524_84

def loopBody524_86 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody524_85 loopBody524_1 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)

def loopBody524_87 : HolLoopProg 64 :=
.mark loopBody524_86

def loopBody524_88 : HolLoopProg 64 :=
.seq loopBody524_87 loopBody524_1

def loopBody524_89 : HolLoopProg 64 :=
.mark loopBody524_88

def loopBody524_90 : HolLoopProg 64 :=
.seq loopBody524_37 loopBody524_89

def loopBody524_91 : HolLoopProg 64 :=
.mark loopBody524_90

def loopBody524_92 : HolLoopProg 64 :=
.seq loopBody524_35 loopBody524_91

def loopBody524_93 : HolLoopProg 64 :=
.mark loopBody524_92

def loopBody524_94 : HolLoopProg 64 :=
.seq loopBody524_29 loopBody524_93

def loopBody524_95 : HolLoopProg 64 :=
.mark loopBody524_94

def loopBody524_96 : HolLoopProg 64 :=
.seq loopBody524_27 loopBody524_95

def loopBody524_97 : HolLoopProg 64 :=
.mark loopBody524_96

def loopBody524_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 0#64]))

def loopBody524_99 : HolLoopProg 64 :=
.mark loopBody524_98

def loopBody524_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 40#64]))

def loopBody524_101 : HolLoopProg 64 :=
.mark loopBody524_100

def loopBody524_102 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.reg 7) loopBody524_31 loopBody524_33 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)

def loopBody524_103 : HolLoopProg 64 :=
.mark loopBody524_102

def loopBody524_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody524_105 : HolLoopProg 64 :=
.mark loopBody524_104

def loopBody524_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody524_107 : HolLoopProg 64 :=
.mark loopBody524_106

def loopBody524_108 : HolLoopProg 64 :=
.seq loopBody524_107 loopBody524_1

def loopBody524_109 : HolLoopProg 64 :=
.mark loopBody524_108

def loopBody524_110 : HolLoopProg 64 :=
.seq loopBody524_105 loopBody524_109

def loopBody524_111 : HolLoopProg 64 :=
.mark loopBody524_110

def loopBody524_112 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody524_111 loopBody524_1 (Flapjack.Spt.ln)

def loopBody524_113 : HolLoopProg 64 :=
.mark loopBody524_112

def loopBody524_114 : HolLoopProg 64 :=
.seq loopBody524_113 loopBody524_1

def loopBody524_115 : HolLoopProg 64 :=
.mark loopBody524_114

def loopBody524_116 : HolLoopProg 64 :=
.seq loopBody524_37 loopBody524_115

def loopBody524_117 : HolLoopProg 64 :=
.mark loopBody524_116

def loopBody524_118 : HolLoopProg 64 :=
.seq loopBody524_103 loopBody524_117

def loopBody524_119 : HolLoopProg 64 :=
.mark loopBody524_118

def loopBody524_120 : HolLoopProg 64 :=
.seq loopBody524_101 loopBody524_119

def loopBody524_121 : HolLoopProg 64 :=
.mark loopBody524_120

def loopBody524_122 : HolLoopProg 64 :=
.seq loopBody524_99 loopBody524_121

def loopBody524_123 : HolLoopProg 64 :=
.mark loopBody524_122

def loopBody524_124 : HolLoopProg 64 :=
.seq loopBody524_97 loopBody524_123

def loopBody524_125 : HolLoopProg 64 :=
.mark loopBody524_124

def loopBody524_126 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody524_127 : HolLoopProg 64 :=
.mark loopBody524_126

def loopBody524_128 : HolLoopProg 64 :=
.seq loopBody524_127 loopBody524_109

def loopBody524_129 : HolLoopProg 64 :=
.mark loopBody524_128

def loopBody524_130 : HolLoopProg 64 :=
.seq loopBody524_125 loopBody524_129

def loopBody524_131 : HolLoopProg 64 :=
.mark loopBody524_130

def loopBody524_132 : HolLoopProg 64 :=
.seq loopBody524_25 loopBody524_131

def loopBody524_133 : HolLoopProg 64 :=
.mark loopBody524_132

def loopBody524_134 : HolLoopProg 64 :=
.seq loopBody524_1 loopBody524_133

def loopBody524_135 : HolLoopProg 64 :=
.mark loopBody524_134

def loopBody524_136 : HolLoopProg 64 :=
.seq loopBody524_1 loopBody524_135

def loopBody524_137 : HolLoopProg 64 :=
.mark loopBody524_136

def loopBody524_138 : HolLoopProg 64 :=
.seq loopBody524_1 loopBody524_137

def loopBody524_139 : HolLoopProg 64 :=
.mark loopBody524_138

def loopBody524_140 : HolLoopProg 64 :=
.seq loopBody524_1 loopBody524_139

def loopBody524_141 : HolLoopProg 64 :=
.mark loopBody524_140

def loopBody524_142 : HolLoopProg 64 :=
.seq loopBody524_11 loopBody524_141

def loopBody524_143 : HolLoopProg 64 :=
.mark loopBody524_142

def loopBody524_144 : HolLoopProg 64 :=
.seq loopBody524_1 loopBody524_143

def loopBody524_145 : HolLoopProg 64 :=
.mark loopBody524_144

def loopBody524_146 : HolLoopProg 64 :=
.seq loopBody524_1 loopBody524_145

def loopBody524_147 : HolLoopProg 64 :=
.mark loopBody524_146

def output524 : Nat × List Nat × HolLoopProg 64 :=
  (588, [0, 1], loopBody524_147)
end InitECandidate.Proofs.FrontendStages.Loop
