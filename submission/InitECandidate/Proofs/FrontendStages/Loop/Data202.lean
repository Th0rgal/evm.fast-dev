import InitECandidate.Proofs.FrontendStages.Loop.Translate186
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody202_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody202_1 : HolLoopProg 64 :=
.mark loopBody202_0

def loopBody202_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody202_3 : HolLoopProg 64 :=
.mark loopBody202_2

def loopBody202_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody202_5 : HolLoopProg 64 :=
.mark loopBody202_4

def loopBody202_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody202_7 : HolLoopProg 64 :=
.mark loopBody202_6

def loopBody202_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody202_9 : HolLoopProg 64 :=
.mark loopBody202_8

def loopBody202_10 : HolLoopProg 64 :=
.call (some ([2, 3], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 265) ([4, 5, 6]) (some (4, loopBody202_9, loopBody202_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody202_11 : HolLoopProg 64 :=
.mark loopBody202_10

def loopBody202_12 : HolLoopProg 64 :=
.seq loopBody202_11 loopBody202_1

def loopBody202_13 : HolLoopProg 64 :=
.mark loopBody202_12

def loopBody202_14 : HolLoopProg 64 :=
.seq loopBody202_7 loopBody202_13

def loopBody202_15 : HolLoopProg 64 :=
.mark loopBody202_14

def loopBody202_16 : HolLoopProg 64 :=
.seq loopBody202_5 loopBody202_15

def loopBody202_17 : HolLoopProg 64 :=
.mark loopBody202_16

def loopBody202_18 : HolLoopProg 64 :=
.seq loopBody202_3 loopBody202_17

def loopBody202_19 : HolLoopProg 64 :=
.mark loopBody202_18

def loopBody202_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 8#64)

def loopBody202_21 : HolLoopProg 64 :=
.mark loopBody202_20

def loopBody202_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody202_23 : HolLoopProg 64 :=
.mark loopBody202_22

def loopBody202_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody202_25 : HolLoopProg 64 :=
.mark loopBody202_24

def loopBody202_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody202_27 : HolLoopProg 64 :=
.mark loopBody202_26

def loopBody202_28 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 5 (Flapjack.RegImm.reg 6) loopBody202_25 loopBody202_27 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody202_29 : HolLoopProg 64 :=
.mark loopBody202_28

def loopBody202_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody202_31 : HolLoopProg 64 :=
.mark loopBody202_30

def loopBody202_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 4#64)

def loopBody202_33 : HolLoopProg 64 :=
.mark loopBody202_32

def loopBody202_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 4)

def loopBody202_35 : HolLoopProg 64 :=
.mark loopBody202_34

def loopBody202_36 : HolLoopProg 64 :=
.seq loopBody202_35 loopBody202_1

def loopBody202_37 : HolLoopProg 64 :=
.mark loopBody202_36

def loopBody202_38 : HolLoopProg 64 :=
.seq loopBody202_37 loopBody202_1

def loopBody202_39 : HolLoopProg 64 :=
.mark loopBody202_38

def loopBody202_40 : HolLoopProg 64 :=
.seq loopBody202_33 loopBody202_39

def loopBody202_41 : HolLoopProg 64 :=
.mark loopBody202_40

def loopBody202_42 : HolLoopProg 64 :=
.seq loopBody202_1 loopBody202_41

def loopBody202_43 : HolLoopProg 64 :=
.mark loopBody202_42

def loopBody202_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 3#64)

def loopBody202_45 : HolLoopProg 64 :=
.mark loopBody202_44

def loopBody202_46 : HolLoopProg 64 :=
.seq loopBody202_45 loopBody202_9

def loopBody202_47 : HolLoopProg 64 :=
.mark loopBody202_46

def loopBody202_48 : HolLoopProg 64 :=
.seq loopBody202_43 loopBody202_47

def loopBody202_49 : HolLoopProg 64 :=
.mark loopBody202_48

def loopBody202_50 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody202_49 loopBody202_1 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody202_51 : HolLoopProg 64 :=
.mark loopBody202_50

def loopBody202_52 : HolLoopProg 64 :=
.seq loopBody202_51 loopBody202_1

def loopBody202_53 : HolLoopProg 64 :=
.mark loopBody202_52

def loopBody202_54 : HolLoopProg 64 :=
.seq loopBody202_31 loopBody202_53

def loopBody202_55 : HolLoopProg 64 :=
.mark loopBody202_54

def loopBody202_56 : HolLoopProg 64 :=
.seq loopBody202_29 loopBody202_55

def loopBody202_57 : HolLoopProg 64 :=
.mark loopBody202_56

def loopBody202_58 : HolLoopProg 64 :=
.seq loopBody202_23 loopBody202_57

def loopBody202_59 : HolLoopProg 64 :=
.mark loopBody202_58

def loopBody202_60 : HolLoopProg 64 :=
.seq loopBody202_21 loopBody202_59

def loopBody202_61 : HolLoopProg 64 :=
.mark loopBody202_60

def loopBody202_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody202_63 : HolLoopProg 64 :=
.mark loopBody202_62

def loopBody202_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody202_65 : HolLoopProg 64 :=
.mark loopBody202_64

def loopBody202_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody202_67 : HolLoopProg 64 :=
.mark loopBody202_66

def loopBody202_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody202_69 : HolLoopProg 64 :=
.mark loopBody202_68

def loopBody202_70 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 7 (Flapjack.RegImm.reg 8) loopBody202_67 loopBody202_69 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody202_71 : HolLoopProg 64 :=
.mark loopBody202_70

def loopBody202_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody202_73 : HolLoopProg 64 :=
.mark loopBody202_72

def loopBody202_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 5])

def loopBody202_75 : HolLoopProg 64 :=
.mark loopBody202_74

def loopBody202_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 6 6

def loopBody202_77 : HolLoopProg 64 :=
.mark loopBody202_76

def loopBody202_78 : HolLoopProg 64 :=
.seq loopBody202_77 loopBody202_1

def loopBody202_79 : HolLoopProg 64 :=
.mark loopBody202_78

def loopBody202_80 : HolLoopProg 64 :=
.seq loopBody202_75 loopBody202_79

def loopBody202_81 : HolLoopProg 64 :=
.mark loopBody202_80

def loopBody202_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 8#64),
      Flapjack.HolLoopExp.var 6])

def loopBody202_83 : HolLoopProg 64 :=
.mark loopBody202_82

def loopBody202_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 7)

def loopBody202_85 : HolLoopProg 64 :=
.mark loopBody202_84

def loopBody202_86 : HolLoopProg 64 :=
.seq loopBody202_85 loopBody202_1

def loopBody202_87 : HolLoopProg 64 :=
.mark loopBody202_86

def loopBody202_88 : HolLoopProg 64 :=
.seq loopBody202_87 loopBody202_1

def loopBody202_89 : HolLoopProg 64 :=
.mark loopBody202_88

def loopBody202_90 : HolLoopProg 64 :=
.seq loopBody202_83 loopBody202_89

def loopBody202_91 : HolLoopProg 64 :=
.mark loopBody202_90

def loopBody202_92 : HolLoopProg 64 :=
.seq loopBody202_81 loopBody202_91

def loopBody202_93 : HolLoopProg 64 :=
.mark loopBody202_92

def loopBody202_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 1#64])

def loopBody202_95 : HolLoopProg 64 :=
.mark loopBody202_94

def loopBody202_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 6)

def loopBody202_97 : HolLoopProg 64 :=
.mark loopBody202_96

def loopBody202_98 : HolLoopProg 64 :=
.seq loopBody202_97 loopBody202_1

def loopBody202_99 : HolLoopProg 64 :=
.mark loopBody202_98

def loopBody202_100 : HolLoopProg 64 :=
.seq loopBody202_99 loopBody202_1

def loopBody202_101 : HolLoopProg 64 :=
.mark loopBody202_100

def loopBody202_102 : HolLoopProg 64 :=
.seq loopBody202_95 loopBody202_101

def loopBody202_103 : HolLoopProg 64 :=
.mark loopBody202_102

def loopBody202_104 : HolLoopProg 64 :=
.seq loopBody202_1 loopBody202_103

def loopBody202_105 : HolLoopProg 64 :=
.mark loopBody202_104

def loopBody202_106 : HolLoopProg 64 :=
.seq loopBody202_93 loopBody202_105

def loopBody202_107 : HolLoopProg 64 :=
.mark loopBody202_106

def loopBody202_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody202_109 : HolLoopProg 64 :=
.mark loopBody202_108

def loopBody202_110 : HolLoopProg 64 :=
.seq loopBody202_107 loopBody202_109

def loopBody202_111 : HolLoopProg 64 :=
.mark loopBody202_110

def loopBody202_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody202_113 : HolLoopProg 64 :=
.mark loopBody202_112

def loopBody202_114 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody202_111 loopBody202_113 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody202_115 : HolLoopProg 64 :=
.mark loopBody202_114

def loopBody202_116 : HolLoopProg 64 :=
.seq loopBody202_115 loopBody202_1

def loopBody202_117 : HolLoopProg 64 :=
.mark loopBody202_116

def loopBody202_118 : HolLoopProg 64 :=
.seq loopBody202_73 loopBody202_117

def loopBody202_119 : HolLoopProg 64 :=
.mark loopBody202_118

def loopBody202_120 : HolLoopProg 64 :=
.seq loopBody202_71 loopBody202_119

def loopBody202_121 : HolLoopProg 64 :=
.mark loopBody202_120

def loopBody202_122 : HolLoopProg 64 :=
.seq loopBody202_65 loopBody202_121

def loopBody202_123 : HolLoopProg 64 :=
.mark loopBody202_122

def loopBody202_124 : HolLoopProg 64 :=
.seq loopBody202_31 loopBody202_123

def loopBody202_125 : HolLoopProg 64 :=
.mark loopBody202_124

def loopBody202_126 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody202_125 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody202_127 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody202_128 : HolLoopProg 64 :=
.mark loopBody202_127

def loopBody202_129 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody202_130 : HolLoopProg 64 :=
.mark loopBody202_129

def loopBody202_131 : HolLoopProg 64 :=
.seq loopBody202_130 loopBody202_1

def loopBody202_132 : HolLoopProg 64 :=
.mark loopBody202_131

def loopBody202_133 : HolLoopProg 64 :=
.seq loopBody202_128 loopBody202_132

def loopBody202_134 : HolLoopProg 64 :=
.mark loopBody202_133

def loopBody202_135 : HolLoopProg 64 :=
.seq loopBody202_126 loopBody202_134

def loopBody202_136 : HolLoopProg 64 :=
.seq loopBody202_27 loopBody202_135

def loopBody202_137 : HolLoopProg 64 :=
.seq loopBody202_1 loopBody202_136

def loopBody202_138 : HolLoopProg 64 :=
.seq loopBody202_63 loopBody202_137

def loopBody202_139 : HolLoopProg 64 :=
.seq loopBody202_1 loopBody202_138

def loopBody202_140 : HolLoopProg 64 :=
.seq loopBody202_61 loopBody202_139

def loopBody202_141 : HolLoopProg 64 :=
.seq loopBody202_19 loopBody202_140

def loopBody202_142 : HolLoopProg 64 :=
.seq loopBody202_1 loopBody202_141

def loopBody202_143 : HolLoopProg 64 :=
.seq loopBody202_1 loopBody202_142

def loopBody202_144 : HolLoopProg 64 :=
.seq loopBody202_1 loopBody202_143

def loopBody202_145 : HolLoopProg 64 :=
.seq loopBody202_1 loopBody202_144

def output202 : Nat × List Nat × HolLoopProg 64 :=
  (266, [0, 1], loopBody202_145)
end InitECandidate.Proofs.FrontendStages.Loop
