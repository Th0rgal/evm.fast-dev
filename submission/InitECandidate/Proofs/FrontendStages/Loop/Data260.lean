import InitECandidate.Proofs.FrontendStages.Loop.Translate244
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody260_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody260_1 : HolLoopProg 64 :=
.mark loopBody260_0

def loopBody260_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 24#64]))

def loopBody260_3 : HolLoopProg 64 :=
.mark loopBody260_2

def loopBody260_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody260_5 : HolLoopProg 64 :=
.mark loopBody260_4

def loopBody260_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody260_7 : HolLoopProg 64 :=
.mark loopBody260_6

def loopBody260_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody260_9 : HolLoopProg 64 :=
.mark loopBody260_8

def loopBody260_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody260_11 : HolLoopProg 64 :=
.mark loopBody260_10

def loopBody260_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 3 (Flapjack.RegImm.reg 4) loopBody260_9 loopBody260_11 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody260_13 : HolLoopProg 64 :=
.mark loopBody260_12

def loopBody260_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody260_15 : HolLoopProg 64 :=
.mark loopBody260_14

def loopBody260_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 1)

def loopBody260_17 : HolLoopProg 64 :=
.mark loopBody260_16

def loopBody260_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody260_19 : HolLoopProg 64 :=
.mark loopBody260_18

def loopBody260_20 : HolLoopProg 64 :=
.seq loopBody260_19 loopBody260_1

def loopBody260_21 : HolLoopProg 64 :=
.mark loopBody260_20

def loopBody260_22 : HolLoopProg 64 :=
.seq loopBody260_17 loopBody260_21

def loopBody260_23 : HolLoopProg 64 :=
.mark loopBody260_22

def loopBody260_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody260_23 loopBody260_1 (Flapjack.Spt.ls PUnit.unit)

def loopBody260_25 : HolLoopProg 64 :=
.mark loopBody260_24

def loopBody260_26 : HolLoopProg 64 :=
.seq loopBody260_25 loopBody260_1

def loopBody260_27 : HolLoopProg 64 :=
.mark loopBody260_26

def loopBody260_28 : HolLoopProg 64 :=
.seq loopBody260_15 loopBody260_27

def loopBody260_29 : HolLoopProg 64 :=
.mark loopBody260_28

def loopBody260_30 : HolLoopProg 64 :=
.seq loopBody260_13 loopBody260_29

def loopBody260_31 : HolLoopProg 64 :=
.mark loopBody260_30

def loopBody260_32 : HolLoopProg 64 :=
.seq loopBody260_7 loopBody260_31

def loopBody260_33 : HolLoopProg 64 :=
.mark loopBody260_32

def loopBody260_34 : HolLoopProg 64 :=
.seq loopBody260_5 loopBody260_33

def loopBody260_35 : HolLoopProg 64 :=
.mark loopBody260_34

def loopBody260_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64]))

def loopBody260_37 : HolLoopProg 64 :=
.mark loopBody260_36

def loopBody260_38 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 3 (Flapjack.RegImm.reg 4) loopBody260_9 loopBody260_11 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody260_39 : HolLoopProg 64 :=
.mark loopBody260_38

def loopBody260_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 13#64)

def loopBody260_41 : HolLoopProg 64 :=
.mark loopBody260_40

def loopBody260_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody260_43 : HolLoopProg 64 :=
.mark loopBody260_42

def loopBody260_44 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ls PUnit.unit)) (some 282) ([3]) (some (3, loopBody260_43, loopBody260_1, (Flapjack.Spt.ls PUnit.unit)))

def loopBody260_45 : HolLoopProg 64 :=
.mark loopBody260_44

def loopBody260_46 : HolLoopProg 64 :=
.seq loopBody260_45 loopBody260_1

def loopBody260_47 : HolLoopProg 64 :=
.mark loopBody260_46

def loopBody260_48 : HolLoopProg 64 :=
.seq loopBody260_41 loopBody260_47

def loopBody260_49 : HolLoopProg 64 :=
.mark loopBody260_48

def loopBody260_50 : HolLoopProg 64 :=
.seq loopBody260_1 loopBody260_49

def loopBody260_51 : HolLoopProg 64 :=
.mark loopBody260_50

def loopBody260_52 : HolLoopProg 64 :=
.seq loopBody260_1 loopBody260_51

def loopBody260_53 : HolLoopProg 64 :=
.mark loopBody260_52

def loopBody260_54 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody260_53 loopBody260_1 (Flapjack.Spt.ls PUnit.unit)

def loopBody260_55 : HolLoopProg 64 :=
.mark loopBody260_54

def loopBody260_56 : HolLoopProg 64 :=
.seq loopBody260_55 loopBody260_1

def loopBody260_57 : HolLoopProg 64 :=
.mark loopBody260_56

def loopBody260_58 : HolLoopProg 64 :=
.seq loopBody260_15 loopBody260_57

def loopBody260_59 : HolLoopProg 64 :=
.mark loopBody260_58

def loopBody260_60 : HolLoopProg 64 :=
.seq loopBody260_39 loopBody260_59

def loopBody260_61 : HolLoopProg 64 :=
.mark loopBody260_60

def loopBody260_62 : HolLoopProg 64 :=
.seq loopBody260_7 loopBody260_61

def loopBody260_63 : HolLoopProg 64 :=
.mark loopBody260_62

def loopBody260_64 : HolLoopProg 64 :=
.seq loopBody260_37 loopBody260_63

def loopBody260_65 : HolLoopProg 64 :=
.mark loopBody260_64

def loopBody260_66 : HolLoopProg 64 :=
.seq loopBody260_35 loopBody260_65

def loopBody260_67 : HolLoopProg 64 :=
.mark loopBody260_66

def loopBody260_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 32#64)

def loopBody260_69 : HolLoopProg 64 :=
.mark loopBody260_68

def loopBody260_70 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ls PUnit.unit)) (some 68) ([3]) (some (3, loopBody260_43, loopBody260_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))

def loopBody260_71 : HolLoopProg 64 :=
.mark loopBody260_70

def loopBody260_72 : HolLoopProg 64 :=
.seq loopBody260_71 loopBody260_1

def loopBody260_73 : HolLoopProg 64 :=
.mark loopBody260_72

def loopBody260_74 : HolLoopProg 64 :=
.seq loopBody260_69 loopBody260_73

def loopBody260_75 : HolLoopProg 64 :=
.mark loopBody260_74

def loopBody260_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64]))

def loopBody260_77 : HolLoopProg 64 :=
.mark loopBody260_76

def loopBody260_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64]))

def loopBody260_79 : HolLoopProg 64 :=
.mark loopBody260_78

def loopBody260_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody260_81 : HolLoopProg 64 :=
.mark loopBody260_80

def loopBody260_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody260_83 : HolLoopProg 64 :=
.mark loopBody260_82

def loopBody260_84 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)) (some 158) ([4, 5, 6]) (some (4, loopBody260_83, loopBody260_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))

def loopBody260_85 : HolLoopProg 64 :=
.mark loopBody260_84

def loopBody260_86 : HolLoopProg 64 :=
.seq loopBody260_85 loopBody260_1

def loopBody260_87 : HolLoopProg 64 :=
.mark loopBody260_86

def loopBody260_88 : HolLoopProg 64 :=
.seq loopBody260_81 loopBody260_87

def loopBody260_89 : HolLoopProg 64 :=
.mark loopBody260_88

def loopBody260_90 : HolLoopProg 64 :=
.seq loopBody260_79 loopBody260_89

def loopBody260_91 : HolLoopProg 64 :=
.mark loopBody260_90

def loopBody260_92 : HolLoopProg 64 :=
.seq loopBody260_77 loopBody260_91

def loopBody260_93 : HolLoopProg 64 :=
.mark loopBody260_92

def loopBody260_94 : HolLoopProg 64 :=
.seq loopBody260_1 loopBody260_93

def loopBody260_95 : HolLoopProg 64 :=
.mark loopBody260_94

def loopBody260_96 : HolLoopProg 64 :=
.seq loopBody260_1 loopBody260_95

def loopBody260_97 : HolLoopProg 64 :=
.mark loopBody260_96

def loopBody260_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 24#64])

def loopBody260_99 : HolLoopProg 64 :=
.mark loopBody260_98

def loopBody260_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody260_101 : HolLoopProg 64 :=
.mark loopBody260_100

def loopBody260_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 4)

def loopBody260_103 : HolLoopProg 64 :=
.mark loopBody260_102

def loopBody260_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 3) 5

def loopBody260_105 : HolLoopProg 64 :=
.mark loopBody260_104

def loopBody260_106 : HolLoopProg 64 :=
.seq loopBody260_105 loopBody260_1

def loopBody260_107 : HolLoopProg 64 :=
.mark loopBody260_106

def loopBody260_108 : HolLoopProg 64 :=
.seq loopBody260_103 loopBody260_107

def loopBody260_109 : HolLoopProg 64 :=
.mark loopBody260_108

def loopBody260_110 : HolLoopProg 64 :=
.seq loopBody260_109 loopBody260_1

def loopBody260_111 : HolLoopProg 64 :=
.mark loopBody260_110

def loopBody260_112 : HolLoopProg 64 :=
.seq loopBody260_101 loopBody260_111

def loopBody260_113 : HolLoopProg 64 :=
.mark loopBody260_112

def loopBody260_114 : HolLoopProg 64 :=
.seq loopBody260_1 loopBody260_113

def loopBody260_115 : HolLoopProg 64 :=
.mark loopBody260_114

def loopBody260_116 : HolLoopProg 64 :=
.seq loopBody260_99 loopBody260_115

def loopBody260_117 : HolLoopProg 64 :=
.mark loopBody260_116

def loopBody260_118 : HolLoopProg 64 :=
.seq loopBody260_1 loopBody260_117

def loopBody260_119 : HolLoopProg 64 :=
.mark loopBody260_118

def loopBody260_120 : HolLoopProg 64 :=
.seq loopBody260_97 loopBody260_119

def loopBody260_121 : HolLoopProg 64 :=
.mark loopBody260_120

def loopBody260_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody260_123 : HolLoopProg 64 :=
.mark loopBody260_122

def loopBody260_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody260_125 : HolLoopProg 64 :=
.mark loopBody260_124

def loopBody260_126 : HolLoopProg 64 :=
.seq loopBody260_125 loopBody260_1

def loopBody260_127 : HolLoopProg 64 :=
.mark loopBody260_126

def loopBody260_128 : HolLoopProg 64 :=
.seq loopBody260_123 loopBody260_127

def loopBody260_129 : HolLoopProg 64 :=
.mark loopBody260_128

def loopBody260_130 : HolLoopProg 64 :=
.seq loopBody260_121 loopBody260_129

def loopBody260_131 : HolLoopProg 64 :=
.mark loopBody260_130

def loopBody260_132 : HolLoopProg 64 :=
.seq loopBody260_75 loopBody260_131

def loopBody260_133 : HolLoopProg 64 :=
.mark loopBody260_132

def loopBody260_134 : HolLoopProg 64 :=
.seq loopBody260_1 loopBody260_133

def loopBody260_135 : HolLoopProg 64 :=
.mark loopBody260_134

def loopBody260_136 : HolLoopProg 64 :=
.seq loopBody260_1 loopBody260_135

def loopBody260_137 : HolLoopProg 64 :=
.mark loopBody260_136

def loopBody260_138 : HolLoopProg 64 :=
.seq loopBody260_67 loopBody260_137

def loopBody260_139 : HolLoopProg 64 :=
.mark loopBody260_138

def loopBody260_140 : HolLoopProg 64 :=
.seq loopBody260_3 loopBody260_139

def loopBody260_141 : HolLoopProg 64 :=
.mark loopBody260_140

def loopBody260_142 : HolLoopProg 64 :=
.seq loopBody260_1 loopBody260_141

def loopBody260_143 : HolLoopProg 64 :=
.mark loopBody260_142

def output260 : Nat × List Nat × HolLoopProg 64 :=
  (324, [0], loopBody260_143)
end InitECandidate.Proofs.FrontendStages.Loop
