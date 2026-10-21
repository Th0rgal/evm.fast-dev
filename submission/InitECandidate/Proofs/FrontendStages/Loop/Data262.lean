import InitECandidate.Proofs.FrontendStages.Loop.Translate246
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody262_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody262_1 : HolLoopProg 64 :=
.mark loopBody262_0

def loopBody262_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 24#64]))

def loopBody262_3 : HolLoopProg 64 :=
.mark loopBody262_2

def loopBody262_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody262_5 : HolLoopProg 64 :=
.mark loopBody262_4

def loopBody262_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody262_7 : HolLoopProg 64 :=
.mark loopBody262_6

def loopBody262_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody262_9 : HolLoopProg 64 :=
.mark loopBody262_8

def loopBody262_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody262_11 : HolLoopProg 64 :=
.mark loopBody262_10

def loopBody262_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 3 (Flapjack.RegImm.reg 4) loopBody262_9 loopBody262_11 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody262_13 : HolLoopProg 64 :=
.mark loopBody262_12

def loopBody262_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody262_15 : HolLoopProg 64 :=
.mark loopBody262_14

def loopBody262_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 1)

def loopBody262_17 : HolLoopProg 64 :=
.mark loopBody262_16

def loopBody262_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody262_19 : HolLoopProg 64 :=
.mark loopBody262_18

def loopBody262_20 : HolLoopProg 64 :=
.seq loopBody262_19 loopBody262_1

def loopBody262_21 : HolLoopProg 64 :=
.mark loopBody262_20

def loopBody262_22 : HolLoopProg 64 :=
.seq loopBody262_17 loopBody262_21

def loopBody262_23 : HolLoopProg 64 :=
.mark loopBody262_22

def loopBody262_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody262_23 loopBody262_1 (Flapjack.Spt.ls PUnit.unit)

def loopBody262_25 : HolLoopProg 64 :=
.mark loopBody262_24

def loopBody262_26 : HolLoopProg 64 :=
.seq loopBody262_25 loopBody262_1

def loopBody262_27 : HolLoopProg 64 :=
.mark loopBody262_26

def loopBody262_28 : HolLoopProg 64 :=
.seq loopBody262_15 loopBody262_27

def loopBody262_29 : HolLoopProg 64 :=
.mark loopBody262_28

def loopBody262_30 : HolLoopProg 64 :=
.seq loopBody262_13 loopBody262_29

def loopBody262_31 : HolLoopProg 64 :=
.mark loopBody262_30

def loopBody262_32 : HolLoopProg 64 :=
.seq loopBody262_7 loopBody262_31

def loopBody262_33 : HolLoopProg 64 :=
.mark loopBody262_32

def loopBody262_34 : HolLoopProg 64 :=
.seq loopBody262_5 loopBody262_33

def loopBody262_35 : HolLoopProg 64 :=
.mark loopBody262_34

def loopBody262_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody262_37 : HolLoopProg 64 :=
.mark loopBody262_36

def loopBody262_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody262_39 : HolLoopProg 64 :=
.mark loopBody262_38

def loopBody262_40 : HolLoopProg 64 :=
.call (some ([2, 3], Flapjack.Spt.ls PUnit.unit)) (some 321) ([4]) (some (4, loopBody262_39, loopBody262_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody262_41 : HolLoopProg 64 :=
.mark loopBody262_40

def loopBody262_42 : HolLoopProg 64 :=
.seq loopBody262_41 loopBody262_1

def loopBody262_43 : HolLoopProg 64 :=
.mark loopBody262_42

def loopBody262_44 : HolLoopProg 64 :=
.seq loopBody262_37 loopBody262_43

def loopBody262_45 : HolLoopProg 64 :=
.mark loopBody262_44

def loopBody262_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 32#64)

def loopBody262_47 : HolLoopProg 64 :=
.mark loopBody262_46

def loopBody262_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody262_49 : HolLoopProg 64 :=
.mark loopBody262_48

def loopBody262_50 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([5]) (some (5, loopBody262_49, loopBody262_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody262_51 : HolLoopProg 64 :=
.mark loopBody262_50

def loopBody262_52 : HolLoopProg 64 :=
.seq loopBody262_51 loopBody262_1

def loopBody262_53 : HolLoopProg 64 :=
.mark loopBody262_52

def loopBody262_54 : HolLoopProg 64 :=
.seq loopBody262_47 loopBody262_53

def loopBody262_55 : HolLoopProg 64 :=
.mark loopBody262_54

def loopBody262_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody262_57 : HolLoopProg 64 :=
.mark loopBody262_56

def loopBody262_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody262_59 : HolLoopProg 64 :=
.mark loopBody262_58

def loopBody262_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 4)

def loopBody262_61 : HolLoopProg 64 :=
.mark loopBody262_60

def loopBody262_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody262_63 : HolLoopProg 64 :=
.mark loopBody262_62

def loopBody262_64 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)) (some 158) ([6, 7, 8]) (some (6, loopBody262_63, loopBody262_1, (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))

def loopBody262_65 : HolLoopProg 64 :=
.mark loopBody262_64

def loopBody262_66 : HolLoopProg 64 :=
.seq loopBody262_65 loopBody262_1

def loopBody262_67 : HolLoopProg 64 :=
.mark loopBody262_66

def loopBody262_68 : HolLoopProg 64 :=
.seq loopBody262_61 loopBody262_67

def loopBody262_69 : HolLoopProg 64 :=
.mark loopBody262_68

def loopBody262_70 : HolLoopProg 64 :=
.seq loopBody262_59 loopBody262_69

def loopBody262_71 : HolLoopProg 64 :=
.mark loopBody262_70

def loopBody262_72 : HolLoopProg 64 :=
.seq loopBody262_57 loopBody262_71

def loopBody262_73 : HolLoopProg 64 :=
.mark loopBody262_72

def loopBody262_74 : HolLoopProg 64 :=
.seq loopBody262_1 loopBody262_73

def loopBody262_75 : HolLoopProg 64 :=
.mark loopBody262_74

def loopBody262_76 : HolLoopProg 64 :=
.seq loopBody262_1 loopBody262_75

def loopBody262_77 : HolLoopProg 64 :=
.mark loopBody262_76

def loopBody262_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 24#64])

def loopBody262_79 : HolLoopProg 64 :=
.mark loopBody262_78

def loopBody262_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody262_81 : HolLoopProg 64 :=
.mark loopBody262_80

def loopBody262_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody262_83 : HolLoopProg 64 :=
.mark loopBody262_82

def loopBody262_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 5) 7

def loopBody262_85 : HolLoopProg 64 :=
.mark loopBody262_84

def loopBody262_86 : HolLoopProg 64 :=
.seq loopBody262_85 loopBody262_1

def loopBody262_87 : HolLoopProg 64 :=
.mark loopBody262_86

def loopBody262_88 : HolLoopProg 64 :=
.seq loopBody262_83 loopBody262_87

def loopBody262_89 : HolLoopProg 64 :=
.mark loopBody262_88

def loopBody262_90 : HolLoopProg 64 :=
.seq loopBody262_89 loopBody262_1

def loopBody262_91 : HolLoopProg 64 :=
.mark loopBody262_90

def loopBody262_92 : HolLoopProg 64 :=
.seq loopBody262_81 loopBody262_91

def loopBody262_93 : HolLoopProg 64 :=
.mark loopBody262_92

def loopBody262_94 : HolLoopProg 64 :=
.seq loopBody262_1 loopBody262_93

def loopBody262_95 : HolLoopProg 64 :=
.mark loopBody262_94

def loopBody262_96 : HolLoopProg 64 :=
.seq loopBody262_79 loopBody262_95

def loopBody262_97 : HolLoopProg 64 :=
.mark loopBody262_96

def loopBody262_98 : HolLoopProg 64 :=
.seq loopBody262_1 loopBody262_97

def loopBody262_99 : HolLoopProg 64 :=
.mark loopBody262_98

def loopBody262_100 : HolLoopProg 64 :=
.seq loopBody262_77 loopBody262_99

def loopBody262_101 : HolLoopProg 64 :=
.mark loopBody262_100

def loopBody262_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 4)

def loopBody262_103 : HolLoopProg 64 :=
.mark loopBody262_102

def loopBody262_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody262_105 : HolLoopProg 64 :=
.mark loopBody262_104

def loopBody262_106 : HolLoopProg 64 :=
.seq loopBody262_105 loopBody262_1

def loopBody262_107 : HolLoopProg 64 :=
.mark loopBody262_106

def loopBody262_108 : HolLoopProg 64 :=
.seq loopBody262_103 loopBody262_107

def loopBody262_109 : HolLoopProg 64 :=
.mark loopBody262_108

def loopBody262_110 : HolLoopProg 64 :=
.seq loopBody262_101 loopBody262_109

def loopBody262_111 : HolLoopProg 64 :=
.mark loopBody262_110

def loopBody262_112 : HolLoopProg 64 :=
.seq loopBody262_55 loopBody262_111

def loopBody262_113 : HolLoopProg 64 :=
.mark loopBody262_112

def loopBody262_114 : HolLoopProg 64 :=
.seq loopBody262_1 loopBody262_113

def loopBody262_115 : HolLoopProg 64 :=
.mark loopBody262_114

def loopBody262_116 : HolLoopProg 64 :=
.seq loopBody262_1 loopBody262_115

def loopBody262_117 : HolLoopProg 64 :=
.mark loopBody262_116

def loopBody262_118 : HolLoopProg 64 :=
.seq loopBody262_45 loopBody262_117

def loopBody262_119 : HolLoopProg 64 :=
.mark loopBody262_118

def loopBody262_120 : HolLoopProg 64 :=
.seq loopBody262_1 loopBody262_119

def loopBody262_121 : HolLoopProg 64 :=
.mark loopBody262_120

def loopBody262_122 : HolLoopProg 64 :=
.seq loopBody262_1 loopBody262_121

def loopBody262_123 : HolLoopProg 64 :=
.mark loopBody262_122

def loopBody262_124 : HolLoopProg 64 :=
.seq loopBody262_1 loopBody262_123

def loopBody262_125 : HolLoopProg 64 :=
.mark loopBody262_124

def loopBody262_126 : HolLoopProg 64 :=
.seq loopBody262_1 loopBody262_125

def loopBody262_127 : HolLoopProg 64 :=
.mark loopBody262_126

def loopBody262_128 : HolLoopProg 64 :=
.seq loopBody262_35 loopBody262_127

def loopBody262_129 : HolLoopProg 64 :=
.mark loopBody262_128

def loopBody262_130 : HolLoopProg 64 :=
.seq loopBody262_3 loopBody262_129

def loopBody262_131 : HolLoopProg 64 :=
.mark loopBody262_130

def loopBody262_132 : HolLoopProg 64 :=
.seq loopBody262_1 loopBody262_131

def loopBody262_133 : HolLoopProg 64 :=
.mark loopBody262_132

def output262 : Nat × List Nat × HolLoopProg 64 :=
  (326, [0], loopBody262_133)
end InitECandidate.Proofs.FrontendStages.Loop
