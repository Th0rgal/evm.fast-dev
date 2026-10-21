import InitECandidate.Proofs.FrontendStages.Loop.Translate348
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody364_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody364_1 : HolLoopProg 64 :=
.mark loopBody364_0

def loopBody364_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 24#64]))

def loopBody364_3 : HolLoopProg 64 :=
.mark loopBody364_2

def loopBody364_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody364_5 : HolLoopProg 64 :=
.mark loopBody364_4

def loopBody364_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody364_7 : HolLoopProg 64 :=
.mark loopBody364_6

def loopBody364_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody364_9 : HolLoopProg 64 :=
.mark loopBody364_8

def loopBody364_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody364_11 : HolLoopProg 64 :=
.mark loopBody364_10

def loopBody364_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody364_13 : HolLoopProg 64 :=
.mark loopBody364_12

def loopBody364_14 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 5 (Flapjack.RegImm.reg 6) loopBody364_11 loopBody364_13 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody364_15 : HolLoopProg 64 :=
.mark loopBody364_14

def loopBody364_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody364_17 : HolLoopProg 64 :=
.mark loopBody364_16

def loopBody364_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody364_19 : HolLoopProg 64 :=
.mark loopBody364_18

def loopBody364_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody364_21 : HolLoopProg 64 :=
.mark loopBody364_20

def loopBody364_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody364_23 : HolLoopProg 64 :=
.mark loopBody364_22

def loopBody364_24 : HolLoopProg 64 :=
.call (some
  ([4, 5, 6],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 197) ([7, 8]) (some (7, loopBody364_23, loopBody364_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody364_25 : HolLoopProg 64 :=
.mark loopBody364_24

def loopBody364_26 : HolLoopProg 64 :=
.seq loopBody364_25 loopBody364_1

def loopBody364_27 : HolLoopProg 64 :=
.mark loopBody364_26

def loopBody364_28 : HolLoopProg 64 :=
.seq loopBody364_21 loopBody364_27

def loopBody364_29 : HolLoopProg 64 :=
.mark loopBody364_28

def loopBody364_30 : HolLoopProg 64 :=
.seq loopBody364_19 loopBody364_29

def loopBody364_31 : HolLoopProg 64 :=
.mark loopBody364_30

def loopBody364_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 4)

def loopBody364_33 : HolLoopProg 64 :=
.mark loopBody364_32

def loopBody364_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody364_35 : HolLoopProg 64 :=
.mark loopBody364_34

def loopBody364_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody364_37 : HolLoopProg 64 :=
.mark loopBody364_36

def loopBody364_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody364_39 : HolLoopProg 64 :=
.mark loopBody364_38

def loopBody364_40 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.reg 9) loopBody364_37 loopBody364_39 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody364_41 : HolLoopProg 64 :=
.mark loopBody364_40

def loopBody364_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody364_43 : HolLoopProg 64 :=
.mark loopBody364_42

def loopBody364_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 0)

def loopBody364_45 : HolLoopProg 64 :=
.mark loopBody364_44

def loopBody364_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody364_47 : HolLoopProg 64 :=
.mark loopBody364_46

def loopBody364_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 6)

def loopBody364_49 : HolLoopProg 64 :=
.mark loopBody364_48

def loopBody364_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody364_51 : HolLoopProg 64 :=
.mark loopBody364_50

def loopBody364_52 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 192) ([8, 9, 10]) (some (8, loopBody364_51, loopBody364_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody364_53 : HolLoopProg 64 :=
.mark loopBody364_52

def loopBody364_54 : HolLoopProg 64 :=
.seq loopBody364_53 loopBody364_1

def loopBody364_55 : HolLoopProg 64 :=
.mark loopBody364_54

def loopBody364_56 : HolLoopProg 64 :=
.seq loopBody364_49 loopBody364_55

def loopBody364_57 : HolLoopProg 64 :=
.mark loopBody364_56

def loopBody364_58 : HolLoopProg 64 :=
.seq loopBody364_47 loopBody364_57

def loopBody364_59 : HolLoopProg 64 :=
.mark loopBody364_58

def loopBody364_60 : HolLoopProg 64 :=
.seq loopBody364_45 loopBody364_59

def loopBody364_61 : HolLoopProg 64 :=
.mark loopBody364_60

def loopBody364_62 : HolLoopProg 64 :=
.seq loopBody364_1 loopBody364_61

def loopBody364_63 : HolLoopProg 64 :=
.mark loopBody364_62

def loopBody364_64 : HolLoopProg 64 :=
.seq loopBody364_1 loopBody364_63

def loopBody364_65 : HolLoopProg 64 :=
.mark loopBody364_64

def loopBody364_66 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody364_65 loopBody364_1 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody364_67 : HolLoopProg 64 :=
.mark loopBody364_66

def loopBody364_68 : HolLoopProg 64 :=
.seq loopBody364_67 loopBody364_1

def loopBody364_69 : HolLoopProg 64 :=
.mark loopBody364_68

def loopBody364_70 : HolLoopProg 64 :=
.seq loopBody364_43 loopBody364_69

def loopBody364_71 : HolLoopProg 64 :=
.mark loopBody364_70

def loopBody364_72 : HolLoopProg 64 :=
.seq loopBody364_41 loopBody364_71

def loopBody364_73 : HolLoopProg 64 :=
.mark loopBody364_72

def loopBody364_74 : HolLoopProg 64 :=
.seq loopBody364_35 loopBody364_73

def loopBody364_75 : HolLoopProg 64 :=
.mark loopBody364_74

def loopBody364_76 : HolLoopProg 64 :=
.seq loopBody364_33 loopBody364_75

def loopBody364_77 : HolLoopProg 64 :=
.mark loopBody364_76

def loopBody364_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 1#64])

def loopBody364_79 : HolLoopProg 64 :=
.mark loopBody364_78

def loopBody364_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 7)

def loopBody364_81 : HolLoopProg 64 :=
.mark loopBody364_80

def loopBody364_82 : HolLoopProg 64 :=
.seq loopBody364_81 loopBody364_1

def loopBody364_83 : HolLoopProg 64 :=
.mark loopBody364_82

def loopBody364_84 : HolLoopProg 64 :=
.seq loopBody364_83 loopBody364_1

def loopBody364_85 : HolLoopProg 64 :=
.mark loopBody364_84

def loopBody364_86 : HolLoopProg 64 :=
.seq loopBody364_79 loopBody364_85

def loopBody364_87 : HolLoopProg 64 :=
.mark loopBody364_86

def loopBody364_88 : HolLoopProg 64 :=
.seq loopBody364_1 loopBody364_87

def loopBody364_89 : HolLoopProg 64 :=
.mark loopBody364_88

def loopBody364_90 : HolLoopProg 64 :=
.seq loopBody364_77 loopBody364_89

def loopBody364_91 : HolLoopProg 64 :=
.mark loopBody364_90

def loopBody364_92 : HolLoopProg 64 :=
.seq loopBody364_31 loopBody364_91

def loopBody364_93 : HolLoopProg 64 :=
.mark loopBody364_92

def loopBody364_94 : HolLoopProg 64 :=
.seq loopBody364_1 loopBody364_93

def loopBody364_95 : HolLoopProg 64 :=
.mark loopBody364_94

def loopBody364_96 : HolLoopProg 64 :=
.seq loopBody364_1 loopBody364_95

def loopBody364_97 : HolLoopProg 64 :=
.mark loopBody364_96

def loopBody364_98 : HolLoopProg 64 :=
.seq loopBody364_1 loopBody364_97

def loopBody364_99 : HolLoopProg 64 :=
.mark loopBody364_98

def loopBody364_100 : HolLoopProg 64 :=
.seq loopBody364_1 loopBody364_99

def loopBody364_101 : HolLoopProg 64 :=
.mark loopBody364_100

def loopBody364_102 : HolLoopProg 64 :=
.seq loopBody364_1 loopBody364_101

def loopBody364_103 : HolLoopProg 64 :=
.mark loopBody364_102

def loopBody364_104 : HolLoopProg 64 :=
.seq loopBody364_1 loopBody364_103

def loopBody364_105 : HolLoopProg 64 :=
.mark loopBody364_104

def loopBody364_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody364_107 : HolLoopProg 64 :=
.mark loopBody364_106

def loopBody364_108 : HolLoopProg 64 :=
.seq loopBody364_105 loopBody364_107

def loopBody364_109 : HolLoopProg 64 :=
.mark loopBody364_108

def loopBody364_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody364_111 : HolLoopProg 64 :=
.mark loopBody364_110

def loopBody364_112 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody364_109 loopBody364_111 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody364_113 : HolLoopProg 64 :=
.mark loopBody364_112

def loopBody364_114 : HolLoopProg 64 :=
.seq loopBody364_113 loopBody364_1

def loopBody364_115 : HolLoopProg 64 :=
.mark loopBody364_114

def loopBody364_116 : HolLoopProg 64 :=
.seq loopBody364_17 loopBody364_115

def loopBody364_117 : HolLoopProg 64 :=
.mark loopBody364_116

def loopBody364_118 : HolLoopProg 64 :=
.seq loopBody364_15 loopBody364_117

def loopBody364_119 : HolLoopProg 64 :=
.mark loopBody364_118

def loopBody364_120 : HolLoopProg 64 :=
.seq loopBody364_9 loopBody364_119

def loopBody364_121 : HolLoopProg 64 :=
.mark loopBody364_120

def loopBody364_122 : HolLoopProg 64 :=
.seq loopBody364_7 loopBody364_121

def loopBody364_123 : HolLoopProg 64 :=
.mark loopBody364_122

def loopBody364_124 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody364_123 (Flapjack.Spt.ln)

def loopBody364_125 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody364_126 : HolLoopProg 64 :=
.mark loopBody364_125

def loopBody364_127 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody364_128 : HolLoopProg 64 :=
.mark loopBody364_127

def loopBody364_129 : HolLoopProg 64 :=
.seq loopBody364_128 loopBody364_1

def loopBody364_130 : HolLoopProg 64 :=
.mark loopBody364_129

def loopBody364_131 : HolLoopProg 64 :=
.seq loopBody364_126 loopBody364_130

def loopBody364_132 : HolLoopProg 64 :=
.mark loopBody364_131

def loopBody364_133 : HolLoopProg 64 :=
.seq loopBody364_124 loopBody364_132

def loopBody364_134 : HolLoopProg 64 :=
.seq loopBody364_5 loopBody364_133

def loopBody364_135 : HolLoopProg 64 :=
.seq loopBody364_1 loopBody364_134

def loopBody364_136 : HolLoopProg 64 :=
.seq loopBody364_3 loopBody364_135

def loopBody364_137 : HolLoopProg 64 :=
.seq loopBody364_1 loopBody364_136

def output364 : Nat × List Nat × HolLoopProg 64 :=
  (428, [0, 1], loopBody364_137)
end InitECandidate.Proofs.FrontendStages.Loop
