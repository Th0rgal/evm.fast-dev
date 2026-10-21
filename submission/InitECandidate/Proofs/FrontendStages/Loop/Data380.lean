import InitECandidate.Proofs.FrontendStages.Loop.Translate364
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody380_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody380_1 : HolLoopProg 64 :=
.mark loopBody380_0

def loopBody380_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 176#64]),
        Flapjack.HolLoopExp.const 32#64]))

def loopBody380_3 : HolLoopProg 64 :=
.mark loopBody380_2

def loopBody380_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody380_5 : HolLoopProg 64 :=
.mark loopBody380_4

def loopBody380_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody380_7 : HolLoopProg 64 :=
.mark loopBody380_6

def loopBody380_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody380_9 : HolLoopProg 64 :=
.mark loopBody380_8

def loopBody380_10 : HolLoopProg 64 :=
.call (some ([2, 3], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 405) ([4, 5, 6]) (some (4, loopBody380_9, loopBody380_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody380_11 : HolLoopProg 64 :=
.mark loopBody380_10

def loopBody380_12 : HolLoopProg 64 :=
.seq loopBody380_11 loopBody380_1

def loopBody380_13 : HolLoopProg 64 :=
.mark loopBody380_12

def loopBody380_14 : HolLoopProg 64 :=
.seq loopBody380_7 loopBody380_13

def loopBody380_15 : HolLoopProg 64 :=
.mark loopBody380_14

def loopBody380_16 : HolLoopProg 64 :=
.seq loopBody380_5 loopBody380_15

def loopBody380_17 : HolLoopProg 64 :=
.mark loopBody380_16

def loopBody380_18 : HolLoopProg 64 :=
.seq loopBody380_3 loopBody380_17

def loopBody380_19 : HolLoopProg 64 :=
.mark loopBody380_18

def loopBody380_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody380_21 : HolLoopProg 64 :=
.mark loopBody380_20

def loopBody380_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody380_23 : HolLoopProg 64 :=
.mark loopBody380_22

def loopBody380_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody380_25 : HolLoopProg 64 :=
.mark loopBody380_24

def loopBody380_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody380_27 : HolLoopProg 64 :=
.mark loopBody380_26

def loopBody380_28 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.reg 6) loopBody380_25 loopBody380_27 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody380_29 : HolLoopProg 64 :=
.mark loopBody380_28

def loopBody380_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody380_31 : HolLoopProg 64 :=
.mark loopBody380_30

def loopBody380_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.var 3))

def loopBody380_33 : HolLoopProg 64 :=
.mark loopBody380_32

def loopBody380_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 8#64]))

def loopBody380_35 : HolLoopProg 64 :=
.mark loopBody380_34

def loopBody380_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 16#64]))

def loopBody380_37 : HolLoopProg 64 :=
.mark loopBody380_36

def loopBody380_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 24#64]))

def loopBody380_39 : HolLoopProg 64 :=
.mark loopBody380_38

def loopBody380_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4, 5, 6, 7]

def loopBody380_41 : HolLoopProg 64 :=
.mark loopBody380_40

def loopBody380_42 : HolLoopProg 64 :=
.seq loopBody380_41 loopBody380_1

def loopBody380_43 : HolLoopProg 64 :=
.mark loopBody380_42

def loopBody380_44 : HolLoopProg 64 :=
.seq loopBody380_39 loopBody380_43

def loopBody380_45 : HolLoopProg 64 :=
.mark loopBody380_44

def loopBody380_46 : HolLoopProg 64 :=
.seq loopBody380_37 loopBody380_45

def loopBody380_47 : HolLoopProg 64 :=
.mark loopBody380_46

def loopBody380_48 : HolLoopProg 64 :=
.seq loopBody380_35 loopBody380_47

def loopBody380_49 : HolLoopProg 64 :=
.mark loopBody380_48

def loopBody380_50 : HolLoopProg 64 :=
.seq loopBody380_33 loopBody380_49

def loopBody380_51 : HolLoopProg 64 :=
.mark loopBody380_50

def loopBody380_52 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody380_51 loopBody380_1 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody380_53 : HolLoopProg 64 :=
.mark loopBody380_52

def loopBody380_54 : HolLoopProg 64 :=
.seq loopBody380_53 loopBody380_1

def loopBody380_55 : HolLoopProg 64 :=
.mark loopBody380_54

def loopBody380_56 : HolLoopProg 64 :=
.seq loopBody380_31 loopBody380_55

def loopBody380_57 : HolLoopProg 64 :=
.mark loopBody380_56

def loopBody380_58 : HolLoopProg 64 :=
.seq loopBody380_29 loopBody380_57

def loopBody380_59 : HolLoopProg 64 :=
.mark loopBody380_58

def loopBody380_60 : HolLoopProg 64 :=
.seq loopBody380_23 loopBody380_59

def loopBody380_61 : HolLoopProg 64 :=
.mark loopBody380_60

def loopBody380_62 : HolLoopProg 64 :=
.seq loopBody380_21 loopBody380_61

def loopBody380_63 : HolLoopProg 64 :=
.mark loopBody380_62

def loopBody380_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody380_65 : HolLoopProg 64 :=
.mark loopBody380_64

def loopBody380_66 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 392) ([5]) (some (5, loopBody380_65, loopBody380_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody380_67 : HolLoopProg 64 :=
.mark loopBody380_66

def loopBody380_68 : HolLoopProg 64 :=
.seq loopBody380_67 loopBody380_1

def loopBody380_69 : HolLoopProg 64 :=
.mark loopBody380_68

def loopBody380_70 : HolLoopProg 64 :=
.seq loopBody380_5 loopBody380_69

def loopBody380_71 : HolLoopProg 64 :=
.mark loopBody380_70

def loopBody380_72 : HolLoopProg 64 :=
.seq loopBody380_1 loopBody380_71

def loopBody380_73 : HolLoopProg 64 :=
.mark loopBody380_72

def loopBody380_74 : HolLoopProg 64 :=
.seq loopBody380_1 loopBody380_73

def loopBody380_75 : HolLoopProg 64 :=
.mark loopBody380_74

def loopBody380_76 : HolLoopProg 64 :=
.seq loopBody380_63 loopBody380_75

def loopBody380_77 : HolLoopProg 64 :=
.mark loopBody380_76

def loopBody380_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 0)

def loopBody380_79 : HolLoopProg 64 :=
.mark loopBody380_78

def loopBody380_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 1)

def loopBody380_81 : HolLoopProg 64 :=
.mark loopBody380_80

def loopBody380_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody380_83 : HolLoopProg 64 :=
.mark loopBody380_82

def loopBody380_84 : HolLoopProg 64 :=
.call (some ([4, 5, 6, 7], Flapjack.Spt.ln)) (some 397) ([8, 9]) (some (8, loopBody380_83, loopBody380_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody380_85 : HolLoopProg 64 :=
.mark loopBody380_84

def loopBody380_86 : HolLoopProg 64 :=
.seq loopBody380_85 loopBody380_1

def loopBody380_87 : HolLoopProg 64 :=
.mark loopBody380_86

def loopBody380_88 : HolLoopProg 64 :=
.seq loopBody380_81 loopBody380_87

def loopBody380_89 : HolLoopProg 64 :=
.mark loopBody380_88

def loopBody380_90 : HolLoopProg 64 :=
.seq loopBody380_79 loopBody380_89

def loopBody380_91 : HolLoopProg 64 :=
.mark loopBody380_90

def loopBody380_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 4)

def loopBody380_93 : HolLoopProg 64 :=
.mark loopBody380_92

def loopBody380_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody380_95 : HolLoopProg 64 :=
.mark loopBody380_94

def loopBody380_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 6)

def loopBody380_97 : HolLoopProg 64 :=
.mark loopBody380_96

def loopBody380_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 7)

def loopBody380_99 : HolLoopProg 64 :=
.mark loopBody380_98

def loopBody380_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [8, 9, 10, 11]

def loopBody380_101 : HolLoopProg 64 :=
.mark loopBody380_100

def loopBody380_102 : HolLoopProg 64 :=
.seq loopBody380_101 loopBody380_1

def loopBody380_103 : HolLoopProg 64 :=
.mark loopBody380_102

def loopBody380_104 : HolLoopProg 64 :=
.seq loopBody380_99 loopBody380_103

def loopBody380_105 : HolLoopProg 64 :=
.mark loopBody380_104

def loopBody380_106 : HolLoopProg 64 :=
.seq loopBody380_97 loopBody380_105

def loopBody380_107 : HolLoopProg 64 :=
.mark loopBody380_106

def loopBody380_108 : HolLoopProg 64 :=
.seq loopBody380_95 loopBody380_107

def loopBody380_109 : HolLoopProg 64 :=
.mark loopBody380_108

def loopBody380_110 : HolLoopProg 64 :=
.seq loopBody380_93 loopBody380_109

def loopBody380_111 : HolLoopProg 64 :=
.mark loopBody380_110

def loopBody380_112 : HolLoopProg 64 :=
.seq loopBody380_91 loopBody380_111

def loopBody380_113 : HolLoopProg 64 :=
.mark loopBody380_112

def loopBody380_114 : HolLoopProg 64 :=
.seq loopBody380_1 loopBody380_113

def loopBody380_115 : HolLoopProg 64 :=
.mark loopBody380_114

def loopBody380_116 : HolLoopProg 64 :=
.seq loopBody380_1 loopBody380_115

def loopBody380_117 : HolLoopProg 64 :=
.mark loopBody380_116

def loopBody380_118 : HolLoopProg 64 :=
.seq loopBody380_1 loopBody380_117

def loopBody380_119 : HolLoopProg 64 :=
.mark loopBody380_118

def loopBody380_120 : HolLoopProg 64 :=
.seq loopBody380_1 loopBody380_119

def loopBody380_121 : HolLoopProg 64 :=
.mark loopBody380_120

def loopBody380_122 : HolLoopProg 64 :=
.seq loopBody380_1 loopBody380_121

def loopBody380_123 : HolLoopProg 64 :=
.mark loopBody380_122

def loopBody380_124 : HolLoopProg 64 :=
.seq loopBody380_1 loopBody380_123

def loopBody380_125 : HolLoopProg 64 :=
.mark loopBody380_124

def loopBody380_126 : HolLoopProg 64 :=
.seq loopBody380_1 loopBody380_125

def loopBody380_127 : HolLoopProg 64 :=
.mark loopBody380_126

def loopBody380_128 : HolLoopProg 64 :=
.seq loopBody380_1 loopBody380_127

def loopBody380_129 : HolLoopProg 64 :=
.mark loopBody380_128

def loopBody380_130 : HolLoopProg 64 :=
.seq loopBody380_77 loopBody380_129

def loopBody380_131 : HolLoopProg 64 :=
.mark loopBody380_130

def loopBody380_132 : HolLoopProg 64 :=
.seq loopBody380_19 loopBody380_131

def loopBody380_133 : HolLoopProg 64 :=
.mark loopBody380_132

def loopBody380_134 : HolLoopProg 64 :=
.seq loopBody380_1 loopBody380_133

def loopBody380_135 : HolLoopProg 64 :=
.mark loopBody380_134

def loopBody380_136 : HolLoopProg 64 :=
.seq loopBody380_1 loopBody380_135

def loopBody380_137 : HolLoopProg 64 :=
.mark loopBody380_136

def loopBody380_138 : HolLoopProg 64 :=
.seq loopBody380_1 loopBody380_137

def loopBody380_139 : HolLoopProg 64 :=
.mark loopBody380_138

def loopBody380_140 : HolLoopProg 64 :=
.seq loopBody380_1 loopBody380_139

def loopBody380_141 : HolLoopProg 64 :=
.mark loopBody380_140

def output380 : Nat × List Nat × HolLoopProg 64 :=
  (444, [0, 1], loopBody380_141)
end InitECandidate.Proofs.FrontendStages.Loop
