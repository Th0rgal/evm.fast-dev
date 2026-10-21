import InitECandidate.Proofs.FrontendStages.Loop.Translate318
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody334_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody334_1 : HolLoopProg 64 :=
.mark loopBody334_0

def loopBody334_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody334_3 : HolLoopProg 64 :=
.mark loopBody334_2

def loopBody334_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 136#64]))

def loopBody334_5 : HolLoopProg 64 :=
.mark loopBody334_4

def loopBody334_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 32#64)

def loopBody334_7 : HolLoopProg 64 :=
.mark loopBody334_6

def loopBody334_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody334_9 : HolLoopProg 64 :=
.mark loopBody334_8

def loopBody334_10 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 79) ([2, 3, 4]) (some (2, loopBody334_9, loopBody334_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody334_11 : HolLoopProg 64 :=
.mark loopBody334_10

def loopBody334_12 : HolLoopProg 64 :=
.seq loopBody334_11 loopBody334_1

def loopBody334_13 : HolLoopProg 64 :=
.mark loopBody334_12

def loopBody334_14 : HolLoopProg 64 :=
.seq loopBody334_7 loopBody334_13

def loopBody334_15 : HolLoopProg 64 :=
.mark loopBody334_14

def loopBody334_16 : HolLoopProg 64 :=
.seq loopBody334_5 loopBody334_15

def loopBody334_17 : HolLoopProg 64 :=
.mark loopBody334_16

def loopBody334_18 : HolLoopProg 64 :=
.seq loopBody334_3 loopBody334_17

def loopBody334_19 : HolLoopProg 64 :=
.mark loopBody334_18

def loopBody334_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody334_21 : HolLoopProg 64 :=
.mark loopBody334_20

def loopBody334_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody334_23 : HolLoopProg 64 :=
.mark loopBody334_22

def loopBody334_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody334_25 : HolLoopProg 64 :=
.mark loopBody334_24

def loopBody334_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody334_27 : HolLoopProg 64 :=
.mark loopBody334_26

def loopBody334_28 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 3 (Flapjack.RegImm.reg 4) loopBody334_25 loopBody334_27 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody334_29 : HolLoopProg 64 :=
.mark loopBody334_28

def loopBody334_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody334_31 : HolLoopProg 64 :=
.mark loopBody334_30

def loopBody334_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody334_33 : HolLoopProg 64 :=
.mark loopBody334_32

def loopBody334_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2, 3]

def loopBody334_35 : HolLoopProg 64 :=
.mark loopBody334_34

def loopBody334_36 : HolLoopProg 64 :=
.seq loopBody334_35 loopBody334_1

def loopBody334_37 : HolLoopProg 64 :=
.mark loopBody334_36

def loopBody334_38 : HolLoopProg 64 :=
.seq loopBody334_27 loopBody334_37

def loopBody334_39 : HolLoopProg 64 :=
.mark loopBody334_38

def loopBody334_40 : HolLoopProg 64 :=
.seq loopBody334_33 loopBody334_39

def loopBody334_41 : HolLoopProg 64 :=
.mark loopBody334_40

def loopBody334_42 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody334_41 loopBody334_1 (Flapjack.Spt.ls PUnit.unit)

def loopBody334_43 : HolLoopProg 64 :=
.mark loopBody334_42

def loopBody334_44 : HolLoopProg 64 :=
.seq loopBody334_43 loopBody334_1

def loopBody334_45 : HolLoopProg 64 :=
.mark loopBody334_44

def loopBody334_46 : HolLoopProg 64 :=
.seq loopBody334_31 loopBody334_45

def loopBody334_47 : HolLoopProg 64 :=
.mark loopBody334_46

def loopBody334_48 : HolLoopProg 64 :=
.seq loopBody334_29 loopBody334_47

def loopBody334_49 : HolLoopProg 64 :=
.mark loopBody334_48

def loopBody334_50 : HolLoopProg 64 :=
.seq loopBody334_23 loopBody334_49

def loopBody334_51 : HolLoopProg 64 :=
.mark loopBody334_50

def loopBody334_52 : HolLoopProg 64 :=
.seq loopBody334_21 loopBody334_51

def loopBody334_53 : HolLoopProg 64 :=
.mark loopBody334_52

def loopBody334_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 168#64]),
        Flapjack.HolLoopExp.const 16#64]))

def loopBody334_55 : HolLoopProg 64 :=
.mark loopBody334_54

def loopBody334_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody334_57 : HolLoopProg 64 :=
.mark loopBody334_56

def loopBody334_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody334_59 : HolLoopProg 64 :=
.mark loopBody334_58

def loopBody334_60 : HolLoopProg 64 :=
.call (some ([2, 3, 4], Flapjack.Spt.ln)) (some 290) ([5, 6]) (some (5, loopBody334_59, loopBody334_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody334_61 : HolLoopProg 64 :=
.mark loopBody334_60

def loopBody334_62 : HolLoopProg 64 :=
.seq loopBody334_61 loopBody334_1

def loopBody334_63 : HolLoopProg 64 :=
.mark loopBody334_62

def loopBody334_64 : HolLoopProg 64 :=
.seq loopBody334_57 loopBody334_63

def loopBody334_65 : HolLoopProg 64 :=
.mark loopBody334_64

def loopBody334_66 : HolLoopProg 64 :=
.seq loopBody334_55 loopBody334_65

def loopBody334_67 : HolLoopProg 64 :=
.mark loopBody334_66

def loopBody334_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody334_69 : HolLoopProg 64 :=
.mark loopBody334_68

def loopBody334_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody334_71 : HolLoopProg 64 :=
.mark loopBody334_70

def loopBody334_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody334_73 : HolLoopProg 64 :=
.mark loopBody334_72

def loopBody334_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody334_75 : HolLoopProg 64 :=
.mark loopBody334_74

def loopBody334_76 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.RegImm.reg 7) loopBody334_73 loopBody334_75 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody334_77 : HolLoopProg 64 :=
.mark loopBody334_76

def loopBody334_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody334_79 : HolLoopProg 64 :=
.mark loopBody334_78

def loopBody334_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 2#64)

def loopBody334_81 : HolLoopProg 64 :=
.mark loopBody334_80

def loopBody334_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 5)

def loopBody334_83 : HolLoopProg 64 :=
.mark loopBody334_82

def loopBody334_84 : HolLoopProg 64 :=
.seq loopBody334_83 loopBody334_1

def loopBody334_85 : HolLoopProg 64 :=
.mark loopBody334_84

def loopBody334_86 : HolLoopProg 64 :=
.seq loopBody334_85 loopBody334_1

def loopBody334_87 : HolLoopProg 64 :=
.mark loopBody334_86

def loopBody334_88 : HolLoopProg 64 :=
.seq loopBody334_81 loopBody334_87

def loopBody334_89 : HolLoopProg 64 :=
.mark loopBody334_88

def loopBody334_90 : HolLoopProg 64 :=
.seq loopBody334_1 loopBody334_89

def loopBody334_91 : HolLoopProg 64 :=
.mark loopBody334_90

def loopBody334_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 7#64)

def loopBody334_93 : HolLoopProg 64 :=
.mark loopBody334_92

def loopBody334_94 : HolLoopProg 64 :=
.seq loopBody334_93 loopBody334_59

def loopBody334_95 : HolLoopProg 64 :=
.mark loopBody334_94

def loopBody334_96 : HolLoopProg 64 :=
.seq loopBody334_91 loopBody334_95

def loopBody334_97 : HolLoopProg 64 :=
.mark loopBody334_96

def loopBody334_98 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody334_97 loopBody334_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody334_99 : HolLoopProg 64 :=
.mark loopBody334_98

def loopBody334_100 : HolLoopProg 64 :=
.seq loopBody334_99 loopBody334_1

def loopBody334_101 : HolLoopProg 64 :=
.mark loopBody334_100

def loopBody334_102 : HolLoopProg 64 :=
.seq loopBody334_79 loopBody334_101

def loopBody334_103 : HolLoopProg 64 :=
.mark loopBody334_102

def loopBody334_104 : HolLoopProg 64 :=
.seq loopBody334_77 loopBody334_103

def loopBody334_105 : HolLoopProg 64 :=
.mark loopBody334_104

def loopBody334_106 : HolLoopProg 64 :=
.seq loopBody334_71 loopBody334_105

def loopBody334_107 : HolLoopProg 64 :=
.mark loopBody334_106

def loopBody334_108 : HolLoopProg 64 :=
.seq loopBody334_69 loopBody334_107

def loopBody334_109 : HolLoopProg 64 :=
.mark loopBody334_108

def loopBody334_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody334_111 : HolLoopProg 64 :=
.mark loopBody334_110

def loopBody334_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5, 6]

def loopBody334_113 : HolLoopProg 64 :=
.mark loopBody334_112

def loopBody334_114 : HolLoopProg 64 :=
.seq loopBody334_113 loopBody334_1

def loopBody334_115 : HolLoopProg 64 :=
.mark loopBody334_114

def loopBody334_116 : HolLoopProg 64 :=
.seq loopBody334_111 loopBody334_115

def loopBody334_117 : HolLoopProg 64 :=
.mark loopBody334_116

def loopBody334_118 : HolLoopProg 64 :=
.seq loopBody334_31 loopBody334_117

def loopBody334_119 : HolLoopProg 64 :=
.mark loopBody334_118

def loopBody334_120 : HolLoopProg 64 :=
.seq loopBody334_109 loopBody334_119

def loopBody334_121 : HolLoopProg 64 :=
.mark loopBody334_120

def loopBody334_122 : HolLoopProg 64 :=
.seq loopBody334_67 loopBody334_121

def loopBody334_123 : HolLoopProg 64 :=
.mark loopBody334_122

def loopBody334_124 : HolLoopProg 64 :=
.seq loopBody334_1 loopBody334_123

def loopBody334_125 : HolLoopProg 64 :=
.mark loopBody334_124

def loopBody334_126 : HolLoopProg 64 :=
.seq loopBody334_1 loopBody334_125

def loopBody334_127 : HolLoopProg 64 :=
.mark loopBody334_126

def loopBody334_128 : HolLoopProg 64 :=
.seq loopBody334_1 loopBody334_127

def loopBody334_129 : HolLoopProg 64 :=
.mark loopBody334_128

def loopBody334_130 : HolLoopProg 64 :=
.seq loopBody334_1 loopBody334_129

def loopBody334_131 : HolLoopProg 64 :=
.mark loopBody334_130

def loopBody334_132 : HolLoopProg 64 :=
.seq loopBody334_1 loopBody334_131

def loopBody334_133 : HolLoopProg 64 :=
.mark loopBody334_132

def loopBody334_134 : HolLoopProg 64 :=
.seq loopBody334_1 loopBody334_133

def loopBody334_135 : HolLoopProg 64 :=
.mark loopBody334_134

def loopBody334_136 : HolLoopProg 64 :=
.seq loopBody334_53 loopBody334_135

def loopBody334_137 : HolLoopProg 64 :=
.mark loopBody334_136

def loopBody334_138 : HolLoopProg 64 :=
.seq loopBody334_19 loopBody334_137

def loopBody334_139 : HolLoopProg 64 :=
.mark loopBody334_138

def loopBody334_140 : HolLoopProg 64 :=
.seq loopBody334_1 loopBody334_139

def loopBody334_141 : HolLoopProg 64 :=
.mark loopBody334_140

def loopBody334_142 : HolLoopProg 64 :=
.seq loopBody334_1 loopBody334_141

def loopBody334_143 : HolLoopProg 64 :=
.mark loopBody334_142

def output334 : Nat × List Nat × HolLoopProg 64 :=
  (398, [0], loopBody334_143)
end InitECandidate.Proofs.FrontendStages.Loop
