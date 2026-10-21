import InitECandidate.Proofs.FrontendStages.Loop.Translate441
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody457_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody457_1 : HolLoopProg 64 :=
.mark loopBody457_0

def loopBody457_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody457_3 : HolLoopProg 64 :=
.mark loopBody457_2

def loopBody457_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody457_3, loopBody457_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody457_5 : HolLoopProg 64 :=
.mark loopBody457_4

def loopBody457_6 : HolLoopProg 64 :=
.seq loopBody457_5 loopBody457_1

def loopBody457_7 : HolLoopProg 64 :=
.mark loopBody457_6

def loopBody457_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 8#64)

def loopBody457_9 : HolLoopProg 64 :=
.mark loopBody457_8

def loopBody457_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody457_11 : HolLoopProg 64 :=
.mark loopBody457_10

def loopBody457_12 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 466) ([6]) (some (6, loopBody457_11, loopBody457_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody457_13 : HolLoopProg 64 :=
.mark loopBody457_12

def loopBody457_14 : HolLoopProg 64 :=
.seq loopBody457_13 loopBody457_1

def loopBody457_15 : HolLoopProg 64 :=
.mark loopBody457_14

def loopBody457_16 : HolLoopProg 64 :=
.seq loopBody457_9 loopBody457_15

def loopBody457_17 : HolLoopProg 64 :=
.mark loopBody457_16

def loopBody457_18 : HolLoopProg 64 :=
.seq loopBody457_1 loopBody457_17

def loopBody457_19 : HolLoopProg 64 :=
.mark loopBody457_18

def loopBody457_20 : HolLoopProg 64 :=
.seq loopBody457_1 loopBody457_19

def loopBody457_21 : HolLoopProg 64 :=
.mark loopBody457_20

def loopBody457_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody457_23 : HolLoopProg 64 :=
.mark loopBody457_22

def loopBody457_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody457_25 : HolLoopProg 64 :=
.mark loopBody457_24

def loopBody457_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody457_27 : HolLoopProg 64 :=
.mark loopBody457_26

def loopBody457_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody457_29 : HolLoopProg 64 :=
.mark loopBody457_28

def loopBody457_30 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 482) ([6, 7, 8, 9]) (some (6, loopBody457_11, loopBody457_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))

def loopBody457_31 : HolLoopProg 64 :=
.mark loopBody457_30

def loopBody457_32 : HolLoopProg 64 :=
.seq loopBody457_31 loopBody457_1

def loopBody457_33 : HolLoopProg 64 :=
.mark loopBody457_32

def loopBody457_34 : HolLoopProg 64 :=
.seq loopBody457_29 loopBody457_33

def loopBody457_35 : HolLoopProg 64 :=
.mark loopBody457_34

def loopBody457_36 : HolLoopProg 64 :=
.seq loopBody457_27 loopBody457_35

def loopBody457_37 : HolLoopProg 64 :=
.mark loopBody457_36

def loopBody457_38 : HolLoopProg 64 :=
.seq loopBody457_25 loopBody457_37

def loopBody457_39 : HolLoopProg 64 :=
.mark loopBody457_38

def loopBody457_40 : HolLoopProg 64 :=
.seq loopBody457_23 loopBody457_39

def loopBody457_41 : HolLoopProg 64 :=
.mark loopBody457_40

def loopBody457_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody457_43 : HolLoopProg 64 :=
.mark loopBody457_42

def loopBody457_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody457_45 : HolLoopProg 64 :=
.mark loopBody457_44

def loopBody457_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody457_47 : HolLoopProg 64 :=
.mark loopBody457_46

def loopBody457_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody457_49 : HolLoopProg 64 :=
.mark loopBody457_48

def loopBody457_50 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 7 (Flapjack.RegImm.reg 8) loopBody457_47 loopBody457_49 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody457_51 : HolLoopProg 64 :=
.mark loopBody457_50

def loopBody457_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody457_53 : HolLoopProg 64 :=
.mark loopBody457_52

def loopBody457_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 6#64)

def loopBody457_55 : HolLoopProg 64 :=
.mark loopBody457_54

def loopBody457_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 6)

def loopBody457_57 : HolLoopProg 64 :=
.mark loopBody457_56

def loopBody457_58 : HolLoopProg 64 :=
.seq loopBody457_57 loopBody457_1

def loopBody457_59 : HolLoopProg 64 :=
.mark loopBody457_58

def loopBody457_60 : HolLoopProg 64 :=
.seq loopBody457_59 loopBody457_1

def loopBody457_61 : HolLoopProg 64 :=
.mark loopBody457_60

def loopBody457_62 : HolLoopProg 64 :=
.seq loopBody457_55 loopBody457_61

def loopBody457_63 : HolLoopProg 64 :=
.mark loopBody457_62

def loopBody457_64 : HolLoopProg 64 :=
.seq loopBody457_1 loopBody457_63

def loopBody457_65 : HolLoopProg 64 :=
.mark loopBody457_64

def loopBody457_66 : HolLoopProg 64 :=
.seq loopBody457_9 loopBody457_11

def loopBody457_67 : HolLoopProg 64 :=
.mark loopBody457_66

def loopBody457_68 : HolLoopProg 64 :=
.seq loopBody457_65 loopBody457_67

def loopBody457_69 : HolLoopProg 64 :=
.mark loopBody457_68

def loopBody457_70 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody457_69 loopBody457_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))

def loopBody457_71 : HolLoopProg 64 :=
.mark loopBody457_70

def loopBody457_72 : HolLoopProg 64 :=
.seq loopBody457_71 loopBody457_1

def loopBody457_73 : HolLoopProg 64 :=
.mark loopBody457_72

def loopBody457_74 : HolLoopProg 64 :=
.seq loopBody457_53 loopBody457_73

def loopBody457_75 : HolLoopProg 64 :=
.mark loopBody457_74

def loopBody457_76 : HolLoopProg 64 :=
.seq loopBody457_51 loopBody457_75

def loopBody457_77 : HolLoopProg 64 :=
.mark loopBody457_76

def loopBody457_78 : HolLoopProg 64 :=
.seq loopBody457_45 loopBody457_77

def loopBody457_79 : HolLoopProg 64 :=
.mark loopBody457_78

def loopBody457_80 : HolLoopProg 64 :=
.seq loopBody457_43 loopBody457_79

def loopBody457_81 : HolLoopProg 64 :=
.mark loopBody457_80

def loopBody457_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 0#64])

def loopBody457_83 : HolLoopProg 64 :=
.mark loopBody457_82

def loopBody457_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody457_85 : HolLoopProg 64 :=
.mark loopBody457_84

def loopBody457_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 7)

def loopBody457_87 : HolLoopProg 64 :=
.mark loopBody457_86

def loopBody457_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 6) 8

def loopBody457_89 : HolLoopProg 64 :=
.mark loopBody457_88

def loopBody457_90 : HolLoopProg 64 :=
.seq loopBody457_89 loopBody457_1

def loopBody457_91 : HolLoopProg 64 :=
.mark loopBody457_90

def loopBody457_92 : HolLoopProg 64 :=
.seq loopBody457_87 loopBody457_91

def loopBody457_93 : HolLoopProg 64 :=
.mark loopBody457_92

def loopBody457_94 : HolLoopProg 64 :=
.seq loopBody457_93 loopBody457_1

def loopBody457_95 : HolLoopProg 64 :=
.mark loopBody457_94

def loopBody457_96 : HolLoopProg 64 :=
.seq loopBody457_85 loopBody457_95

def loopBody457_97 : HolLoopProg 64 :=
.mark loopBody457_96

def loopBody457_98 : HolLoopProg 64 :=
.seq loopBody457_1 loopBody457_97

def loopBody457_99 : HolLoopProg 64 :=
.mark loopBody457_98

def loopBody457_100 : HolLoopProg 64 :=
.seq loopBody457_83 loopBody457_99

def loopBody457_101 : HolLoopProg 64 :=
.mark loopBody457_100

def loopBody457_102 : HolLoopProg 64 :=
.seq loopBody457_1 loopBody457_101

def loopBody457_103 : HolLoopProg 64 :=
.mark loopBody457_102

def loopBody457_104 : HolLoopProg 64 :=
.seq loopBody457_81 loopBody457_103

def loopBody457_105 : HolLoopProg 64 :=
.mark loopBody457_104

def loopBody457_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody457_107 : HolLoopProg 64 :=
.mark loopBody457_106

def loopBody457_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody457_109 : HolLoopProg 64 :=
.mark loopBody457_108

def loopBody457_110 : HolLoopProg 64 :=
.seq loopBody457_109 loopBody457_1

def loopBody457_111 : HolLoopProg 64 :=
.mark loopBody457_110

def loopBody457_112 : HolLoopProg 64 :=
.seq loopBody457_107 loopBody457_111

def loopBody457_113 : HolLoopProg 64 :=
.mark loopBody457_112

def loopBody457_114 : HolLoopProg 64 :=
.seq loopBody457_105 loopBody457_113

def loopBody457_115 : HolLoopProg 64 :=
.mark loopBody457_114

def loopBody457_116 : HolLoopProg 64 :=
.seq loopBody457_41 loopBody457_115

def loopBody457_117 : HolLoopProg 64 :=
.mark loopBody457_116

def loopBody457_118 : HolLoopProg 64 :=
.seq loopBody457_1 loopBody457_117

def loopBody457_119 : HolLoopProg 64 :=
.mark loopBody457_118

def loopBody457_120 : HolLoopProg 64 :=
.seq loopBody457_1 loopBody457_119

def loopBody457_121 : HolLoopProg 64 :=
.mark loopBody457_120

def loopBody457_122 : HolLoopProg 64 :=
.seq loopBody457_21 loopBody457_121

def loopBody457_123 : HolLoopProg 64 :=
.mark loopBody457_122

def loopBody457_124 : HolLoopProg 64 :=
.seq loopBody457_7 loopBody457_123

def loopBody457_125 : HolLoopProg 64 :=
.mark loopBody457_124

def loopBody457_126 : HolLoopProg 64 :=
.seq loopBody457_1 loopBody457_125

def loopBody457_127 : HolLoopProg 64 :=
.mark loopBody457_126

def loopBody457_128 : HolLoopProg 64 :=
.seq loopBody457_1 loopBody457_127

def loopBody457_129 : HolLoopProg 64 :=
.mark loopBody457_128

def loopBody457_130 : HolLoopProg 64 :=
.seq loopBody457_1 loopBody457_129

def loopBody457_131 : HolLoopProg 64 :=
.mark loopBody457_130

def loopBody457_132 : HolLoopProg 64 :=
.seq loopBody457_1 loopBody457_131

def loopBody457_133 : HolLoopProg 64 :=
.mark loopBody457_132

def loopBody457_134 : HolLoopProg 64 :=
.seq loopBody457_1 loopBody457_133

def loopBody457_135 : HolLoopProg 64 :=
.mark loopBody457_134

def loopBody457_136 : HolLoopProg 64 :=
.seq loopBody457_1 loopBody457_135

def loopBody457_137 : HolLoopProg 64 :=
.mark loopBody457_136

def loopBody457_138 : HolLoopProg 64 :=
.seq loopBody457_1 loopBody457_137

def loopBody457_139 : HolLoopProg 64 :=
.mark loopBody457_138

def loopBody457_140 : HolLoopProg 64 :=
.seq loopBody457_1 loopBody457_139

def loopBody457_141 : HolLoopProg 64 :=
.mark loopBody457_140

def output457 : Nat × List Nat × HolLoopProg 64 :=
  (521, [], loopBody457_141)
end InitECandidate.Proofs.FrontendStages.Loop
