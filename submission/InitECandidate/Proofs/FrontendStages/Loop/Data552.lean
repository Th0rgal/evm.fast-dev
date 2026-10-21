import InitECandidate.Proofs.FrontendStages.Loop.Translate536
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody552_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody552_1 : HolLoopProg 64 :=
.mark loopBody552_0

def loopBody552_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 0)

def loopBody552_3 : HolLoopProg 64 :=
.mark loopBody552_2

def loopBody552_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 1)

def loopBody552_5 : HolLoopProg 64 :=
.mark loopBody552_4

def loopBody552_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 2)

def loopBody552_7 : HolLoopProg 64 :=
.mark loopBody552_6

def loopBody552_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 3)

def loopBody552_9 : HolLoopProg 64 :=
.mark loopBody552_8

def loopBody552_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody552_11 : HolLoopProg 64 :=
.mark loopBody552_10

def loopBody552_12 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))) (some 102) ([9, 10, 11, 12]) (some (9, loopBody552_11, loopBody552_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody552_13 : HolLoopProg 64 :=
.mark loopBody552_12

def loopBody552_14 : HolLoopProg 64 :=
.seq loopBody552_13 loopBody552_1

def loopBody552_15 : HolLoopProg 64 :=
.mark loopBody552_14

def loopBody552_16 : HolLoopProg 64 :=
.seq loopBody552_9 loopBody552_15

def loopBody552_17 : HolLoopProg 64 :=
.mark loopBody552_16

def loopBody552_18 : HolLoopProg 64 :=
.seq loopBody552_7 loopBody552_17

def loopBody552_19 : HolLoopProg 64 :=
.mark loopBody552_18

def loopBody552_20 : HolLoopProg 64 :=
.seq loopBody552_5 loopBody552_19

def loopBody552_21 : HolLoopProg 64 :=
.mark loopBody552_20

def loopBody552_22 : HolLoopProg 64 :=
.seq loopBody552_3 loopBody552_21

def loopBody552_23 : HolLoopProg 64 :=
.mark loopBody552_22

def loopBody552_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody552_25 : HolLoopProg 64 :=
.mark loopBody552_24

def loopBody552_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 8)

def loopBody552_27 : HolLoopProg 64 :=
.mark loopBody552_26

def loopBody552_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 0#64)

def loopBody552_29 : HolLoopProg 64 :=
.mark loopBody552_28

def loopBody552_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 1#64)

def loopBody552_31 : HolLoopProg 64 :=
.mark loopBody552_30

def loopBody552_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody552_33 : HolLoopProg 64 :=
.mark loopBody552_32

def loopBody552_34 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 11 (Flapjack.RegImm.reg 12) loopBody552_31 loopBody552_33 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))

def loopBody552_35 : HolLoopProg 64 :=
.mark loopBody552_34

def loopBody552_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 11)

def loopBody552_37 : HolLoopProg 64 :=
.mark loopBody552_36

def loopBody552_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 2300#64)

def loopBody552_39 : HolLoopProg 64 :=
.mark loopBody552_38

def loopBody552_40 : HolLoopProg 64 :=
.seq loopBody552_39 loopBody552_1

def loopBody552_41 : HolLoopProg 64 :=
.mark loopBody552_40

def loopBody552_42 : HolLoopProg 64 :=
.seq loopBody552_41 loopBody552_1

def loopBody552_43 : HolLoopProg 64 :=
.mark loopBody552_42

def loopBody552_44 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 13 (Flapjack.RegImm.imm 0#64) loopBody552_43 loopBody552_1 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody552_45 : HolLoopProg 64 :=
.mark loopBody552_44

def loopBody552_46 : HolLoopProg 64 :=
.seq loopBody552_45 loopBody552_1

def loopBody552_47 : HolLoopProg 64 :=
.mark loopBody552_46

def loopBody552_48 : HolLoopProg 64 :=
.seq loopBody552_37 loopBody552_47

def loopBody552_49 : HolLoopProg 64 :=
.mark loopBody552_48

def loopBody552_50 : HolLoopProg 64 :=
.seq loopBody552_35 loopBody552_49

def loopBody552_51 : HolLoopProg 64 :=
.mark loopBody552_50

def loopBody552_52 : HolLoopProg 64 :=
.seq loopBody552_29 loopBody552_51

def loopBody552_53 : HolLoopProg 64 :=
.mark loopBody552_52

def loopBody552_54 : HolLoopProg 64 :=
.seq loopBody552_27 loopBody552_53

def loopBody552_55 : HolLoopProg 64 :=
.mark loopBody552_54

def loopBody552_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 7)

def loopBody552_57 : HolLoopProg 64 :=
.mark loopBody552_56

def loopBody552_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 6)

def loopBody552_59 : HolLoopProg 64 :=
.mark loopBody552_58

def loopBody552_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 11

def loopBody552_61 : HolLoopProg 64 :=
.mark loopBody552_60

def loopBody552_62 : HolLoopProg 64 :=
.call (some
  ([10],
    Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))) (some 459) ([11, 12]) (some (11, loopBody552_61, loopBody552_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody552_63 : HolLoopProg 64 :=
.mark loopBody552_62

def loopBody552_64 : HolLoopProg 64 :=
.seq loopBody552_63 loopBody552_1

def loopBody552_65 : HolLoopProg 64 :=
.mark loopBody552_64

def loopBody552_66 : HolLoopProg 64 :=
.seq loopBody552_59 loopBody552_65

def loopBody552_67 : HolLoopProg 64 :=
.mark loopBody552_66

def loopBody552_68 : HolLoopProg 64 :=
.seq loopBody552_57 loopBody552_67

def loopBody552_69 : HolLoopProg 64 :=
.mark loopBody552_68

def loopBody552_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 5)

def loopBody552_71 : HolLoopProg 64 :=
.mark loopBody552_70

def loopBody552_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 10)

def loopBody552_73 : HolLoopProg 64 :=
.mark loopBody552_72

def loopBody552_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody552_75 : HolLoopProg 64 :=
.mark loopBody552_74

def loopBody552_76 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 12 (Flapjack.RegImm.reg 13) loopBody552_75 loopBody552_29 (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody552_77 : HolLoopProg 64 :=
.mark loopBody552_76

def loopBody552_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 12)

def loopBody552_79 : HolLoopProg 64 :=
.mark loopBody552_78

def loopBody552_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 4)

def loopBody552_81 : HolLoopProg 64 :=
.mark loopBody552_80

def loopBody552_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 7)

def loopBody552_83 : HolLoopProg 64 :=
.mark loopBody552_82

def loopBody552_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 12

def loopBody552_85 : HolLoopProg 64 :=
.mark loopBody552_84

def loopBody552_86 : HolLoopProg 64 :=
.call (some
  ([11],
    Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))) (some 459) ([12, 13]) (some (12, loopBody552_85, loopBody552_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))

def loopBody552_87 : HolLoopProg 64 :=
.mark loopBody552_86

def loopBody552_88 : HolLoopProg 64 :=
.seq loopBody552_87 loopBody552_1

def loopBody552_89 : HolLoopProg 64 :=
.mark loopBody552_88

def loopBody552_90 : HolLoopProg 64 :=
.seq loopBody552_83 loopBody552_89

def loopBody552_91 : HolLoopProg 64 :=
.mark loopBody552_90

def loopBody552_92 : HolLoopProg 64 :=
.seq loopBody552_81 loopBody552_91

def loopBody552_93 : HolLoopProg 64 :=
.mark loopBody552_92

def loopBody552_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 4)

def loopBody552_95 : HolLoopProg 64 :=
.mark loopBody552_94

def loopBody552_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 9)

def loopBody552_97 : HolLoopProg 64 :=
.mark loopBody552_96

def loopBody552_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 13

def loopBody552_99 : HolLoopProg 64 :=
.mark loopBody552_98

def loopBody552_100 : HolLoopProg 64 :=
.call (some
  ([12],
    Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))) (some 459) ([13, 14]) (some (13, loopBody552_99, loopBody552_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))

def loopBody552_101 : HolLoopProg 64 :=
.mark loopBody552_100

def loopBody552_102 : HolLoopProg 64 :=
.seq loopBody552_101 loopBody552_1

def loopBody552_103 : HolLoopProg 64 :=
.mark loopBody552_102

def loopBody552_104 : HolLoopProg 64 :=
.seq loopBody552_97 loopBody552_103

def loopBody552_105 : HolLoopProg 64 :=
.mark loopBody552_104

def loopBody552_106 : HolLoopProg 64 :=
.seq loopBody552_95 loopBody552_105

def loopBody552_107 : HolLoopProg 64 :=
.mark loopBody552_106

def loopBody552_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [13, 14]

def loopBody552_109 : HolLoopProg 64 :=
.mark loopBody552_108

def loopBody552_110 : HolLoopProg 64 :=
.seq loopBody552_109 loopBody552_1

def loopBody552_111 : HolLoopProg 64 :=
.mark loopBody552_110

def loopBody552_112 : HolLoopProg 64 :=
.seq loopBody552_79 loopBody552_111

def loopBody552_113 : HolLoopProg 64 :=
.mark loopBody552_112

def loopBody552_114 : HolLoopProg 64 :=
.seq loopBody552_37 loopBody552_113

def loopBody552_115 : HolLoopProg 64 :=
.mark loopBody552_114

def loopBody552_116 : HolLoopProg 64 :=
.seq loopBody552_107 loopBody552_115

def loopBody552_117 : HolLoopProg 64 :=
.mark loopBody552_116

def loopBody552_118 : HolLoopProg 64 :=
.seq loopBody552_1 loopBody552_117

def loopBody552_119 : HolLoopProg 64 :=
.mark loopBody552_118

def loopBody552_120 : HolLoopProg 64 :=
.seq loopBody552_1 loopBody552_119

def loopBody552_121 : HolLoopProg 64 :=
.mark loopBody552_120

def loopBody552_122 : HolLoopProg 64 :=
.seq loopBody552_93 loopBody552_121

def loopBody552_123 : HolLoopProg 64 :=
.mark loopBody552_122

def loopBody552_124 : HolLoopProg 64 :=
.seq loopBody552_1 loopBody552_123

def loopBody552_125 : HolLoopProg 64 :=
.mark loopBody552_124

def loopBody552_126 : HolLoopProg 64 :=
.seq loopBody552_1 loopBody552_125

def loopBody552_127 : HolLoopProg 64 :=
.mark loopBody552_126

def loopBody552_128 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.RegImm.imm 0#64) loopBody552_127 loopBody552_1 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody552_129 : HolLoopProg 64 :=
.mark loopBody552_128

def loopBody552_130 : HolLoopProg 64 :=
.seq loopBody552_129 loopBody552_1

def loopBody552_131 : HolLoopProg 64 :=
.mark loopBody552_130

def loopBody552_132 : HolLoopProg 64 :=
.seq loopBody552_79 loopBody552_131

def loopBody552_133 : HolLoopProg 64 :=
.mark loopBody552_132

def loopBody552_134 : HolLoopProg 64 :=
.seq loopBody552_77 loopBody552_133

def loopBody552_135 : HolLoopProg 64 :=
.mark loopBody552_134

def loopBody552_136 : HolLoopProg 64 :=
.seq loopBody552_73 loopBody552_135

def loopBody552_137 : HolLoopProg 64 :=
.mark loopBody552_136

def loopBody552_138 : HolLoopProg 64 :=
.seq loopBody552_71 loopBody552_137

def loopBody552_139 : HolLoopProg 64 :=
.mark loopBody552_138

def loopBody552_140 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
    [Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.var 6],
      Flapjack.HolLoopExp.var 7])

def loopBody552_141 : HolLoopProg 64 :=
.mark loopBody552_140

def loopBody552_142 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
    [Flapjack.HolLoopExp.var 11,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 11) (Flapjack.HolLoopExp.const 6#64)])

def loopBody552_143 : HolLoopProg 64 :=
.mark loopBody552_142

def loopBody552_144 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 12)

def loopBody552_145 : HolLoopProg 64 :=
.mark loopBody552_144

def loopBody552_146 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 13)

def loopBody552_147 : HolLoopProg 64 :=
.mark loopBody552_146

def loopBody552_148 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 1#64)

def loopBody552_149 : HolLoopProg 64 :=
.mark loopBody552_148

def loopBody552_150 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 0#64)

def loopBody552_151 : HolLoopProg 64 :=
.mark loopBody552_150

def loopBody552_152 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 15 (Flapjack.RegImm.reg 16) loopBody552_149 loopBody552_151 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody552_153 : HolLoopProg 64 :=
.mark loopBody552_152

def loopBody552_154 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 15)

def loopBody552_155 : HolLoopProg 64 :=
.mark loopBody552_154

def loopBody552_156 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 12)

def loopBody552_157 : HolLoopProg 64 :=
.mark loopBody552_156

def loopBody552_158 : HolLoopProg 64 :=
.seq loopBody552_157 loopBody552_1

def loopBody552_159 : HolLoopProg 64 :=
.mark loopBody552_158

def loopBody552_160 : HolLoopProg 64 :=
.seq loopBody552_159 loopBody552_1

def loopBody552_161 : HolLoopProg 64 :=
.mark loopBody552_160

def loopBody552_162 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 17 (Flapjack.RegImm.imm 0#64) loopBody552_161 loopBody552_1 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody552_163 : HolLoopProg 64 :=
.mark loopBody552_162

def loopBody552_164 : HolLoopProg 64 :=
.seq loopBody552_163 loopBody552_1

def loopBody552_165 : HolLoopProg 64 :=
.mark loopBody552_164

def loopBody552_166 : HolLoopProg 64 :=
.seq loopBody552_155 loopBody552_165

def loopBody552_167 : HolLoopProg 64 :=
.mark loopBody552_166

def loopBody552_168 : HolLoopProg 64 :=
.seq loopBody552_153 loopBody552_167

def loopBody552_169 : HolLoopProg 64 :=
.mark loopBody552_168

def loopBody552_170 : HolLoopProg 64 :=
.seq loopBody552_147 loopBody552_169

def loopBody552_171 : HolLoopProg 64 :=
.mark loopBody552_170

def loopBody552_172 : HolLoopProg 64 :=
.seq loopBody552_145 loopBody552_171

def loopBody552_173 : HolLoopProg 64 :=
.mark loopBody552_172

def loopBody552_174 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 13, Flapjack.HolLoopExp.var 7])

def loopBody552_175 : HolLoopProg 64 :=
.mark loopBody552_174

def loopBody552_176 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 13, Flapjack.HolLoopExp.var 9])

def loopBody552_177 : HolLoopProg 64 :=
.mark loopBody552_176

def loopBody552_178 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [14, 15]

def loopBody552_179 : HolLoopProg 64 :=
.mark loopBody552_178

def loopBody552_180 : HolLoopProg 64 :=
.seq loopBody552_179 loopBody552_1

def loopBody552_181 : HolLoopProg 64 :=
.mark loopBody552_180

def loopBody552_182 : HolLoopProg 64 :=
.seq loopBody552_177 loopBody552_181

def loopBody552_183 : HolLoopProg 64 :=
.mark loopBody552_182

def loopBody552_184 : HolLoopProg 64 :=
.seq loopBody552_175 loopBody552_183

def loopBody552_185 : HolLoopProg 64 :=
.mark loopBody552_184

def loopBody552_186 : HolLoopProg 64 :=
.seq loopBody552_173 loopBody552_185

def loopBody552_187 : HolLoopProg 64 :=
.mark loopBody552_186

def loopBody552_188 : HolLoopProg 64 :=
.seq loopBody552_95 loopBody552_187

def loopBody552_189 : HolLoopProg 64 :=
.mark loopBody552_188

def loopBody552_190 : HolLoopProg 64 :=
.seq loopBody552_1 loopBody552_189

def loopBody552_191 : HolLoopProg 64 :=
.mark loopBody552_190

def loopBody552_192 : HolLoopProg 64 :=
.seq loopBody552_143 loopBody552_191

def loopBody552_193 : HolLoopProg 64 :=
.mark loopBody552_192

def loopBody552_194 : HolLoopProg 64 :=
.seq loopBody552_1 loopBody552_193

def loopBody552_195 : HolLoopProg 64 :=
.mark loopBody552_194

def loopBody552_196 : HolLoopProg 64 :=
.seq loopBody552_141 loopBody552_195

def loopBody552_197 : HolLoopProg 64 :=
.mark loopBody552_196

def loopBody552_198 : HolLoopProg 64 :=
.seq loopBody552_1 loopBody552_197

def loopBody552_199 : HolLoopProg 64 :=
.mark loopBody552_198

def loopBody552_200 : HolLoopProg 64 :=
.seq loopBody552_139 loopBody552_199

def loopBody552_201 : HolLoopProg 64 :=
.mark loopBody552_200

def loopBody552_202 : HolLoopProg 64 :=
.seq loopBody552_69 loopBody552_201

def loopBody552_203 : HolLoopProg 64 :=
.mark loopBody552_202

def loopBody552_204 : HolLoopProg 64 :=
.seq loopBody552_1 loopBody552_203

def loopBody552_205 : HolLoopProg 64 :=
.mark loopBody552_204

def loopBody552_206 : HolLoopProg 64 :=
.seq loopBody552_1 loopBody552_205

def loopBody552_207 : HolLoopProg 64 :=
.mark loopBody552_206

def loopBody552_208 : HolLoopProg 64 :=
.seq loopBody552_55 loopBody552_207

def loopBody552_209 : HolLoopProg 64 :=
.mark loopBody552_208

def loopBody552_210 : HolLoopProg 64 :=
.seq loopBody552_25 loopBody552_209

def loopBody552_211 : HolLoopProg 64 :=
.mark loopBody552_210

def loopBody552_212 : HolLoopProg 64 :=
.seq loopBody552_1 loopBody552_211

def loopBody552_213 : HolLoopProg 64 :=
.mark loopBody552_212

def loopBody552_214 : HolLoopProg 64 :=
.seq loopBody552_23 loopBody552_213

def loopBody552_215 : HolLoopProg 64 :=
.mark loopBody552_214

def loopBody552_216 : HolLoopProg 64 :=
.seq loopBody552_1 loopBody552_215

def loopBody552_217 : HolLoopProg 64 :=
.mark loopBody552_216

def loopBody552_218 : HolLoopProg 64 :=
.seq loopBody552_1 loopBody552_217

def loopBody552_219 : HolLoopProg 64 :=
.mark loopBody552_218

def output552 : Nat × List Nat × HolLoopProg 64 :=
  (616, [0, 1, 2, 3, 4, 5, 6, 7], loopBody552_219)
end InitECandidate.Proofs.FrontendStages.Loop
