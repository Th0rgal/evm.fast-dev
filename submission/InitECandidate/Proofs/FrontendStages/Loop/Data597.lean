import InitECandidate.Proofs.FrontendStages.Loop.Translate581
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody597_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody597_1 : HolLoopProg 64 :=
.mark loopBody597_0

def loopBody597_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody597_3 : HolLoopProg 64 :=
.mark loopBody597_2

def loopBody597_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody597_5 : HolLoopProg 64 :=
.mark loopBody597_4

def loopBody597_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody597_7 : HolLoopProg 64 :=
.mark loopBody597_6

def loopBody597_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody597_9 : HolLoopProg 64 :=
.mark loopBody597_8

def loopBody597_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 4)

def loopBody597_11 : HolLoopProg 64 :=
.mark loopBody597_10

def loopBody597_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody597_13 : HolLoopProg 64 :=
.mark loopBody597_12

def loopBody597_14 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 137) ([10]) (some (10, loopBody597_13, loopBody597_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody597_15 : HolLoopProg 64 :=
.mark loopBody597_14

def loopBody597_16 : HolLoopProg 64 :=
.seq loopBody597_15 loopBody597_1

def loopBody597_17 : HolLoopProg 64 :=
.mark loopBody597_16

def loopBody597_18 : HolLoopProg 64 :=
.seq loopBody597_11 loopBody597_17

def loopBody597_19 : HolLoopProg 64 :=
.mark loopBody597_18

def loopBody597_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody597_21 : HolLoopProg 64 :=
.mark loopBody597_20

def loopBody597_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 9)

def loopBody597_23 : HolLoopProg 64 :=
.mark loopBody597_22

def loopBody597_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 1#64)

def loopBody597_25 : HolLoopProg 64 :=
.mark loopBody597_24

def loopBody597_26 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 11 (Flapjack.RegImm.reg 12) loopBody597_25 loopBody597_21 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody597_27 : HolLoopProg 64 :=
.mark loopBody597_26

def loopBody597_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 11)

def loopBody597_29 : HolLoopProg 64 :=
.mark loopBody597_28

def loopBody597_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 9, Flapjack.HolLoopExp.const 1#64])

def loopBody597_31 : HolLoopProg 64 :=
.mark loopBody597_30

def loopBody597_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 10)

def loopBody597_33 : HolLoopProg 64 :=
.mark loopBody597_32

def loopBody597_34 : HolLoopProg 64 :=
.seq loopBody597_33 loopBody597_1

def loopBody597_35 : HolLoopProg 64 :=
.mark loopBody597_34

def loopBody597_36 : HolLoopProg 64 :=
.seq loopBody597_35 loopBody597_1

def loopBody597_37 : HolLoopProg 64 :=
.mark loopBody597_36

def loopBody597_38 : HolLoopProg 64 :=
.seq loopBody597_31 loopBody597_37

def loopBody597_39 : HolLoopProg 64 :=
.mark loopBody597_38

def loopBody597_40 : HolLoopProg 64 :=
.seq loopBody597_1 loopBody597_39

def loopBody597_41 : HolLoopProg 64 :=
.mark loopBody597_40

def loopBody597_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 5)

def loopBody597_43 : HolLoopProg 64 :=
.mark loopBody597_42

def loopBody597_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 6)

def loopBody597_45 : HolLoopProg 64 :=
.mark loopBody597_44

def loopBody597_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 7)

def loopBody597_47 : HolLoopProg 64 :=
.mark loopBody597_46

def loopBody597_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 8)

def loopBody597_49 : HolLoopProg 64 :=
.mark loopBody597_48

def loopBody597_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 5)

def loopBody597_51 : HolLoopProg 64 :=
.mark loopBody597_50

def loopBody597_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 6)

def loopBody597_53 : HolLoopProg 64 :=
.mark loopBody597_52

def loopBody597_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 7)

def loopBody597_55 : HolLoopProg 64 :=
.mark loopBody597_54

def loopBody597_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 8)

def loopBody597_57 : HolLoopProg 64 :=
.mark loopBody597_56

def loopBody597_58 : HolLoopProg 64 :=
.call (some
  ([5, 6, 7, 8],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))) (some 654) ([10, 11, 12, 13, 14, 15, 16, 17]) (some (10, loopBody597_13, loopBody597_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody597_59 : HolLoopProg 64 :=
.mark loopBody597_58

def loopBody597_60 : HolLoopProg 64 :=
.seq loopBody597_59 loopBody597_1

def loopBody597_61 : HolLoopProg 64 :=
.mark loopBody597_60

def loopBody597_62 : HolLoopProg 64 :=
.seq loopBody597_57 loopBody597_61

def loopBody597_63 : HolLoopProg 64 :=
.mark loopBody597_62

def loopBody597_64 : HolLoopProg 64 :=
.seq loopBody597_55 loopBody597_63

def loopBody597_65 : HolLoopProg 64 :=
.mark loopBody597_64

def loopBody597_66 : HolLoopProg 64 :=
.seq loopBody597_53 loopBody597_65

def loopBody597_67 : HolLoopProg 64 :=
.mark loopBody597_66

def loopBody597_68 : HolLoopProg 64 :=
.seq loopBody597_51 loopBody597_67

def loopBody597_69 : HolLoopProg 64 :=
.mark loopBody597_68

def loopBody597_70 : HolLoopProg 64 :=
.seq loopBody597_49 loopBody597_69

def loopBody597_71 : HolLoopProg 64 :=
.mark loopBody597_70

def loopBody597_72 : HolLoopProg 64 :=
.seq loopBody597_47 loopBody597_71

def loopBody597_73 : HolLoopProg 64 :=
.mark loopBody597_72

def loopBody597_74 : HolLoopProg 64 :=
.seq loopBody597_45 loopBody597_73

def loopBody597_75 : HolLoopProg 64 :=
.mark loopBody597_74

def loopBody597_76 : HolLoopProg 64 :=
.seq loopBody597_43 loopBody597_75

def loopBody597_77 : HolLoopProg 64 :=
.mark loopBody597_76

def loopBody597_78 : HolLoopProg 64 :=
.seq loopBody597_41 loopBody597_77

def loopBody597_79 : HolLoopProg 64 :=
.mark loopBody597_78

def loopBody597_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.var 9),
      Flapjack.HolLoopExp.const 1#64])

def loopBody597_81 : HolLoopProg 64 :=
.mark loopBody597_80

def loopBody597_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody597_83 : HolLoopProg 64 :=
.mark loopBody597_82

def loopBody597_84 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 11 (Flapjack.RegImm.reg 12) loopBody597_25 loopBody597_21 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody597_85 : HolLoopProg 64 :=
.mark loopBody597_84

def loopBody597_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 0)

def loopBody597_87 : HolLoopProg 64 :=
.mark loopBody597_86

def loopBody597_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 1)

def loopBody597_89 : HolLoopProg 64 :=
.mark loopBody597_88

def loopBody597_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 2)

def loopBody597_91 : HolLoopProg 64 :=
.mark loopBody597_90

def loopBody597_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 3)

def loopBody597_93 : HolLoopProg 64 :=
.mark loopBody597_92

def loopBody597_94 : HolLoopProg 64 :=
.seq loopBody597_93 loopBody597_61

def loopBody597_95 : HolLoopProg 64 :=
.mark loopBody597_94

def loopBody597_96 : HolLoopProg 64 :=
.seq loopBody597_91 loopBody597_95

def loopBody597_97 : HolLoopProg 64 :=
.mark loopBody597_96

def loopBody597_98 : HolLoopProg 64 :=
.seq loopBody597_89 loopBody597_97

def loopBody597_99 : HolLoopProg 64 :=
.mark loopBody597_98

def loopBody597_100 : HolLoopProg 64 :=
.seq loopBody597_87 loopBody597_99

def loopBody597_101 : HolLoopProg 64 :=
.mark loopBody597_100

def loopBody597_102 : HolLoopProg 64 :=
.seq loopBody597_49 loopBody597_101

def loopBody597_103 : HolLoopProg 64 :=
.mark loopBody597_102

def loopBody597_104 : HolLoopProg 64 :=
.seq loopBody597_47 loopBody597_103

def loopBody597_105 : HolLoopProg 64 :=
.mark loopBody597_104

def loopBody597_106 : HolLoopProg 64 :=
.seq loopBody597_45 loopBody597_105

def loopBody597_107 : HolLoopProg 64 :=
.mark loopBody597_106

def loopBody597_108 : HolLoopProg 64 :=
.seq loopBody597_43 loopBody597_107

def loopBody597_109 : HolLoopProg 64 :=
.mark loopBody597_108

def loopBody597_110 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 13 (Flapjack.RegImm.imm 0#64) loopBody597_109 loopBody597_1 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody597_111 : HolLoopProg 64 :=
.mark loopBody597_110

def loopBody597_112 : HolLoopProg 64 :=
.seq loopBody597_111 loopBody597_1

def loopBody597_113 : HolLoopProg 64 :=
.mark loopBody597_112

def loopBody597_114 : HolLoopProg 64 :=
.seq loopBody597_29 loopBody597_113

def loopBody597_115 : HolLoopProg 64 :=
.mark loopBody597_114

def loopBody597_116 : HolLoopProg 64 :=
.seq loopBody597_85 loopBody597_115

def loopBody597_117 : HolLoopProg 64 :=
.mark loopBody597_116

def loopBody597_118 : HolLoopProg 64 :=
.seq loopBody597_83 loopBody597_117

def loopBody597_119 : HolLoopProg 64 :=
.mark loopBody597_118

def loopBody597_120 : HolLoopProg 64 :=
.seq loopBody597_81 loopBody597_119

def loopBody597_121 : HolLoopProg 64 :=
.mark loopBody597_120

def loopBody597_122 : HolLoopProg 64 :=
.seq loopBody597_79 loopBody597_121

def loopBody597_123 : HolLoopProg 64 :=
.mark loopBody597_122

def loopBody597_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody597_125 : HolLoopProg 64 :=
.mark loopBody597_124

def loopBody597_126 : HolLoopProg 64 :=
.seq loopBody597_123 loopBody597_125

def loopBody597_127 : HolLoopProg 64 :=
.mark loopBody597_126

def loopBody597_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody597_129 : HolLoopProg 64 :=
.mark loopBody597_128

def loopBody597_130 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 13 (Flapjack.RegImm.imm 0#64) loopBody597_127 loopBody597_129 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody597_131 : HolLoopProg 64 :=
.mark loopBody597_130

def loopBody597_132 : HolLoopProg 64 :=
.seq loopBody597_131 loopBody597_1

def loopBody597_133 : HolLoopProg 64 :=
.mark loopBody597_132

def loopBody597_134 : HolLoopProg 64 :=
.seq loopBody597_29 loopBody597_133

def loopBody597_135 : HolLoopProg 64 :=
.mark loopBody597_134

def loopBody597_136 : HolLoopProg 64 :=
.seq loopBody597_27 loopBody597_135

def loopBody597_137 : HolLoopProg 64 :=
.mark loopBody597_136

def loopBody597_138 : HolLoopProg 64 :=
.seq loopBody597_23 loopBody597_137

def loopBody597_139 : HolLoopProg 64 :=
.mark loopBody597_138

def loopBody597_140 : HolLoopProg 64 :=
.seq loopBody597_21 loopBody597_139

def loopBody597_141 : HolLoopProg 64 :=
.mark loopBody597_140

def loopBody597_142 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) loopBody597_141 (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody597_143 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [10, 11, 12, 13]

def loopBody597_144 : HolLoopProg 64 :=
.mark loopBody597_143

def loopBody597_145 : HolLoopProg 64 :=
.seq loopBody597_144 loopBody597_1

def loopBody597_146 : HolLoopProg 64 :=
.mark loopBody597_145

def loopBody597_147 : HolLoopProg 64 :=
.seq loopBody597_49 loopBody597_146

def loopBody597_148 : HolLoopProg 64 :=
.mark loopBody597_147

def loopBody597_149 : HolLoopProg 64 :=
.seq loopBody597_47 loopBody597_148

def loopBody597_150 : HolLoopProg 64 :=
.mark loopBody597_149

def loopBody597_151 : HolLoopProg 64 :=
.seq loopBody597_45 loopBody597_150

def loopBody597_152 : HolLoopProg 64 :=
.mark loopBody597_151

def loopBody597_153 : HolLoopProg 64 :=
.seq loopBody597_43 loopBody597_152

def loopBody597_154 : HolLoopProg 64 :=
.mark loopBody597_153

def loopBody597_155 : HolLoopProg 64 :=
.seq loopBody597_142 loopBody597_154

def loopBody597_156 : HolLoopProg 64 :=
.seq loopBody597_19 loopBody597_155

def loopBody597_157 : HolLoopProg 64 :=
.seq loopBody597_1 loopBody597_156

def loopBody597_158 : HolLoopProg 64 :=
.seq loopBody597_1 loopBody597_157

def loopBody597_159 : HolLoopProg 64 :=
.seq loopBody597_9 loopBody597_158

def loopBody597_160 : HolLoopProg 64 :=
.seq loopBody597_1 loopBody597_159

def loopBody597_161 : HolLoopProg 64 :=
.seq loopBody597_7 loopBody597_160

def loopBody597_162 : HolLoopProg 64 :=
.seq loopBody597_1 loopBody597_161

def loopBody597_163 : HolLoopProg 64 :=
.seq loopBody597_5 loopBody597_162

def loopBody597_164 : HolLoopProg 64 :=
.seq loopBody597_1 loopBody597_163

def loopBody597_165 : HolLoopProg 64 :=
.seq loopBody597_3 loopBody597_164

def loopBody597_166 : HolLoopProg 64 :=
.seq loopBody597_1 loopBody597_165

def output597 : Nat × List Nat × HolLoopProg 64 :=
  (661, [0, 1, 2, 3, 4], loopBody597_166)
end InitECandidate.Proofs.FrontendStages.Loop
