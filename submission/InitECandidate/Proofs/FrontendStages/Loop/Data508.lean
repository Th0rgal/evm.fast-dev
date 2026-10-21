import InitECandidate.Proofs.FrontendStages.Loop.Translate492
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody508_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody508_1 : HolLoopProg 64 :=
.mark loopBody508_0

def loopBody508_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody508_3 : HolLoopProg 64 :=
.mark loopBody508_2

def loopBody508_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody508_3, loopBody508_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody508_5 : HolLoopProg 64 :=
.mark loopBody508_4

def loopBody508_6 : HolLoopProg 64 :=
.seq loopBody508_5 loopBody508_1

def loopBody508_7 : HolLoopProg 64 :=
.mark loopBody508_6

def loopBody508_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 20#64)

def loopBody508_9 : HolLoopProg 64 :=
.mark loopBody508_8

def loopBody508_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody508_11 : HolLoopProg 64 :=
.mark loopBody508_10

def loopBody508_12 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 466) ([6]) (some (6, loopBody508_11, loopBody508_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody508_13 : HolLoopProg 64 :=
.mark loopBody508_12

def loopBody508_14 : HolLoopProg 64 :=
.seq loopBody508_13 loopBody508_1

def loopBody508_15 : HolLoopProg 64 :=
.mark loopBody508_14

def loopBody508_16 : HolLoopProg 64 :=
.seq loopBody508_9 loopBody508_15

def loopBody508_17 : HolLoopProg 64 :=
.mark loopBody508_16

def loopBody508_18 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_17

def loopBody508_19 : HolLoopProg 64 :=
.mark loopBody508_18

def loopBody508_20 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_19

def loopBody508_21 : HolLoopProg 64 :=
.mark loopBody508_20

def loopBody508_22 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 568) ([]) (some (6, loopBody508_11, loopBody508_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody508_23 : HolLoopProg 64 :=
.mark loopBody508_22

def loopBody508_24 : HolLoopProg 64 :=
.seq loopBody508_23 loopBody508_1

def loopBody508_25 : HolLoopProg 64 :=
.mark loopBody508_24

def loopBody508_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 40#64]))

def loopBody508_27 : HolLoopProg 64 :=
.mark loopBody508_26

def loopBody508_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody508_29 : HolLoopProg 64 :=
.mark loopBody508_28

def loopBody508_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 2)

def loopBody508_31 : HolLoopProg 64 :=
.mark loopBody508_30

def loopBody508_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 3)

def loopBody508_33 : HolLoopProg 64 :=
.mark loopBody508_32

def loopBody508_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 4)

def loopBody508_35 : HolLoopProg 64 :=
.mark loopBody508_34

def loopBody508_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody508_37 : HolLoopProg 64 :=
.mark loopBody508_36

def loopBody508_38 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))) (some 458) ([8, 9, 10, 11]) (some (8, loopBody508_37, loopBody508_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody508_39 : HolLoopProg 64 :=
.mark loopBody508_38

def loopBody508_40 : HolLoopProg 64 :=
.seq loopBody508_39 loopBody508_1

def loopBody508_41 : HolLoopProg 64 :=
.mark loopBody508_40

def loopBody508_42 : HolLoopProg 64 :=
.seq loopBody508_35 loopBody508_41

def loopBody508_43 : HolLoopProg 64 :=
.mark loopBody508_42

def loopBody508_44 : HolLoopProg 64 :=
.seq loopBody508_33 loopBody508_43

def loopBody508_45 : HolLoopProg 64 :=
.mark loopBody508_44

def loopBody508_46 : HolLoopProg 64 :=
.seq loopBody508_31 loopBody508_45

def loopBody508_47 : HolLoopProg 64 :=
.mark loopBody508_46

def loopBody508_48 : HolLoopProg 64 :=
.seq loopBody508_29 loopBody508_47

def loopBody508_49 : HolLoopProg 64 :=
.mark loopBody508_48

def loopBody508_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody508_51 : HolLoopProg 64 :=
.mark loopBody508_50

def loopBody508_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 6)

def loopBody508_53 : HolLoopProg 64 :=
.mark loopBody508_52

def loopBody508_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 1#64)

def loopBody508_55 : HolLoopProg 64 :=
.mark loopBody508_54

def loopBody508_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody508_57 : HolLoopProg 64 :=
.mark loopBody508_56

def loopBody508_58 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notLower) 9 (Flapjack.RegImm.reg 10) loopBody508_55 loopBody508_57 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody508_59 : HolLoopProg 64 :=
.mark loopBody508_58

def loopBody508_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 256#64])

def loopBody508_61 : HolLoopProg 64 :=
.mark loopBody508_60

def loopBody508_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 6)

def loopBody508_63 : HolLoopProg 64 :=
.mark loopBody508_62

def loopBody508_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody508_65 : HolLoopProg 64 :=
.mark loopBody508_64

def loopBody508_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 0#64)

def loopBody508_67 : HolLoopProg 64 :=
.mark loopBody508_66

def loopBody508_68 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 12 (Flapjack.RegImm.reg 13) loopBody508_65 loopBody508_67 (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody508_69 : HolLoopProg 64 :=
.mark loopBody508_68

def loopBody508_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 7)

def loopBody508_71 : HolLoopProg 64 :=
.mark loopBody508_70

def loopBody508_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.const 18446744073709551615#64)

def loopBody508_73 : HolLoopProg 64 :=
.mark loopBody508_72

def loopBody508_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 1#64)

def loopBody508_75 : HolLoopProg 64 :=
.mark loopBody508_74

def loopBody508_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 0#64)

def loopBody508_77 : HolLoopProg 64 :=
.mark loopBody508_76

def loopBody508_78 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 15 (Flapjack.RegImm.reg 16) loopBody508_75 loopBody508_77 (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody508_79 : HolLoopProg 64 :=
.mark loopBody508_78

def loopBody508_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.const 0#64)

def loopBody508_81 : HolLoopProg 64 :=
.mark loopBody508_80

def loopBody508_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.var 9, Flapjack.HolLoopExp.var 12, Flapjack.HolLoopExp.var 15])

def loopBody508_83 : HolLoopProg 64 :=
.mark loopBody508_82

def loopBody508_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.const 1#64)

def loopBody508_85 : HolLoopProg 64 :=
.mark loopBody508_84

def loopBody508_86 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.RegImm.reg 19) loopBody508_85 loopBody508_81 (Flapjack.Spt.bn
  (Flapjack.Spt.bn
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody508_87 : HolLoopProg 64 :=
.mark loopBody508_86

def loopBody508_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.var 18)

def loopBody508_89 : HolLoopProg 64 :=
.mark loopBody508_88

def loopBody508_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody508_91 : HolLoopProg 64 :=
.mark loopBody508_90

def loopBody508_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody508_93 : HolLoopProg 64 :=
.mark loopBody508_92

def loopBody508_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody508_95 : HolLoopProg 64 :=
.mark loopBody508_94

def loopBody508_96 : HolLoopProg 64 :=
.call (some ([8], Flapjack.Spt.ln)) (some 472) ([9, 10, 11, 12]) (some (9, loopBody508_95, loopBody508_1, (Flapjack.Spt.ln)))

def loopBody508_97 : HolLoopProg 64 :=
.mark loopBody508_96

def loopBody508_98 : HolLoopProg 64 :=
.seq loopBody508_97 loopBody508_1

def loopBody508_99 : HolLoopProg 64 :=
.mark loopBody508_98

def loopBody508_100 : HolLoopProg 64 :=
.seq loopBody508_67 loopBody508_99

def loopBody508_101 : HolLoopProg 64 :=
.mark loopBody508_100

def loopBody508_102 : HolLoopProg 64 :=
.seq loopBody508_93 loopBody508_101

def loopBody508_103 : HolLoopProg 64 :=
.mark loopBody508_102

def loopBody508_104 : HolLoopProg 64 :=
.seq loopBody508_91 loopBody508_103

def loopBody508_105 : HolLoopProg 64 :=
.mark loopBody508_104

def loopBody508_106 : HolLoopProg 64 :=
.seq loopBody508_57 loopBody508_105

def loopBody508_107 : HolLoopProg 64 :=
.mark loopBody508_106

def loopBody508_108 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_107

def loopBody508_109 : HolLoopProg 64 :=
.mark loopBody508_108

def loopBody508_110 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_109

def loopBody508_111 : HolLoopProg 64 :=
.mark loopBody508_110

def loopBody508_112 : HolLoopProg 64 :=
.call (some ([8], Flapjack.Spt.ln)) (some 486) ([9]) (some (9, loopBody508_95, loopBody508_1, (Flapjack.Spt.ln)))

def loopBody508_113 : HolLoopProg 64 :=
.mark loopBody508_112

def loopBody508_114 : HolLoopProg 64 :=
.seq loopBody508_113 loopBody508_1

def loopBody508_115 : HolLoopProg 64 :=
.mark loopBody508_114

def loopBody508_116 : HolLoopProg 64 :=
.seq loopBody508_55 loopBody508_115

def loopBody508_117 : HolLoopProg 64 :=
.mark loopBody508_116

def loopBody508_118 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_117

def loopBody508_119 : HolLoopProg 64 :=
.mark loopBody508_118

def loopBody508_120 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_119

def loopBody508_121 : HolLoopProg 64 :=
.mark loopBody508_120

def loopBody508_122 : HolLoopProg 64 :=
.seq loopBody508_111 loopBody508_121

def loopBody508_123 : HolLoopProg 64 :=
.mark loopBody508_122

def loopBody508_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody508_125 : HolLoopProg 64 :=
.mark loopBody508_124

def loopBody508_126 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [8]

def loopBody508_127 : HolLoopProg 64 :=
.mark loopBody508_126

def loopBody508_128 : HolLoopProg 64 :=
.seq loopBody508_127 loopBody508_1

def loopBody508_129 : HolLoopProg 64 :=
.mark loopBody508_128

def loopBody508_130 : HolLoopProg 64 :=
.seq loopBody508_125 loopBody508_129

def loopBody508_131 : HolLoopProg 64 :=
.mark loopBody508_130

def loopBody508_132 : HolLoopProg 64 :=
.seq loopBody508_123 loopBody508_131

def loopBody508_133 : HolLoopProg 64 :=
.mark loopBody508_132

def loopBody508_134 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.RegImm.imm 0#64) loopBody508_133 loopBody508_1 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody508_135 : HolLoopProg 64 :=
.mark loopBody508_134

def loopBody508_136 : HolLoopProg 64 :=
.seq loopBody508_135 loopBody508_1

def loopBody508_137 : HolLoopProg 64 :=
.mark loopBody508_136

def loopBody508_138 : HolLoopProg 64 :=
.seq loopBody508_89 loopBody508_137

def loopBody508_139 : HolLoopProg 64 :=
.mark loopBody508_138

def loopBody508_140 : HolLoopProg 64 :=
.seq loopBody508_87 loopBody508_139

def loopBody508_141 : HolLoopProg 64 :=
.mark loopBody508_140

def loopBody508_142 : HolLoopProg 64 :=
.seq loopBody508_83 loopBody508_141

def loopBody508_143 : HolLoopProg 64 :=
.mark loopBody508_142

def loopBody508_144 : HolLoopProg 64 :=
.seq loopBody508_81 loopBody508_143

def loopBody508_145 : HolLoopProg 64 :=
.mark loopBody508_144

def loopBody508_146 : HolLoopProg 64 :=
.seq loopBody508_79 loopBody508_145

def loopBody508_147 : HolLoopProg 64 :=
.mark loopBody508_146

def loopBody508_148 : HolLoopProg 64 :=
.seq loopBody508_73 loopBody508_147

def loopBody508_149 : HolLoopProg 64 :=
.mark loopBody508_148

def loopBody508_150 : HolLoopProg 64 :=
.seq loopBody508_71 loopBody508_149

def loopBody508_151 : HolLoopProg 64 :=
.mark loopBody508_150

def loopBody508_152 : HolLoopProg 64 :=
.seq loopBody508_69 loopBody508_151

def loopBody508_153 : HolLoopProg 64 :=
.mark loopBody508_152

def loopBody508_154 : HolLoopProg 64 :=
.seq loopBody508_63 loopBody508_153

def loopBody508_155 : HolLoopProg 64 :=
.mark loopBody508_154

def loopBody508_156 : HolLoopProg 64 :=
.seq loopBody508_61 loopBody508_155

def loopBody508_157 : HolLoopProg 64 :=
.mark loopBody508_156

def loopBody508_158 : HolLoopProg 64 :=
.seq loopBody508_59 loopBody508_157

def loopBody508_159 : HolLoopProg 64 :=
.mark loopBody508_158

def loopBody508_160 : HolLoopProg 64 :=
.seq loopBody508_53 loopBody508_159

def loopBody508_161 : HolLoopProg 64 :=
.mark loopBody508_160

def loopBody508_162 : HolLoopProg 64 :=
.seq loopBody508_51 loopBody508_161

def loopBody508_163 : HolLoopProg 64 :=
.mark loopBody508_162

def loopBody508_164 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.var 7])

def loopBody508_165 : HolLoopProg 64 :=
.mark loopBody508_164

def loopBody508_166 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 24#64]))

def loopBody508_167 : HolLoopProg 64 :=
.mark loopBody508_166

def loopBody508_168 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody508_169 : HolLoopProg 64 :=
.mark loopBody508_168

def loopBody508_170 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 8)

def loopBody508_171 : HolLoopProg 64 :=
.mark loopBody508_170

def loopBody508_172 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 1#64)

def loopBody508_173 : HolLoopProg 64 :=
.mark loopBody508_172

def loopBody508_174 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 11 (Flapjack.RegImm.reg 12) loopBody508_173 loopBody508_93 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody508_175 : HolLoopProg 64 :=
.mark loopBody508_174

def loopBody508_176 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 11)

def loopBody508_177 : HolLoopProg 64 :=
.mark loopBody508_176

def loopBody508_178 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 50#64)

def loopBody508_179 : HolLoopProg 64 :=
.mark loopBody508_178

def loopBody508_180 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 10)

def loopBody508_181 : HolLoopProg 64 :=
.mark loopBody508_180

def loopBody508_182 : HolLoopProg 64 :=
.seq loopBody508_181 loopBody508_1

def loopBody508_183 : HolLoopProg 64 :=
.mark loopBody508_182

def loopBody508_184 : HolLoopProg 64 :=
.seq loopBody508_183 loopBody508_1

def loopBody508_185 : HolLoopProg 64 :=
.mark loopBody508_184

def loopBody508_186 : HolLoopProg 64 :=
.seq loopBody508_179 loopBody508_185

def loopBody508_187 : HolLoopProg 64 :=
.mark loopBody508_186

def loopBody508_188 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_187

def loopBody508_189 : HolLoopProg 64 :=
.mark loopBody508_188

def loopBody508_190 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 4#64)

def loopBody508_191 : HolLoopProg 64 :=
.mark loopBody508_190

def loopBody508_192 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody508_193 : HolLoopProg 64 :=
.mark loopBody508_192

def loopBody508_194 : HolLoopProg 64 :=
.seq loopBody508_191 loopBody508_193

def loopBody508_195 : HolLoopProg 64 :=
.mark loopBody508_194

def loopBody508_196 : HolLoopProg 64 :=
.seq loopBody508_189 loopBody508_195

def loopBody508_197 : HolLoopProg 64 :=
.mark loopBody508_196

def loopBody508_198 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 13 (Flapjack.RegImm.imm 0#64) loopBody508_197 loopBody508_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))

def loopBody508_199 : HolLoopProg 64 :=
.mark loopBody508_198

def loopBody508_200 : HolLoopProg 64 :=
.seq loopBody508_199 loopBody508_1

def loopBody508_201 : HolLoopProg 64 :=
.mark loopBody508_200

def loopBody508_202 : HolLoopProg 64 :=
.seq loopBody508_177 loopBody508_201

def loopBody508_203 : HolLoopProg 64 :=
.mark loopBody508_202

def loopBody508_204 : HolLoopProg 64 :=
.seq loopBody508_175 loopBody508_203

def loopBody508_205 : HolLoopProg 64 :=
.mark loopBody508_204

def loopBody508_206 : HolLoopProg 64 :=
.seq loopBody508_171 loopBody508_205

def loopBody508_207 : HolLoopProg 64 :=
.mark loopBody508_206

def loopBody508_208 : HolLoopProg 64 :=
.seq loopBody508_169 loopBody508_207

def loopBody508_209 : HolLoopProg 64 :=
.mark loopBody508_208

def loopBody508_210 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 16#64]),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 9, Flapjack.HolLoopExp.var 8])
        (Flapjack.HolLoopExp.const 5#64)])

def loopBody508_211 : HolLoopProg 64 :=
.mark loopBody508_210

def loopBody508_212 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 32#64)

def loopBody508_213 : HolLoopProg 64 :=
.mark loopBody508_212

def loopBody508_214 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 14

def loopBody508_215 : HolLoopProg 64 :=
.mark loopBody508_214

def loopBody508_216 : HolLoopProg 64 :=
.call (some
  ([10, 11, 12, 13],
    Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)) (some 146) ([14, 15]) (some (14, loopBody508_215, loopBody508_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))

def loopBody508_217 : HolLoopProg 64 :=
.mark loopBody508_216

def loopBody508_218 : HolLoopProg 64 :=
.seq loopBody508_217 loopBody508_1

def loopBody508_219 : HolLoopProg 64 :=
.mark loopBody508_218

def loopBody508_220 : HolLoopProg 64 :=
.seq loopBody508_213 loopBody508_219

def loopBody508_221 : HolLoopProg 64 :=
.mark loopBody508_220

def loopBody508_222 : HolLoopProg 64 :=
.seq loopBody508_211 loopBody508_221

def loopBody508_223 : HolLoopProg 64 :=
.mark loopBody508_222

def loopBody508_224 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 8)

def loopBody508_225 : HolLoopProg 64 :=
.mark loopBody508_224

def loopBody508_226 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 15

def loopBody508_227 : HolLoopProg 64 :=
.mark loopBody508_226

def loopBody508_228 : HolLoopProg 64 :=
.call (some
  ([14],
    Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))) (some 430) ([15]) (some (15, loopBody508_227, loopBody508_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))

def loopBody508_229 : HolLoopProg 64 :=
.mark loopBody508_228

def loopBody508_230 : HolLoopProg 64 :=
.seq loopBody508_229 loopBody508_1

def loopBody508_231 : HolLoopProg 64 :=
.mark loopBody508_230

def loopBody508_232 : HolLoopProg 64 :=
.seq loopBody508_225 loopBody508_231

def loopBody508_233 : HolLoopProg 64 :=
.mark loopBody508_232

def loopBody508_234 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_233

def loopBody508_235 : HolLoopProg 64 :=
.mark loopBody508_234

def loopBody508_236 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_235

def loopBody508_237 : HolLoopProg 64 :=
.mark loopBody508_236

def loopBody508_238 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 10)

def loopBody508_239 : HolLoopProg 64 :=
.mark loopBody508_238

def loopBody508_240 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 11)

def loopBody508_241 : HolLoopProg 64 :=
.mark loopBody508_240

def loopBody508_242 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 12)

def loopBody508_243 : HolLoopProg 64 :=
.mark loopBody508_242

def loopBody508_244 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 13)

def loopBody508_245 : HolLoopProg 64 :=
.mark loopBody508_244

def loopBody508_246 : HolLoopProg 64 :=
.call (some ([14], Flapjack.Spt.ln)) (some 472) ([15, 16, 17, 18]) (some (15, loopBody508_227, loopBody508_1, (Flapjack.Spt.ln)))

def loopBody508_247 : HolLoopProg 64 :=
.mark loopBody508_246

def loopBody508_248 : HolLoopProg 64 :=
.seq loopBody508_247 loopBody508_1

def loopBody508_249 : HolLoopProg 64 :=
.mark loopBody508_248

def loopBody508_250 : HolLoopProg 64 :=
.seq loopBody508_245 loopBody508_249

def loopBody508_251 : HolLoopProg 64 :=
.mark loopBody508_250

def loopBody508_252 : HolLoopProg 64 :=
.seq loopBody508_243 loopBody508_251

def loopBody508_253 : HolLoopProg 64 :=
.mark loopBody508_252

def loopBody508_254 : HolLoopProg 64 :=
.seq loopBody508_241 loopBody508_253

def loopBody508_255 : HolLoopProg 64 :=
.mark loopBody508_254

def loopBody508_256 : HolLoopProg 64 :=
.seq loopBody508_239 loopBody508_255

def loopBody508_257 : HolLoopProg 64 :=
.mark loopBody508_256

def loopBody508_258 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_257

def loopBody508_259 : HolLoopProg 64 :=
.mark loopBody508_258

def loopBody508_260 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_259

def loopBody508_261 : HolLoopProg 64 :=
.mark loopBody508_260

def loopBody508_262 : HolLoopProg 64 :=
.seq loopBody508_237 loopBody508_261

def loopBody508_263 : HolLoopProg 64 :=
.mark loopBody508_262

def loopBody508_264 : HolLoopProg 64 :=
.call (some ([14], Flapjack.Spt.ln)) (some 486) ([15]) (some (15, loopBody508_227, loopBody508_1, (Flapjack.Spt.ln)))

def loopBody508_265 : HolLoopProg 64 :=
.mark loopBody508_264

def loopBody508_266 : HolLoopProg 64 :=
.seq loopBody508_265 loopBody508_1

def loopBody508_267 : HolLoopProg 64 :=
.mark loopBody508_266

def loopBody508_268 : HolLoopProg 64 :=
.seq loopBody508_75 loopBody508_267

def loopBody508_269 : HolLoopProg 64 :=
.mark loopBody508_268

def loopBody508_270 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_269

def loopBody508_271 : HolLoopProg 64 :=
.mark loopBody508_270

def loopBody508_272 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_271

def loopBody508_273 : HolLoopProg 64 :=
.mark loopBody508_272

def loopBody508_274 : HolLoopProg 64 :=
.seq loopBody508_263 loopBody508_273

def loopBody508_275 : HolLoopProg 64 :=
.mark loopBody508_274

def loopBody508_276 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 0#64)

def loopBody508_277 : HolLoopProg 64 :=
.mark loopBody508_276

def loopBody508_278 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [14]

def loopBody508_279 : HolLoopProg 64 :=
.mark loopBody508_278

def loopBody508_280 : HolLoopProg 64 :=
.seq loopBody508_279 loopBody508_1

def loopBody508_281 : HolLoopProg 64 :=
.mark loopBody508_280

def loopBody508_282 : HolLoopProg 64 :=
.seq loopBody508_277 loopBody508_281

def loopBody508_283 : HolLoopProg 64 :=
.mark loopBody508_282

def loopBody508_284 : HolLoopProg 64 :=
.seq loopBody508_275 loopBody508_283

def loopBody508_285 : HolLoopProg 64 :=
.mark loopBody508_284

def loopBody508_286 : HolLoopProg 64 :=
.seq loopBody508_223 loopBody508_285

def loopBody508_287 : HolLoopProg 64 :=
.mark loopBody508_286

def loopBody508_288 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_287

def loopBody508_289 : HolLoopProg 64 :=
.mark loopBody508_288

def loopBody508_290 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_289

def loopBody508_291 : HolLoopProg 64 :=
.mark loopBody508_290

def loopBody508_292 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_291

def loopBody508_293 : HolLoopProg 64 :=
.mark loopBody508_292

def loopBody508_294 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_293

def loopBody508_295 : HolLoopProg 64 :=
.mark loopBody508_294

def loopBody508_296 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_295

def loopBody508_297 : HolLoopProg 64 :=
.mark loopBody508_296

def loopBody508_298 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_297

def loopBody508_299 : HolLoopProg 64 :=
.mark loopBody508_298

def loopBody508_300 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_299

def loopBody508_301 : HolLoopProg 64 :=
.mark loopBody508_300

def loopBody508_302 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_301

def loopBody508_303 : HolLoopProg 64 :=
.mark loopBody508_302

def loopBody508_304 : HolLoopProg 64 :=
.seq loopBody508_209 loopBody508_303

def loopBody508_305 : HolLoopProg 64 :=
.mark loopBody508_304

def loopBody508_306 : HolLoopProg 64 :=
.seq loopBody508_167 loopBody508_305

def loopBody508_307 : HolLoopProg 64 :=
.mark loopBody508_306

def loopBody508_308 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_307

def loopBody508_309 : HolLoopProg 64 :=
.mark loopBody508_308

def loopBody508_310 : HolLoopProg 64 :=
.seq loopBody508_165 loopBody508_309

def loopBody508_311 : HolLoopProg 64 :=
.mark loopBody508_310

def loopBody508_312 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_311

def loopBody508_313 : HolLoopProg 64 :=
.mark loopBody508_312

def loopBody508_314 : HolLoopProg 64 :=
.seq loopBody508_163 loopBody508_313

def loopBody508_315 : HolLoopProg 64 :=
.mark loopBody508_314

def loopBody508_316 : HolLoopProg 64 :=
.seq loopBody508_49 loopBody508_315

def loopBody508_317 : HolLoopProg 64 :=
.mark loopBody508_316

def loopBody508_318 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_317

def loopBody508_319 : HolLoopProg 64 :=
.mark loopBody508_318

def loopBody508_320 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_319

def loopBody508_321 : HolLoopProg 64 :=
.mark loopBody508_320

def loopBody508_322 : HolLoopProg 64 :=
.seq loopBody508_27 loopBody508_321

def loopBody508_323 : HolLoopProg 64 :=
.mark loopBody508_322

def loopBody508_324 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_323

def loopBody508_325 : HolLoopProg 64 :=
.mark loopBody508_324

def loopBody508_326 : HolLoopProg 64 :=
.seq loopBody508_25 loopBody508_325

def loopBody508_327 : HolLoopProg 64 :=
.mark loopBody508_326

def loopBody508_328 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_327

def loopBody508_329 : HolLoopProg 64 :=
.mark loopBody508_328

def loopBody508_330 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_329

def loopBody508_331 : HolLoopProg 64 :=
.mark loopBody508_330

def loopBody508_332 : HolLoopProg 64 :=
.seq loopBody508_21 loopBody508_331

def loopBody508_333 : HolLoopProg 64 :=
.mark loopBody508_332

def loopBody508_334 : HolLoopProg 64 :=
.seq loopBody508_7 loopBody508_333

def loopBody508_335 : HolLoopProg 64 :=
.mark loopBody508_334

def loopBody508_336 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_335

def loopBody508_337 : HolLoopProg 64 :=
.mark loopBody508_336

def loopBody508_338 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_337

def loopBody508_339 : HolLoopProg 64 :=
.mark loopBody508_338

def loopBody508_340 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_339

def loopBody508_341 : HolLoopProg 64 :=
.mark loopBody508_340

def loopBody508_342 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_341

def loopBody508_343 : HolLoopProg 64 :=
.mark loopBody508_342

def loopBody508_344 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_343

def loopBody508_345 : HolLoopProg 64 :=
.mark loopBody508_344

def loopBody508_346 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_345

def loopBody508_347 : HolLoopProg 64 :=
.mark loopBody508_346

def loopBody508_348 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_347

def loopBody508_349 : HolLoopProg 64 :=
.mark loopBody508_348

def loopBody508_350 : HolLoopProg 64 :=
.seq loopBody508_1 loopBody508_349

def loopBody508_351 : HolLoopProg 64 :=
.mark loopBody508_350

def output508 : Nat × List Nat × HolLoopProg 64 :=
  (572, [], loopBody508_351)
end InitECandidate.Proofs.FrontendStages.Loop
