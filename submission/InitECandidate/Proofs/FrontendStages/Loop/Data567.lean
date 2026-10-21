import InitECandidate.Proofs.FrontendStages.Loop.Translate551
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody567_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody567_1 : HolLoopProg 64 :=
.mark loopBody567_0

def loopBody567_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 3#64])
    (Flapjack.HolLoopExp.const 2#64))

def loopBody567_3 : HolLoopProg 64 :=
.mark loopBody567_2

def loopBody567_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody567_5 : HolLoopProg 64 :=
.mark loopBody567_4

def loopBody567_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody567_7 : HolLoopProg 64 :=
.mark loopBody567_6

def loopBody567_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody567_9 : HolLoopProg 64 :=
.mark loopBody567_8

def loopBody567_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody567_11 : HolLoopProg 64 :=
.mark loopBody567_10

def loopBody567_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody567_13 : HolLoopProg 64 :=
.mark loopBody567_12

def loopBody567_14 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 6 (Flapjack.RegImm.reg 7) loopBody567_11 loopBody567_13 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody567_15 : HolLoopProg 64 :=
.mark loopBody567_14

def loopBody567_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody567_17 : HolLoopProg 64 :=
.mark loopBody567_16

def loopBody567_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 2,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 3#64)])

def loopBody567_19 : HolLoopProg 64 :=
.mark loopBody567_18

def loopBody567_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody567_21 : HolLoopProg 64 :=
.mark loopBody567_20

def loopBody567_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 5) 7

def loopBody567_23 : HolLoopProg 64 :=
.mark loopBody567_22

def loopBody567_24 : HolLoopProg 64 :=
.seq loopBody567_23 loopBody567_1

def loopBody567_25 : HolLoopProg 64 :=
.mark loopBody567_24

def loopBody567_26 : HolLoopProg 64 :=
.seq loopBody567_21 loopBody567_25

def loopBody567_27 : HolLoopProg 64 :=
.mark loopBody567_26

def loopBody567_28 : HolLoopProg 64 :=
.seq loopBody567_27 loopBody567_1

def loopBody567_29 : HolLoopProg 64 :=
.mark loopBody567_28

def loopBody567_30 : HolLoopProg 64 :=
.seq loopBody567_13 loopBody567_29

def loopBody567_31 : HolLoopProg 64 :=
.mark loopBody567_30

def loopBody567_32 : HolLoopProg 64 :=
.seq loopBody567_1 loopBody567_31

def loopBody567_33 : HolLoopProg 64 :=
.mark loopBody567_32

def loopBody567_34 : HolLoopProg 64 :=
.seq loopBody567_19 loopBody567_33

def loopBody567_35 : HolLoopProg 64 :=
.mark loopBody567_34

def loopBody567_36 : HolLoopProg 64 :=
.seq loopBody567_1 loopBody567_35

def loopBody567_37 : HolLoopProg 64 :=
.mark loopBody567_36

def loopBody567_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])

def loopBody567_39 : HolLoopProg 64 :=
.mark loopBody567_38

def loopBody567_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 5)

def loopBody567_41 : HolLoopProg 64 :=
.mark loopBody567_40

def loopBody567_42 : HolLoopProg 64 :=
.seq loopBody567_41 loopBody567_1

def loopBody567_43 : HolLoopProg 64 :=
.mark loopBody567_42

def loopBody567_44 : HolLoopProg 64 :=
.seq loopBody567_43 loopBody567_1

def loopBody567_45 : HolLoopProg 64 :=
.mark loopBody567_44

def loopBody567_46 : HolLoopProg 64 :=
.seq loopBody567_39 loopBody567_45

def loopBody567_47 : HolLoopProg 64 :=
.mark loopBody567_46

def loopBody567_48 : HolLoopProg 64 :=
.seq loopBody567_1 loopBody567_47

def loopBody567_49 : HolLoopProg 64 :=
.mark loopBody567_48

def loopBody567_50 : HolLoopProg 64 :=
.seq loopBody567_37 loopBody567_49

def loopBody567_51 : HolLoopProg 64 :=
.mark loopBody567_50

def loopBody567_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody567_53 : HolLoopProg 64 :=
.mark loopBody567_52

def loopBody567_54 : HolLoopProg 64 :=
.seq loopBody567_51 loopBody567_53

def loopBody567_55 : HolLoopProg 64 :=
.mark loopBody567_54

def loopBody567_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody567_57 : HolLoopProg 64 :=
.mark loopBody567_56

def loopBody567_58 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody567_55 loopBody567_57 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody567_59 : HolLoopProg 64 :=
.mark loopBody567_58

def loopBody567_60 : HolLoopProg 64 :=
.seq loopBody567_59 loopBody567_1

def loopBody567_61 : HolLoopProg 64 :=
.mark loopBody567_60

def loopBody567_62 : HolLoopProg 64 :=
.seq loopBody567_17 loopBody567_61

def loopBody567_63 : HolLoopProg 64 :=
.mark loopBody567_62

def loopBody567_64 : HolLoopProg 64 :=
.seq loopBody567_15 loopBody567_63

def loopBody567_65 : HolLoopProg 64 :=
.mark loopBody567_64

def loopBody567_66 : HolLoopProg 64 :=
.seq loopBody567_9 loopBody567_65

def loopBody567_67 : HolLoopProg 64 :=
.mark loopBody567_66

def loopBody567_68 : HolLoopProg 64 :=
.seq loopBody567_7 loopBody567_67

def loopBody567_69 : HolLoopProg 64 :=
.mark loopBody567_68

def loopBody567_70 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody567_69 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody567_71 : HolLoopProg 64 :=
.seq loopBody567_5 loopBody567_1

def loopBody567_72 : HolLoopProg 64 :=
.mark loopBody567_71

def loopBody567_73 : HolLoopProg 64 :=
.seq loopBody567_72 loopBody567_1

def loopBody567_74 : HolLoopProg 64 :=
.mark loopBody567_73

def loopBody567_75 : HolLoopProg 64 :=
.seq loopBody567_70 loopBody567_74

def loopBody567_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody567_77 : HolLoopProg 64 :=
.mark loopBody567_76

def loopBody567_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
    [Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 1#64],
      Flapjack.HolLoopExp.var 4])

def loopBody567_79 : HolLoopProg 64 :=
.mark loopBody567_78

def loopBody567_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 2,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
        (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.const 2#64))
        (Flapjack.HolLoopExp.const 3#64)])

def loopBody567_81 : HolLoopProg 64 :=
.mark loopBody567_80

def loopBody567_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 4])

def loopBody567_83 : HolLoopProg 64 :=
.mark loopBody567_82

def loopBody567_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 8 8

def loopBody567_85 : HolLoopProg 64 :=
.mark loopBody567_84

def loopBody567_86 : HolLoopProg 64 :=
.seq loopBody567_85 loopBody567_1

def loopBody567_87 : HolLoopProg 64 :=
.mark loopBody567_86

def loopBody567_88 : HolLoopProg 64 :=
.seq loopBody567_83 loopBody567_87

def loopBody567_89 : HolLoopProg 64 :=
.mark loopBody567_88

def loopBody567_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.var 6),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 8)
        (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
          (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 3#64])
          (Flapjack.HolLoopExp.const 3#64))])

def loopBody567_91 : HolLoopProg 64 :=
.mark loopBody567_90

def loopBody567_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 9)

def loopBody567_93 : HolLoopProg 64 :=
.mark loopBody567_92

def loopBody567_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 7) 10

def loopBody567_95 : HolLoopProg 64 :=
.mark loopBody567_94

def loopBody567_96 : HolLoopProg 64 :=
.seq loopBody567_95 loopBody567_1

def loopBody567_97 : HolLoopProg 64 :=
.mark loopBody567_96

def loopBody567_98 : HolLoopProg 64 :=
.seq loopBody567_93 loopBody567_97

def loopBody567_99 : HolLoopProg 64 :=
.mark loopBody567_98

def loopBody567_100 : HolLoopProg 64 :=
.seq loopBody567_99 loopBody567_1

def loopBody567_101 : HolLoopProg 64 :=
.mark loopBody567_100

def loopBody567_102 : HolLoopProg 64 :=
.seq loopBody567_91 loopBody567_101

def loopBody567_103 : HolLoopProg 64 :=
.mark loopBody567_102

def loopBody567_104 : HolLoopProg 64 :=
.seq loopBody567_89 loopBody567_103

def loopBody567_105 : HolLoopProg 64 :=
.mark loopBody567_104

def loopBody567_106 : HolLoopProg 64 :=
.seq loopBody567_21 loopBody567_105

def loopBody567_107 : HolLoopProg 64 :=
.mark loopBody567_106

def loopBody567_108 : HolLoopProg 64 :=
.seq loopBody567_1 loopBody567_107

def loopBody567_109 : HolLoopProg 64 :=
.mark loopBody567_108

def loopBody567_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])

def loopBody567_111 : HolLoopProg 64 :=
.mark loopBody567_110

def loopBody567_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 7)

def loopBody567_113 : HolLoopProg 64 :=
.mark loopBody567_112

def loopBody567_114 : HolLoopProg 64 :=
.seq loopBody567_113 loopBody567_1

def loopBody567_115 : HolLoopProg 64 :=
.mark loopBody567_114

def loopBody567_116 : HolLoopProg 64 :=
.seq loopBody567_115 loopBody567_1

def loopBody567_117 : HolLoopProg 64 :=
.mark loopBody567_116

def loopBody567_118 : HolLoopProg 64 :=
.seq loopBody567_111 loopBody567_117

def loopBody567_119 : HolLoopProg 64 :=
.mark loopBody567_118

def loopBody567_120 : HolLoopProg 64 :=
.seq loopBody567_1 loopBody567_119

def loopBody567_121 : HolLoopProg 64 :=
.mark loopBody567_120

def loopBody567_122 : HolLoopProg 64 :=
.seq loopBody567_109 loopBody567_121

def loopBody567_123 : HolLoopProg 64 :=
.mark loopBody567_122

def loopBody567_124 : HolLoopProg 64 :=
.seq loopBody567_81 loopBody567_123

def loopBody567_125 : HolLoopProg 64 :=
.mark loopBody567_124

def loopBody567_126 : HolLoopProg 64 :=
.seq loopBody567_1 loopBody567_125

def loopBody567_127 : HolLoopProg 64 :=
.mark loopBody567_126

def loopBody567_128 : HolLoopProg 64 :=
.seq loopBody567_79 loopBody567_127

def loopBody567_129 : HolLoopProg 64 :=
.mark loopBody567_128

def loopBody567_130 : HolLoopProg 64 :=
.seq loopBody567_1 loopBody567_129

def loopBody567_131 : HolLoopProg 64 :=
.mark loopBody567_130

def loopBody567_132 : HolLoopProg 64 :=
.seq loopBody567_131 loopBody567_53

def loopBody567_133 : HolLoopProg 64 :=
.mark loopBody567_132

def loopBody567_134 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody567_133 loopBody567_57 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody567_135 : HolLoopProg 64 :=
.mark loopBody567_134

def loopBody567_136 : HolLoopProg 64 :=
.seq loopBody567_135 loopBody567_1

def loopBody567_137 : HolLoopProg 64 :=
.mark loopBody567_136

def loopBody567_138 : HolLoopProg 64 :=
.seq loopBody567_17 loopBody567_137

def loopBody567_139 : HolLoopProg 64 :=
.mark loopBody567_138

def loopBody567_140 : HolLoopProg 64 :=
.seq loopBody567_15 loopBody567_139

def loopBody567_141 : HolLoopProg 64 :=
.mark loopBody567_140

def loopBody567_142 : HolLoopProg 64 :=
.seq loopBody567_77 loopBody567_141

def loopBody567_143 : HolLoopProg 64 :=
.mark loopBody567_142

def loopBody567_144 : HolLoopProg 64 :=
.seq loopBody567_7 loopBody567_143

def loopBody567_145 : HolLoopProg 64 :=
.mark loopBody567_144

def loopBody567_146 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody567_145 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody567_147 : HolLoopProg 64 :=
.seq loopBody567_75 loopBody567_146

def loopBody567_148 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody567_149 : HolLoopProg 64 :=
.mark loopBody567_148

def loopBody567_150 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody567_151 : HolLoopProg 64 :=
.mark loopBody567_150

def loopBody567_152 : HolLoopProg 64 :=
.seq loopBody567_151 loopBody567_1

def loopBody567_153 : HolLoopProg 64 :=
.mark loopBody567_152

def loopBody567_154 : HolLoopProg 64 :=
.seq loopBody567_149 loopBody567_153

def loopBody567_155 : HolLoopProg 64 :=
.mark loopBody567_154

def loopBody567_156 : HolLoopProg 64 :=
.seq loopBody567_147 loopBody567_155

def loopBody567_157 : HolLoopProg 64 :=
.seq loopBody567_5 loopBody567_156

def loopBody567_158 : HolLoopProg 64 :=
.seq loopBody567_1 loopBody567_157

def loopBody567_159 : HolLoopProg 64 :=
.seq loopBody567_3 loopBody567_158

def loopBody567_160 : HolLoopProg 64 :=
.seq loopBody567_1 loopBody567_159

def output567 : Nat × List Nat × HolLoopProg 64 :=
  (631, [0, 1, 2], loopBody567_160)
end InitECandidate.Proofs.FrontendStages.Loop
