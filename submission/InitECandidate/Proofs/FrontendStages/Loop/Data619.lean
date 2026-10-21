import InitECandidate.Proofs.FrontendStages.Loop.Translate603
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody619_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody619_1 : HolLoopProg 64 :=
.mark loopBody619_0

def loopBody619_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody619_3 : HolLoopProg 64 :=
.mark loopBody619_2

def loopBody619_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1152#64)

def loopBody619_5 : HolLoopProg 64 :=
.mark loopBody619_4

def loopBody619_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody619_7 : HolLoopProg 64 :=
.mark loopBody619_6

def loopBody619_8 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 78) ([3, 4]) (some (3, loopBody619_7, loopBody619_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody619_9 : HolLoopProg 64 :=
.mark loopBody619_8

def loopBody619_10 : HolLoopProg 64 :=
.seq loopBody619_9 loopBody619_1

def loopBody619_11 : HolLoopProg 64 :=
.mark loopBody619_10

def loopBody619_12 : HolLoopProg 64 :=
.seq loopBody619_5 loopBody619_11

def loopBody619_13 : HolLoopProg 64 :=
.mark loopBody619_12

def loopBody619_14 : HolLoopProg 64 :=
.seq loopBody619_3 loopBody619_13

def loopBody619_15 : HolLoopProg 64 :=
.mark loopBody619_14

def loopBody619_16 : HolLoopProg 64 :=
.seq loopBody619_1 loopBody619_15

def loopBody619_17 : HolLoopProg 64 :=
.mark loopBody619_16

def loopBody619_18 : HolLoopProg 64 :=
.seq loopBody619_1 loopBody619_17

def loopBody619_19 : HolLoopProg 64 :=
.mark loopBody619_18

def loopBody619_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody619_21 : HolLoopProg 64 :=
.mark loopBody619_20

def loopBody619_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.var 1))

def loopBody619_23 : HolLoopProg 64 :=
.mark loopBody619_22

def loopBody619_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 8#64]))

def loopBody619_25 : HolLoopProg 64 :=
.mark loopBody619_24

def loopBody619_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 16#64]))

def loopBody619_27 : HolLoopProg 64 :=
.mark loopBody619_26

def loopBody619_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 24#64]))

def loopBody619_29 : HolLoopProg 64 :=
.mark loopBody619_28

def loopBody619_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody619_31 : HolLoopProg 64 :=
.mark loopBody619_30

def loopBody619_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 2) 7

def loopBody619_33 : HolLoopProg 64 :=
.mark loopBody619_32

def loopBody619_34 : HolLoopProg 64 :=
.seq loopBody619_33 loopBody619_1

def loopBody619_35 : HolLoopProg 64 :=
.mark loopBody619_34

def loopBody619_36 : HolLoopProg 64 :=
.seq loopBody619_31 loopBody619_35

def loopBody619_37 : HolLoopProg 64 :=
.mark loopBody619_36

def loopBody619_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody619_39 : HolLoopProg 64 :=
.mark loopBody619_38

def loopBody619_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 8#64]) 7

def loopBody619_41 : HolLoopProg 64 :=
.mark loopBody619_40

def loopBody619_42 : HolLoopProg 64 :=
.seq loopBody619_41 loopBody619_1

def loopBody619_43 : HolLoopProg 64 :=
.mark loopBody619_42

def loopBody619_44 : HolLoopProg 64 :=
.seq loopBody619_39 loopBody619_43

def loopBody619_45 : HolLoopProg 64 :=
.mark loopBody619_44

def loopBody619_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody619_47 : HolLoopProg 64 :=
.mark loopBody619_46

def loopBody619_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 16#64]) 7

def loopBody619_49 : HolLoopProg 64 :=
.mark loopBody619_48

def loopBody619_50 : HolLoopProg 64 :=
.seq loopBody619_49 loopBody619_1

def loopBody619_51 : HolLoopProg 64 :=
.mark loopBody619_50

def loopBody619_52 : HolLoopProg 64 :=
.seq loopBody619_47 loopBody619_51

def loopBody619_53 : HolLoopProg 64 :=
.mark loopBody619_52

def loopBody619_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody619_55 : HolLoopProg 64 :=
.mark loopBody619_54

def loopBody619_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 24#64]) 7

def loopBody619_57 : HolLoopProg 64 :=
.mark loopBody619_56

def loopBody619_58 : HolLoopProg 64 :=
.seq loopBody619_57 loopBody619_1

def loopBody619_59 : HolLoopProg 64 :=
.mark loopBody619_58

def loopBody619_60 : HolLoopProg 64 :=
.seq loopBody619_55 loopBody619_59

def loopBody619_61 : HolLoopProg 64 :=
.mark loopBody619_60

def loopBody619_62 : HolLoopProg 64 :=
.seq loopBody619_61 loopBody619_1

def loopBody619_63 : HolLoopProg 64 :=
.mark loopBody619_62

def loopBody619_64 : HolLoopProg 64 :=
.seq loopBody619_53 loopBody619_63

def loopBody619_65 : HolLoopProg 64 :=
.mark loopBody619_64

def loopBody619_66 : HolLoopProg 64 :=
.seq loopBody619_45 loopBody619_65

def loopBody619_67 : HolLoopProg 64 :=
.mark loopBody619_66

def loopBody619_68 : HolLoopProg 64 :=
.seq loopBody619_37 loopBody619_67

def loopBody619_69 : HolLoopProg 64 :=
.mark loopBody619_68

def loopBody619_70 : HolLoopProg 64 :=
.seq loopBody619_29 loopBody619_69

def loopBody619_71 : HolLoopProg 64 :=
.mark loopBody619_70

def loopBody619_72 : HolLoopProg 64 :=
.seq loopBody619_1 loopBody619_71

def loopBody619_73 : HolLoopProg 64 :=
.mark loopBody619_72

def loopBody619_74 : HolLoopProg 64 :=
.seq loopBody619_27 loopBody619_73

def loopBody619_75 : HolLoopProg 64 :=
.mark loopBody619_74

def loopBody619_76 : HolLoopProg 64 :=
.seq loopBody619_1 loopBody619_75

def loopBody619_77 : HolLoopProg 64 :=
.mark loopBody619_76

def loopBody619_78 : HolLoopProg 64 :=
.seq loopBody619_25 loopBody619_77

def loopBody619_79 : HolLoopProg 64 :=
.mark loopBody619_78

def loopBody619_80 : HolLoopProg 64 :=
.seq loopBody619_1 loopBody619_79

def loopBody619_81 : HolLoopProg 64 :=
.mark loopBody619_80

def loopBody619_82 : HolLoopProg 64 :=
.seq loopBody619_23 loopBody619_81

def loopBody619_83 : HolLoopProg 64 :=
.mark loopBody619_82

def loopBody619_84 : HolLoopProg 64 :=
.seq loopBody619_1 loopBody619_83

def loopBody619_85 : HolLoopProg 64 :=
.mark loopBody619_84

def loopBody619_86 : HolLoopProg 64 :=
.seq loopBody619_21 loopBody619_85

def loopBody619_87 : HolLoopProg 64 :=
.mark loopBody619_86

def loopBody619_88 : HolLoopProg 64 :=
.seq loopBody619_1 loopBody619_87

def loopBody619_89 : HolLoopProg 64 :=
.mark loopBody619_88

def loopBody619_90 : HolLoopProg 64 :=
.seq loopBody619_19 loopBody619_89

def loopBody619_91 : HolLoopProg 64 :=
.mark loopBody619_90

def loopBody619_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 384#64])

def loopBody619_93 : HolLoopProg 64 :=
.mark loopBody619_92

def loopBody619_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 32#64]))

def loopBody619_95 : HolLoopProg 64 :=
.mark loopBody619_94

def loopBody619_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 32#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody619_97 : HolLoopProg 64 :=
.mark loopBody619_96

def loopBody619_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 32#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody619_99 : HolLoopProg 64 :=
.mark loopBody619_98

def loopBody619_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 32#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody619_101 : HolLoopProg 64 :=
.mark loopBody619_100

def loopBody619_102 : HolLoopProg 64 :=
.seq loopBody619_101 loopBody619_69

def loopBody619_103 : HolLoopProg 64 :=
.mark loopBody619_102

def loopBody619_104 : HolLoopProg 64 :=
.seq loopBody619_1 loopBody619_103

def loopBody619_105 : HolLoopProg 64 :=
.mark loopBody619_104

def loopBody619_106 : HolLoopProg 64 :=
.seq loopBody619_99 loopBody619_105

def loopBody619_107 : HolLoopProg 64 :=
.mark loopBody619_106

def loopBody619_108 : HolLoopProg 64 :=
.seq loopBody619_1 loopBody619_107

def loopBody619_109 : HolLoopProg 64 :=
.mark loopBody619_108

def loopBody619_110 : HolLoopProg 64 :=
.seq loopBody619_97 loopBody619_109

def loopBody619_111 : HolLoopProg 64 :=
.mark loopBody619_110

def loopBody619_112 : HolLoopProg 64 :=
.seq loopBody619_1 loopBody619_111

def loopBody619_113 : HolLoopProg 64 :=
.mark loopBody619_112

def loopBody619_114 : HolLoopProg 64 :=
.seq loopBody619_95 loopBody619_113

def loopBody619_115 : HolLoopProg 64 :=
.mark loopBody619_114

def loopBody619_116 : HolLoopProg 64 :=
.seq loopBody619_1 loopBody619_115

def loopBody619_117 : HolLoopProg 64 :=
.mark loopBody619_116

def loopBody619_118 : HolLoopProg 64 :=
.seq loopBody619_93 loopBody619_117

def loopBody619_119 : HolLoopProg 64 :=
.mark loopBody619_118

def loopBody619_120 : HolLoopProg 64 :=
.seq loopBody619_1 loopBody619_119

def loopBody619_121 : HolLoopProg 64 :=
.mark loopBody619_120

def loopBody619_122 : HolLoopProg 64 :=
.seq loopBody619_91 loopBody619_121

def loopBody619_123 : HolLoopProg 64 :=
.mark loopBody619_122

def loopBody619_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 768#64])

def loopBody619_125 : HolLoopProg 64 :=
.mark loopBody619_124

def loopBody619_126 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 64#64]))

def loopBody619_127 : HolLoopProg 64 :=
.mark loopBody619_126

def loopBody619_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 64#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody619_129 : HolLoopProg 64 :=
.mark loopBody619_128

def loopBody619_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 64#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody619_131 : HolLoopProg 64 :=
.mark loopBody619_130

def loopBody619_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 64#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody619_133 : HolLoopProg 64 :=
.mark loopBody619_132

def loopBody619_134 : HolLoopProg 64 :=
.seq loopBody619_133 loopBody619_69

def loopBody619_135 : HolLoopProg 64 :=
.mark loopBody619_134

def loopBody619_136 : HolLoopProg 64 :=
.seq loopBody619_1 loopBody619_135

def loopBody619_137 : HolLoopProg 64 :=
.mark loopBody619_136

def loopBody619_138 : HolLoopProg 64 :=
.seq loopBody619_131 loopBody619_137

def loopBody619_139 : HolLoopProg 64 :=
.mark loopBody619_138

def loopBody619_140 : HolLoopProg 64 :=
.seq loopBody619_1 loopBody619_139

def loopBody619_141 : HolLoopProg 64 :=
.mark loopBody619_140

def loopBody619_142 : HolLoopProg 64 :=
.seq loopBody619_129 loopBody619_141

def loopBody619_143 : HolLoopProg 64 :=
.mark loopBody619_142

def loopBody619_144 : HolLoopProg 64 :=
.seq loopBody619_1 loopBody619_143

def loopBody619_145 : HolLoopProg 64 :=
.mark loopBody619_144

def loopBody619_146 : HolLoopProg 64 :=
.seq loopBody619_127 loopBody619_145

def loopBody619_147 : HolLoopProg 64 :=
.mark loopBody619_146

def loopBody619_148 : HolLoopProg 64 :=
.seq loopBody619_1 loopBody619_147

def loopBody619_149 : HolLoopProg 64 :=
.mark loopBody619_148

def loopBody619_150 : HolLoopProg 64 :=
.seq loopBody619_125 loopBody619_149

def loopBody619_151 : HolLoopProg 64 :=
.mark loopBody619_150

def loopBody619_152 : HolLoopProg 64 :=
.seq loopBody619_1 loopBody619_151

def loopBody619_153 : HolLoopProg 64 :=
.mark loopBody619_152

def loopBody619_154 : HolLoopProg 64 :=
.seq loopBody619_123 loopBody619_153

def loopBody619_155 : HolLoopProg 64 :=
.mark loopBody619_154

def loopBody619_156 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody619_157 : HolLoopProg 64 :=
.mark loopBody619_156

def loopBody619_158 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody619_159 : HolLoopProg 64 :=
.mark loopBody619_158

def loopBody619_160 : HolLoopProg 64 :=
.seq loopBody619_159 loopBody619_1

def loopBody619_161 : HolLoopProg 64 :=
.mark loopBody619_160

def loopBody619_162 : HolLoopProg 64 :=
.seq loopBody619_157 loopBody619_161

def loopBody619_163 : HolLoopProg 64 :=
.mark loopBody619_162

def loopBody619_164 : HolLoopProg 64 :=
.seq loopBody619_155 loopBody619_163

def loopBody619_165 : HolLoopProg 64 :=
.mark loopBody619_164

def output619 : Nat × List Nat × HolLoopProg 64 :=
  (683, [0, 1], loopBody619_165)
end InitECandidate.Proofs.FrontendStages.Loop
