import InitECandidate.Proofs.FrontendStages.Loop.Translate309
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody325_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody325_1 : HolLoopProg 64 :=
.mark loopBody325_0

def loopBody325_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 56#64)

def loopBody325_3 : HolLoopProg 64 :=
.mark loopBody325_2

def loopBody325_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody325_5 : HolLoopProg 64 :=
.mark loopBody325_4

def loopBody325_6 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([7]) (some (7, loopBody325_5, loopBody325_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody325_7 : HolLoopProg 64 :=
.mark loopBody325_6

def loopBody325_8 : HolLoopProg 64 :=
.seq loopBody325_7 loopBody325_1

def loopBody325_9 : HolLoopProg 64 :=
.mark loopBody325_8

def loopBody325_10 : HolLoopProg 64 :=
.seq loopBody325_3 loopBody325_9

def loopBody325_11 : HolLoopProg 64 :=
.mark loopBody325_10

def loopBody325_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 0#64])

def loopBody325_13 : HolLoopProg 64 :=
.mark loopBody325_12

def loopBody325_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 0)

def loopBody325_15 : HolLoopProg 64 :=
.mark loopBody325_14

def loopBody325_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 8)

def loopBody325_17 : HolLoopProg 64 :=
.mark loopBody325_16

def loopBody325_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 7) 9

def loopBody325_19 : HolLoopProg 64 :=
.mark loopBody325_18

def loopBody325_20 : HolLoopProg 64 :=
.seq loopBody325_19 loopBody325_1

def loopBody325_21 : HolLoopProg 64 :=
.mark loopBody325_20

def loopBody325_22 : HolLoopProg 64 :=
.seq loopBody325_17 loopBody325_21

def loopBody325_23 : HolLoopProg 64 :=
.mark loopBody325_22

def loopBody325_24 : HolLoopProg 64 :=
.seq loopBody325_23 loopBody325_1

def loopBody325_25 : HolLoopProg 64 :=
.mark loopBody325_24

def loopBody325_26 : HolLoopProg 64 :=
.seq loopBody325_15 loopBody325_25

def loopBody325_27 : HolLoopProg 64 :=
.mark loopBody325_26

def loopBody325_28 : HolLoopProg 64 :=
.seq loopBody325_1 loopBody325_27

def loopBody325_29 : HolLoopProg 64 :=
.mark loopBody325_28

def loopBody325_30 : HolLoopProg 64 :=
.seq loopBody325_13 loopBody325_29

def loopBody325_31 : HolLoopProg 64 :=
.mark loopBody325_30

def loopBody325_32 : HolLoopProg 64 :=
.seq loopBody325_1 loopBody325_31

def loopBody325_33 : HolLoopProg 64 :=
.mark loopBody325_32

def loopBody325_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 8#64])

def loopBody325_35 : HolLoopProg 64 :=
.mark loopBody325_34

def loopBody325_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody325_37 : HolLoopProg 64 :=
.mark loopBody325_36

def loopBody325_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 2)

def loopBody325_39 : HolLoopProg 64 :=
.mark loopBody325_38

def loopBody325_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 3)

def loopBody325_41 : HolLoopProg 64 :=
.mark loopBody325_40

def loopBody325_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 4)

def loopBody325_43 : HolLoopProg 64 :=
.mark loopBody325_42

def loopBody325_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 8)

def loopBody325_45 : HolLoopProg 64 :=
.mark loopBody325_44

def loopBody325_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 7) 12

def loopBody325_47 : HolLoopProg 64 :=
.mark loopBody325_46

def loopBody325_48 : HolLoopProg 64 :=
.seq loopBody325_47 loopBody325_1

def loopBody325_49 : HolLoopProg 64 :=
.mark loopBody325_48

def loopBody325_50 : HolLoopProg 64 :=
.seq loopBody325_45 loopBody325_49

def loopBody325_51 : HolLoopProg 64 :=
.mark loopBody325_50

def loopBody325_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 9)

def loopBody325_53 : HolLoopProg 64 :=
.mark loopBody325_52

def loopBody325_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 8#64]) 12

def loopBody325_55 : HolLoopProg 64 :=
.mark loopBody325_54

def loopBody325_56 : HolLoopProg 64 :=
.seq loopBody325_55 loopBody325_1

def loopBody325_57 : HolLoopProg 64 :=
.mark loopBody325_56

def loopBody325_58 : HolLoopProg 64 :=
.seq loopBody325_53 loopBody325_57

def loopBody325_59 : HolLoopProg 64 :=
.mark loopBody325_58

def loopBody325_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 10)

def loopBody325_61 : HolLoopProg 64 :=
.mark loopBody325_60

def loopBody325_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 16#64]) 12

def loopBody325_63 : HolLoopProg 64 :=
.mark loopBody325_62

def loopBody325_64 : HolLoopProg 64 :=
.seq loopBody325_63 loopBody325_1

def loopBody325_65 : HolLoopProg 64 :=
.mark loopBody325_64

def loopBody325_66 : HolLoopProg 64 :=
.seq loopBody325_61 loopBody325_65

def loopBody325_67 : HolLoopProg 64 :=
.mark loopBody325_66

def loopBody325_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 11)

def loopBody325_69 : HolLoopProg 64 :=
.mark loopBody325_68

def loopBody325_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 24#64]) 12

def loopBody325_71 : HolLoopProg 64 :=
.mark loopBody325_70

def loopBody325_72 : HolLoopProg 64 :=
.seq loopBody325_71 loopBody325_1

def loopBody325_73 : HolLoopProg 64 :=
.mark loopBody325_72

def loopBody325_74 : HolLoopProg 64 :=
.seq loopBody325_69 loopBody325_73

def loopBody325_75 : HolLoopProg 64 :=
.mark loopBody325_74

def loopBody325_76 : HolLoopProg 64 :=
.seq loopBody325_75 loopBody325_1

def loopBody325_77 : HolLoopProg 64 :=
.mark loopBody325_76

def loopBody325_78 : HolLoopProg 64 :=
.seq loopBody325_67 loopBody325_77

def loopBody325_79 : HolLoopProg 64 :=
.mark loopBody325_78

def loopBody325_80 : HolLoopProg 64 :=
.seq loopBody325_59 loopBody325_79

def loopBody325_81 : HolLoopProg 64 :=
.mark loopBody325_80

def loopBody325_82 : HolLoopProg 64 :=
.seq loopBody325_51 loopBody325_81

def loopBody325_83 : HolLoopProg 64 :=
.mark loopBody325_82

def loopBody325_84 : HolLoopProg 64 :=
.seq loopBody325_43 loopBody325_83

def loopBody325_85 : HolLoopProg 64 :=
.mark loopBody325_84

def loopBody325_86 : HolLoopProg 64 :=
.seq loopBody325_1 loopBody325_85

def loopBody325_87 : HolLoopProg 64 :=
.mark loopBody325_86

def loopBody325_88 : HolLoopProg 64 :=
.seq loopBody325_41 loopBody325_87

def loopBody325_89 : HolLoopProg 64 :=
.mark loopBody325_88

def loopBody325_90 : HolLoopProg 64 :=
.seq loopBody325_1 loopBody325_89

def loopBody325_91 : HolLoopProg 64 :=
.mark loopBody325_90

def loopBody325_92 : HolLoopProg 64 :=
.seq loopBody325_39 loopBody325_91

def loopBody325_93 : HolLoopProg 64 :=
.mark loopBody325_92

def loopBody325_94 : HolLoopProg 64 :=
.seq loopBody325_1 loopBody325_93

def loopBody325_95 : HolLoopProg 64 :=
.mark loopBody325_94

def loopBody325_96 : HolLoopProg 64 :=
.seq loopBody325_37 loopBody325_95

def loopBody325_97 : HolLoopProg 64 :=
.mark loopBody325_96

def loopBody325_98 : HolLoopProg 64 :=
.seq loopBody325_1 loopBody325_97

def loopBody325_99 : HolLoopProg 64 :=
.mark loopBody325_98

def loopBody325_100 : HolLoopProg 64 :=
.seq loopBody325_35 loopBody325_99

def loopBody325_101 : HolLoopProg 64 :=
.mark loopBody325_100

def loopBody325_102 : HolLoopProg 64 :=
.seq loopBody325_1 loopBody325_101

def loopBody325_103 : HolLoopProg 64 :=
.mark loopBody325_102

def loopBody325_104 : HolLoopProg 64 :=
.seq loopBody325_33 loopBody325_103

def loopBody325_105 : HolLoopProg 64 :=
.mark loopBody325_104

def loopBody325_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 40#64])

def loopBody325_107 : HolLoopProg 64 :=
.mark loopBody325_106

def loopBody325_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 128#64]))

def loopBody325_109 : HolLoopProg 64 :=
.mark loopBody325_108

def loopBody325_110 : HolLoopProg 64 :=
.seq loopBody325_109 loopBody325_25

def loopBody325_111 : HolLoopProg 64 :=
.mark loopBody325_110

def loopBody325_112 : HolLoopProg 64 :=
.seq loopBody325_1 loopBody325_111

def loopBody325_113 : HolLoopProg 64 :=
.mark loopBody325_112

def loopBody325_114 : HolLoopProg 64 :=
.seq loopBody325_107 loopBody325_113

def loopBody325_115 : HolLoopProg 64 :=
.mark loopBody325_114

def loopBody325_116 : HolLoopProg 64 :=
.seq loopBody325_1 loopBody325_115

def loopBody325_117 : HolLoopProg 64 :=
.mark loopBody325_116

def loopBody325_118 : HolLoopProg 64 :=
.seq loopBody325_105 loopBody325_117

def loopBody325_119 : HolLoopProg 64 :=
.mark loopBody325_118

def loopBody325_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 48#64])

def loopBody325_121 : HolLoopProg 64 :=
.mark loopBody325_120

def loopBody325_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody325_123 : HolLoopProg 64 :=
.mark loopBody325_122

def loopBody325_124 : HolLoopProg 64 :=
.seq loopBody325_123 loopBody325_25

def loopBody325_125 : HolLoopProg 64 :=
.mark loopBody325_124

def loopBody325_126 : HolLoopProg 64 :=
.seq loopBody325_1 loopBody325_125

def loopBody325_127 : HolLoopProg 64 :=
.mark loopBody325_126

def loopBody325_128 : HolLoopProg 64 :=
.seq loopBody325_121 loopBody325_127

def loopBody325_129 : HolLoopProg 64 :=
.mark loopBody325_128

def loopBody325_130 : HolLoopProg 64 :=
.seq loopBody325_1 loopBody325_129

def loopBody325_131 : HolLoopProg 64 :=
.mark loopBody325_130

def loopBody325_132 : HolLoopProg 64 :=
.seq loopBody325_119 loopBody325_131

def loopBody325_133 : HolLoopProg 64 :=
.mark loopBody325_132

def loopBody325_134 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody325_135 : HolLoopProg 64 :=
.mark loopBody325_134

def loopBody325_136 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [7]

def loopBody325_137 : HolLoopProg 64 :=
.mark loopBody325_136

def loopBody325_138 : HolLoopProg 64 :=
.seq loopBody325_137 loopBody325_1

def loopBody325_139 : HolLoopProg 64 :=
.mark loopBody325_138

def loopBody325_140 : HolLoopProg 64 :=
.seq loopBody325_135 loopBody325_139

def loopBody325_141 : HolLoopProg 64 :=
.mark loopBody325_140

def loopBody325_142 : HolLoopProg 64 :=
.seq loopBody325_133 loopBody325_141

def loopBody325_143 : HolLoopProg 64 :=
.mark loopBody325_142

def loopBody325_144 : HolLoopProg 64 :=
.seq loopBody325_11 loopBody325_143

def loopBody325_145 : HolLoopProg 64 :=
.mark loopBody325_144

def loopBody325_146 : HolLoopProg 64 :=
.seq loopBody325_1 loopBody325_145

def loopBody325_147 : HolLoopProg 64 :=
.mark loopBody325_146

def loopBody325_148 : HolLoopProg 64 :=
.seq loopBody325_1 loopBody325_147

def loopBody325_149 : HolLoopProg 64 :=
.mark loopBody325_148

def output325 : Nat × List Nat × HolLoopProg 64 :=
  (389, [0, 1, 2, 3, 4, 5], loopBody325_149)
end InitECandidate.Proofs.FrontendStages.Loop
