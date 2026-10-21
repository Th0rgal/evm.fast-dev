import InitECandidate.Proofs.FrontendStages.Loop.Translate181
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody197_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody197_1 : HolLoopProg 64 :=
.mark loopBody197_0

def loopBody197_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody197_3 : HolLoopProg 64 :=
.mark loopBody197_2

def loopBody197_4 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 69) ([]) (some (6, loopBody197_3, loopBody197_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody197_5 : HolLoopProg 64 :=
.mark loopBody197_4

def loopBody197_6 : HolLoopProg 64 :=
.seq loopBody197_5 loopBody197_1

def loopBody197_7 : HolLoopProg 64 :=
.mark loopBody197_6

def loopBody197_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 2) (Flapjack.HolLoopExp.const 5#64),
      Flapjack.HolLoopExp.const 32#64])

def loopBody197_9 : HolLoopProg 64 :=
.mark loopBody197_8

def loopBody197_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody197_11 : HolLoopProg 64 :=
.mark loopBody197_10

def loopBody197_12 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([7]) (some (7, loopBody197_11, loopBody197_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody197_13 : HolLoopProg 64 :=
.mark loopBody197_12

def loopBody197_14 : HolLoopProg 64 :=
.seq loopBody197_13 loopBody197_1

def loopBody197_15 : HolLoopProg 64 :=
.mark loopBody197_14

def loopBody197_16 : HolLoopProg 64 :=
.seq loopBody197_9 loopBody197_15

def loopBody197_17 : HolLoopProg 64 :=
.mark loopBody197_16

def loopBody197_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody197_19 : HolLoopProg 64 :=
.mark loopBody197_18

def loopBody197_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody197_21 : HolLoopProg 64 :=
.mark loopBody197_20

def loopBody197_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 2)

def loopBody197_23 : HolLoopProg 64 :=
.mark loopBody197_22

def loopBody197_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 1#64)

def loopBody197_25 : HolLoopProg 64 :=
.mark loopBody197_24

def loopBody197_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody197_27 : HolLoopProg 64 :=
.mark loopBody197_26

def loopBody197_28 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 9 (Flapjack.RegImm.reg 10) loopBody197_25 loopBody197_27 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody197_29 : HolLoopProg 64 :=
.mark loopBody197_28

def loopBody197_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody197_31 : HolLoopProg 64 :=
.mark loopBody197_30

def loopBody197_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 0)

def loopBody197_33 : HolLoopProg 64 :=
.mark loopBody197_32

def loopBody197_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody197_35 : HolLoopProg 64 :=
.mark loopBody197_34

def loopBody197_36 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 9 (Flapjack.RegImm.reg 10) loopBody197_25 loopBody197_27 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody197_37 : HolLoopProg 64 :=
.mark loopBody197_36

def loopBody197_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 3)

def loopBody197_39 : HolLoopProg 64 :=
.mark loopBody197_38

def loopBody197_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 11 11 9 10)

def loopBody197_41 : HolLoopProg 64 :=
.mark loopBody197_40

def loopBody197_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 11])

def loopBody197_43 : HolLoopProg 64 :=
.mark loopBody197_42

def loopBody197_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 6,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 7) (Flapjack.HolLoopExp.const 5#64)])

def loopBody197_45 : HolLoopProg 64 :=
.mark loopBody197_44

def loopBody197_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody197_47 : HolLoopProg 64 :=
.mark loopBody197_46

def loopBody197_48 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 256) ([12, 13]) (some (9, loopBody197_47, loopBody197_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody197_49 : HolLoopProg 64 :=
.mark loopBody197_48

def loopBody197_50 : HolLoopProg 64 :=
.seq loopBody197_49 loopBody197_1

def loopBody197_51 : HolLoopProg 64 :=
.mark loopBody197_50

def loopBody197_52 : HolLoopProg 64 :=
.seq loopBody197_45 loopBody197_51

def loopBody197_53 : HolLoopProg 64 :=
.mark loopBody197_52

def loopBody197_54 : HolLoopProg 64 :=
.seq loopBody197_43 loopBody197_53

def loopBody197_55 : HolLoopProg 64 :=
.mark loopBody197_54

def loopBody197_56 : HolLoopProg 64 :=
.seq loopBody197_41 loopBody197_55

def loopBody197_57 : HolLoopProg 64 :=
.mark loopBody197_56

def loopBody197_58 : HolLoopProg 64 :=
.seq loopBody197_39 loopBody197_57

def loopBody197_59 : HolLoopProg 64 :=
.mark loopBody197_58

def loopBody197_60 : HolLoopProg 64 :=
.seq loopBody197_21 loopBody197_59

def loopBody197_61 : HolLoopProg 64 :=
.mark loopBody197_60

def loopBody197_62 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_61

def loopBody197_63 : HolLoopProg 64 :=
.mark loopBody197_62

def loopBody197_64 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_63

def loopBody197_65 : HolLoopProg 64 :=
.mark loopBody197_64

def loopBody197_66 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody197_65 loopBody197_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody197_67 : HolLoopProg 64 :=
.mark loopBody197_66

def loopBody197_68 : HolLoopProg 64 :=
.seq loopBody197_67 loopBody197_1

def loopBody197_69 : HolLoopProg 64 :=
.mark loopBody197_68

def loopBody197_70 : HolLoopProg 64 :=
.seq loopBody197_31 loopBody197_69

def loopBody197_71 : HolLoopProg 64 :=
.mark loopBody197_70

def loopBody197_72 : HolLoopProg 64 :=
.seq loopBody197_37 loopBody197_71

def loopBody197_73 : HolLoopProg 64 :=
.mark loopBody197_72

def loopBody197_74 : HolLoopProg 64 :=
.seq loopBody197_35 loopBody197_73

def loopBody197_75 : HolLoopProg 64 :=
.mark loopBody197_74

def loopBody197_76 : HolLoopProg 64 :=
.seq loopBody197_33 loopBody197_75

def loopBody197_77 : HolLoopProg 64 :=
.mark loopBody197_76

def loopBody197_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 1#64)

def loopBody197_79 : HolLoopProg 64 :=
.mark loopBody197_78

def loopBody197_80 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 257) ([12, 13]) (some (9, loopBody197_47, loopBody197_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody197_81 : HolLoopProg 64 :=
.mark loopBody197_80

def loopBody197_82 : HolLoopProg 64 :=
.seq loopBody197_81 loopBody197_1

def loopBody197_83 : HolLoopProg 64 :=
.mark loopBody197_82

def loopBody197_84 : HolLoopProg 64 :=
.seq loopBody197_45 loopBody197_83

def loopBody197_85 : HolLoopProg 64 :=
.mark loopBody197_84

def loopBody197_86 : HolLoopProg 64 :=
.seq loopBody197_43 loopBody197_85

def loopBody197_87 : HolLoopProg 64 :=
.mark loopBody197_86

def loopBody197_88 : HolLoopProg 64 :=
.seq loopBody197_41 loopBody197_87

def loopBody197_89 : HolLoopProg 64 :=
.mark loopBody197_88

def loopBody197_90 : HolLoopProg 64 :=
.seq loopBody197_39 loopBody197_89

def loopBody197_91 : HolLoopProg 64 :=
.mark loopBody197_90

def loopBody197_92 : HolLoopProg 64 :=
.seq loopBody197_21 loopBody197_91

def loopBody197_93 : HolLoopProg 64 :=
.mark loopBody197_92

def loopBody197_94 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_93

def loopBody197_95 : HolLoopProg 64 :=
.mark loopBody197_94

def loopBody197_96 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_95

def loopBody197_97 : HolLoopProg 64 :=
.mark loopBody197_96

def loopBody197_98 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody197_97 loopBody197_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody197_99 : HolLoopProg 64 :=
.mark loopBody197_98

def loopBody197_100 : HolLoopProg 64 :=
.seq loopBody197_99 loopBody197_1

def loopBody197_101 : HolLoopProg 64 :=
.mark loopBody197_100

def loopBody197_102 : HolLoopProg 64 :=
.seq loopBody197_31 loopBody197_101

def loopBody197_103 : HolLoopProg 64 :=
.mark loopBody197_102

def loopBody197_104 : HolLoopProg 64 :=
.seq loopBody197_37 loopBody197_103

def loopBody197_105 : HolLoopProg 64 :=
.mark loopBody197_104

def loopBody197_106 : HolLoopProg 64 :=
.seq loopBody197_79 loopBody197_105

def loopBody197_107 : HolLoopProg 64 :=
.mark loopBody197_106

def loopBody197_108 : HolLoopProg 64 :=
.seq loopBody197_33 loopBody197_107

def loopBody197_109 : HolLoopProg 64 :=
.mark loopBody197_108

def loopBody197_110 : HolLoopProg 64 :=
.seq loopBody197_77 loopBody197_109

def loopBody197_111 : HolLoopProg 64 :=
.mark loopBody197_110

def loopBody197_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 2#64)

def loopBody197_113 : HolLoopProg 64 :=
.mark loopBody197_112

def loopBody197_114 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 258) ([12, 13]) (some (9, loopBody197_47, loopBody197_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody197_115 : HolLoopProg 64 :=
.mark loopBody197_114

def loopBody197_116 : HolLoopProg 64 :=
.seq loopBody197_115 loopBody197_1

def loopBody197_117 : HolLoopProg 64 :=
.mark loopBody197_116

def loopBody197_118 : HolLoopProg 64 :=
.seq loopBody197_45 loopBody197_117

def loopBody197_119 : HolLoopProg 64 :=
.mark loopBody197_118

def loopBody197_120 : HolLoopProg 64 :=
.seq loopBody197_43 loopBody197_119

def loopBody197_121 : HolLoopProg 64 :=
.mark loopBody197_120

def loopBody197_122 : HolLoopProg 64 :=
.seq loopBody197_41 loopBody197_121

def loopBody197_123 : HolLoopProg 64 :=
.mark loopBody197_122

def loopBody197_124 : HolLoopProg 64 :=
.seq loopBody197_39 loopBody197_123

def loopBody197_125 : HolLoopProg 64 :=
.mark loopBody197_124

def loopBody197_126 : HolLoopProg 64 :=
.seq loopBody197_21 loopBody197_125

def loopBody197_127 : HolLoopProg 64 :=
.mark loopBody197_126

def loopBody197_128 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_127

def loopBody197_129 : HolLoopProg 64 :=
.mark loopBody197_128

def loopBody197_130 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_129

def loopBody197_131 : HolLoopProg 64 :=
.mark loopBody197_130

def loopBody197_132 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody197_131 loopBody197_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody197_133 : HolLoopProg 64 :=
.mark loopBody197_132

def loopBody197_134 : HolLoopProg 64 :=
.seq loopBody197_133 loopBody197_1

def loopBody197_135 : HolLoopProg 64 :=
.mark loopBody197_134

def loopBody197_136 : HolLoopProg 64 :=
.seq loopBody197_31 loopBody197_135

def loopBody197_137 : HolLoopProg 64 :=
.mark loopBody197_136

def loopBody197_138 : HolLoopProg 64 :=
.seq loopBody197_37 loopBody197_137

def loopBody197_139 : HolLoopProg 64 :=
.mark loopBody197_138

def loopBody197_140 : HolLoopProg 64 :=
.seq loopBody197_113 loopBody197_139

def loopBody197_141 : HolLoopProg 64 :=
.mark loopBody197_140

def loopBody197_142 : HolLoopProg 64 :=
.seq loopBody197_33 loopBody197_141

def loopBody197_143 : HolLoopProg 64 :=
.mark loopBody197_142

def loopBody197_144 : HolLoopProg 64 :=
.seq loopBody197_111 loopBody197_143

def loopBody197_145 : HolLoopProg 64 :=
.mark loopBody197_144

def loopBody197_146 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 3#64)

def loopBody197_147 : HolLoopProg 64 :=
.mark loopBody197_146

def loopBody197_148 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 259) ([12, 13]) (some (9, loopBody197_47, loopBody197_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody197_149 : HolLoopProg 64 :=
.mark loopBody197_148

def loopBody197_150 : HolLoopProg 64 :=
.seq loopBody197_149 loopBody197_1

def loopBody197_151 : HolLoopProg 64 :=
.mark loopBody197_150

def loopBody197_152 : HolLoopProg 64 :=
.seq loopBody197_45 loopBody197_151

def loopBody197_153 : HolLoopProg 64 :=
.mark loopBody197_152

def loopBody197_154 : HolLoopProg 64 :=
.seq loopBody197_43 loopBody197_153

def loopBody197_155 : HolLoopProg 64 :=
.mark loopBody197_154

def loopBody197_156 : HolLoopProg 64 :=
.seq loopBody197_41 loopBody197_155

def loopBody197_157 : HolLoopProg 64 :=
.mark loopBody197_156

def loopBody197_158 : HolLoopProg 64 :=
.seq loopBody197_39 loopBody197_157

def loopBody197_159 : HolLoopProg 64 :=
.mark loopBody197_158

def loopBody197_160 : HolLoopProg 64 :=
.seq loopBody197_21 loopBody197_159

def loopBody197_161 : HolLoopProg 64 :=
.mark loopBody197_160

def loopBody197_162 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_161

def loopBody197_163 : HolLoopProg 64 :=
.mark loopBody197_162

def loopBody197_164 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_163

def loopBody197_165 : HolLoopProg 64 :=
.mark loopBody197_164

def loopBody197_166 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody197_165 loopBody197_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody197_167 : HolLoopProg 64 :=
.mark loopBody197_166

def loopBody197_168 : HolLoopProg 64 :=
.seq loopBody197_167 loopBody197_1

def loopBody197_169 : HolLoopProg 64 :=
.mark loopBody197_168

def loopBody197_170 : HolLoopProg 64 :=
.seq loopBody197_31 loopBody197_169

def loopBody197_171 : HolLoopProg 64 :=
.mark loopBody197_170

def loopBody197_172 : HolLoopProg 64 :=
.seq loopBody197_37 loopBody197_171

def loopBody197_173 : HolLoopProg 64 :=
.mark loopBody197_172

def loopBody197_174 : HolLoopProg 64 :=
.seq loopBody197_147 loopBody197_173

def loopBody197_175 : HolLoopProg 64 :=
.mark loopBody197_174

def loopBody197_176 : HolLoopProg 64 :=
.seq loopBody197_33 loopBody197_175

def loopBody197_177 : HolLoopProg 64 :=
.mark loopBody197_176

def loopBody197_178 : HolLoopProg 64 :=
.seq loopBody197_145 loopBody197_177

def loopBody197_179 : HolLoopProg 64 :=
.mark loopBody197_178

def loopBody197_180 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 4#64)

def loopBody197_181 : HolLoopProg 64 :=
.mark loopBody197_180

def loopBody197_182 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 260) ([12, 13]) (some (9, loopBody197_47, loopBody197_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody197_183 : HolLoopProg 64 :=
.mark loopBody197_182

def loopBody197_184 : HolLoopProg 64 :=
.seq loopBody197_183 loopBody197_1

def loopBody197_185 : HolLoopProg 64 :=
.mark loopBody197_184

def loopBody197_186 : HolLoopProg 64 :=
.seq loopBody197_45 loopBody197_185

def loopBody197_187 : HolLoopProg 64 :=
.mark loopBody197_186

def loopBody197_188 : HolLoopProg 64 :=
.seq loopBody197_43 loopBody197_187

def loopBody197_189 : HolLoopProg 64 :=
.mark loopBody197_188

def loopBody197_190 : HolLoopProg 64 :=
.seq loopBody197_41 loopBody197_189

def loopBody197_191 : HolLoopProg 64 :=
.mark loopBody197_190

def loopBody197_192 : HolLoopProg 64 :=
.seq loopBody197_39 loopBody197_191

def loopBody197_193 : HolLoopProg 64 :=
.mark loopBody197_192

def loopBody197_194 : HolLoopProg 64 :=
.seq loopBody197_21 loopBody197_193

def loopBody197_195 : HolLoopProg 64 :=
.mark loopBody197_194

def loopBody197_196 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_195

def loopBody197_197 : HolLoopProg 64 :=
.mark loopBody197_196

def loopBody197_198 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_197

def loopBody197_199 : HolLoopProg 64 :=
.mark loopBody197_198

def loopBody197_200 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody197_199 loopBody197_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody197_201 : HolLoopProg 64 :=
.mark loopBody197_200

def loopBody197_202 : HolLoopProg 64 :=
.seq loopBody197_201 loopBody197_1

def loopBody197_203 : HolLoopProg 64 :=
.mark loopBody197_202

def loopBody197_204 : HolLoopProg 64 :=
.seq loopBody197_31 loopBody197_203

def loopBody197_205 : HolLoopProg 64 :=
.mark loopBody197_204

def loopBody197_206 : HolLoopProg 64 :=
.seq loopBody197_37 loopBody197_205

def loopBody197_207 : HolLoopProg 64 :=
.mark loopBody197_206

def loopBody197_208 : HolLoopProg 64 :=
.seq loopBody197_181 loopBody197_207

def loopBody197_209 : HolLoopProg 64 :=
.mark loopBody197_208

def loopBody197_210 : HolLoopProg 64 :=
.seq loopBody197_33 loopBody197_209

def loopBody197_211 : HolLoopProg 64 :=
.mark loopBody197_210

def loopBody197_212 : HolLoopProg 64 :=
.seq loopBody197_179 loopBody197_211

def loopBody197_213 : HolLoopProg 64 :=
.mark loopBody197_212

def loopBody197_214 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 1#64])

def loopBody197_215 : HolLoopProg 64 :=
.mark loopBody197_214

def loopBody197_216 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 8)

def loopBody197_217 : HolLoopProg 64 :=
.mark loopBody197_216

def loopBody197_218 : HolLoopProg 64 :=
.seq loopBody197_217 loopBody197_1

def loopBody197_219 : HolLoopProg 64 :=
.mark loopBody197_218

def loopBody197_220 : HolLoopProg 64 :=
.seq loopBody197_219 loopBody197_1

def loopBody197_221 : HolLoopProg 64 :=
.mark loopBody197_220

def loopBody197_222 : HolLoopProg 64 :=
.seq loopBody197_215 loopBody197_221

def loopBody197_223 : HolLoopProg 64 :=
.mark loopBody197_222

def loopBody197_224 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_223

def loopBody197_225 : HolLoopProg 64 :=
.mark loopBody197_224

def loopBody197_226 : HolLoopProg 64 :=
.seq loopBody197_213 loopBody197_225

def loopBody197_227 : HolLoopProg 64 :=
.mark loopBody197_226

def loopBody197_228 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody197_229 : HolLoopProg 64 :=
.mark loopBody197_228

def loopBody197_230 : HolLoopProg 64 :=
.seq loopBody197_227 loopBody197_229

def loopBody197_231 : HolLoopProg 64 :=
.mark loopBody197_230

def loopBody197_232 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody197_233 : HolLoopProg 64 :=
.mark loopBody197_232

def loopBody197_234 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody197_231 loopBody197_233 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody197_235 : HolLoopProg 64 :=
.mark loopBody197_234

def loopBody197_236 : HolLoopProg 64 :=
.seq loopBody197_235 loopBody197_1

def loopBody197_237 : HolLoopProg 64 :=
.mark loopBody197_236

def loopBody197_238 : HolLoopProg 64 :=
.seq loopBody197_31 loopBody197_237

def loopBody197_239 : HolLoopProg 64 :=
.mark loopBody197_238

def loopBody197_240 : HolLoopProg 64 :=
.seq loopBody197_29 loopBody197_239

def loopBody197_241 : HolLoopProg 64 :=
.mark loopBody197_240

def loopBody197_242 : HolLoopProg 64 :=
.seq loopBody197_23 loopBody197_241

def loopBody197_243 : HolLoopProg 64 :=
.mark loopBody197_242

def loopBody197_244 : HolLoopProg 64 :=
.seq loopBody197_21 loopBody197_243

def loopBody197_245 : HolLoopProg 64 :=
.mark loopBody197_244

def loopBody197_246 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) loopBody197_245 (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody197_247 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 6)

def loopBody197_248 : HolLoopProg 64 :=
.mark loopBody197_247

def loopBody197_249 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 2)

def loopBody197_250 : HolLoopProg 64 :=
.mark loopBody197_249

def loopBody197_251 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 4)

def loopBody197_252 : HolLoopProg 64 :=
.mark loopBody197_251

def loopBody197_253 : HolLoopProg 64 :=
.call (some ([8], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))) (some 238) ([9, 10, 11, 12]) (some (9, loopBody197_47, loopBody197_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody197_254 : HolLoopProg 64 :=
.mark loopBody197_253

def loopBody197_255 : HolLoopProg 64 :=
.seq loopBody197_254 loopBody197_1

def loopBody197_256 : HolLoopProg 64 :=
.mark loopBody197_255

def loopBody197_257 : HolLoopProg 64 :=
.seq loopBody197_252 loopBody197_256

def loopBody197_258 : HolLoopProg 64 :=
.mark loopBody197_257

def loopBody197_259 : HolLoopProg 64 :=
.seq loopBody197_250 loopBody197_258

def loopBody197_260 : HolLoopProg 64 :=
.mark loopBody197_259

def loopBody197_261 : HolLoopProg 64 :=
.seq loopBody197_23 loopBody197_260

def loopBody197_262 : HolLoopProg 64 :=
.mark loopBody197_261

def loopBody197_263 : HolLoopProg 64 :=
.seq loopBody197_248 loopBody197_262

def loopBody197_264 : HolLoopProg 64 :=
.mark loopBody197_263

def loopBody197_265 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_264

def loopBody197_266 : HolLoopProg 64 :=
.mark loopBody197_265

def loopBody197_267 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_266

def loopBody197_268 : HolLoopProg 64 :=
.mark loopBody197_267

def loopBody197_269 : HolLoopProg 64 :=
.seq loopBody197_246 loopBody197_268

def loopBody197_270 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody197_271 : HolLoopProg 64 :=
.mark loopBody197_270

def loopBody197_272 : HolLoopProg 64 :=
.call (some ([8], Flapjack.Spt.ln)) (some 70) ([9]) (some (9, loopBody197_47, loopBody197_1, (Flapjack.Spt.ln)))

def loopBody197_273 : HolLoopProg 64 :=
.mark loopBody197_272

def loopBody197_274 : HolLoopProg 64 :=
.seq loopBody197_273 loopBody197_1

def loopBody197_275 : HolLoopProg 64 :=
.mark loopBody197_274

def loopBody197_276 : HolLoopProg 64 :=
.seq loopBody197_271 loopBody197_275

def loopBody197_277 : HolLoopProg 64 :=
.mark loopBody197_276

def loopBody197_278 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_277

def loopBody197_279 : HolLoopProg 64 :=
.mark loopBody197_278

def loopBody197_280 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_279

def loopBody197_281 : HolLoopProg 64 :=
.mark loopBody197_280

def loopBody197_282 : HolLoopProg 64 :=
.seq loopBody197_269 loopBody197_281

def loopBody197_283 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody197_284 : HolLoopProg 64 :=
.mark loopBody197_283

def loopBody197_285 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [8]

def loopBody197_286 : HolLoopProg 64 :=
.mark loopBody197_285

def loopBody197_287 : HolLoopProg 64 :=
.seq loopBody197_286 loopBody197_1

def loopBody197_288 : HolLoopProg 64 :=
.mark loopBody197_287

def loopBody197_289 : HolLoopProg 64 :=
.seq loopBody197_284 loopBody197_288

def loopBody197_290 : HolLoopProg 64 :=
.mark loopBody197_289

def loopBody197_291 : HolLoopProg 64 :=
.seq loopBody197_282 loopBody197_290

def loopBody197_292 : HolLoopProg 64 :=
.seq loopBody197_19 loopBody197_291

def loopBody197_293 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_292

def loopBody197_294 : HolLoopProg 64 :=
.seq loopBody197_17 loopBody197_293

def loopBody197_295 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_294

def loopBody197_296 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_295

def loopBody197_297 : HolLoopProg 64 :=
.seq loopBody197_7 loopBody197_296

def loopBody197_298 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_297

def loopBody197_299 : HolLoopProg 64 :=
.seq loopBody197_1 loopBody197_298

def output197 : Nat × List Nat × HolLoopProg 64 :=
  (261, [0, 1, 2, 3, 4], loopBody197_299)
end InitECandidate.Proofs.FrontendStages.Loop
