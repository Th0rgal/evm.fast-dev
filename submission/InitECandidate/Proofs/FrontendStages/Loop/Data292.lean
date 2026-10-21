import InitECandidate.Proofs.FrontendStages.Loop.Translate276
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody292_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody292_1 : HolLoopProg 64 :=
.mark loopBody292_0

def loopBody292_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody292_3 : HolLoopProg 64 :=
.mark loopBody292_2

def loopBody292_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody292_5 : HolLoopProg 64 :=
.mark loopBody292_4

def loopBody292_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody292_7 : HolLoopProg 64 :=
.mark loopBody292_6

def loopBody292_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody292_9 : HolLoopProg 64 :=
.mark loopBody292_8

def loopBody292_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody292_11 : HolLoopProg 64 :=
.mark loopBody292_10

def loopBody292_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody292_13 : HolLoopProg 64 :=
.mark loopBody292_12

def loopBody292_14 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 5 (Flapjack.RegImm.reg 6) loopBody292_11 loopBody292_13 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody292_15 : HolLoopProg 64 :=
.mark loopBody292_14

def loopBody292_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody292_17 : HolLoopProg 64 :=
.mark loopBody292_16

def loopBody292_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody292_19 : HolLoopProg 64 :=
.mark loopBody292_18

def loopBody292_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 24#64)

def loopBody292_21 : HolLoopProg 64 :=
.mark loopBody292_20

def loopBody292_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 6 6 4 5)

def loopBody292_23 : HolLoopProg 64 :=
.mark loopBody292_22

def loopBody292_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 16#64]))

def loopBody292_25 : HolLoopProg 64 :=
.mark loopBody292_24

def loopBody292_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 33#64)

def loopBody292_27 : HolLoopProg 64 :=
.mark loopBody292_26

def loopBody292_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 9 9 7 8)

def loopBody292_29 : HolLoopProg 64 :=
.mark loopBody292_28

def loopBody292_30 : HolLoopProg 64 :=
.seq loopBody292_29 loopBody292_1

def loopBody292_31 : HolLoopProg 64 :=
.mark loopBody292_30

def loopBody292_32 : HolLoopProg 64 :=
.seq loopBody292_27 loopBody292_31

def loopBody292_33 : HolLoopProg 64 :=
.mark loopBody292_32

def loopBody292_34 : HolLoopProg 64 :=
.seq loopBody292_25 loopBody292_33

def loopBody292_35 : HolLoopProg 64 :=
.mark loopBody292_34

def loopBody292_36 : HolLoopProg 64 :=
.seq loopBody292_23 loopBody292_35

def loopBody292_37 : HolLoopProg 64 :=
.mark loopBody292_36

def loopBody292_38 : HolLoopProg 64 :=
.seq loopBody292_21 loopBody292_37

def loopBody292_39 : HolLoopProg 64 :=
.mark loopBody292_38

def loopBody292_40 : HolLoopProg 64 :=
.seq loopBody292_19 loopBody292_39

def loopBody292_41 : HolLoopProg 64 :=
.mark loopBody292_40

def loopBody292_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 9)

def loopBody292_43 : HolLoopProg 64 :=
.mark loopBody292_42

def loopBody292_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 10)

def loopBody292_45 : HolLoopProg 64 :=
.mark loopBody292_44

def loopBody292_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 12

def loopBody292_47 : HolLoopProg 64 :=
.mark loopBody292_46

def loopBody292_48 : HolLoopProg 64 :=
.call (some
  ([11],
    Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 180) ([12]) (some (12, loopBody292_47, loopBody292_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))))

def loopBody292_49 : HolLoopProg 64 :=
.mark loopBody292_48

def loopBody292_50 : HolLoopProg 64 :=
.seq loopBody292_49 loopBody292_1

def loopBody292_51 : HolLoopProg 64 :=
.mark loopBody292_50

def loopBody292_52 : HolLoopProg 64 :=
.seq loopBody292_45 loopBody292_51

def loopBody292_53 : HolLoopProg 64 :=
.mark loopBody292_52

def loopBody292_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.const 21#64, Flapjack.HolLoopExp.var 11, Flapjack.HolLoopExp.var 10])

def loopBody292_55 : HolLoopProg 64 :=
.mark loopBody292_54

def loopBody292_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 12)

def loopBody292_57 : HolLoopProg 64 :=
.mark loopBody292_56

def loopBody292_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 14

def loopBody292_59 : HolLoopProg 64 :=
.mark loopBody292_58

def loopBody292_60 : HolLoopProg 64 :=
.call (some
  ([13],
    Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 180) ([14]) (some (14, loopBody292_59, loopBody292_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit)))))

def loopBody292_61 : HolLoopProg 64 :=
.mark loopBody292_60

def loopBody292_62 : HolLoopProg 64 :=
.seq loopBody292_61 loopBody292_1

def loopBody292_63 : HolLoopProg 64 :=
.mark loopBody292_62

def loopBody292_64 : HolLoopProg 64 :=
.seq loopBody292_57 loopBody292_63

def loopBody292_65 : HolLoopProg 64 :=
.mark loopBody292_64

def loopBody292_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 13, Flapjack.HolLoopExp.var 12])

def loopBody292_67 : HolLoopProg 64 :=
.mark loopBody292_66

def loopBody292_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 14)

def loopBody292_69 : HolLoopProg 64 :=
.mark loopBody292_68

def loopBody292_70 : HolLoopProg 64 :=
.seq loopBody292_69 loopBody292_1

def loopBody292_71 : HolLoopProg 64 :=
.mark loopBody292_70

def loopBody292_72 : HolLoopProg 64 :=
.seq loopBody292_71 loopBody292_1

def loopBody292_73 : HolLoopProg 64 :=
.mark loopBody292_72

def loopBody292_74 : HolLoopProg 64 :=
.seq loopBody292_67 loopBody292_73

def loopBody292_75 : HolLoopProg 64 :=
.mark loopBody292_74

def loopBody292_76 : HolLoopProg 64 :=
.seq loopBody292_1 loopBody292_75

def loopBody292_77 : HolLoopProg 64 :=
.mark loopBody292_76

def loopBody292_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 1#64])

def loopBody292_79 : HolLoopProg 64 :=
.mark loopBody292_78

def loopBody292_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 14)

def loopBody292_81 : HolLoopProg 64 :=
.mark loopBody292_80

def loopBody292_82 : HolLoopProg 64 :=
.seq loopBody292_81 loopBody292_1

def loopBody292_83 : HolLoopProg 64 :=
.mark loopBody292_82

def loopBody292_84 : HolLoopProg 64 :=
.seq loopBody292_83 loopBody292_1

def loopBody292_85 : HolLoopProg 64 :=
.mark loopBody292_84

def loopBody292_86 : HolLoopProg 64 :=
.seq loopBody292_79 loopBody292_85

def loopBody292_87 : HolLoopProg 64 :=
.mark loopBody292_86

def loopBody292_88 : HolLoopProg 64 :=
.seq loopBody292_1 loopBody292_87

def loopBody292_89 : HolLoopProg 64 :=
.mark loopBody292_88

def loopBody292_90 : HolLoopProg 64 :=
.seq loopBody292_77 loopBody292_89

def loopBody292_91 : HolLoopProg 64 :=
.mark loopBody292_90

def loopBody292_92 : HolLoopProg 64 :=
.seq loopBody292_65 loopBody292_91

def loopBody292_93 : HolLoopProg 64 :=
.mark loopBody292_92

def loopBody292_94 : HolLoopProg 64 :=
.seq loopBody292_1 loopBody292_93

def loopBody292_95 : HolLoopProg 64 :=
.mark loopBody292_94

def loopBody292_96 : HolLoopProg 64 :=
.seq loopBody292_1 loopBody292_95

def loopBody292_97 : HolLoopProg 64 :=
.mark loopBody292_96

def loopBody292_98 : HolLoopProg 64 :=
.seq loopBody292_55 loopBody292_97

def loopBody292_99 : HolLoopProg 64 :=
.mark loopBody292_98

def loopBody292_100 : HolLoopProg 64 :=
.seq loopBody292_1 loopBody292_99

def loopBody292_101 : HolLoopProg 64 :=
.mark loopBody292_100

def loopBody292_102 : HolLoopProg 64 :=
.seq loopBody292_53 loopBody292_101

def loopBody292_103 : HolLoopProg 64 :=
.mark loopBody292_102

def loopBody292_104 : HolLoopProg 64 :=
.seq loopBody292_1 loopBody292_103

def loopBody292_105 : HolLoopProg 64 :=
.mark loopBody292_104

def loopBody292_106 : HolLoopProg 64 :=
.seq loopBody292_1 loopBody292_105

def loopBody292_107 : HolLoopProg 64 :=
.mark loopBody292_106

def loopBody292_108 : HolLoopProg 64 :=
.seq loopBody292_43 loopBody292_107

def loopBody292_109 : HolLoopProg 64 :=
.mark loopBody292_108

def loopBody292_110 : HolLoopProg 64 :=
.seq loopBody292_41 loopBody292_109

def loopBody292_111 : HolLoopProg 64 :=
.mark loopBody292_110

def loopBody292_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody292_113 : HolLoopProg 64 :=
.mark loopBody292_112

def loopBody292_114 : HolLoopProg 64 :=
.seq loopBody292_111 loopBody292_113

def loopBody292_115 : HolLoopProg 64 :=
.mark loopBody292_114

def loopBody292_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody292_117 : HolLoopProg 64 :=
.mark loopBody292_116

def loopBody292_118 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody292_115 loopBody292_117 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody292_119 : HolLoopProg 64 :=
.mark loopBody292_118

def loopBody292_120 : HolLoopProg 64 :=
.seq loopBody292_119 loopBody292_1

def loopBody292_121 : HolLoopProg 64 :=
.mark loopBody292_120

def loopBody292_122 : HolLoopProg 64 :=
.seq loopBody292_17 loopBody292_121

def loopBody292_123 : HolLoopProg 64 :=
.mark loopBody292_122

def loopBody292_124 : HolLoopProg 64 :=
.seq loopBody292_15 loopBody292_123

def loopBody292_125 : HolLoopProg 64 :=
.mark loopBody292_124

def loopBody292_126 : HolLoopProg 64 :=
.seq loopBody292_9 loopBody292_125

def loopBody292_127 : HolLoopProg 64 :=
.mark loopBody292_126

def loopBody292_128 : HolLoopProg 64 :=
.seq loopBody292_7 loopBody292_127

def loopBody292_129 : HolLoopProg 64 :=
.mark loopBody292_128

def loopBody292_130 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody292_129 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)

def loopBody292_131 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody292_132 : HolLoopProg 64 :=
.mark loopBody292_131

def loopBody292_133 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody292_134 : HolLoopProg 64 :=
.mark loopBody292_133

def loopBody292_135 : HolLoopProg 64 :=
.seq loopBody292_134 loopBody292_1

def loopBody292_136 : HolLoopProg 64 :=
.mark loopBody292_135

def loopBody292_137 : HolLoopProg 64 :=
.seq loopBody292_132 loopBody292_136

def loopBody292_138 : HolLoopProg 64 :=
.mark loopBody292_137

def loopBody292_139 : HolLoopProg 64 :=
.seq loopBody292_130 loopBody292_138

def loopBody292_140 : HolLoopProg 64 :=
.seq loopBody292_5 loopBody292_139

def loopBody292_141 : HolLoopProg 64 :=
.seq loopBody292_1 loopBody292_140

def loopBody292_142 : HolLoopProg 64 :=
.seq loopBody292_3 loopBody292_141

def loopBody292_143 : HolLoopProg 64 :=
.seq loopBody292_1 loopBody292_142

def output292 : Nat × List Nat × HolLoopProg 64 :=
  (356, [0, 1], loopBody292_143)
end InitECandidate.Proofs.FrontendStages.Loop
