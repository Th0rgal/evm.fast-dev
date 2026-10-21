import InitECandidate.Proofs.FrontendStages.Loop.Translate166
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody182_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody182_1 : HolLoopProg 64 :=
.mark loopBody182_0

def loopBody182_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody182_3 : HolLoopProg 64 :=
.mark loopBody182_2

def loopBody182_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody182_5 : HolLoopProg 64 :=
.mark loopBody182_4

def loopBody182_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody182_7 : HolLoopProg 64 :=
.mark loopBody182_6

def loopBody182_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 5 (Flapjack.RegImm.reg 6) loopBody182_5 loopBody182_7 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody182_9 : HolLoopProg 64 :=
.mark loopBody182_8

def loopBody182_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody182_11 : HolLoopProg 64 :=
.mark loopBody182_10

def loopBody182_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody182_13 : HolLoopProg 64 :=
.mark loopBody182_12

def loopBody182_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody182_15 : HolLoopProg 64 :=
.mark loopBody182_14

def loopBody182_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody182_17 : HolLoopProg 64 :=
.mark loopBody182_16

def loopBody182_18 : HolLoopProg 64 :=
.seq loopBody182_15 loopBody182_17

def loopBody182_19 : HolLoopProg 64 :=
.mark loopBody182_18

def loopBody182_20 : HolLoopProg 64 :=
.seq loopBody182_13 loopBody182_19

def loopBody182_21 : HolLoopProg 64 :=
.mark loopBody182_20

def loopBody182_22 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody182_21 loopBody182_17 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody182_23 : HolLoopProg 64 :=
.mark loopBody182_22

def loopBody182_24 : HolLoopProg 64 :=
.seq loopBody182_23 loopBody182_17

def loopBody182_25 : HolLoopProg 64 :=
.mark loopBody182_24

def loopBody182_26 : HolLoopProg 64 :=
.seq loopBody182_11 loopBody182_25

def loopBody182_27 : HolLoopProg 64 :=
.mark loopBody182_26

def loopBody182_28 : HolLoopProg 64 :=
.seq loopBody182_9 loopBody182_27

def loopBody182_29 : HolLoopProg 64 :=
.mark loopBody182_28

def loopBody182_30 : HolLoopProg 64 :=
.seq loopBody182_3 loopBody182_29

def loopBody182_31 : HolLoopProg 64 :=
.mark loopBody182_30

def loopBody182_32 : HolLoopProg 64 :=
.seq loopBody182_1 loopBody182_31

def loopBody182_33 : HolLoopProg 64 :=
.mark loopBody182_32

def loopBody182_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody182_35 : HolLoopProg 64 :=
.mark loopBody182_34

def loopBody182_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody182_37 : HolLoopProg 64 :=
.mark loopBody182_36

def loopBody182_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody182_39 : HolLoopProg 64 :=
.mark loopBody182_38

def loopBody182_40 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 6 (Flapjack.RegImm.reg 7) loopBody182_39 loopBody182_3 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody182_41 : HolLoopProg 64 :=
.mark loopBody182_40

def loopBody182_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody182_43 : HolLoopProg 64 :=
.mark loopBody182_42

def loopBody182_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 3#64)]))

def loopBody182_45 : HolLoopProg 64 :=
.mark loopBody182_44

def loopBody182_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody182_47 : HolLoopProg 64 :=
.mark loopBody182_46

def loopBody182_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody182_49 : HolLoopProg 64 :=
.mark loopBody182_48

def loopBody182_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody182_51 : HolLoopProg 64 :=
.mark loopBody182_50

def loopBody182_52 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 7 (Flapjack.RegImm.reg 8) loopBody182_49 loopBody182_51 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody182_53 : HolLoopProg 64 :=
.mark loopBody182_52

def loopBody182_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 3)

def loopBody182_55 : HolLoopProg 64 :=
.mark loopBody182_54

def loopBody182_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 5)

def loopBody182_57 : HolLoopProg 64 :=
.mark loopBody182_56

def loopBody182_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 1#64)

def loopBody182_59 : HolLoopProg 64 :=
.mark loopBody182_58

def loopBody182_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody182_61 : HolLoopProg 64 :=
.mark loopBody182_60

def loopBody182_62 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.RegImm.reg 11) loopBody182_59 loopBody182_61 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody182_63 : HolLoopProg 64 :=
.mark loopBody182_62

def loopBody182_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 0#64)

def loopBody182_65 : HolLoopProg 64 :=
.mark loopBody182_64

def loopBody182_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.var 10])

def loopBody182_67 : HolLoopProg 64 :=
.mark loopBody182_66

def loopBody182_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 1#64)

def loopBody182_69 : HolLoopProg 64 :=
.mark loopBody182_68

def loopBody182_70 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 13 (Flapjack.RegImm.reg 14) loopBody182_69 loopBody182_65 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit)))

def loopBody182_71 : HolLoopProg 64 :=
.mark loopBody182_70

def loopBody182_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 13)

def loopBody182_73 : HolLoopProg 64 :=
.mark loopBody182_72

def loopBody182_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 10#64)

def loopBody182_75 : HolLoopProg 64 :=
.mark loopBody182_74

def loopBody182_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody182_77 : HolLoopProg 64 :=
.mark loopBody182_76

def loopBody182_78 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 245) ([7]) (some (7, loopBody182_77, loopBody182_17, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody182_79 : HolLoopProg 64 :=
.mark loopBody182_78

def loopBody182_80 : HolLoopProg 64 :=
.seq loopBody182_79 loopBody182_17

def loopBody182_81 : HolLoopProg 64 :=
.mark loopBody182_80

def loopBody182_82 : HolLoopProg 64 :=
.seq loopBody182_75 loopBody182_81

def loopBody182_83 : HolLoopProg 64 :=
.mark loopBody182_82

def loopBody182_84 : HolLoopProg 64 :=
.seq loopBody182_17 loopBody182_83

def loopBody182_85 : HolLoopProg 64 :=
.mark loopBody182_84

def loopBody182_86 : HolLoopProg 64 :=
.seq loopBody182_17 loopBody182_85

def loopBody182_87 : HolLoopProg 64 :=
.mark loopBody182_86

def loopBody182_88 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 15 (Flapjack.RegImm.imm 0#64) loopBody182_87 loopBody182_17 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody182_89 : HolLoopProg 64 :=
.mark loopBody182_88

def loopBody182_90 : HolLoopProg 64 :=
.seq loopBody182_89 loopBody182_17

def loopBody182_91 : HolLoopProg 64 :=
.mark loopBody182_90

def loopBody182_92 : HolLoopProg 64 :=
.seq loopBody182_73 loopBody182_91

def loopBody182_93 : HolLoopProg 64 :=
.mark loopBody182_92

def loopBody182_94 : HolLoopProg 64 :=
.seq loopBody182_71 loopBody182_93

def loopBody182_95 : HolLoopProg 64 :=
.mark loopBody182_94

def loopBody182_96 : HolLoopProg 64 :=
.seq loopBody182_67 loopBody182_95

def loopBody182_97 : HolLoopProg 64 :=
.mark loopBody182_96

def loopBody182_98 : HolLoopProg 64 :=
.seq loopBody182_65 loopBody182_97

def loopBody182_99 : HolLoopProg 64 :=
.mark loopBody182_98

def loopBody182_100 : HolLoopProg 64 :=
.seq loopBody182_63 loopBody182_99

def loopBody182_101 : HolLoopProg 64 :=
.mark loopBody182_100

def loopBody182_102 : HolLoopProg 64 :=
.seq loopBody182_57 loopBody182_101

def loopBody182_103 : HolLoopProg 64 :=
.mark loopBody182_102

def loopBody182_104 : HolLoopProg 64 :=
.seq loopBody182_55 loopBody182_103

def loopBody182_105 : HolLoopProg 64 :=
.mark loopBody182_104

def loopBody182_106 : HolLoopProg 64 :=
.seq loopBody182_53 loopBody182_105

def loopBody182_107 : HolLoopProg 64 :=
.mark loopBody182_106

def loopBody182_108 : HolLoopProg 64 :=
.seq loopBody182_47 loopBody182_107

def loopBody182_109 : HolLoopProg 64 :=
.mark loopBody182_108

def loopBody182_110 : HolLoopProg 64 :=
.seq loopBody182_11 loopBody182_109

def loopBody182_111 : HolLoopProg 64 :=
.mark loopBody182_110

def loopBody182_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 4)

def loopBody182_113 : HolLoopProg 64 :=
.mark loopBody182_112

def loopBody182_114 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 7 (Flapjack.RegImm.reg 8) loopBody182_49 loopBody182_51 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody182_115 : HolLoopProg 64 :=
.mark loopBody182_114

def loopBody182_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody182_117 : HolLoopProg 64 :=
.mark loopBody182_116

def loopBody182_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.var 0,
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 3#64)],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody182_119 : HolLoopProg 64 :=
.mark loopBody182_118

def loopBody182_120 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 7 (Flapjack.RegImm.reg 8) loopBody182_49 loopBody182_51 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody182_121 : HolLoopProg 64 :=
.mark loopBody182_120

def loopBody182_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 11#64)

def loopBody182_123 : HolLoopProg 64 :=
.mark loopBody182_122

def loopBody182_124 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 245) ([7]) (some (7, loopBody182_77, loopBody182_17, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody182_125 : HolLoopProg 64 :=
.mark loopBody182_124

def loopBody182_126 : HolLoopProg 64 :=
.seq loopBody182_125 loopBody182_17

def loopBody182_127 : HolLoopProg 64 :=
.mark loopBody182_126

def loopBody182_128 : HolLoopProg 64 :=
.seq loopBody182_123 loopBody182_127

def loopBody182_129 : HolLoopProg 64 :=
.mark loopBody182_128

def loopBody182_130 : HolLoopProg 64 :=
.seq loopBody182_17 loopBody182_129

def loopBody182_131 : HolLoopProg 64 :=
.mark loopBody182_130

def loopBody182_132 : HolLoopProg 64 :=
.seq loopBody182_17 loopBody182_131

def loopBody182_133 : HolLoopProg 64 :=
.mark loopBody182_132

def loopBody182_134 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody182_133 loopBody182_17 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody182_135 : HolLoopProg 64 :=
.mark loopBody182_134

def loopBody182_136 : HolLoopProg 64 :=
.seq loopBody182_135 loopBody182_17

def loopBody182_137 : HolLoopProg 64 :=
.mark loopBody182_136

def loopBody182_138 : HolLoopProg 64 :=
.seq loopBody182_117 loopBody182_137

def loopBody182_139 : HolLoopProg 64 :=
.mark loopBody182_138

def loopBody182_140 : HolLoopProg 64 :=
.seq loopBody182_121 loopBody182_139

def loopBody182_141 : HolLoopProg 64 :=
.mark loopBody182_140

def loopBody182_142 : HolLoopProg 64 :=
.seq loopBody182_119 loopBody182_141

def loopBody182_143 : HolLoopProg 64 :=
.mark loopBody182_142

def loopBody182_144 : HolLoopProg 64 :=
.seq loopBody182_11 loopBody182_143

def loopBody182_145 : HolLoopProg 64 :=
.mark loopBody182_144

def loopBody182_146 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody182_145 loopBody182_17 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody182_147 : HolLoopProg 64 :=
.mark loopBody182_146

def loopBody182_148 : HolLoopProg 64 :=
.seq loopBody182_147 loopBody182_17

def loopBody182_149 : HolLoopProg 64 :=
.mark loopBody182_148

def loopBody182_150 : HolLoopProg 64 :=
.seq loopBody182_117 loopBody182_149

def loopBody182_151 : HolLoopProg 64 :=
.mark loopBody182_150

def loopBody182_152 : HolLoopProg 64 :=
.seq loopBody182_115 loopBody182_151

def loopBody182_153 : HolLoopProg 64 :=
.mark loopBody182_152

def loopBody182_154 : HolLoopProg 64 :=
.seq loopBody182_113 loopBody182_153

def loopBody182_155 : HolLoopProg 64 :=
.mark loopBody182_154

def loopBody182_156 : HolLoopProg 64 :=
.seq loopBody182_51 loopBody182_155

def loopBody182_157 : HolLoopProg 64 :=
.mark loopBody182_156

def loopBody182_158 : HolLoopProg 64 :=
.seq loopBody182_111 loopBody182_157

def loopBody182_159 : HolLoopProg 64 :=
.mark loopBody182_158

def loopBody182_160 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])

def loopBody182_161 : HolLoopProg 64 :=
.mark loopBody182_160

def loopBody182_162 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 6)

def loopBody182_163 : HolLoopProg 64 :=
.mark loopBody182_162

def loopBody182_164 : HolLoopProg 64 :=
.seq loopBody182_163 loopBody182_17

def loopBody182_165 : HolLoopProg 64 :=
.mark loopBody182_164

def loopBody182_166 : HolLoopProg 64 :=
.seq loopBody182_165 loopBody182_17

def loopBody182_167 : HolLoopProg 64 :=
.mark loopBody182_166

def loopBody182_168 : HolLoopProg 64 :=
.seq loopBody182_161 loopBody182_167

def loopBody182_169 : HolLoopProg 64 :=
.mark loopBody182_168

def loopBody182_170 : HolLoopProg 64 :=
.seq loopBody182_17 loopBody182_169

def loopBody182_171 : HolLoopProg 64 :=
.mark loopBody182_170

def loopBody182_172 : HolLoopProg 64 :=
.seq loopBody182_159 loopBody182_171

def loopBody182_173 : HolLoopProg 64 :=
.mark loopBody182_172

def loopBody182_174 : HolLoopProg 64 :=
.seq loopBody182_45 loopBody182_173

def loopBody182_175 : HolLoopProg 64 :=
.mark loopBody182_174

def loopBody182_176 : HolLoopProg 64 :=
.seq loopBody182_17 loopBody182_175

def loopBody182_177 : HolLoopProg 64 :=
.mark loopBody182_176

def loopBody182_178 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody182_179 : HolLoopProg 64 :=
.mark loopBody182_178

def loopBody182_180 : HolLoopProg 64 :=
.seq loopBody182_177 loopBody182_179

def loopBody182_181 : HolLoopProg 64 :=
.mark loopBody182_180

def loopBody182_182 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody182_183 : HolLoopProg 64 :=
.mark loopBody182_182

def loopBody182_184 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody182_181 loopBody182_183 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody182_185 : HolLoopProg 64 :=
.mark loopBody182_184

def loopBody182_186 : HolLoopProg 64 :=
.seq loopBody182_185 loopBody182_17

def loopBody182_187 : HolLoopProg 64 :=
.mark loopBody182_186

def loopBody182_188 : HolLoopProg 64 :=
.seq loopBody182_43 loopBody182_187

def loopBody182_189 : HolLoopProg 64 :=
.mark loopBody182_188

def loopBody182_190 : HolLoopProg 64 :=
.seq loopBody182_41 loopBody182_189

def loopBody182_191 : HolLoopProg 64 :=
.mark loopBody182_190

def loopBody182_192 : HolLoopProg 64 :=
.seq loopBody182_37 loopBody182_191

def loopBody182_193 : HolLoopProg 64 :=
.mark loopBody182_192

def loopBody182_194 : HolLoopProg 64 :=
.seq loopBody182_35 loopBody182_193

def loopBody182_195 : HolLoopProg 64 :=
.mark loopBody182_194

def loopBody182_196 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody182_195 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)

def loopBody182_197 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.var 0))

def loopBody182_198 : HolLoopProg 64 :=
.mark loopBody182_197

def loopBody182_199 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody182_200 : HolLoopProg 64 :=
.mark loopBody182_199

def loopBody182_201 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.reg 7) loopBody182_39 loopBody182_3 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)

def loopBody182_202 : HolLoopProg 64 :=
.mark loopBody182_201

def loopBody182_203 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 12#64)

def loopBody182_204 : HolLoopProg 64 :=
.mark loopBody182_203

def loopBody182_205 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody182_206 : HolLoopProg 64 :=
.mark loopBody182_205

def loopBody182_207 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 245) ([6]) (some (6, loopBody182_206, loopBody182_17, (Flapjack.Spt.ln)))

def loopBody182_208 : HolLoopProg 64 :=
.mark loopBody182_207

def loopBody182_209 : HolLoopProg 64 :=
.seq loopBody182_208 loopBody182_17

def loopBody182_210 : HolLoopProg 64 :=
.mark loopBody182_209

def loopBody182_211 : HolLoopProg 64 :=
.seq loopBody182_204 loopBody182_210

def loopBody182_212 : HolLoopProg 64 :=
.mark loopBody182_211

def loopBody182_213 : HolLoopProg 64 :=
.seq loopBody182_17 loopBody182_212

def loopBody182_214 : HolLoopProg 64 :=
.mark loopBody182_213

def loopBody182_215 : HolLoopProg 64 :=
.seq loopBody182_17 loopBody182_214

def loopBody182_216 : HolLoopProg 64 :=
.mark loopBody182_215

def loopBody182_217 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody182_216 loopBody182_17 (Flapjack.Spt.ln)

def loopBody182_218 : HolLoopProg 64 :=
.mark loopBody182_217

def loopBody182_219 : HolLoopProg 64 :=
.seq loopBody182_218 loopBody182_17

def loopBody182_220 : HolLoopProg 64 :=
.mark loopBody182_219

def loopBody182_221 : HolLoopProg 64 :=
.seq loopBody182_43 loopBody182_220

def loopBody182_222 : HolLoopProg 64 :=
.mark loopBody182_221

def loopBody182_223 : HolLoopProg 64 :=
.seq loopBody182_202 loopBody182_222

def loopBody182_224 : HolLoopProg 64 :=
.mark loopBody182_223

def loopBody182_225 : HolLoopProg 64 :=
.seq loopBody182_200 loopBody182_224

def loopBody182_226 : HolLoopProg 64 :=
.mark loopBody182_225

def loopBody182_227 : HolLoopProg 64 :=
.seq loopBody182_198 loopBody182_226

def loopBody182_228 : HolLoopProg 64 :=
.mark loopBody182_227

def loopBody182_229 : HolLoopProg 64 :=
.seq loopBody182_196 loopBody182_228

def loopBody182_230 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody182_231 : HolLoopProg 64 :=
.mark loopBody182_230

def loopBody182_232 : HolLoopProg 64 :=
.seq loopBody182_231 loopBody182_17

def loopBody182_233 : HolLoopProg 64 :=
.mark loopBody182_232

def loopBody182_234 : HolLoopProg 64 :=
.seq loopBody182_7 loopBody182_233

def loopBody182_235 : HolLoopProg 64 :=
.mark loopBody182_234

def loopBody182_236 : HolLoopProg 64 :=
.seq loopBody182_229 loopBody182_235

def loopBody182_237 : HolLoopProg 64 :=
.seq loopBody182_13 loopBody182_236

def loopBody182_238 : HolLoopProg 64 :=
.seq loopBody182_17 loopBody182_237

def loopBody182_239 : HolLoopProg 64 :=
.seq loopBody182_33 loopBody182_238

def output182 : Nat × List Nat × HolLoopProg 64 :=
  (246, [0, 1, 2, 3], loopBody182_239)
end InitECandidate.Proofs.FrontendStages.Loop
