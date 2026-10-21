import InitECandidate.Proofs.FrontendStages.Loop.Translate392
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody408_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody408_1 : HolLoopProg 64 :=
.mark loopBody408_0

def loopBody408_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 16#64]))

def loopBody408_3 : HolLoopProg 64 :=
.mark loopBody408_2

def loopBody408_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 232#64]))

def loopBody408_5 : HolLoopProg 64 :=
.mark loopBody408_4

def loopBody408_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody408_7 : HolLoopProg 64 :=
.mark loopBody408_6

def loopBody408_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody408_9 : HolLoopProg 64 :=
.mark loopBody408_8

def loopBody408_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody408_11 : HolLoopProg 64 :=
.mark loopBody408_10

def loopBody408_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody408_13 : HolLoopProg 64 :=
.mark loopBody408_12

def loopBody408_14 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notLower) 7 (Flapjack.RegImm.reg 8) loopBody408_11 loopBody408_13 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody408_15 : HolLoopProg 64 :=
.mark loopBody408_14

def loopBody408_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody408_17 : HolLoopProg 64 :=
.mark loopBody408_16

def loopBody408_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody408_19 : HolLoopProg 64 :=
.mark loopBody408_18

def loopBody408_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1024#64)

def loopBody408_21 : HolLoopProg 64 :=
.mark loopBody408_20

def loopBody408_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 3#64)

def loopBody408_23 : HolLoopProg 64 :=
.mark loopBody408_22

def loopBody408_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 6)

def loopBody408_25 : HolLoopProg 64 :=
.mark loopBody408_24

def loopBody408_26 : HolLoopProg 64 :=
.seq loopBody408_25 loopBody408_1

def loopBody408_27 : HolLoopProg 64 :=
.mark loopBody408_26

def loopBody408_28 : HolLoopProg 64 :=
.seq loopBody408_27 loopBody408_1

def loopBody408_29 : HolLoopProg 64 :=
.mark loopBody408_28

def loopBody408_30 : HolLoopProg 64 :=
.seq loopBody408_23 loopBody408_29

def loopBody408_31 : HolLoopProg 64 :=
.mark loopBody408_30

def loopBody408_32 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_31

def loopBody408_33 : HolLoopProg 64 :=
.mark loopBody408_32

def loopBody408_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 8#64)

def loopBody408_35 : HolLoopProg 64 :=
.mark loopBody408_34

def loopBody408_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody408_37 : HolLoopProg 64 :=
.mark loopBody408_36

def loopBody408_38 : HolLoopProg 64 :=
.seq loopBody408_35 loopBody408_37

def loopBody408_39 : HolLoopProg 64 :=
.mark loopBody408_38

def loopBody408_40 : HolLoopProg 64 :=
.seq loopBody408_33 loopBody408_39

def loopBody408_41 : HolLoopProg 64 :=
.mark loopBody408_40

def loopBody408_42 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody408_41 loopBody408_1 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody408_43 : HolLoopProg 64 :=
.mark loopBody408_42

def loopBody408_44 : HolLoopProg 64 :=
.seq loopBody408_43 loopBody408_1

def loopBody408_45 : HolLoopProg 64 :=
.mark loopBody408_44

def loopBody408_46 : HolLoopProg 64 :=
.seq loopBody408_17 loopBody408_45

def loopBody408_47 : HolLoopProg 64 :=
.mark loopBody408_46

def loopBody408_48 : HolLoopProg 64 :=
.seq loopBody408_15 loopBody408_47

def loopBody408_49 : HolLoopProg 64 :=
.mark loopBody408_48

def loopBody408_50 : HolLoopProg 64 :=
.seq loopBody408_21 loopBody408_49

def loopBody408_51 : HolLoopProg 64 :=
.mark loopBody408_50

def loopBody408_52 : HolLoopProg 64 :=
.seq loopBody408_19 loopBody408_51

def loopBody408_53 : HolLoopProg 64 :=
.mark loopBody408_52

def loopBody408_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.const 1#64))

def loopBody408_55 : HolLoopProg 64 :=
.mark loopBody408_54

def loopBody408_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 6)

def loopBody408_57 : HolLoopProg 64 :=
.mark loopBody408_56

def loopBody408_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody408_59 : HolLoopProg 64 :=
.mark loopBody408_58

def loopBody408_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody408_61 : HolLoopProg 64 :=
.mark loopBody408_60

def loopBody408_62 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 8 (Flapjack.RegImm.reg 9) loopBody408_59 loopBody408_61 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody408_63 : HolLoopProg 64 :=
.mark loopBody408_62

def loopBody408_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody408_65 : HolLoopProg 64 :=
.mark loopBody408_64

def loopBody408_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1024#64)

def loopBody408_67 : HolLoopProg 64 :=
.mark loopBody408_66

def loopBody408_68 : HolLoopProg 64 :=
.seq loopBody408_67 loopBody408_1

def loopBody408_69 : HolLoopProg 64 :=
.mark loopBody408_68

def loopBody408_70 : HolLoopProg 64 :=
.seq loopBody408_69 loopBody408_1

def loopBody408_71 : HolLoopProg 64 :=
.mark loopBody408_70

def loopBody408_72 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody408_71 loopBody408_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody408_73 : HolLoopProg 64 :=
.mark loopBody408_72

def loopBody408_74 : HolLoopProg 64 :=
.seq loopBody408_73 loopBody408_1

def loopBody408_75 : HolLoopProg 64 :=
.mark loopBody408_74

def loopBody408_76 : HolLoopProg 64 :=
.seq loopBody408_65 loopBody408_75

def loopBody408_77 : HolLoopProg 64 :=
.mark loopBody408_76

def loopBody408_78 : HolLoopProg 64 :=
.seq loopBody408_63 loopBody408_77

def loopBody408_79 : HolLoopProg 64 :=
.mark loopBody408_78

def loopBody408_80 : HolLoopProg 64 :=
.seq loopBody408_57 loopBody408_79

def loopBody408_81 : HolLoopProg 64 :=
.mark loopBody408_80

def loopBody408_82 : HolLoopProg 64 :=
.seq loopBody408_21 loopBody408_81

def loopBody408_83 : HolLoopProg 64 :=
.mark loopBody408_82

def loopBody408_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 6) (Flapjack.HolLoopExp.const 5#64))

def loopBody408_85 : HolLoopProg 64 :=
.mark loopBody408_84

def loopBody408_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody408_87 : HolLoopProg 64 :=
.mark loopBody408_86

def loopBody408_88 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 74) ([8]) (some (8, loopBody408_87, loopBody408_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody408_89 : HolLoopProg 64 :=
.mark loopBody408_88

def loopBody408_90 : HolLoopProg 64 :=
.seq loopBody408_89 loopBody408_1

def loopBody408_91 : HolLoopProg 64 :=
.mark loopBody408_90

def loopBody408_92 : HolLoopProg 64 :=
.seq loopBody408_85 loopBody408_91

def loopBody408_93 : HolLoopProg 64 :=
.mark loopBody408_92

def loopBody408_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody408_95 : HolLoopProg 64 :=
.mark loopBody408_94

def loopBody408_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64))

def loopBody408_97 : HolLoopProg 64 :=
.mark loopBody408_96

def loopBody408_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody408_99 : HolLoopProg 64 :=
.mark loopBody408_98

def loopBody408_100 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 77) ([9, 10, 11]) (some (9, loopBody408_99, loopBody408_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody408_101 : HolLoopProg 64 :=
.mark loopBody408_100

def loopBody408_102 : HolLoopProg 64 :=
.seq loopBody408_101 loopBody408_1

def loopBody408_103 : HolLoopProg 64 :=
.mark loopBody408_102

def loopBody408_104 : HolLoopProg 64 :=
.seq loopBody408_97 loopBody408_103

def loopBody408_105 : HolLoopProg 64 :=
.mark loopBody408_104

def loopBody408_106 : HolLoopProg 64 :=
.seq loopBody408_95 loopBody408_105

def loopBody408_107 : HolLoopProg 64 :=
.mark loopBody408_106

def loopBody408_108 : HolLoopProg 64 :=
.seq loopBody408_17 loopBody408_107

def loopBody408_109 : HolLoopProg 64 :=
.mark loopBody408_108

def loopBody408_110 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_109

def loopBody408_111 : HolLoopProg 64 :=
.mark loopBody408_110

def loopBody408_112 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_111

def loopBody408_113 : HolLoopProg 64 :=
.mark loopBody408_112

def loopBody408_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 8#64])

def loopBody408_115 : HolLoopProg 64 :=
.mark loopBody408_114

def loopBody408_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 9)

def loopBody408_117 : HolLoopProg 64 :=
.mark loopBody408_116

def loopBody408_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 8) 10

def loopBody408_119 : HolLoopProg 64 :=
.mark loopBody408_118

def loopBody408_120 : HolLoopProg 64 :=
.seq loopBody408_119 loopBody408_1

def loopBody408_121 : HolLoopProg 64 :=
.mark loopBody408_120

def loopBody408_122 : HolLoopProg 64 :=
.seq loopBody408_117 loopBody408_121

def loopBody408_123 : HolLoopProg 64 :=
.mark loopBody408_122

def loopBody408_124 : HolLoopProg 64 :=
.seq loopBody408_123 loopBody408_1

def loopBody408_125 : HolLoopProg 64 :=
.mark loopBody408_124

def loopBody408_126 : HolLoopProg 64 :=
.seq loopBody408_17 loopBody408_125

def loopBody408_127 : HolLoopProg 64 :=
.mark loopBody408_126

def loopBody408_128 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_127

def loopBody408_129 : HolLoopProg 64 :=
.mark loopBody408_128

def loopBody408_130 : HolLoopProg 64 :=
.seq loopBody408_115 loopBody408_129

def loopBody408_131 : HolLoopProg 64 :=
.mark loopBody408_130

def loopBody408_132 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_131

def loopBody408_133 : HolLoopProg 64 :=
.mark loopBody408_132

def loopBody408_134 : HolLoopProg 64 :=
.seq loopBody408_113 loopBody408_133

def loopBody408_135 : HolLoopProg 64 :=
.mark loopBody408_134

def loopBody408_136 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 232#64])

def loopBody408_137 : HolLoopProg 64 :=
.mark loopBody408_136

def loopBody408_138 : HolLoopProg 64 :=
.seq loopBody408_57 loopBody408_125

def loopBody408_139 : HolLoopProg 64 :=
.mark loopBody408_138

def loopBody408_140 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_139

def loopBody408_141 : HolLoopProg 64 :=
.mark loopBody408_140

def loopBody408_142 : HolLoopProg 64 :=
.seq loopBody408_137 loopBody408_141

def loopBody408_143 : HolLoopProg 64 :=
.mark loopBody408_142

def loopBody408_144 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_143

def loopBody408_145 : HolLoopProg 64 :=
.mark loopBody408_144

def loopBody408_146 : HolLoopProg 64 :=
.seq loopBody408_135 loopBody408_145

def loopBody408_147 : HolLoopProg 64 :=
.mark loopBody408_146

def loopBody408_148 : HolLoopProg 64 :=
.seq loopBody408_93 loopBody408_147

def loopBody408_149 : HolLoopProg 64 :=
.mark loopBody408_148

def loopBody408_150 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_149

def loopBody408_151 : HolLoopProg 64 :=
.mark loopBody408_150

def loopBody408_152 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_151

def loopBody408_153 : HolLoopProg 64 :=
.mark loopBody408_152

def loopBody408_154 : HolLoopProg 64 :=
.seq loopBody408_83 loopBody408_153

def loopBody408_155 : HolLoopProg 64 :=
.mark loopBody408_154

def loopBody408_156 : HolLoopProg 64 :=
.seq loopBody408_55 loopBody408_155

def loopBody408_157 : HolLoopProg 64 :=
.mark loopBody408_156

def loopBody408_158 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_157

def loopBody408_159 : HolLoopProg 64 :=
.mark loopBody408_158

def loopBody408_160 : HolLoopProg 64 :=
.seq loopBody408_53 loopBody408_159

def loopBody408_161 : HolLoopProg 64 :=
.mark loopBody408_160

def loopBody408_162 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody408_161 loopBody408_1 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody408_163 : HolLoopProg 64 :=
.mark loopBody408_162

def loopBody408_164 : HolLoopProg 64 :=
.seq loopBody408_163 loopBody408_1

def loopBody408_165 : HolLoopProg 64 :=
.mark loopBody408_164

def loopBody408_166 : HolLoopProg 64 :=
.seq loopBody408_17 loopBody408_165

def loopBody408_167 : HolLoopProg 64 :=
.mark loopBody408_166

def loopBody408_168 : HolLoopProg 64 :=
.seq loopBody408_15 loopBody408_167

def loopBody408_169 : HolLoopProg 64 :=
.mark loopBody408_168

def loopBody408_170 : HolLoopProg 64 :=
.seq loopBody408_9 loopBody408_169

def loopBody408_171 : HolLoopProg 64 :=
.mark loopBody408_170

def loopBody408_172 : HolLoopProg 64 :=
.seq loopBody408_7 loopBody408_171

def loopBody408_173 : HolLoopProg 64 :=
.mark loopBody408_172

def loopBody408_174 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 7 (Flapjack.RegImm.reg 8) loopBody408_11 loopBody408_13 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody408_175 : HolLoopProg 64 :=
.mark loopBody408_174

def loopBody408_176 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody408_41 loopBody408_1 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody408_177 : HolLoopProg 64 :=
.mark loopBody408_176

def loopBody408_178 : HolLoopProg 64 :=
.seq loopBody408_177 loopBody408_1

def loopBody408_179 : HolLoopProg 64 :=
.mark loopBody408_178

def loopBody408_180 : HolLoopProg 64 :=
.seq loopBody408_17 loopBody408_179

def loopBody408_181 : HolLoopProg 64 :=
.mark loopBody408_180

def loopBody408_182 : HolLoopProg 64 :=
.seq loopBody408_175 loopBody408_181

def loopBody408_183 : HolLoopProg 64 :=
.mark loopBody408_182

def loopBody408_184 : HolLoopProg 64 :=
.seq loopBody408_21 loopBody408_183

def loopBody408_185 : HolLoopProg 64 :=
.mark loopBody408_184

def loopBody408_186 : HolLoopProg 64 :=
.seq loopBody408_7 loopBody408_185

def loopBody408_187 : HolLoopProg 64 :=
.mark loopBody408_186

def loopBody408_188 : HolLoopProg 64 :=
.seq loopBody408_173 loopBody408_187

def loopBody408_189 : HolLoopProg 64 :=
.mark loopBody408_188

def loopBody408_190 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 8#64]),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)])

def loopBody408_191 : HolLoopProg 64 :=
.mark loopBody408_190

def loopBody408_192 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 0)

def loopBody408_193 : HolLoopProg 64 :=
.mark loopBody408_192

def loopBody408_194 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody408_195 : HolLoopProg 64 :=
.mark loopBody408_194

def loopBody408_196 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 2)

def loopBody408_197 : HolLoopProg 64 :=
.mark loopBody408_196

def loopBody408_198 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 3)

def loopBody408_199 : HolLoopProg 64 :=
.mark loopBody408_198

def loopBody408_200 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 7)

def loopBody408_201 : HolLoopProg 64 :=
.mark loopBody408_200

def loopBody408_202 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 6) 11

def loopBody408_203 : HolLoopProg 64 :=
.mark loopBody408_202

def loopBody408_204 : HolLoopProg 64 :=
.seq loopBody408_203 loopBody408_1

def loopBody408_205 : HolLoopProg 64 :=
.mark loopBody408_204

def loopBody408_206 : HolLoopProg 64 :=
.seq loopBody408_201 loopBody408_205

def loopBody408_207 : HolLoopProg 64 :=
.mark loopBody408_206

def loopBody408_208 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 8)

def loopBody408_209 : HolLoopProg 64 :=
.mark loopBody408_208

def loopBody408_210 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 8#64]) 11

def loopBody408_211 : HolLoopProg 64 :=
.mark loopBody408_210

def loopBody408_212 : HolLoopProg 64 :=
.seq loopBody408_211 loopBody408_1

def loopBody408_213 : HolLoopProg 64 :=
.mark loopBody408_212

def loopBody408_214 : HolLoopProg 64 :=
.seq loopBody408_209 loopBody408_213

def loopBody408_215 : HolLoopProg 64 :=
.mark loopBody408_214

def loopBody408_216 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody408_217 : HolLoopProg 64 :=
.mark loopBody408_216

def loopBody408_218 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 16#64]) 11

def loopBody408_219 : HolLoopProg 64 :=
.mark loopBody408_218

def loopBody408_220 : HolLoopProg 64 :=
.seq loopBody408_219 loopBody408_1

def loopBody408_221 : HolLoopProg 64 :=
.mark loopBody408_220

def loopBody408_222 : HolLoopProg 64 :=
.seq loopBody408_217 loopBody408_221

def loopBody408_223 : HolLoopProg 64 :=
.mark loopBody408_222

def loopBody408_224 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 10)

def loopBody408_225 : HolLoopProg 64 :=
.mark loopBody408_224

def loopBody408_226 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 24#64]) 11

def loopBody408_227 : HolLoopProg 64 :=
.mark loopBody408_226

def loopBody408_228 : HolLoopProg 64 :=
.seq loopBody408_227 loopBody408_1

def loopBody408_229 : HolLoopProg 64 :=
.mark loopBody408_228

def loopBody408_230 : HolLoopProg 64 :=
.seq loopBody408_225 loopBody408_229

def loopBody408_231 : HolLoopProg 64 :=
.mark loopBody408_230

def loopBody408_232 : HolLoopProg 64 :=
.seq loopBody408_231 loopBody408_1

def loopBody408_233 : HolLoopProg 64 :=
.mark loopBody408_232

def loopBody408_234 : HolLoopProg 64 :=
.seq loopBody408_223 loopBody408_233

def loopBody408_235 : HolLoopProg 64 :=
.mark loopBody408_234

def loopBody408_236 : HolLoopProg 64 :=
.seq loopBody408_215 loopBody408_235

def loopBody408_237 : HolLoopProg 64 :=
.mark loopBody408_236

def loopBody408_238 : HolLoopProg 64 :=
.seq loopBody408_207 loopBody408_237

def loopBody408_239 : HolLoopProg 64 :=
.mark loopBody408_238

def loopBody408_240 : HolLoopProg 64 :=
.seq loopBody408_199 loopBody408_239

def loopBody408_241 : HolLoopProg 64 :=
.mark loopBody408_240

def loopBody408_242 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_241

def loopBody408_243 : HolLoopProg 64 :=
.mark loopBody408_242

def loopBody408_244 : HolLoopProg 64 :=
.seq loopBody408_197 loopBody408_243

def loopBody408_245 : HolLoopProg 64 :=
.mark loopBody408_244

def loopBody408_246 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_245

def loopBody408_247 : HolLoopProg 64 :=
.mark loopBody408_246

def loopBody408_248 : HolLoopProg 64 :=
.seq loopBody408_195 loopBody408_247

def loopBody408_249 : HolLoopProg 64 :=
.mark loopBody408_248

def loopBody408_250 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_249

def loopBody408_251 : HolLoopProg 64 :=
.mark loopBody408_250

def loopBody408_252 : HolLoopProg 64 :=
.seq loopBody408_193 loopBody408_251

def loopBody408_253 : HolLoopProg 64 :=
.mark loopBody408_252

def loopBody408_254 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_253

def loopBody408_255 : HolLoopProg 64 :=
.mark loopBody408_254

def loopBody408_256 : HolLoopProg 64 :=
.seq loopBody408_191 loopBody408_255

def loopBody408_257 : HolLoopProg 64 :=
.mark loopBody408_256

def loopBody408_258 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_257

def loopBody408_259 : HolLoopProg 64 :=
.mark loopBody408_258

def loopBody408_260 : HolLoopProg 64 :=
.seq loopBody408_189 loopBody408_259

def loopBody408_261 : HolLoopProg 64 :=
.mark loopBody408_260

def loopBody408_262 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 16#64])

def loopBody408_263 : HolLoopProg 64 :=
.mark loopBody408_262

def loopBody408_264 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])

def loopBody408_265 : HolLoopProg 64 :=
.mark loopBody408_264

def loopBody408_266 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 7)

def loopBody408_267 : HolLoopProg 64 :=
.mark loopBody408_266

def loopBody408_268 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 6) 8

def loopBody408_269 : HolLoopProg 64 :=
.mark loopBody408_268

def loopBody408_270 : HolLoopProg 64 :=
.seq loopBody408_269 loopBody408_1

def loopBody408_271 : HolLoopProg 64 :=
.mark loopBody408_270

def loopBody408_272 : HolLoopProg 64 :=
.seq loopBody408_267 loopBody408_271

def loopBody408_273 : HolLoopProg 64 :=
.mark loopBody408_272

def loopBody408_274 : HolLoopProg 64 :=
.seq loopBody408_273 loopBody408_1

def loopBody408_275 : HolLoopProg 64 :=
.mark loopBody408_274

def loopBody408_276 : HolLoopProg 64 :=
.seq loopBody408_265 loopBody408_275

def loopBody408_277 : HolLoopProg 64 :=
.mark loopBody408_276

def loopBody408_278 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_277

def loopBody408_279 : HolLoopProg 64 :=
.mark loopBody408_278

def loopBody408_280 : HolLoopProg 64 :=
.seq loopBody408_263 loopBody408_279

def loopBody408_281 : HolLoopProg 64 :=
.mark loopBody408_280

def loopBody408_282 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_281

def loopBody408_283 : HolLoopProg 64 :=
.mark loopBody408_282

def loopBody408_284 : HolLoopProg 64 :=
.seq loopBody408_261 loopBody408_283

def loopBody408_285 : HolLoopProg 64 :=
.mark loopBody408_284

def loopBody408_286 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody408_287 : HolLoopProg 64 :=
.mark loopBody408_286

def loopBody408_288 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody408_289 : HolLoopProg 64 :=
.mark loopBody408_288

def loopBody408_290 : HolLoopProg 64 :=
.seq loopBody408_289 loopBody408_1

def loopBody408_291 : HolLoopProg 64 :=
.mark loopBody408_290

def loopBody408_292 : HolLoopProg 64 :=
.seq loopBody408_287 loopBody408_291

def loopBody408_293 : HolLoopProg 64 :=
.mark loopBody408_292

def loopBody408_294 : HolLoopProg 64 :=
.seq loopBody408_285 loopBody408_293

def loopBody408_295 : HolLoopProg 64 :=
.mark loopBody408_294

def loopBody408_296 : HolLoopProg 64 :=
.seq loopBody408_5 loopBody408_295

def loopBody408_297 : HolLoopProg 64 :=
.mark loopBody408_296

def loopBody408_298 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_297

def loopBody408_299 : HolLoopProg 64 :=
.mark loopBody408_298

def loopBody408_300 : HolLoopProg 64 :=
.seq loopBody408_3 loopBody408_299

def loopBody408_301 : HolLoopProg 64 :=
.mark loopBody408_300

def loopBody408_302 : HolLoopProg 64 :=
.seq loopBody408_1 loopBody408_301

def loopBody408_303 : HolLoopProg 64 :=
.mark loopBody408_302

def output408 : Nat × List Nat × HolLoopProg 64 :=
  (472, [0, 1, 2, 3], loopBody408_303)
end InitECandidate.Proofs.FrontendStages.Loop
