import InitECandidate.Proofs.FrontendStages.Loop.Translate230
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody246_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody246_1 : HolLoopProg 64 :=
.mark loopBody246_0

def loopBody246_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 32#64]))

def loopBody246_3 : HolLoopProg 64 :=
.mark loopBody246_2

def loopBody246_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 40#64]))

def loopBody246_5 : HolLoopProg 64 :=
.mark loopBody246_4

def loopBody246_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 48#64]))

def loopBody246_7 : HolLoopProg 64 :=
.mark loopBody246_6

def loopBody246_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody246_9 : HolLoopProg 64 :=
.mark loopBody246_8

def loopBody246_10 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 294) ([]) (some (10, loopBody246_9, loopBody246_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody246_11 : HolLoopProg 64 :=
.mark loopBody246_10

def loopBody246_12 : HolLoopProg 64 :=
.seq loopBody246_11 loopBody246_1

def loopBody246_13 : HolLoopProg 64 :=
.mark loopBody246_12

def loopBody246_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.var 5])

def loopBody246_15 : HolLoopProg 64 :=
.mark loopBody246_14

def loopBody246_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 10)

def loopBody246_17 : HolLoopProg 64 :=
.mark loopBody246_16

def loopBody246_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 1#64)

def loopBody246_19 : HolLoopProg 64 :=
.mark loopBody246_18

def loopBody246_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody246_21 : HolLoopProg 64 :=
.mark loopBody246_20

def loopBody246_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 0#64)

def loopBody246_23 : HolLoopProg 64 :=
.mark loopBody246_22

def loopBody246_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.RegImm.reg 13) loopBody246_21 loopBody246_23 (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit)))

def loopBody246_25 : HolLoopProg 64 :=
.mark loopBody246_24

def loopBody246_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 12)

def loopBody246_27 : HolLoopProg 64 :=
.mark loopBody246_26

def loopBody246_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.var 5])

def loopBody246_29 : HolLoopProg 64 :=
.mark loopBody246_28

def loopBody246_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 11 11

def loopBody246_31 : HolLoopProg 64 :=
.mark loopBody246_30

def loopBody246_32 : HolLoopProg 64 :=
.seq loopBody246_31 loopBody246_1

def loopBody246_33 : HolLoopProg 64 :=
.mark loopBody246_32

def loopBody246_34 : HolLoopProg 64 :=
.seq loopBody246_29 loopBody246_33

def loopBody246_35 : HolLoopProg 64 :=
.mark loopBody246_34

def loopBody246_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 9, Flapjack.HolLoopExp.const 32#64,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 11) (Flapjack.HolLoopExp.const 3#64)])

def loopBody246_37 : HolLoopProg 64 :=
.mark loopBody246_36

def loopBody246_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 8)

def loopBody246_39 : HolLoopProg 64 :=
.mark loopBody246_38

def loopBody246_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 13)

def loopBody246_41 : HolLoopProg 64 :=
.mark loopBody246_40

def loopBody246_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 12) 14

def loopBody246_43 : HolLoopProg 64 :=
.mark loopBody246_42

def loopBody246_44 : HolLoopProg 64 :=
.seq loopBody246_43 loopBody246_1

def loopBody246_45 : HolLoopProg 64 :=
.mark loopBody246_44

def loopBody246_46 : HolLoopProg 64 :=
.seq loopBody246_41 loopBody246_45

def loopBody246_47 : HolLoopProg 64 :=
.mark loopBody246_46

def loopBody246_48 : HolLoopProg 64 :=
.seq loopBody246_47 loopBody246_1

def loopBody246_49 : HolLoopProg 64 :=
.mark loopBody246_48

def loopBody246_50 : HolLoopProg 64 :=
.seq loopBody246_39 loopBody246_49

def loopBody246_51 : HolLoopProg 64 :=
.mark loopBody246_50

def loopBody246_52 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_51

def loopBody246_53 : HolLoopProg 64 :=
.mark loopBody246_52

def loopBody246_54 : HolLoopProg 64 :=
.seq loopBody246_37 loopBody246_53

def loopBody246_55 : HolLoopProg 64 :=
.mark loopBody246_54

def loopBody246_56 : HolLoopProg 64 :=
.seq loopBody246_35 loopBody246_55

def loopBody246_57 : HolLoopProg 64 :=
.mark loopBody246_56

def loopBody246_58 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.RegImm.imm 0#64) loopBody246_57 loopBody246_1 (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit)))

def loopBody246_59 : HolLoopProg 64 :=
.mark loopBody246_58

def loopBody246_60 : HolLoopProg 64 :=
.seq loopBody246_59 loopBody246_1

def loopBody246_61 : HolLoopProg 64 :=
.mark loopBody246_60

def loopBody246_62 : HolLoopProg 64 :=
.seq loopBody246_27 loopBody246_61

def loopBody246_63 : HolLoopProg 64 :=
.mark loopBody246_62

def loopBody246_64 : HolLoopProg 64 :=
.seq loopBody246_25 loopBody246_63

def loopBody246_65 : HolLoopProg 64 :=
.mark loopBody246_64

def loopBody246_66 : HolLoopProg 64 :=
.seq loopBody246_19 loopBody246_65

def loopBody246_67 : HolLoopProg 64 :=
.mark loopBody246_66

def loopBody246_68 : HolLoopProg 64 :=
.seq loopBody246_17 loopBody246_67

def loopBody246_69 : HolLoopProg 64 :=
.mark loopBody246_68

def loopBody246_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 10)

def loopBody246_71 : HolLoopProg 64 :=
.mark loopBody246_70

def loopBody246_72 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 12 (Flapjack.RegImm.reg 13) loopBody246_21 loopBody246_23 (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit)))

def loopBody246_73 : HolLoopProg 64 :=
.mark loopBody246_72

def loopBody246_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 1#64])

def loopBody246_75 : HolLoopProg 64 :=
.mark loopBody246_74

def loopBody246_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 10, Flapjack.HolLoopExp.const 1#64])

def loopBody246_77 : HolLoopProg 64 :=
.mark loopBody246_76

def loopBody246_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 8)

def loopBody246_79 : HolLoopProg 64 :=
.mark loopBody246_78

def loopBody246_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 12

def loopBody246_81 : HolLoopProg 64 :=
.mark loopBody246_80

def loopBody246_82 : HolLoopProg 64 :=
.call (some
  ([11],
    Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))) (some 293) ([12, 13, 14]) (some (12, loopBody246_81, loopBody246_1, (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))))

def loopBody246_83 : HolLoopProg 64 :=
.mark loopBody246_82

def loopBody246_84 : HolLoopProg 64 :=
.seq loopBody246_83 loopBody246_1

def loopBody246_85 : HolLoopProg 64 :=
.mark loopBody246_84

def loopBody246_86 : HolLoopProg 64 :=
.seq loopBody246_79 loopBody246_85

def loopBody246_87 : HolLoopProg 64 :=
.mark loopBody246_86

def loopBody246_88 : HolLoopProg 64 :=
.seq loopBody246_77 loopBody246_87

def loopBody246_89 : HolLoopProg 64 :=
.mark loopBody246_88

def loopBody246_90 : HolLoopProg 64 :=
.seq loopBody246_75 loopBody246_89

def loopBody246_91 : HolLoopProg 64 :=
.mark loopBody246_90

def loopBody246_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.var 5])

def loopBody246_93 : HolLoopProg 64 :=
.mark loopBody246_92

def loopBody246_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 12 12

def loopBody246_95 : HolLoopProg 64 :=
.mark loopBody246_94

def loopBody246_96 : HolLoopProg 64 :=
.seq loopBody246_95 loopBody246_1

def loopBody246_97 : HolLoopProg 64 :=
.mark loopBody246_96

def loopBody246_98 : HolLoopProg 64 :=
.seq loopBody246_93 loopBody246_97

def loopBody246_99 : HolLoopProg 64 :=
.mark loopBody246_98

def loopBody246_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 9, Flapjack.HolLoopExp.const 32#64,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 12) (Flapjack.HolLoopExp.const 3#64)])

def loopBody246_101 : HolLoopProg 64 :=
.mark loopBody246_100

def loopBody246_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 11)

def loopBody246_103 : HolLoopProg 64 :=
.mark loopBody246_102

def loopBody246_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 14)

def loopBody246_105 : HolLoopProg 64 :=
.mark loopBody246_104

def loopBody246_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 13) 15

def loopBody246_107 : HolLoopProg 64 :=
.mark loopBody246_106

def loopBody246_108 : HolLoopProg 64 :=
.seq loopBody246_107 loopBody246_1

def loopBody246_109 : HolLoopProg 64 :=
.mark loopBody246_108

def loopBody246_110 : HolLoopProg 64 :=
.seq loopBody246_105 loopBody246_109

def loopBody246_111 : HolLoopProg 64 :=
.mark loopBody246_110

def loopBody246_112 : HolLoopProg 64 :=
.seq loopBody246_111 loopBody246_1

def loopBody246_113 : HolLoopProg 64 :=
.mark loopBody246_112

def loopBody246_114 : HolLoopProg 64 :=
.seq loopBody246_103 loopBody246_113

def loopBody246_115 : HolLoopProg 64 :=
.mark loopBody246_114

def loopBody246_116 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_115

def loopBody246_117 : HolLoopProg 64 :=
.mark loopBody246_116

def loopBody246_118 : HolLoopProg 64 :=
.seq loopBody246_101 loopBody246_117

def loopBody246_119 : HolLoopProg 64 :=
.mark loopBody246_118

def loopBody246_120 : HolLoopProg 64 :=
.seq loopBody246_99 loopBody246_119

def loopBody246_121 : HolLoopProg 64 :=
.mark loopBody246_120

def loopBody246_122 : HolLoopProg 64 :=
.seq loopBody246_91 loopBody246_121

def loopBody246_123 : HolLoopProg 64 :=
.mark loopBody246_122

def loopBody246_124 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_123

def loopBody246_125 : HolLoopProg 64 :=
.mark loopBody246_124

def loopBody246_126 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_125

def loopBody246_127 : HolLoopProg 64 :=
.mark loopBody246_126

def loopBody246_128 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.RegImm.imm 0#64) loopBody246_127 loopBody246_1 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit)))

def loopBody246_129 : HolLoopProg 64 :=
.mark loopBody246_128

def loopBody246_130 : HolLoopProg 64 :=
.seq loopBody246_129 loopBody246_1

def loopBody246_131 : HolLoopProg 64 :=
.mark loopBody246_130

def loopBody246_132 : HolLoopProg 64 :=
.seq loopBody246_27 loopBody246_131

def loopBody246_133 : HolLoopProg 64 :=
.mark loopBody246_132

def loopBody246_134 : HolLoopProg 64 :=
.seq loopBody246_73 loopBody246_133

def loopBody246_135 : HolLoopProg 64 :=
.mark loopBody246_134

def loopBody246_136 : HolLoopProg 64 :=
.seq loopBody246_71 loopBody246_135

def loopBody246_137 : HolLoopProg 64 :=
.mark loopBody246_136

def loopBody246_138 : HolLoopProg 64 :=
.seq loopBody246_21 loopBody246_137

def loopBody246_139 : HolLoopProg 64 :=
.mark loopBody246_138

def loopBody246_140 : HolLoopProg 64 :=
.seq loopBody246_69 loopBody246_139

def loopBody246_141 : HolLoopProg 64 :=
.mark loopBody246_140

def loopBody246_142 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 5])

def loopBody246_143 : HolLoopProg 64 :=
.mark loopBody246_142

def loopBody246_144 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 11)

def loopBody246_145 : HolLoopProg 64 :=
.mark loopBody246_144

def loopBody246_146 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 0#64)

def loopBody246_147 : HolLoopProg 64 :=
.mark loopBody246_146

def loopBody246_148 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 0#64)

def loopBody246_149 : HolLoopProg 64 :=
.mark loopBody246_148

def loopBody246_150 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 13 (Flapjack.RegImm.reg 14) loopBody246_19 loopBody246_149 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))

def loopBody246_151 : HolLoopProg 64 :=
.mark loopBody246_150

def loopBody246_152 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 13)

def loopBody246_153 : HolLoopProg 64 :=
.mark loopBody246_152

def loopBody246_154 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 9, Flapjack.HolLoopExp.const 160#64])

def loopBody246_155 : HolLoopProg 64 :=
.mark loopBody246_154

def loopBody246_156 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 3)

def loopBody246_157 : HolLoopProg 64 :=
.mark loopBody246_156

def loopBody246_158 : HolLoopProg 64 :=
.seq loopBody246_157 loopBody246_49

def loopBody246_159 : HolLoopProg 64 :=
.mark loopBody246_158

def loopBody246_160 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_159

def loopBody246_161 : HolLoopProg 64 :=
.mark loopBody246_160

def loopBody246_162 : HolLoopProg 64 :=
.seq loopBody246_155 loopBody246_161

def loopBody246_163 : HolLoopProg 64 :=
.mark loopBody246_162

def loopBody246_164 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_163

def loopBody246_165 : HolLoopProg 64 :=
.mark loopBody246_164

def loopBody246_166 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 9, Flapjack.HolLoopExp.const 168#64])

def loopBody246_167 : HolLoopProg 64 :=
.mark loopBody246_166

def loopBody246_168 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 4)

def loopBody246_169 : HolLoopProg 64 :=
.mark loopBody246_168

def loopBody246_170 : HolLoopProg 64 :=
.seq loopBody246_169 loopBody246_49

def loopBody246_171 : HolLoopProg 64 :=
.mark loopBody246_170

def loopBody246_172 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_171

def loopBody246_173 : HolLoopProg 64 :=
.mark loopBody246_172

def loopBody246_174 : HolLoopProg 64 :=
.seq loopBody246_167 loopBody246_173

def loopBody246_175 : HolLoopProg 64 :=
.mark loopBody246_174

def loopBody246_176 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_175

def loopBody246_177 : HolLoopProg 64 :=
.mark loopBody246_176

def loopBody246_178 : HolLoopProg 64 :=
.seq loopBody246_165 loopBody246_177

def loopBody246_179 : HolLoopProg 64 :=
.mark loopBody246_178

def loopBody246_180 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 5])

def loopBody246_181 : HolLoopProg 64 :=
.mark loopBody246_180

def loopBody246_182 : HolLoopProg 64 :=
.seq loopBody246_181 loopBody246_97

def loopBody246_183 : HolLoopProg 64 :=
.mark loopBody246_182

def loopBody246_184 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 12)

def loopBody246_185 : HolLoopProg 64 :=
.mark loopBody246_184

def loopBody246_186 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 9, Flapjack.HolLoopExp.const 32#64,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 13) (Flapjack.HolLoopExp.const 3#64)]))

def loopBody246_187 : HolLoopProg 64 :=
.mark loopBody246_186

def loopBody246_188 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.const 0#64)

def loopBody246_189 : HolLoopProg 64 :=
.mark loopBody246_188

def loopBody246_190 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 1#64)

def loopBody246_191 : HolLoopProg 64 :=
.mark loopBody246_190

def loopBody246_192 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 0#64)

def loopBody246_193 : HolLoopProg 64 :=
.mark loopBody246_192

def loopBody246_194 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 15 (Flapjack.RegImm.reg 16) loopBody246_191 loopBody246_193 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody246_195 : HolLoopProg 64 :=
.mark loopBody246_194

def loopBody246_196 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 15)

def loopBody246_197 : HolLoopProg 64 :=
.mark loopBody246_196

def loopBody246_198 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 11#64)

def loopBody246_199 : HolLoopProg 64 :=
.mark loopBody246_198

def loopBody246_200 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 15

def loopBody246_201 : HolLoopProg 64 :=
.mark loopBody246_200

def loopBody246_202 : HolLoopProg 64 :=
.call (some
  ([14],
    Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))) (some 282) ([15]) (some (15, loopBody246_201, loopBody246_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))))

def loopBody246_203 : HolLoopProg 64 :=
.mark loopBody246_202

def loopBody246_204 : HolLoopProg 64 :=
.seq loopBody246_203 loopBody246_1

def loopBody246_205 : HolLoopProg 64 :=
.mark loopBody246_204

def loopBody246_206 : HolLoopProg 64 :=
.seq loopBody246_199 loopBody246_205

def loopBody246_207 : HolLoopProg 64 :=
.mark loopBody246_206

def loopBody246_208 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_207

def loopBody246_209 : HolLoopProg 64 :=
.mark loopBody246_208

def loopBody246_210 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_209

def loopBody246_211 : HolLoopProg 64 :=
.mark loopBody246_210

def loopBody246_212 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 17 (Flapjack.RegImm.imm 0#64) loopBody246_211 loopBody246_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))

def loopBody246_213 : HolLoopProg 64 :=
.mark loopBody246_212

def loopBody246_214 : HolLoopProg 64 :=
.seq loopBody246_213 loopBody246_1

def loopBody246_215 : HolLoopProg 64 :=
.mark loopBody246_214

def loopBody246_216 : HolLoopProg 64 :=
.seq loopBody246_197 loopBody246_215

def loopBody246_217 : HolLoopProg 64 :=
.mark loopBody246_216

def loopBody246_218 : HolLoopProg 64 :=
.seq loopBody246_195 loopBody246_217

def loopBody246_219 : HolLoopProg 64 :=
.mark loopBody246_218

def loopBody246_220 : HolLoopProg 64 :=
.seq loopBody246_189 loopBody246_219

def loopBody246_221 : HolLoopProg 64 :=
.mark loopBody246_220

def loopBody246_222 : HolLoopProg 64 :=
.seq loopBody246_187 loopBody246_221

def loopBody246_223 : HolLoopProg 64 :=
.mark loopBody246_222

def loopBody246_224 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 1#64])

def loopBody246_225 : HolLoopProg 64 :=
.mark loopBody246_224

def loopBody246_226 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 11, Flapjack.HolLoopExp.const 1#64])

def loopBody246_227 : HolLoopProg 64 :=
.mark loopBody246_226

def loopBody246_228 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 3)

def loopBody246_229 : HolLoopProg 64 :=
.mark loopBody246_228

def loopBody246_230 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 4)

def loopBody246_231 : HolLoopProg 64 :=
.mark loopBody246_230

def loopBody246_232 : HolLoopProg 64 :=
.call (some
  ([14],
    Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))) (some 292) ([15, 16, 17, 18]) (some (15, loopBody246_201, loopBody246_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))

def loopBody246_233 : HolLoopProg 64 :=
.mark loopBody246_232

def loopBody246_234 : HolLoopProg 64 :=
.seq loopBody246_233 loopBody246_1

def loopBody246_235 : HolLoopProg 64 :=
.mark loopBody246_234

def loopBody246_236 : HolLoopProg 64 :=
.seq loopBody246_231 loopBody246_235

def loopBody246_237 : HolLoopProg 64 :=
.mark loopBody246_236

def loopBody246_238 : HolLoopProg 64 :=
.seq loopBody246_229 loopBody246_237

def loopBody246_239 : HolLoopProg 64 :=
.mark loopBody246_238

def loopBody246_240 : HolLoopProg 64 :=
.seq loopBody246_227 loopBody246_239

def loopBody246_241 : HolLoopProg 64 :=
.mark loopBody246_240

def loopBody246_242 : HolLoopProg 64 :=
.seq loopBody246_225 loopBody246_241

def loopBody246_243 : HolLoopProg 64 :=
.mark loopBody246_242

def loopBody246_244 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 9, Flapjack.HolLoopExp.const 32#64,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 13) (Flapjack.HolLoopExp.const 3#64)])

def loopBody246_245 : HolLoopProg 64 :=
.mark loopBody246_244

def loopBody246_246 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 14)

def loopBody246_247 : HolLoopProg 64 :=
.mark loopBody246_246

def loopBody246_248 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 16)

def loopBody246_249 : HolLoopProg 64 :=
.mark loopBody246_248

def loopBody246_250 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 15) 17

def loopBody246_251 : HolLoopProg 64 :=
.mark loopBody246_250

def loopBody246_252 : HolLoopProg 64 :=
.seq loopBody246_251 loopBody246_1

def loopBody246_253 : HolLoopProg 64 :=
.mark loopBody246_252

def loopBody246_254 : HolLoopProg 64 :=
.seq loopBody246_249 loopBody246_253

def loopBody246_255 : HolLoopProg 64 :=
.mark loopBody246_254

def loopBody246_256 : HolLoopProg 64 :=
.seq loopBody246_255 loopBody246_1

def loopBody246_257 : HolLoopProg 64 :=
.mark loopBody246_256

def loopBody246_258 : HolLoopProg 64 :=
.seq loopBody246_247 loopBody246_257

def loopBody246_259 : HolLoopProg 64 :=
.mark loopBody246_258

def loopBody246_260 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_259

def loopBody246_261 : HolLoopProg 64 :=
.mark loopBody246_260

def loopBody246_262 : HolLoopProg 64 :=
.seq loopBody246_245 loopBody246_261

def loopBody246_263 : HolLoopProg 64 :=
.mark loopBody246_262

def loopBody246_264 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_263

def loopBody246_265 : HolLoopProg 64 :=
.mark loopBody246_264

def loopBody246_266 : HolLoopProg 64 :=
.seq loopBody246_243 loopBody246_265

def loopBody246_267 : HolLoopProg 64 :=
.mark loopBody246_266

def loopBody246_268 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_267

def loopBody246_269 : HolLoopProg 64 :=
.mark loopBody246_268

def loopBody246_270 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_269

def loopBody246_271 : HolLoopProg 64 :=
.mark loopBody246_270

def loopBody246_272 : HolLoopProg 64 :=
.seq loopBody246_223 loopBody246_271

def loopBody246_273 : HolLoopProg 64 :=
.mark loopBody246_272

def loopBody246_274 : HolLoopProg 64 :=
.seq loopBody246_185 loopBody246_273

def loopBody246_275 : HolLoopProg 64 :=
.mark loopBody246_274

def loopBody246_276 : HolLoopProg 64 :=
.seq loopBody246_183 loopBody246_275

def loopBody246_277 : HolLoopProg 64 :=
.mark loopBody246_276

def loopBody246_278 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 15 (Flapjack.RegImm.imm 0#64) loopBody246_179 loopBody246_277 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))

def loopBody246_279 : HolLoopProg 64 :=
.mark loopBody246_278

def loopBody246_280 : HolLoopProg 64 :=
.seq loopBody246_279 loopBody246_1

def loopBody246_281 : HolLoopProg 64 :=
.mark loopBody246_280

def loopBody246_282 : HolLoopProg 64 :=
.seq loopBody246_153 loopBody246_281

def loopBody246_283 : HolLoopProg 64 :=
.mark loopBody246_282

def loopBody246_284 : HolLoopProg 64 :=
.seq loopBody246_151 loopBody246_283

def loopBody246_285 : HolLoopProg 64 :=
.mark loopBody246_284

def loopBody246_286 : HolLoopProg 64 :=
.seq loopBody246_147 loopBody246_285

def loopBody246_287 : HolLoopProg 64 :=
.mark loopBody246_286

def loopBody246_288 : HolLoopProg 64 :=
.seq loopBody246_145 loopBody246_287

def loopBody246_289 : HolLoopProg 64 :=
.mark loopBody246_288

def loopBody246_290 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 9)

def loopBody246_291 : HolLoopProg 64 :=
.mark loopBody246_290

def loopBody246_292 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [12]

def loopBody246_293 : HolLoopProg 64 :=
.mark loopBody246_292

def loopBody246_294 : HolLoopProg 64 :=
.seq loopBody246_293 loopBody246_1

def loopBody246_295 : HolLoopProg 64 :=
.mark loopBody246_294

def loopBody246_296 : HolLoopProg 64 :=
.seq loopBody246_291 loopBody246_295

def loopBody246_297 : HolLoopProg 64 :=
.mark loopBody246_296

def loopBody246_298 : HolLoopProg 64 :=
.seq loopBody246_289 loopBody246_297

def loopBody246_299 : HolLoopProg 64 :=
.mark loopBody246_298

def loopBody246_300 : HolLoopProg 64 :=
.seq loopBody246_143 loopBody246_299

def loopBody246_301 : HolLoopProg 64 :=
.mark loopBody246_300

def loopBody246_302 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_301

def loopBody246_303 : HolLoopProg 64 :=
.mark loopBody246_302

def loopBody246_304 : HolLoopProg 64 :=
.seq loopBody246_141 loopBody246_303

def loopBody246_305 : HolLoopProg 64 :=
.mark loopBody246_304

def loopBody246_306 : HolLoopProg 64 :=
.seq loopBody246_15 loopBody246_305

def loopBody246_307 : HolLoopProg 64 :=
.mark loopBody246_306

def loopBody246_308 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_307

def loopBody246_309 : HolLoopProg 64 :=
.mark loopBody246_308

def loopBody246_310 : HolLoopProg 64 :=
.seq loopBody246_13 loopBody246_309

def loopBody246_311 : HolLoopProg 64 :=
.mark loopBody246_310

def loopBody246_312 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_311

def loopBody246_313 : HolLoopProg 64 :=
.mark loopBody246_312

def loopBody246_314 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_313

def loopBody246_315 : HolLoopProg 64 :=
.mark loopBody246_314

def loopBody246_316 : HolLoopProg 64 :=
.seq loopBody246_7 loopBody246_315

def loopBody246_317 : HolLoopProg 64 :=
.mark loopBody246_316

def loopBody246_318 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_317

def loopBody246_319 : HolLoopProg 64 :=
.mark loopBody246_318

def loopBody246_320 : HolLoopProg 64 :=
.seq loopBody246_5 loopBody246_319

def loopBody246_321 : HolLoopProg 64 :=
.mark loopBody246_320

def loopBody246_322 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_321

def loopBody246_323 : HolLoopProg 64 :=
.mark loopBody246_322

def loopBody246_324 : HolLoopProg 64 :=
.seq loopBody246_3 loopBody246_323

def loopBody246_325 : HolLoopProg 64 :=
.mark loopBody246_324

def loopBody246_326 : HolLoopProg 64 :=
.seq loopBody246_1 loopBody246_325

def loopBody246_327 : HolLoopProg 64 :=
.mark loopBody246_326

def output246 : Nat × List Nat × HolLoopProg 64 :=
  (310, [0, 1, 2, 3, 4, 5], loopBody246_327)
end InitECandidate.Proofs.FrontendStages.Loop
