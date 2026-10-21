import InitECandidate.Proofs.FrontendStages.Loop.Translate608
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody624_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody624_1 : HolLoopProg 64 :=
.mark loopBody624_0

def loopBody624_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 12#64)

def loopBody624_3 : HolLoopProg 64 :=
.mark loopBody624_2

def loopBody624_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody624_5 : HolLoopProg 64 :=
.mark loopBody624_4

def loopBody624_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody624_7 : HolLoopProg 64 :=
.mark loopBody624_6

def loopBody624_8 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 675) ([5, 6]) (some (5, loopBody624_7, loopBody624_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody624_9 : HolLoopProg 64 :=
.mark loopBody624_8

def loopBody624_10 : HolLoopProg 64 :=
.seq loopBody624_9 loopBody624_1

def loopBody624_11 : HolLoopProg 64 :=
.mark loopBody624_10

def loopBody624_12 : HolLoopProg 64 :=
.seq loopBody624_5 loopBody624_11

def loopBody624_13 : HolLoopProg 64 :=
.mark loopBody624_12

def loopBody624_14 : HolLoopProg 64 :=
.seq loopBody624_3 loopBody624_13

def loopBody624_15 : HolLoopProg 64 :=
.mark loopBody624_14

def loopBody624_16 : HolLoopProg 64 :=
.seq loopBody624_1 loopBody624_15

def loopBody624_17 : HolLoopProg 64 :=
.mark loopBody624_16

def loopBody624_18 : HolLoopProg 64 :=
.seq loopBody624_1 loopBody624_17

def loopBody624_19 : HolLoopProg 64 :=
.mark loopBody624_18

def loopBody624_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody624_21 : HolLoopProg 64 :=
.mark loopBody624_20

def loopBody624_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 6#64))

def loopBody624_23 : HolLoopProg 64 :=
.mark loopBody624_22

def loopBody624_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody624_25 : HolLoopProg 64 :=
.mark loopBody624_24

def loopBody624_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody624_27 : HolLoopProg 64 :=
.mark loopBody624_26

def loopBody624_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody624_29 : HolLoopProg 64 :=
.mark loopBody624_28

def loopBody624_30 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 7 (Flapjack.RegImm.reg 8) loopBody624_29 loopBody624_25 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody624_31 : HolLoopProg 64 :=
.mark loopBody624_30

def loopBody624_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody624_33 : HolLoopProg 64 :=
.mark loopBody624_32

def loopBody624_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 1#64])

def loopBody624_35 : HolLoopProg 64 :=
.mark loopBody624_34

def loopBody624_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 6)

def loopBody624_37 : HolLoopProg 64 :=
.mark loopBody624_36

def loopBody624_38 : HolLoopProg 64 :=
.seq loopBody624_37 loopBody624_1

def loopBody624_39 : HolLoopProg 64 :=
.mark loopBody624_38

def loopBody624_40 : HolLoopProg 64 :=
.seq loopBody624_39 loopBody624_1

def loopBody624_41 : HolLoopProg 64 :=
.mark loopBody624_40

def loopBody624_42 : HolLoopProg 64 :=
.seq loopBody624_35 loopBody624_41

def loopBody624_43 : HolLoopProg 64 :=
.mark loopBody624_42

def loopBody624_44 : HolLoopProg 64 :=
.seq loopBody624_1 loopBody624_43

def loopBody624_45 : HolLoopProg 64 :=
.mark loopBody624_44

def loopBody624_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody624_47 : HolLoopProg 64 :=
.mark loopBody624_46

def loopBody624_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody624_49 : HolLoopProg 64 :=
.mark loopBody624_48

def loopBody624_50 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 7 (Flapjack.RegImm.reg 8) loopBody624_29 loopBody624_25 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody624_51 : HolLoopProg 64 :=
.mark loopBody624_50

def loopBody624_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 0)

def loopBody624_53 : HolLoopProg 64 :=
.mark loopBody624_52

def loopBody624_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 0)

def loopBody624_55 : HolLoopProg 64 :=
.mark loopBody624_54

def loopBody624_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody624_57 : HolLoopProg 64 :=
.mark loopBody624_56

def loopBody624_58 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 665) ([7, 8]) (some (7, loopBody624_57, loopBody624_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody624_59 : HolLoopProg 64 :=
.mark loopBody624_58

def loopBody624_60 : HolLoopProg 64 :=
.seq loopBody624_59 loopBody624_1

def loopBody624_61 : HolLoopProg 64 :=
.mark loopBody624_60

def loopBody624_62 : HolLoopProg 64 :=
.seq loopBody624_55 loopBody624_61

def loopBody624_63 : HolLoopProg 64 :=
.mark loopBody624_62

def loopBody624_64 : HolLoopProg 64 :=
.seq loopBody624_53 loopBody624_63

def loopBody624_65 : HolLoopProg 64 :=
.mark loopBody624_64

def loopBody624_66 : HolLoopProg 64 :=
.seq loopBody624_1 loopBody624_65

def loopBody624_67 : HolLoopProg 64 :=
.mark loopBody624_66

def loopBody624_68 : HolLoopProg 64 :=
.seq loopBody624_1 loopBody624_67

def loopBody624_69 : HolLoopProg 64 :=
.mark loopBody624_68

def loopBody624_70 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody624_69 loopBody624_1 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody624_71 : HolLoopProg 64 :=
.mark loopBody624_70

def loopBody624_72 : HolLoopProg 64 :=
.seq loopBody624_71 loopBody624_1

def loopBody624_73 : HolLoopProg 64 :=
.mark loopBody624_72

def loopBody624_74 : HolLoopProg 64 :=
.seq loopBody624_33 loopBody624_73

def loopBody624_75 : HolLoopProg 64 :=
.mark loopBody624_74

def loopBody624_76 : HolLoopProg 64 :=
.seq loopBody624_51 loopBody624_75

def loopBody624_77 : HolLoopProg 64 :=
.mark loopBody624_76

def loopBody624_78 : HolLoopProg 64 :=
.seq loopBody624_49 loopBody624_77

def loopBody624_79 : HolLoopProg 64 :=
.mark loopBody624_78

def loopBody624_80 : HolLoopProg 64 :=
.seq loopBody624_47 loopBody624_79

def loopBody624_81 : HolLoopProg 64 :=
.mark loopBody624_80

def loopBody624_82 : HolLoopProg 64 :=
.seq loopBody624_45 loopBody624_81

def loopBody624_83 : HolLoopProg 64 :=
.mark loopBody624_82

def loopBody624_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr
        (Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.add
            [Flapjack.HolLoopExp.var 2,
              Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
                (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 5)
                  (Flapjack.HolLoopExp.const 6#64))
                (Flapjack.HolLoopExp.const 3#64)]))
        (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 63#64]),
      Flapjack.HolLoopExp.const 1#64])

def loopBody624_85 : HolLoopProg 64 :=
.mark loopBody624_84

def loopBody624_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody624_87 : HolLoopProg 64 :=
.mark loopBody624_86

def loopBody624_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 1#64)

def loopBody624_89 : HolLoopProg 64 :=
.mark loopBody624_88

def loopBody624_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody624_91 : HolLoopProg 64 :=
.mark loopBody624_90

def loopBody624_92 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 8 (Flapjack.RegImm.reg 9) loopBody624_49 loopBody624_91 (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody624_93 : HolLoopProg 64 :=
.mark loopBody624_92

def loopBody624_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody624_95 : HolLoopProg 64 :=
.mark loopBody624_94

def loopBody624_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 0)

def loopBody624_97 : HolLoopProg 64 :=
.mark loopBody624_96

def loopBody624_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 1)

def loopBody624_99 : HolLoopProg 64 :=
.mark loopBody624_98

def loopBody624_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody624_101 : HolLoopProg 64 :=
.mark loopBody624_100

def loopBody624_102 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 664) ([8, 9, 10]) (some (8, loopBody624_101, loopBody624_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody624_103 : HolLoopProg 64 :=
.mark loopBody624_102

def loopBody624_104 : HolLoopProg 64 :=
.seq loopBody624_103 loopBody624_1

def loopBody624_105 : HolLoopProg 64 :=
.mark loopBody624_104

def loopBody624_106 : HolLoopProg 64 :=
.seq loopBody624_99 loopBody624_105

def loopBody624_107 : HolLoopProg 64 :=
.mark loopBody624_106

def loopBody624_108 : HolLoopProg 64 :=
.seq loopBody624_97 loopBody624_107

def loopBody624_109 : HolLoopProg 64 :=
.mark loopBody624_108

def loopBody624_110 : HolLoopProg 64 :=
.seq loopBody624_55 loopBody624_109

def loopBody624_111 : HolLoopProg 64 :=
.mark loopBody624_110

def loopBody624_112 : HolLoopProg 64 :=
.seq loopBody624_1 loopBody624_111

def loopBody624_113 : HolLoopProg 64 :=
.mark loopBody624_112

def loopBody624_114 : HolLoopProg 64 :=
.seq loopBody624_1 loopBody624_113

def loopBody624_115 : HolLoopProg 64 :=
.mark loopBody624_114

def loopBody624_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody624_117 : HolLoopProg 64 :=
.mark loopBody624_116

def loopBody624_118 : HolLoopProg 64 :=
.seq loopBody624_117 loopBody624_1

def loopBody624_119 : HolLoopProg 64 :=
.mark loopBody624_118

def loopBody624_120 : HolLoopProg 64 :=
.seq loopBody624_119 loopBody624_1

def loopBody624_121 : HolLoopProg 64 :=
.mark loopBody624_120

def loopBody624_122 : HolLoopProg 64 :=
.seq loopBody624_115 loopBody624_121

def loopBody624_123 : HolLoopProg 64 :=
.mark loopBody624_122

def loopBody624_124 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody624_123 loopBody624_1 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody624_125 : HolLoopProg 64 :=
.mark loopBody624_124

def loopBody624_126 : HolLoopProg 64 :=
.seq loopBody624_125 loopBody624_1

def loopBody624_127 : HolLoopProg 64 :=
.mark loopBody624_126

def loopBody624_128 : HolLoopProg 64 :=
.seq loopBody624_95 loopBody624_127

def loopBody624_129 : HolLoopProg 64 :=
.mark loopBody624_128

def loopBody624_130 : HolLoopProg 64 :=
.seq loopBody624_93 loopBody624_129

def loopBody624_131 : HolLoopProg 64 :=
.mark loopBody624_130

def loopBody624_132 : HolLoopProg 64 :=
.seq loopBody624_89 loopBody624_131

def loopBody624_133 : HolLoopProg 64 :=
.mark loopBody624_132

def loopBody624_134 : HolLoopProg 64 :=
.seq loopBody624_87 loopBody624_133

def loopBody624_135 : HolLoopProg 64 :=
.mark loopBody624_134

def loopBody624_136 : HolLoopProg 64 :=
.seq loopBody624_85 loopBody624_135

def loopBody624_137 : HolLoopProg 64 :=
.mark loopBody624_136

def loopBody624_138 : HolLoopProg 64 :=
.seq loopBody624_1 loopBody624_137

def loopBody624_139 : HolLoopProg 64 :=
.mark loopBody624_138

def loopBody624_140 : HolLoopProg 64 :=
.seq loopBody624_83 loopBody624_139

def loopBody624_141 : HolLoopProg 64 :=
.mark loopBody624_140

def loopBody624_142 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody624_143 : HolLoopProg 64 :=
.mark loopBody624_142

def loopBody624_144 : HolLoopProg 64 :=
.seq loopBody624_141 loopBody624_143

def loopBody624_145 : HolLoopProg 64 :=
.mark loopBody624_144

def loopBody624_146 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody624_147 : HolLoopProg 64 :=
.mark loopBody624_146

def loopBody624_148 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody624_145 loopBody624_147 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody624_149 : HolLoopProg 64 :=
.mark loopBody624_148

def loopBody624_150 : HolLoopProg 64 :=
.seq loopBody624_149 loopBody624_1

def loopBody624_151 : HolLoopProg 64 :=
.mark loopBody624_150

def loopBody624_152 : HolLoopProg 64 :=
.seq loopBody624_33 loopBody624_151

def loopBody624_153 : HolLoopProg 64 :=
.mark loopBody624_152

def loopBody624_154 : HolLoopProg 64 :=
.seq loopBody624_31 loopBody624_153

def loopBody624_155 : HolLoopProg 64 :=
.mark loopBody624_154

def loopBody624_156 : HolLoopProg 64 :=
.seq loopBody624_27 loopBody624_155

def loopBody624_157 : HolLoopProg 64 :=
.mark loopBody624_156

def loopBody624_158 : HolLoopProg 64 :=
.seq loopBody624_25 loopBody624_157

def loopBody624_159 : HolLoopProg 64 :=
.mark loopBody624_158

def loopBody624_160 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody624_159 (Flapjack.Spt.ln)

def loopBody624_161 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody624_162 : HolLoopProg 64 :=
.mark loopBody624_161

def loopBody624_163 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody624_164 : HolLoopProg 64 :=
.mark loopBody624_163

def loopBody624_165 : HolLoopProg 64 :=
.seq loopBody624_164 loopBody624_1

def loopBody624_166 : HolLoopProg 64 :=
.mark loopBody624_165

def loopBody624_167 : HolLoopProg 64 :=
.seq loopBody624_162 loopBody624_166

def loopBody624_168 : HolLoopProg 64 :=
.mark loopBody624_167

def loopBody624_169 : HolLoopProg 64 :=
.seq loopBody624_160 loopBody624_168

def loopBody624_170 : HolLoopProg 64 :=
.seq loopBody624_23 loopBody624_169

def loopBody624_171 : HolLoopProg 64 :=
.seq loopBody624_1 loopBody624_170

def loopBody624_172 : HolLoopProg 64 :=
.seq loopBody624_21 loopBody624_171

def loopBody624_173 : HolLoopProg 64 :=
.seq loopBody624_1 loopBody624_172

def loopBody624_174 : HolLoopProg 64 :=
.seq loopBody624_19 loopBody624_173

def output624 : Nat × List Nat × HolLoopProg 64 :=
  (688, [0, 1, 2, 3], loopBody624_174)
end InitECandidate.Proofs.FrontendStages.Loop
