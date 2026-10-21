import InitECandidate.Proofs.FrontendStages.Loop.Translate761
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody777_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody777_1 : HolLoopProg 64 :=
.mark loopBody777_0

def loopBody777_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 64#64)

def loopBody777_3 : HolLoopProg 64 :=
.mark loopBody777_2

def loopBody777_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody777_5 : HolLoopProg 64 :=
.mark loopBody777_4

def loopBody777_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 68) ([2]) (some (2, loopBody777_5, loopBody777_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody777_7 : HolLoopProg 64 :=
.mark loopBody777_6

def loopBody777_8 : HolLoopProg 64 :=
.seq loopBody777_7 loopBody777_1

def loopBody777_9 : HolLoopProg 64 :=
.mark loopBody777_8

def loopBody777_10 : HolLoopProg 64 :=
.seq loopBody777_3 loopBody777_9

def loopBody777_11 : HolLoopProg 64 :=
.mark loopBody777_10

def loopBody777_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 9#64])

def loopBody777_13 : HolLoopProg 64 :=
.mark loopBody777_12

def loopBody777_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody777_15 : HolLoopProg 64 :=
.mark loopBody777_14

def loopBody777_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 4 4

def loopBody777_17 : HolLoopProg 64 :=
.mark loopBody777_16

def loopBody777_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 1#64])

def loopBody777_19 : HolLoopProg 64 :=
.mark loopBody777_18

def loopBody777_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 5 5

def loopBody777_21 : HolLoopProg 64 :=
.mark loopBody777_20

def loopBody777_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 2#64])

def loopBody777_23 : HolLoopProg 64 :=
.mark loopBody777_22

def loopBody777_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 6 6

def loopBody777_25 : HolLoopProg 64 :=
.mark loopBody777_24

def loopBody777_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 3#64])

def loopBody777_27 : HolLoopProg 64 :=
.mark loopBody777_26

def loopBody777_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 7 7

def loopBody777_29 : HolLoopProg 64 :=
.mark loopBody777_28

def loopBody777_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 4#64])

def loopBody777_31 : HolLoopProg 64 :=
.mark loopBody777_30

def loopBody777_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 8 8

def loopBody777_33 : HolLoopProg 64 :=
.mark loopBody777_32

def loopBody777_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 4#64, Flapjack.HolLoopExp.const 1#64])

def loopBody777_35 : HolLoopProg 64 :=
.mark loopBody777_34

def loopBody777_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 9 9

def loopBody777_37 : HolLoopProg 64 :=
.mark loopBody777_36

def loopBody777_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 4#64, Flapjack.HolLoopExp.const 2#64])

def loopBody777_39 : HolLoopProg 64 :=
.mark loopBody777_38

def loopBody777_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 10 10

def loopBody777_41 : HolLoopProg 64 :=
.mark loopBody777_40

def loopBody777_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 4#64, Flapjack.HolLoopExp.const 3#64])

def loopBody777_43 : HolLoopProg 64 :=
.mark loopBody777_42

def loopBody777_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 11 11

def loopBody777_45 : HolLoopProg 64 :=
.mark loopBody777_44

def loopBody777_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 2)

def loopBody777_47 : HolLoopProg 64 :=
.mark loopBody777_46

def loopBody777_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.var 4,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.const 8#64),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 6) (Flapjack.HolLoopExp.const 16#64),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 7) (Flapjack.HolLoopExp.const 24#64),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
        (Flapjack.HolLoopExp.op Flapjack.BinOp.or
          [Flapjack.HolLoopExp.var 8,
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 9) (Flapjack.HolLoopExp.const 8#64),
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 10) (Flapjack.HolLoopExp.const 16#64),
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 11)
              (Flapjack.HolLoopExp.const 24#64)])
        (Flapjack.HolLoopExp.const 32#64)])

def loopBody777_49 : HolLoopProg 64 :=
.mark loopBody777_48

def loopBody777_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody777_51 : HolLoopProg 64 :=
.mark loopBody777_50

def loopBody777_52 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 177) ([12, 13]) (some (4, loopBody777_51, loopBody777_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody777_53 : HolLoopProg 64 :=
.mark loopBody777_52

def loopBody777_54 : HolLoopProg 64 :=
.seq loopBody777_53 loopBody777_1

def loopBody777_55 : HolLoopProg 64 :=
.mark loopBody777_54

def loopBody777_56 : HolLoopProg 64 :=
.seq loopBody777_49 loopBody777_55

def loopBody777_57 : HolLoopProg 64 :=
.mark loopBody777_56

def loopBody777_58 : HolLoopProg 64 :=
.seq loopBody777_47 loopBody777_57

def loopBody777_59 : HolLoopProg 64 :=
.mark loopBody777_58

def loopBody777_60 : HolLoopProg 64 :=
.seq loopBody777_45 loopBody777_59

def loopBody777_61 : HolLoopProg 64 :=
.mark loopBody777_60

def loopBody777_62 : HolLoopProg 64 :=
.seq loopBody777_43 loopBody777_61

def loopBody777_63 : HolLoopProg 64 :=
.mark loopBody777_62

def loopBody777_64 : HolLoopProg 64 :=
.seq loopBody777_41 loopBody777_63

def loopBody777_65 : HolLoopProg 64 :=
.mark loopBody777_64

def loopBody777_66 : HolLoopProg 64 :=
.seq loopBody777_39 loopBody777_65

def loopBody777_67 : HolLoopProg 64 :=
.mark loopBody777_66

def loopBody777_68 : HolLoopProg 64 :=
.seq loopBody777_37 loopBody777_67

def loopBody777_69 : HolLoopProg 64 :=
.mark loopBody777_68

def loopBody777_70 : HolLoopProg 64 :=
.seq loopBody777_35 loopBody777_69

def loopBody777_71 : HolLoopProg 64 :=
.mark loopBody777_70

def loopBody777_72 : HolLoopProg 64 :=
.seq loopBody777_33 loopBody777_71

def loopBody777_73 : HolLoopProg 64 :=
.mark loopBody777_72

def loopBody777_74 : HolLoopProg 64 :=
.seq loopBody777_31 loopBody777_73

def loopBody777_75 : HolLoopProg 64 :=
.mark loopBody777_74

def loopBody777_76 : HolLoopProg 64 :=
.seq loopBody777_29 loopBody777_75

def loopBody777_77 : HolLoopProg 64 :=
.mark loopBody777_76

def loopBody777_78 : HolLoopProg 64 :=
.seq loopBody777_27 loopBody777_77

def loopBody777_79 : HolLoopProg 64 :=
.mark loopBody777_78

def loopBody777_80 : HolLoopProg 64 :=
.seq loopBody777_25 loopBody777_79

def loopBody777_81 : HolLoopProg 64 :=
.mark loopBody777_80

def loopBody777_82 : HolLoopProg 64 :=
.seq loopBody777_23 loopBody777_81

def loopBody777_83 : HolLoopProg 64 :=
.mark loopBody777_82

def loopBody777_84 : HolLoopProg 64 :=
.seq loopBody777_21 loopBody777_83

def loopBody777_85 : HolLoopProg 64 :=
.mark loopBody777_84

def loopBody777_86 : HolLoopProg 64 :=
.seq loopBody777_19 loopBody777_85

def loopBody777_87 : HolLoopProg 64 :=
.mark loopBody777_86

def loopBody777_88 : HolLoopProg 64 :=
.seq loopBody777_17 loopBody777_87

def loopBody777_89 : HolLoopProg 64 :=
.mark loopBody777_88

def loopBody777_90 : HolLoopProg 64 :=
.seq loopBody777_15 loopBody777_89

def loopBody777_91 : HolLoopProg 64 :=
.mark loopBody777_90

def loopBody777_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 3])

def loopBody777_93 : HolLoopProg 64 :=
.mark loopBody777_92

def loopBody777_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 4)

def loopBody777_95 : HolLoopProg 64 :=
.mark loopBody777_94

def loopBody777_96 : HolLoopProg 64 :=
.seq loopBody777_95 loopBody777_1

def loopBody777_97 : HolLoopProg 64 :=
.mark loopBody777_96

def loopBody777_98 : HolLoopProg 64 :=
.seq loopBody777_97 loopBody777_1

def loopBody777_99 : HolLoopProg 64 :=
.mark loopBody777_98

def loopBody777_100 : HolLoopProg 64 :=
.seq loopBody777_93 loopBody777_99

def loopBody777_101 : HolLoopProg 64 :=
.mark loopBody777_100

def loopBody777_102 : HolLoopProg 64 :=
.seq loopBody777_1 loopBody777_101

def loopBody777_103 : HolLoopProg 64 :=
.mark loopBody777_102

def loopBody777_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64])

def loopBody777_105 : HolLoopProg 64 :=
.mark loopBody777_104

def loopBody777_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64, Flapjack.HolLoopExp.const 1#64])

def loopBody777_107 : HolLoopProg 64 :=
.mark loopBody777_106

def loopBody777_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64, Flapjack.HolLoopExp.const 2#64])

def loopBody777_109 : HolLoopProg 64 :=
.mark loopBody777_108

def loopBody777_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64, Flapjack.HolLoopExp.const 3#64])

def loopBody777_111 : HolLoopProg 64 :=
.mark loopBody777_110

def loopBody777_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64, Flapjack.HolLoopExp.const 4#64])

def loopBody777_113 : HolLoopProg 64 :=
.mark loopBody777_112

def loopBody777_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64, Flapjack.HolLoopExp.const 4#64,
      Flapjack.HolLoopExp.const 1#64])

def loopBody777_115 : HolLoopProg 64 :=
.mark loopBody777_114

def loopBody777_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64, Flapjack.HolLoopExp.const 4#64,
      Flapjack.HolLoopExp.const 2#64])

def loopBody777_117 : HolLoopProg 64 :=
.mark loopBody777_116

def loopBody777_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64, Flapjack.HolLoopExp.const 4#64,
      Flapjack.HolLoopExp.const 3#64])

def loopBody777_119 : HolLoopProg 64 :=
.mark loopBody777_118

def loopBody777_120 : HolLoopProg 64 :=
.seq loopBody777_119 loopBody777_61

def loopBody777_121 : HolLoopProg 64 :=
.mark loopBody777_120

def loopBody777_122 : HolLoopProg 64 :=
.seq loopBody777_41 loopBody777_121

def loopBody777_123 : HolLoopProg 64 :=
.mark loopBody777_122

def loopBody777_124 : HolLoopProg 64 :=
.seq loopBody777_117 loopBody777_123

def loopBody777_125 : HolLoopProg 64 :=
.mark loopBody777_124

def loopBody777_126 : HolLoopProg 64 :=
.seq loopBody777_37 loopBody777_125

def loopBody777_127 : HolLoopProg 64 :=
.mark loopBody777_126

def loopBody777_128 : HolLoopProg 64 :=
.seq loopBody777_115 loopBody777_127

def loopBody777_129 : HolLoopProg 64 :=
.mark loopBody777_128

def loopBody777_130 : HolLoopProg 64 :=
.seq loopBody777_33 loopBody777_129

def loopBody777_131 : HolLoopProg 64 :=
.mark loopBody777_130

def loopBody777_132 : HolLoopProg 64 :=
.seq loopBody777_113 loopBody777_131

def loopBody777_133 : HolLoopProg 64 :=
.mark loopBody777_132

def loopBody777_134 : HolLoopProg 64 :=
.seq loopBody777_29 loopBody777_133

def loopBody777_135 : HolLoopProg 64 :=
.mark loopBody777_134

def loopBody777_136 : HolLoopProg 64 :=
.seq loopBody777_111 loopBody777_135

def loopBody777_137 : HolLoopProg 64 :=
.mark loopBody777_136

def loopBody777_138 : HolLoopProg 64 :=
.seq loopBody777_25 loopBody777_137

def loopBody777_139 : HolLoopProg 64 :=
.mark loopBody777_138

def loopBody777_140 : HolLoopProg 64 :=
.seq loopBody777_109 loopBody777_139

def loopBody777_141 : HolLoopProg 64 :=
.mark loopBody777_140

def loopBody777_142 : HolLoopProg 64 :=
.seq loopBody777_21 loopBody777_141

def loopBody777_143 : HolLoopProg 64 :=
.mark loopBody777_142

def loopBody777_144 : HolLoopProg 64 :=
.seq loopBody777_107 loopBody777_143

def loopBody777_145 : HolLoopProg 64 :=
.mark loopBody777_144

def loopBody777_146 : HolLoopProg 64 :=
.seq loopBody777_17 loopBody777_145

def loopBody777_147 : HolLoopProg 64 :=
.mark loopBody777_146

def loopBody777_148 : HolLoopProg 64 :=
.seq loopBody777_105 loopBody777_147

def loopBody777_149 : HolLoopProg 64 :=
.mark loopBody777_148

def loopBody777_150 : HolLoopProg 64 :=
.seq loopBody777_103 loopBody777_149

def loopBody777_151 : HolLoopProg 64 :=
.mark loopBody777_150

def loopBody777_152 : HolLoopProg 64 :=
.seq loopBody777_151 loopBody777_103

def loopBody777_153 : HolLoopProg 64 :=
.mark loopBody777_152

def loopBody777_154 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody777_155 : HolLoopProg 64 :=
.mark loopBody777_154

def loopBody777_156 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64])

def loopBody777_157 : HolLoopProg 64 :=
.mark loopBody777_156

def loopBody777_158 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 20#64)

def loopBody777_159 : HolLoopProg 64 :=
.mark loopBody777_158

def loopBody777_160 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 176) ([4, 5, 6]) (some (4, loopBody777_51, loopBody777_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody777_161 : HolLoopProg 64 :=
.mark loopBody777_160

def loopBody777_162 : HolLoopProg 64 :=
.seq loopBody777_161 loopBody777_1

def loopBody777_163 : HolLoopProg 64 :=
.mark loopBody777_162

def loopBody777_164 : HolLoopProg 64 :=
.seq loopBody777_159 loopBody777_163

def loopBody777_165 : HolLoopProg 64 :=
.mark loopBody777_164

def loopBody777_166 : HolLoopProg 64 :=
.seq loopBody777_157 loopBody777_165

def loopBody777_167 : HolLoopProg 64 :=
.mark loopBody777_166

def loopBody777_168 : HolLoopProg 64 :=
.seq loopBody777_155 loopBody777_167

def loopBody777_169 : HolLoopProg 64 :=
.mark loopBody777_168

def loopBody777_170 : HolLoopProg 64 :=
.seq loopBody777_153 loopBody777_169

def loopBody777_171 : HolLoopProg 64 :=
.mark loopBody777_170

def loopBody777_172 : HolLoopProg 64 :=
.seq loopBody777_171 loopBody777_103

def loopBody777_173 : HolLoopProg 64 :=
.mark loopBody777_172

def loopBody777_174 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 36#64])

def loopBody777_175 : HolLoopProg 64 :=
.mark loopBody777_174

def loopBody777_176 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 36#64, Flapjack.HolLoopExp.const 1#64])

def loopBody777_177 : HolLoopProg 64 :=
.mark loopBody777_176

def loopBody777_178 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 36#64, Flapjack.HolLoopExp.const 2#64])

def loopBody777_179 : HolLoopProg 64 :=
.mark loopBody777_178

def loopBody777_180 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 36#64, Flapjack.HolLoopExp.const 3#64])

def loopBody777_181 : HolLoopProg 64 :=
.mark loopBody777_180

def loopBody777_182 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 36#64, Flapjack.HolLoopExp.const 4#64])

def loopBody777_183 : HolLoopProg 64 :=
.mark loopBody777_182

def loopBody777_184 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 36#64, Flapjack.HolLoopExp.const 4#64,
      Flapjack.HolLoopExp.const 1#64])

def loopBody777_185 : HolLoopProg 64 :=
.mark loopBody777_184

def loopBody777_186 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 36#64, Flapjack.HolLoopExp.const 4#64,
      Flapjack.HolLoopExp.const 2#64])

def loopBody777_187 : HolLoopProg 64 :=
.mark loopBody777_186

def loopBody777_188 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 36#64, Flapjack.HolLoopExp.const 4#64,
      Flapjack.HolLoopExp.const 3#64])

def loopBody777_189 : HolLoopProg 64 :=
.mark loopBody777_188

def loopBody777_190 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 177) ([12, 13]) (some (4, loopBody777_51, loopBody777_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody777_191 : HolLoopProg 64 :=
.mark loopBody777_190

def loopBody777_192 : HolLoopProg 64 :=
.seq loopBody777_191 loopBody777_1

def loopBody777_193 : HolLoopProg 64 :=
.mark loopBody777_192

def loopBody777_194 : HolLoopProg 64 :=
.seq loopBody777_49 loopBody777_193

def loopBody777_195 : HolLoopProg 64 :=
.mark loopBody777_194

def loopBody777_196 : HolLoopProg 64 :=
.seq loopBody777_47 loopBody777_195

def loopBody777_197 : HolLoopProg 64 :=
.mark loopBody777_196

def loopBody777_198 : HolLoopProg 64 :=
.seq loopBody777_45 loopBody777_197

def loopBody777_199 : HolLoopProg 64 :=
.mark loopBody777_198

def loopBody777_200 : HolLoopProg 64 :=
.seq loopBody777_189 loopBody777_199

def loopBody777_201 : HolLoopProg 64 :=
.mark loopBody777_200

def loopBody777_202 : HolLoopProg 64 :=
.seq loopBody777_41 loopBody777_201

def loopBody777_203 : HolLoopProg 64 :=
.mark loopBody777_202

def loopBody777_204 : HolLoopProg 64 :=
.seq loopBody777_187 loopBody777_203

def loopBody777_205 : HolLoopProg 64 :=
.mark loopBody777_204

def loopBody777_206 : HolLoopProg 64 :=
.seq loopBody777_37 loopBody777_205

def loopBody777_207 : HolLoopProg 64 :=
.mark loopBody777_206

def loopBody777_208 : HolLoopProg 64 :=
.seq loopBody777_185 loopBody777_207

def loopBody777_209 : HolLoopProg 64 :=
.mark loopBody777_208

def loopBody777_210 : HolLoopProg 64 :=
.seq loopBody777_33 loopBody777_209

def loopBody777_211 : HolLoopProg 64 :=
.mark loopBody777_210

def loopBody777_212 : HolLoopProg 64 :=
.seq loopBody777_183 loopBody777_211

def loopBody777_213 : HolLoopProg 64 :=
.mark loopBody777_212

def loopBody777_214 : HolLoopProg 64 :=
.seq loopBody777_29 loopBody777_213

def loopBody777_215 : HolLoopProg 64 :=
.mark loopBody777_214

def loopBody777_216 : HolLoopProg 64 :=
.seq loopBody777_181 loopBody777_215

def loopBody777_217 : HolLoopProg 64 :=
.mark loopBody777_216

def loopBody777_218 : HolLoopProg 64 :=
.seq loopBody777_25 loopBody777_217

def loopBody777_219 : HolLoopProg 64 :=
.mark loopBody777_218

def loopBody777_220 : HolLoopProg 64 :=
.seq loopBody777_179 loopBody777_219

def loopBody777_221 : HolLoopProg 64 :=
.mark loopBody777_220

def loopBody777_222 : HolLoopProg 64 :=
.seq loopBody777_21 loopBody777_221

def loopBody777_223 : HolLoopProg 64 :=
.mark loopBody777_222

def loopBody777_224 : HolLoopProg 64 :=
.seq loopBody777_177 loopBody777_223

def loopBody777_225 : HolLoopProg 64 :=
.mark loopBody777_224

def loopBody777_226 : HolLoopProg 64 :=
.seq loopBody777_17 loopBody777_225

def loopBody777_227 : HolLoopProg 64 :=
.mark loopBody777_226

def loopBody777_228 : HolLoopProg 64 :=
.seq loopBody777_175 loopBody777_227

def loopBody777_229 : HolLoopProg 64 :=
.mark loopBody777_228

def loopBody777_230 : HolLoopProg 64 :=
.seq loopBody777_173 loopBody777_229

def loopBody777_231 : HolLoopProg 64 :=
.mark loopBody777_230

def loopBody777_232 : HolLoopProg 64 :=
.seq loopBody777_231 loopBody777_103

def loopBody777_233 : HolLoopProg 64 :=
.mark loopBody777_232

def loopBody777_234 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody777_235 : HolLoopProg 64 :=
.mark loopBody777_234

def loopBody777_236 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody777_237 : HolLoopProg 64 :=
.mark loopBody777_236

def loopBody777_238 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody777_239 : HolLoopProg 64 :=
.mark loopBody777_238

def loopBody777_240 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 836) ([5, 6]) (some (5, loopBody777_239, loopBody777_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))

def loopBody777_241 : HolLoopProg 64 :=
.mark loopBody777_240

def loopBody777_242 : HolLoopProg 64 :=
.seq loopBody777_241 loopBody777_1

def loopBody777_243 : HolLoopProg 64 :=
.mark loopBody777_242

def loopBody777_244 : HolLoopProg 64 :=
.seq loopBody777_237 loopBody777_243

def loopBody777_245 : HolLoopProg 64 :=
.mark loopBody777_244

def loopBody777_246 : HolLoopProg 64 :=
.seq loopBody777_235 loopBody777_245

def loopBody777_247 : HolLoopProg 64 :=
.mark loopBody777_246

def loopBody777_248 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody777_249 : HolLoopProg 64 :=
.mark loopBody777_248

def loopBody777_250 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5, 6]

def loopBody777_251 : HolLoopProg 64 :=
.mark loopBody777_250

def loopBody777_252 : HolLoopProg 64 :=
.seq loopBody777_251 loopBody777_1

def loopBody777_253 : HolLoopProg 64 :=
.mark loopBody777_252

def loopBody777_254 : HolLoopProg 64 :=
.seq loopBody777_249 loopBody777_253

def loopBody777_255 : HolLoopProg 64 :=
.mark loopBody777_254

def loopBody777_256 : HolLoopProg 64 :=
.seq loopBody777_235 loopBody777_255

def loopBody777_257 : HolLoopProg 64 :=
.mark loopBody777_256

def loopBody777_258 : HolLoopProg 64 :=
.seq loopBody777_247 loopBody777_257

def loopBody777_259 : HolLoopProg 64 :=
.mark loopBody777_258

def loopBody777_260 : HolLoopProg 64 :=
.seq loopBody777_1 loopBody777_259

def loopBody777_261 : HolLoopProg 64 :=
.mark loopBody777_260

def loopBody777_262 : HolLoopProg 64 :=
.seq loopBody777_1 loopBody777_261

def loopBody777_263 : HolLoopProg 64 :=
.mark loopBody777_262

def loopBody777_264 : HolLoopProg 64 :=
.seq loopBody777_233 loopBody777_263

def loopBody777_265 : HolLoopProg 64 :=
.mark loopBody777_264

def loopBody777_266 : HolLoopProg 64 :=
.seq loopBody777_91 loopBody777_265

def loopBody777_267 : HolLoopProg 64 :=
.mark loopBody777_266

def loopBody777_268 : HolLoopProg 64 :=
.seq loopBody777_1 loopBody777_267

def loopBody777_269 : HolLoopProg 64 :=
.mark loopBody777_268

def loopBody777_270 : HolLoopProg 64 :=
.seq loopBody777_1 loopBody777_269

def loopBody777_271 : HolLoopProg 64 :=
.mark loopBody777_270

def loopBody777_272 : HolLoopProg 64 :=
.seq loopBody777_13 loopBody777_271

def loopBody777_273 : HolLoopProg 64 :=
.mark loopBody777_272

def loopBody777_274 : HolLoopProg 64 :=
.seq loopBody777_1 loopBody777_273

def loopBody777_275 : HolLoopProg 64 :=
.mark loopBody777_274

def loopBody777_276 : HolLoopProg 64 :=
.seq loopBody777_11 loopBody777_275

def loopBody777_277 : HolLoopProg 64 :=
.mark loopBody777_276

def loopBody777_278 : HolLoopProg 64 :=
.seq loopBody777_1 loopBody777_277

def loopBody777_279 : HolLoopProg 64 :=
.mark loopBody777_278

def loopBody777_280 : HolLoopProg 64 :=
.seq loopBody777_1 loopBody777_279

def loopBody777_281 : HolLoopProg 64 :=
.mark loopBody777_280

def output777 : Nat × List Nat × HolLoopProg 64 :=
  (841, [0], loopBody777_281)
end InitECandidate.Proofs.FrontendStages.Loop
