import InitECandidate.Proofs.FrontendStages.Loop.Translate447
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody463_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody463_1 : HolLoopProg 64 :=
.mark loopBody463_0

def loopBody463_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody463_3 : HolLoopProg 64 :=
.mark loopBody463_2

def loopBody463_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody463_3, loopBody463_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody463_5 : HolLoopProg 64 :=
.mark loopBody463_4

def loopBody463_6 : HolLoopProg 64 :=
.seq loopBody463_5 loopBody463_1

def loopBody463_7 : HolLoopProg 64 :=
.mark loopBody463_6

def loopBody463_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody463_9 : HolLoopProg 64 :=
.mark loopBody463_8

def loopBody463_10 : HolLoopProg 64 :=
.call (some
  ([5, 6, 7, 8],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 471) ([]) (some (9, loopBody463_9, loopBody463_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody463_11 : HolLoopProg 64 :=
.mark loopBody463_10

def loopBody463_12 : HolLoopProg 64 :=
.seq loopBody463_11 loopBody463_1

def loopBody463_13 : HolLoopProg 64 :=
.mark loopBody463_12

def loopBody463_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 3#64)

def loopBody463_15 : HolLoopProg 64 :=
.mark loopBody463_14

def loopBody463_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 1)

def loopBody463_17 : HolLoopProg 64 :=
.mark loopBody463_16

def loopBody463_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 2)

def loopBody463_19 : HolLoopProg 64 :=
.mark loopBody463_18

def loopBody463_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 3)

def loopBody463_21 : HolLoopProg 64 :=
.mark loopBody463_20

def loopBody463_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 4)

def loopBody463_23 : HolLoopProg 64 :=
.mark loopBody463_22

def loopBody463_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 1#64)

def loopBody463_25 : HolLoopProg 64 :=
.mark loopBody463_24

def loopBody463_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.const 0#64)

def loopBody463_27 : HolLoopProg 64 :=
.mark loopBody463_26

def loopBody463_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.const 0#64)

def loopBody463_29 : HolLoopProg 64 :=
.mark loopBody463_28

def loopBody463_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.const 0#64)

def loopBody463_31 : HolLoopProg 64 :=
.mark loopBody463_30

def loopBody463_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody463_33 : HolLoopProg 64 :=
.mark loopBody463_32

def loopBody463_34 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 479) ([10, 11, 12, 13, 14, 15, 16, 17, 18]) (some (10, loopBody463_33, loopBody463_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody463_35 : HolLoopProg 64 :=
.mark loopBody463_34

def loopBody463_36 : HolLoopProg 64 :=
.seq loopBody463_35 loopBody463_1

def loopBody463_37 : HolLoopProg 64 :=
.mark loopBody463_36

def loopBody463_38 : HolLoopProg 64 :=
.seq loopBody463_31 loopBody463_37

def loopBody463_39 : HolLoopProg 64 :=
.mark loopBody463_38

def loopBody463_40 : HolLoopProg 64 :=
.seq loopBody463_29 loopBody463_39

def loopBody463_41 : HolLoopProg 64 :=
.mark loopBody463_40

def loopBody463_42 : HolLoopProg 64 :=
.seq loopBody463_27 loopBody463_41

def loopBody463_43 : HolLoopProg 64 :=
.mark loopBody463_42

def loopBody463_44 : HolLoopProg 64 :=
.seq loopBody463_25 loopBody463_43

def loopBody463_45 : HolLoopProg 64 :=
.mark loopBody463_44

def loopBody463_46 : HolLoopProg 64 :=
.seq loopBody463_23 loopBody463_45

def loopBody463_47 : HolLoopProg 64 :=
.mark loopBody463_46

def loopBody463_48 : HolLoopProg 64 :=
.seq loopBody463_21 loopBody463_47

def loopBody463_49 : HolLoopProg 64 :=
.mark loopBody463_48

def loopBody463_50 : HolLoopProg 64 :=
.seq loopBody463_19 loopBody463_49

def loopBody463_51 : HolLoopProg 64 :=
.mark loopBody463_50

def loopBody463_52 : HolLoopProg 64 :=
.seq loopBody463_17 loopBody463_51

def loopBody463_53 : HolLoopProg 64 :=
.mark loopBody463_52

def loopBody463_54 : HolLoopProg 64 :=
.seq loopBody463_15 loopBody463_53

def loopBody463_55 : HolLoopProg 64 :=
.mark loopBody463_54

def loopBody463_56 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_55

def loopBody463_57 : HolLoopProg 64 :=
.mark loopBody463_56

def loopBody463_58 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_57

def loopBody463_59 : HolLoopProg 64 :=
.mark loopBody463_58

def loopBody463_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 1)

def loopBody463_61 : HolLoopProg 64 :=
.mark loopBody463_60

def loopBody463_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 2)

def loopBody463_63 : HolLoopProg 64 :=
.mark loopBody463_62

def loopBody463_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 3)

def loopBody463_65 : HolLoopProg 64 :=
.mark loopBody463_64

def loopBody463_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 4)

def loopBody463_67 : HolLoopProg 64 :=
.mark loopBody463_66

def loopBody463_68 : HolLoopProg 64 :=
.call (some ([9], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))) (some 458) ([10, 11, 12, 13]) (some (10, loopBody463_33, loopBody463_1, (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))

def loopBody463_69 : HolLoopProg 64 :=
.mark loopBody463_68

def loopBody463_70 : HolLoopProg 64 :=
.seq loopBody463_69 loopBody463_1

def loopBody463_71 : HolLoopProg 64 :=
.mark loopBody463_70

def loopBody463_72 : HolLoopProg 64 :=
.seq loopBody463_67 loopBody463_71

def loopBody463_73 : HolLoopProg 64 :=
.mark loopBody463_72

def loopBody463_74 : HolLoopProg 64 :=
.seq loopBody463_65 loopBody463_73

def loopBody463_75 : HolLoopProg 64 :=
.mark loopBody463_74

def loopBody463_76 : HolLoopProg 64 :=
.seq loopBody463_63 loopBody463_75

def loopBody463_77 : HolLoopProg 64 :=
.mark loopBody463_76

def loopBody463_78 : HolLoopProg 64 :=
.seq loopBody463_61 loopBody463_77

def loopBody463_79 : HolLoopProg 64 :=
.mark loopBody463_78

def loopBody463_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 24#64]),
      Flapjack.HolLoopExp.var 9])

def loopBody463_81 : HolLoopProg 64 :=
.mark loopBody463_80

def loopBody463_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 255#64])

def loopBody463_83 : HolLoopProg 64 :=
.mark loopBody463_82

def loopBody463_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 10 11

def loopBody463_85 : HolLoopProg 64 :=
.mark loopBody463_84

def loopBody463_86 : HolLoopProg 64 :=
.seq loopBody463_85 loopBody463_1

def loopBody463_87 : HolLoopProg 64 :=
.mark loopBody463_86

def loopBody463_88 : HolLoopProg 64 :=
.seq loopBody463_83 loopBody463_87

def loopBody463_89 : HolLoopProg 64 :=
.mark loopBody463_88

def loopBody463_90 : HolLoopProg 64 :=
.seq loopBody463_81 loopBody463_89

def loopBody463_91 : HolLoopProg 64 :=
.mark loopBody463_90

def loopBody463_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 1#64)

def loopBody463_93 : HolLoopProg 64 :=
.mark loopBody463_92

def loopBody463_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 11

def loopBody463_95 : HolLoopProg 64 :=
.mark loopBody463_94

def loopBody463_96 : HolLoopProg 64 :=
.call (some ([10], Flapjack.Spt.ln)) (some 486) ([11]) (some (11, loopBody463_95, loopBody463_1, (Flapjack.Spt.ln)))

def loopBody463_97 : HolLoopProg 64 :=
.mark loopBody463_96

def loopBody463_98 : HolLoopProg 64 :=
.seq loopBody463_97 loopBody463_1

def loopBody463_99 : HolLoopProg 64 :=
.mark loopBody463_98

def loopBody463_100 : HolLoopProg 64 :=
.seq loopBody463_93 loopBody463_99

def loopBody463_101 : HolLoopProg 64 :=
.mark loopBody463_100

def loopBody463_102 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_101

def loopBody463_103 : HolLoopProg 64 :=
.mark loopBody463_102

def loopBody463_104 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_103

def loopBody463_105 : HolLoopProg 64 :=
.mark loopBody463_104

def loopBody463_106 : HolLoopProg 64 :=
.seq loopBody463_91 loopBody463_105

def loopBody463_107 : HolLoopProg 64 :=
.mark loopBody463_106

def loopBody463_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody463_109 : HolLoopProg 64 :=
.mark loopBody463_108

def loopBody463_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [10]

def loopBody463_111 : HolLoopProg 64 :=
.mark loopBody463_110

def loopBody463_112 : HolLoopProg 64 :=
.seq loopBody463_111 loopBody463_1

def loopBody463_113 : HolLoopProg 64 :=
.mark loopBody463_112

def loopBody463_114 : HolLoopProg 64 :=
.seq loopBody463_109 loopBody463_113

def loopBody463_115 : HolLoopProg 64 :=
.mark loopBody463_114

def loopBody463_116 : HolLoopProg 64 :=
.seq loopBody463_107 loopBody463_115

def loopBody463_117 : HolLoopProg 64 :=
.mark loopBody463_116

def loopBody463_118 : HolLoopProg 64 :=
.seq loopBody463_79 loopBody463_117

def loopBody463_119 : HolLoopProg 64 :=
.mark loopBody463_118

def loopBody463_120 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_119

def loopBody463_121 : HolLoopProg 64 :=
.mark loopBody463_120

def loopBody463_122 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_121

def loopBody463_123 : HolLoopProg 64 :=
.mark loopBody463_122

def loopBody463_124 : HolLoopProg 64 :=
.seq loopBody463_59 loopBody463_123

def loopBody463_125 : HolLoopProg 64 :=
.mark loopBody463_124

def loopBody463_126 : HolLoopProg 64 :=
.seq loopBody463_13 loopBody463_125

def loopBody463_127 : HolLoopProg 64 :=
.mark loopBody463_126

def loopBody463_128 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_127

def loopBody463_129 : HolLoopProg 64 :=
.mark loopBody463_128

def loopBody463_130 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_129

def loopBody463_131 : HolLoopProg 64 :=
.mark loopBody463_130

def loopBody463_132 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_131

def loopBody463_133 : HolLoopProg 64 :=
.mark loopBody463_132

def loopBody463_134 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_133

def loopBody463_135 : HolLoopProg 64 :=
.mark loopBody463_134

def loopBody463_136 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_135

def loopBody463_137 : HolLoopProg 64 :=
.mark loopBody463_136

def loopBody463_138 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_137

def loopBody463_139 : HolLoopProg 64 :=
.mark loopBody463_138

def loopBody463_140 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_139

def loopBody463_141 : HolLoopProg 64 :=
.mark loopBody463_140

def loopBody463_142 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_141

def loopBody463_143 : HolLoopProg 64 :=
.mark loopBody463_142

def loopBody463_144 : HolLoopProg 64 :=
.seq loopBody463_7 loopBody463_143

def loopBody463_145 : HolLoopProg 64 :=
.mark loopBody463_144

def loopBody463_146 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_145

def loopBody463_147 : HolLoopProg 64 :=
.mark loopBody463_146

def loopBody463_148 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_147

def loopBody463_149 : HolLoopProg 64 :=
.mark loopBody463_148

def loopBody463_150 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_149

def loopBody463_151 : HolLoopProg 64 :=
.mark loopBody463_150

def loopBody463_152 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_151

def loopBody463_153 : HolLoopProg 64 :=
.mark loopBody463_152

def loopBody463_154 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_153

def loopBody463_155 : HolLoopProg 64 :=
.mark loopBody463_154

def loopBody463_156 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_155

def loopBody463_157 : HolLoopProg 64 :=
.mark loopBody463_156

def loopBody463_158 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_157

def loopBody463_159 : HolLoopProg 64 :=
.mark loopBody463_158

def loopBody463_160 : HolLoopProg 64 :=
.seq loopBody463_1 loopBody463_159

def loopBody463_161 : HolLoopProg 64 :=
.mark loopBody463_160

def output463 : Nat × List Nat × HolLoopProg 64 :=
  (527, [], loopBody463_161)
end InitECandidate.Proofs.FrontendStages.Loop
