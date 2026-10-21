import InitECandidate.Proofs.FrontendStages.Loop.Translate574
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody590_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody590_1 : HolLoopProg 64 :=
.mark loopBody590_0

def loopBody590_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 0)

def loopBody590_3 : HolLoopProg 64 :=
.mark loopBody590_2

def loopBody590_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 1)

def loopBody590_5 : HolLoopProg 64 :=
.mark loopBody590_4

def loopBody590_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 2)

def loopBody590_7 : HolLoopProg 64 :=
.mark loopBody590_6

def loopBody590_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 3)

def loopBody590_9 : HolLoopProg 64 :=
.mark loopBody590_8

def loopBody590_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 4)

def loopBody590_11 : HolLoopProg 64 :=
.mark loopBody590_10

def loopBody590_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 5)

def loopBody590_13 : HolLoopProg 64 :=
.mark loopBody590_12

def loopBody590_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 6)

def loopBody590_15 : HolLoopProg 64 :=
.mark loopBody590_14

def loopBody590_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 7)

def loopBody590_17 : HolLoopProg 64 :=
.mark loopBody590_16

def loopBody590_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 12

def loopBody590_19 : HolLoopProg 64 :=
.mark loopBody590_18

def loopBody590_20 : HolLoopProg 64 :=
.call (some ([8, 9, 10, 11], Flapjack.Spt.ln)) (some 116) ([12, 13, 14, 15, 16, 17, 18, 19]) (some (12, loopBody590_19, loopBody590_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))

def loopBody590_21 : HolLoopProg 64 :=
.mark loopBody590_20

def loopBody590_22 : HolLoopProg 64 :=
.seq loopBody590_21 loopBody590_1

def loopBody590_23 : HolLoopProg 64 :=
.mark loopBody590_22

def loopBody590_24 : HolLoopProg 64 :=
.seq loopBody590_17 loopBody590_23

def loopBody590_25 : HolLoopProg 64 :=
.mark loopBody590_24

def loopBody590_26 : HolLoopProg 64 :=
.seq loopBody590_15 loopBody590_25

def loopBody590_27 : HolLoopProg 64 :=
.mark loopBody590_26

def loopBody590_28 : HolLoopProg 64 :=
.seq loopBody590_13 loopBody590_27

def loopBody590_29 : HolLoopProg 64 :=
.mark loopBody590_28

def loopBody590_30 : HolLoopProg 64 :=
.seq loopBody590_11 loopBody590_29

def loopBody590_31 : HolLoopProg 64 :=
.mark loopBody590_30

def loopBody590_32 : HolLoopProg 64 :=
.seq loopBody590_9 loopBody590_31

def loopBody590_33 : HolLoopProg 64 :=
.mark loopBody590_32

def loopBody590_34 : HolLoopProg 64 :=
.seq loopBody590_7 loopBody590_33

def loopBody590_35 : HolLoopProg 64 :=
.mark loopBody590_34

def loopBody590_36 : HolLoopProg 64 :=
.seq loopBody590_5 loopBody590_35

def loopBody590_37 : HolLoopProg 64 :=
.mark loopBody590_36

def loopBody590_38 : HolLoopProg 64 :=
.seq loopBody590_3 loopBody590_37

def loopBody590_39 : HolLoopProg 64 :=
.mark loopBody590_38

def loopBody590_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 8)

def loopBody590_41 : HolLoopProg 64 :=
.mark loopBody590_40

def loopBody590_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 9)

def loopBody590_43 : HolLoopProg 64 :=
.mark loopBody590_42

def loopBody590_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 10)

def loopBody590_45 : HolLoopProg 64 :=
.mark loopBody590_44

def loopBody590_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 11)

def loopBody590_47 : HolLoopProg 64 :=
.mark loopBody590_46

def loopBody590_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.const 4332616871279656263#64)

def loopBody590_49 : HolLoopProg 64 :=
.mark loopBody590_48

def loopBody590_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.const 10917124144477883021#64)

def loopBody590_51 : HolLoopProg 64 :=
.mark loopBody590_50

def loopBody590_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.const 13281191951274694749#64)

def loopBody590_53 : HolLoopProg 64 :=
.mark loopBody590_52

def loopBody590_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.const 3486998266802970665#64)

def loopBody590_55 : HolLoopProg 64 :=
.mark loopBody590_54

def loopBody590_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 13

def loopBody590_57 : HolLoopProg 64 :=
.mark loopBody590_56

def loopBody590_58 : HolLoopProg 64 :=
.call (some
  ([12],
    Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))) (some 106) ([13, 14, 15, 16, 17, 18, 19, 20]) (some (13, loopBody590_57, loopBody590_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))

def loopBody590_59 : HolLoopProg 64 :=
.mark loopBody590_58

def loopBody590_60 : HolLoopProg 64 :=
.seq loopBody590_59 loopBody590_1

def loopBody590_61 : HolLoopProg 64 :=
.mark loopBody590_60

def loopBody590_62 : HolLoopProg 64 :=
.seq loopBody590_55 loopBody590_61

def loopBody590_63 : HolLoopProg 64 :=
.mark loopBody590_62

def loopBody590_64 : HolLoopProg 64 :=
.seq loopBody590_53 loopBody590_63

def loopBody590_65 : HolLoopProg 64 :=
.mark loopBody590_64

def loopBody590_66 : HolLoopProg 64 :=
.seq loopBody590_51 loopBody590_65

def loopBody590_67 : HolLoopProg 64 :=
.mark loopBody590_66

def loopBody590_68 : HolLoopProg 64 :=
.seq loopBody590_49 loopBody590_67

def loopBody590_69 : HolLoopProg 64 :=
.mark loopBody590_68

def loopBody590_70 : HolLoopProg 64 :=
.seq loopBody590_47 loopBody590_69

def loopBody590_71 : HolLoopProg 64 :=
.mark loopBody590_70

def loopBody590_72 : HolLoopProg 64 :=
.seq loopBody590_45 loopBody590_71

def loopBody590_73 : HolLoopProg 64 :=
.mark loopBody590_72

def loopBody590_74 : HolLoopProg 64 :=
.seq loopBody590_43 loopBody590_73

def loopBody590_75 : HolLoopProg 64 :=
.mark loopBody590_74

def loopBody590_76 : HolLoopProg 64 :=
.seq loopBody590_41 loopBody590_75

def loopBody590_77 : HolLoopProg 64 :=
.mark loopBody590_76

def loopBody590_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 12)

def loopBody590_79 : HolLoopProg 64 :=
.mark loopBody590_78

def loopBody590_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 0#64)

def loopBody590_81 : HolLoopProg 64 :=
.mark loopBody590_80

def loopBody590_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 1#64)

def loopBody590_83 : HolLoopProg 64 :=
.mark loopBody590_82

def loopBody590_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 0#64)

def loopBody590_85 : HolLoopProg 64 :=
.mark loopBody590_84

def loopBody590_86 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.RegImm.reg 15) loopBody590_83 loopBody590_85 (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody590_87 : HolLoopProg 64 :=
.mark loopBody590_86

def loopBody590_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 14)

def loopBody590_89 : HolLoopProg 64 :=
.mark loopBody590_88

def loopBody590_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 117) [13, 14, 15, 16, 17, 18, 19, 20] none

def loopBody590_91 : HolLoopProg 64 :=
.mark loopBody590_90

def loopBody590_92 : HolLoopProg 64 :=
.seq loopBody590_91 loopBody590_1

def loopBody590_93 : HolLoopProg 64 :=
.mark loopBody590_92

def loopBody590_94 : HolLoopProg 64 :=
.seq loopBody590_55 loopBody590_93

def loopBody590_95 : HolLoopProg 64 :=
.mark loopBody590_94

def loopBody590_96 : HolLoopProg 64 :=
.seq loopBody590_53 loopBody590_95

def loopBody590_97 : HolLoopProg 64 :=
.mark loopBody590_96

def loopBody590_98 : HolLoopProg 64 :=
.seq loopBody590_51 loopBody590_97

def loopBody590_99 : HolLoopProg 64 :=
.mark loopBody590_98

def loopBody590_100 : HolLoopProg 64 :=
.seq loopBody590_49 loopBody590_99

def loopBody590_101 : HolLoopProg 64 :=
.mark loopBody590_100

def loopBody590_102 : HolLoopProg 64 :=
.seq loopBody590_47 loopBody590_101

def loopBody590_103 : HolLoopProg 64 :=
.mark loopBody590_102

def loopBody590_104 : HolLoopProg 64 :=
.seq loopBody590_45 loopBody590_103

def loopBody590_105 : HolLoopProg 64 :=
.mark loopBody590_104

def loopBody590_106 : HolLoopProg 64 :=
.seq loopBody590_43 loopBody590_105

def loopBody590_107 : HolLoopProg 64 :=
.mark loopBody590_106

def loopBody590_108 : HolLoopProg 64 :=
.seq loopBody590_41 loopBody590_107

def loopBody590_109 : HolLoopProg 64 :=
.mark loopBody590_108

def loopBody590_110 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.RegImm.imm 0#64) loopBody590_109 loopBody590_1 (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody590_111 : HolLoopProg 64 :=
.mark loopBody590_110

def loopBody590_112 : HolLoopProg 64 :=
.seq loopBody590_111 loopBody590_1

def loopBody590_113 : HolLoopProg 64 :=
.mark loopBody590_112

def loopBody590_114 : HolLoopProg 64 :=
.seq loopBody590_89 loopBody590_113

def loopBody590_115 : HolLoopProg 64 :=
.mark loopBody590_114

def loopBody590_116 : HolLoopProg 64 :=
.seq loopBody590_87 loopBody590_115

def loopBody590_117 : HolLoopProg 64 :=
.mark loopBody590_116

def loopBody590_118 : HolLoopProg 64 :=
.seq loopBody590_81 loopBody590_117

def loopBody590_119 : HolLoopProg 64 :=
.mark loopBody590_118

def loopBody590_120 : HolLoopProg 64 :=
.seq loopBody590_79 loopBody590_119

def loopBody590_121 : HolLoopProg 64 :=
.mark loopBody590_120

def loopBody590_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [13, 14, 15, 16]

def loopBody590_123 : HolLoopProg 64 :=
.mark loopBody590_122

def loopBody590_124 : HolLoopProg 64 :=
.seq loopBody590_123 loopBody590_1

def loopBody590_125 : HolLoopProg 64 :=
.mark loopBody590_124

def loopBody590_126 : HolLoopProg 64 :=
.seq loopBody590_47 loopBody590_125

def loopBody590_127 : HolLoopProg 64 :=
.mark loopBody590_126

def loopBody590_128 : HolLoopProg 64 :=
.seq loopBody590_45 loopBody590_127

def loopBody590_129 : HolLoopProg 64 :=
.mark loopBody590_128

def loopBody590_130 : HolLoopProg 64 :=
.seq loopBody590_43 loopBody590_129

def loopBody590_131 : HolLoopProg 64 :=
.mark loopBody590_130

def loopBody590_132 : HolLoopProg 64 :=
.seq loopBody590_41 loopBody590_131

def loopBody590_133 : HolLoopProg 64 :=
.mark loopBody590_132

def loopBody590_134 : HolLoopProg 64 :=
.seq loopBody590_121 loopBody590_133

def loopBody590_135 : HolLoopProg 64 :=
.mark loopBody590_134

def loopBody590_136 : HolLoopProg 64 :=
.seq loopBody590_77 loopBody590_135

def loopBody590_137 : HolLoopProg 64 :=
.mark loopBody590_136

def loopBody590_138 : HolLoopProg 64 :=
.seq loopBody590_1 loopBody590_137

def loopBody590_139 : HolLoopProg 64 :=
.mark loopBody590_138

def loopBody590_140 : HolLoopProg 64 :=
.seq loopBody590_1 loopBody590_139

def loopBody590_141 : HolLoopProg 64 :=
.mark loopBody590_140

def loopBody590_142 : HolLoopProg 64 :=
.seq loopBody590_39 loopBody590_141

def loopBody590_143 : HolLoopProg 64 :=
.mark loopBody590_142

def loopBody590_144 : HolLoopProg 64 :=
.seq loopBody590_1 loopBody590_143

def loopBody590_145 : HolLoopProg 64 :=
.mark loopBody590_144

def loopBody590_146 : HolLoopProg 64 :=
.seq loopBody590_1 loopBody590_145

def loopBody590_147 : HolLoopProg 64 :=
.mark loopBody590_146

def loopBody590_148 : HolLoopProg 64 :=
.seq loopBody590_1 loopBody590_147

def loopBody590_149 : HolLoopProg 64 :=
.mark loopBody590_148

def loopBody590_150 : HolLoopProg 64 :=
.seq loopBody590_1 loopBody590_149

def loopBody590_151 : HolLoopProg 64 :=
.mark loopBody590_150

def loopBody590_152 : HolLoopProg 64 :=
.seq loopBody590_1 loopBody590_151

def loopBody590_153 : HolLoopProg 64 :=
.mark loopBody590_152

def loopBody590_154 : HolLoopProg 64 :=
.seq loopBody590_1 loopBody590_153

def loopBody590_155 : HolLoopProg 64 :=
.mark loopBody590_154

def loopBody590_156 : HolLoopProg 64 :=
.seq loopBody590_1 loopBody590_155

def loopBody590_157 : HolLoopProg 64 :=
.mark loopBody590_156

def loopBody590_158 : HolLoopProg 64 :=
.seq loopBody590_1 loopBody590_157

def loopBody590_159 : HolLoopProg 64 :=
.mark loopBody590_158

def output590 : Nat × List Nat × HolLoopProg 64 :=
  (654, [0, 1, 2, 3, 4, 5, 6, 7], loopBody590_159)
end InitECandidate.Proofs.FrontendStages.Loop
