import InitECandidate.Proofs.WordStages.Source690
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody706_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody706_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 2)

def sourceBody706_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 4)

def sourceBody706_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 6)

def sourceBody706_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 84 (Flapjack.WordLangExpHOL.var 8)

def sourceBody706_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody706_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 12)

def sourceBody706_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 14)

def sourceBody706_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 16)

def sourceBody706_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 18)

def sourceBody706_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 20)

def sourceBody706_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 22)

def sourceBody706_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 88 (Flapjack.WordLangExpHOL.var 24)

def sourceBody706_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody706_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([70, 54, 86, 28, 60, 44, 76]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody706_0, 706, 2)) (some 704) ([36, 68, 52, 84, 32, 64, 48, 80, 40, 72, 56, 88]) (some (36, sourceBody706_13, 706, 3))

def sourceBody706_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody706_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_14 sourceBody706_15

def sourceBody706_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_16 sourceBody706_0

def sourceBody706_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_12 sourceBody706_17

def sourceBody706_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_11 sourceBody706_18

def sourceBody706_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_10 sourceBody706_19

def sourceBody706_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_9 sourceBody706_20

def sourceBody706_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_8 sourceBody706_21

def sourceBody706_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_7 sourceBody706_22

def sourceBody706_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_6 sourceBody706_23

def sourceBody706_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_5 sourceBody706_24

def sourceBody706_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_4 sourceBody706_25

def sourceBody706_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_3 sourceBody706_26

def sourceBody706_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_2 sourceBody706_27

def sourceBody706_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_1 sourceBody706_28

def sourceBody706_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 70)

def sourceBody706_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 54)

def sourceBody706_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 86)

def sourceBody706_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 84 (Flapjack.WordLangExpHOL.var 28)

def sourceBody706_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 60)

def sourceBody706_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 44)

def sourceBody706_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 36)

def sourceBody706_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 68)

def sourceBody706_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 52)

def sourceBody706_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 84)

def sourceBody706_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 32)

def sourceBody706_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 64)

def sourceBody706_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.const 13402431016077863595#64)

def sourceBody706_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 2210141511517208575#64)

def sourceBody706_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 7435674573564081700#64)

def sourceBody706_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 7239337960414712511#64)

def sourceBody706_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.const 5412103778470702295#64)

def sourceBody706_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1873798617647539866#64)

def sourceBody706_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 58

def sourceBody706_49 : WordLangProgHOL (BitVec 64) :=
.call (some (([48, 80, 40, 72, 56, 88, 26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody706_0, 706, 4)) (some 705) ([58, 42, 74, 34, 66, 50, 82, 30, 62, 46, 78, 38]) (some (58, sourceBody706_48, 706, 5))

def sourceBody706_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_49 sourceBody706_15

def sourceBody706_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_50 sourceBody706_0

def sourceBody706_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_47 sourceBody706_51

def sourceBody706_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_46 sourceBody706_52

def sourceBody706_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_45 sourceBody706_53

def sourceBody706_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_44 sourceBody706_54

def sourceBody706_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_43 sourceBody706_55

def sourceBody706_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_42 sourceBody706_56

def sourceBody706_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_41 sourceBody706_57

def sourceBody706_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_40 sourceBody706_58

def sourceBody706_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_39 sourceBody706_59

def sourceBody706_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_38 sourceBody706_60

def sourceBody706_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_37 sourceBody706_61

def sourceBody706_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_36 sourceBody706_62

def sourceBody706_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 26)

def sourceBody706_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody706_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody706_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody706_68 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 42 (Flapjack.WordRegImm.reg 74) sourceBody706_66 sourceBody706_67

def sourceBody706_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_68 sourceBody706_15

def sourceBody706_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 42)

def sourceBody706_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 48)

def sourceBody706_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 80)

def sourceBody706_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 40)

def sourceBody706_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 72)

def sourceBody706_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 56)

def sourceBody706_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 88)

def sourceBody706_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [58, 42, 74, 34, 66, 50]

def sourceBody706_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_77 sourceBody706_0

def sourceBody706_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_76 sourceBody706_78

def sourceBody706_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_75 sourceBody706_79

def sourceBody706_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_74 sourceBody706_80

def sourceBody706_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_73 sourceBody706_81

def sourceBody706_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_72 sourceBody706_82

def sourceBody706_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_71 sourceBody706_83

def sourceBody706_85 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.imm 0#64) sourceBody706_84 sourceBody706_0

def sourceBody706_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_85 sourceBody706_15

def sourceBody706_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_86 sourceBody706_0

def sourceBody706_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_70 sourceBody706_87

def sourceBody706_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_69 sourceBody706_88

def sourceBody706_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_65 sourceBody706_89

def sourceBody706_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_64 sourceBody706_90

def sourceBody706_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_41 sourceBody706_78

def sourceBody706_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_40 sourceBody706_92

def sourceBody706_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_39 sourceBody706_93

def sourceBody706_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_38 sourceBody706_94

def sourceBody706_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_37 sourceBody706_95

def sourceBody706_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_36 sourceBody706_96

def sourceBody706_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_91 sourceBody706_97

def sourceBody706_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_63 sourceBody706_98

def sourceBody706_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_99

def sourceBody706_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_100

def sourceBody706_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_101

def sourceBody706_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_102

def sourceBody706_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_103

def sourceBody706_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_104

def sourceBody706_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_105

def sourceBody706_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_106

def sourceBody706_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_107

def sourceBody706_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_108

def sourceBody706_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_109

def sourceBody706_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_110

def sourceBody706_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_111

def sourceBody706_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_112

def sourceBody706_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_35 sourceBody706_113

def sourceBody706_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_114

def sourceBody706_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_34 sourceBody706_115

def sourceBody706_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_116

def sourceBody706_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_33 sourceBody706_117

def sourceBody706_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_118

def sourceBody706_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_32 sourceBody706_119

def sourceBody706_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_120

def sourceBody706_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_31 sourceBody706_121

def sourceBody706_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_122

def sourceBody706_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_30 sourceBody706_123

def sourceBody706_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_124

def sourceBody706_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_29 sourceBody706_125

def sourceBody706_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_126

def sourceBody706_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_127

def sourceBody706_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_128

def sourceBody706_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_129

def sourceBody706_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_130

def sourceBody706_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_131

def sourceBody706_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_132

def sourceBody706_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_133

def sourceBody706_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_134

def sourceBody706_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_135

def sourceBody706_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_136

def sourceBody706_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_137

def sourceBody706_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_138

def sourceBody706_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody706_0 sourceBody706_139

def source706 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (706, 13, sourceBody706_140)
end InitECandidate.Proofs.WordStages
