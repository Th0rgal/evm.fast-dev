import InitECandidate.Proofs.WordStages.Source622
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody638_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody638_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 2)

def sourceBody638_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 4)

def sourceBody638_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody638_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 8)

def sourceBody638_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody638_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 12)

def sourceBody638_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody638_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 16)

def sourceBody638_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody638_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([38, 28, 48, 24, 44]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody638_0, 638, 2)) (some 115) ([34, 52, 18, 36, 26, 46, 22, 42]) (some (34, sourceBody638_9, 638, 3))

def sourceBody638_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody638_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_10 sourceBody638_11

def sourceBody638_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_12 sourceBody638_0

def sourceBody638_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_8 sourceBody638_13

def sourceBody638_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_7 sourceBody638_14

def sourceBody638_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_6 sourceBody638_15

def sourceBody638_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_5 sourceBody638_16

def sourceBody638_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_4 sourceBody638_17

def sourceBody638_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_3 sourceBody638_18

def sourceBody638_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_2 sourceBody638_19

def sourceBody638_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_1 sourceBody638_20

def sourceBody638_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 38)

def sourceBody638_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 28)

def sourceBody638_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 48)

def sourceBody638_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 24)

def sourceBody638_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 44)

def sourceBody638_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody638_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody638_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody638_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 46 (Flapjack.WordRegImm.reg 22) sourceBody638_28 sourceBody638_29

def sourceBody638_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_30 sourceBody638_11

def sourceBody638_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 46)

def sourceBody638_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 34)

def sourceBody638_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 52)

def sourceBody638_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody638_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 36)

def sourceBody638_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 18446744073709551615#64)

def sourceBody638_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 4294967295#64)

def sourceBody638_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody638_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 18446744069414584321#64)

def sourceBody638_41 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 117) ([0, 26, 46, 22, 42, 32, 50, 20, 40]) (none)

def sourceBody638_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_41 sourceBody638_0

def sourceBody638_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_40 sourceBody638_42

def sourceBody638_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_39 sourceBody638_43

def sourceBody638_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_38 sourceBody638_44

def sourceBody638_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_37 sourceBody638_45

def sourceBody638_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_36 sourceBody638_46

def sourceBody638_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_35 sourceBody638_47

def sourceBody638_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_34 sourceBody638_48

def sourceBody638_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_33 sourceBody638_49

def sourceBody638_51 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.imm 0#64) sourceBody638_50 sourceBody638_0

def sourceBody638_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_51 sourceBody638_11

def sourceBody638_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_52 sourceBody638_0

def sourceBody638_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_32 sourceBody638_53

def sourceBody638_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_31 sourceBody638_54

def sourceBody638_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_27 sourceBody638_55

def sourceBody638_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_26 sourceBody638_56

def sourceBody638_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 34)

def sourceBody638_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 52)

def sourceBody638_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 18)

def sourceBody638_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 36)

def sourceBody638_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 18446744073709551615#64)

def sourceBody638_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 4294967295#64)

def sourceBody638_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody638_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 18446744069414584321#64)

def sourceBody638_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody638_67 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody638_0, 638, 4)) (some 106) ([46, 22, 42, 32, 50, 20, 40, 30]) (some (46, sourceBody638_66, 638, 5))

def sourceBody638_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_67 sourceBody638_11

def sourceBody638_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_68 sourceBody638_0

def sourceBody638_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_65 sourceBody638_69

def sourceBody638_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_64 sourceBody638_70

def sourceBody638_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_63 sourceBody638_71

def sourceBody638_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_62 sourceBody638_72

def sourceBody638_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_61 sourceBody638_73

def sourceBody638_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_60 sourceBody638_74

def sourceBody638_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_59 sourceBody638_75

def sourceBody638_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_58 sourceBody638_76

def sourceBody638_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody638_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody638_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody638_81 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 22 (Flapjack.WordRegImm.reg 42) sourceBody638_27 sourceBody638_80

def sourceBody638_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_81 sourceBody638_11

def sourceBody638_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 22)

def sourceBody638_84 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 117) ([0, 46, 22, 42, 32, 50, 20, 40, 30]) (none)

def sourceBody638_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_84 sourceBody638_0

def sourceBody638_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_65 sourceBody638_85

def sourceBody638_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_64 sourceBody638_86

def sourceBody638_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_63 sourceBody638_87

def sourceBody638_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_62 sourceBody638_88

def sourceBody638_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_61 sourceBody638_89

def sourceBody638_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_60 sourceBody638_90

def sourceBody638_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_59 sourceBody638_91

def sourceBody638_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_58 sourceBody638_92

def sourceBody638_94 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody638_93 sourceBody638_0

def sourceBody638_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_94 sourceBody638_11

def sourceBody638_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_95 sourceBody638_0

def sourceBody638_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_83 sourceBody638_96

def sourceBody638_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_82 sourceBody638_97

def sourceBody638_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_79 sourceBody638_98

def sourceBody638_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_78 sourceBody638_99

def sourceBody638_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [46, 22, 42, 32]

def sourceBody638_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_101 sourceBody638_0

def sourceBody638_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_61 sourceBody638_102

def sourceBody638_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_60 sourceBody638_103

def sourceBody638_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_59 sourceBody638_104

def sourceBody638_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_58 sourceBody638_105

def sourceBody638_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_100 sourceBody638_106

def sourceBody638_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_77 sourceBody638_107

def sourceBody638_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_0 sourceBody638_108

def sourceBody638_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_0 sourceBody638_109

def sourceBody638_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_57 sourceBody638_110

def sourceBody638_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_25 sourceBody638_111

def sourceBody638_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_0 sourceBody638_112

def sourceBody638_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_24 sourceBody638_113

def sourceBody638_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_0 sourceBody638_114

def sourceBody638_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_23 sourceBody638_115

def sourceBody638_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_0 sourceBody638_116

def sourceBody638_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_22 sourceBody638_117

def sourceBody638_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_0 sourceBody638_118

def sourceBody638_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_21 sourceBody638_119

def sourceBody638_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_0 sourceBody638_120

def sourceBody638_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_0 sourceBody638_121

def sourceBody638_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_0 sourceBody638_122

def sourceBody638_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_0 sourceBody638_123

def sourceBody638_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_0 sourceBody638_124

def sourceBody638_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_0 sourceBody638_125

def sourceBody638_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_0 sourceBody638_126

def sourceBody638_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_0 sourceBody638_127

def sourceBody638_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_0 sourceBody638_128

def sourceBody638_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody638_0 sourceBody638_129

def source638 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (638, 9, sourceBody638_130)
end InitECandidate.Proofs.WordStages
