import InitECandidate.Proofs.WordStages.Source486
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody502_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody502_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody502_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 34, 6, 28]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody502_0, 502, 2)) (some 471) ([]) (some (18, sourceBody502_1, 502, 3))

def sourceBody502_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody502_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_2 sourceBody502_3

def sourceBody502_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_4 sourceBody502_0

def sourceBody502_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody502_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 40, 4, 26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody502_0, 502, 4)) (some 471) ([]) (some (16, sourceBody502_6, 502, 5))

def sourceBody502_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_7 sourceBody502_3

def sourceBody502_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_8 sourceBody502_0

def sourceBody502_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 18)

def sourceBody502_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 40)

def sourceBody502_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 4)

def sourceBody502_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody502_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody502_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody502_0, 502, 6)) (some 139) ([38, 10, 32, 22]) (some (38, sourceBody502_14, 502, 7))

def sourceBody502_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_15 sourceBody502_3

def sourceBody502_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_16 sourceBody502_0

def sourceBody502_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_13 sourceBody502_17

def sourceBody502_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_12 sourceBody502_18

def sourceBody502_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_11 sourceBody502_19

def sourceBody502_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_10 sourceBody502_20

def sourceBody502_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody502_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 50#64)

def sourceBody502_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 22 22 10 32))

def sourceBody502_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.const 10#64, Flapjack.WordLangExpHOL.var 22])

def sourceBody502_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody502_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody502_0, 502, 8)) (some 466) ([42]) (some (10, sourceBody502_26, 502, 9))

def sourceBody502_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_27 sourceBody502_3

def sourceBody502_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_28 sourceBody502_0

def sourceBody502_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_25 sourceBody502_29

def sourceBody502_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_24 sourceBody502_30

def sourceBody502_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_23 sourceBody502_31

def sourceBody502_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_22 sourceBody502_32

def sourceBody502_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_33

def sourceBody502_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_34

def sourceBody502_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 12)

def sourceBody502_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 34)

def sourceBody502_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 6)

def sourceBody502_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 28)

def sourceBody502_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 18)

def sourceBody502_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 40)

def sourceBody502_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 4)

def sourceBody502_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 26)

def sourceBody502_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody502_45 : WordLangProgHOL (BitVec 64) :=
.call (some (([38, 10, 32, 22]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody502_0, 502, 10)) (some 140) ([42, 2, 24, 14, 36, 8, 30, 20]) (some (42, sourceBody502_44, 502, 11))

def sourceBody502_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_45 sourceBody502_3

def sourceBody502_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_46 sourceBody502_0

def sourceBody502_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_43 sourceBody502_47

def sourceBody502_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_42 sourceBody502_48

def sourceBody502_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_41 sourceBody502_49

def sourceBody502_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_40 sourceBody502_50

def sourceBody502_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_39 sourceBody502_51

def sourceBody502_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_38 sourceBody502_52

def sourceBody502_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_37 sourceBody502_53

def sourceBody502_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_36 sourceBody502_54

def sourceBody502_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 38)

def sourceBody502_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody502_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 32)

def sourceBody502_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 22)

def sourceBody502_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody502_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody502_0, 502, 12)) (some 472) ([2, 24, 14, 36]) (some (2, sourceBody502_60, 502, 13))

def sourceBody502_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_61 sourceBody502_3

def sourceBody502_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_62 sourceBody502_0

def sourceBody502_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_59 sourceBody502_63

def sourceBody502_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_58 sourceBody502_64

def sourceBody502_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_57 sourceBody502_65

def sourceBody502_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_56 sourceBody502_66

def sourceBody502_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_67

def sourceBody502_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_68

def sourceBody502_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody502_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody502_0, 502, 14)) (some 486) ([2]) (some (2, sourceBody502_60, 502, 15))

def sourceBody502_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_71 sourceBody502_3

def sourceBody502_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_72 sourceBody502_0

def sourceBody502_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_70 sourceBody502_73

def sourceBody502_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_74

def sourceBody502_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_75

def sourceBody502_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_69 sourceBody502_76

def sourceBody502_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody502_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [42]

def sourceBody502_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_79 sourceBody502_0

def sourceBody502_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_78 sourceBody502_80

def sourceBody502_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_77 sourceBody502_81

def sourceBody502_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_55 sourceBody502_82

def sourceBody502_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_83

def sourceBody502_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_84

def sourceBody502_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_85

def sourceBody502_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_86

def sourceBody502_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_87

def sourceBody502_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_88

def sourceBody502_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_89

def sourceBody502_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_90

def sourceBody502_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_35 sourceBody502_91

def sourceBody502_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_21 sourceBody502_92

def sourceBody502_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_93

def sourceBody502_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_94

def sourceBody502_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_9 sourceBody502_95

def sourceBody502_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_96

def sourceBody502_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_97

def sourceBody502_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_98

def sourceBody502_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_99

def sourceBody502_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_100

def sourceBody502_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_101

def sourceBody502_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_102

def sourceBody502_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_103

def sourceBody502_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_5 sourceBody502_104

def sourceBody502_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_105

def sourceBody502_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_106

def sourceBody502_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_107

def sourceBody502_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_108

def sourceBody502_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_109

def sourceBody502_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_110

def sourceBody502_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_111

def sourceBody502_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody502_0 sourceBody502_112

def source502 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (502, 1, sourceBody502_113)
end InitECandidate.Proofs.WordStages
