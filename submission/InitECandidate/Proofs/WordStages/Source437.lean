import InitECandidate.Proofs.WordStages.Source421
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody437_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody437_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 2)

def sourceBody437_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody437_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody437_0, 437, 2)) (some 435) ([30]) (some (30, sourceBody437_2, 437, 3))

def sourceBody437_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody437_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_3 sourceBody437_4

def sourceBody437_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_5 sourceBody437_0

def sourceBody437_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_1 sourceBody437_6

def sourceBody437_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody437_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 30)

def sourceBody437_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 4)

def sourceBody437_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody437_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([24, 36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody437_0, 437, 4)) (some 186) ([20, 32]) (some (20, sourceBody437_11, 437, 5))

def sourceBody437_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_12 sourceBody437_4

def sourceBody437_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_13 sourceBody437_0

def sourceBody437_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_10 sourceBody437_14

def sourceBody437_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_9 sourceBody437_15

def sourceBody437_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 24)

def sourceBody437_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody437_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody437_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody437_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 26 (Flapjack.WordRegImm.reg 38) sourceBody437_19 sourceBody437_20

def sourceBody437_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_21 sourceBody437_4

def sourceBody437_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 26)

def sourceBody437_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 40#64)

def sourceBody437_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody437_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody437_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody437_0, 437, 6)) (some 431) ([32, 26]) (some (32, sourceBody437_26, 437, 7))

def sourceBody437_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_27 sourceBody437_4

def sourceBody437_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_28 sourceBody437_0

def sourceBody437_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_25 sourceBody437_29

def sourceBody437_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_24 sourceBody437_30

def sourceBody437_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody437_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 4)

def sourceBody437_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody437_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody437_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody437_0, 437, 8)) (some 192) ([26, 38, 16]) (some (26, sourceBody437_35, 437, 9))

def sourceBody437_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_36 sourceBody437_4

def sourceBody437_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_37 sourceBody437_0

def sourceBody437_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_34 sourceBody437_38

def sourceBody437_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_33 sourceBody437_39

def sourceBody437_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_32 sourceBody437_40

def sourceBody437_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_41

def sourceBody437_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_42

def sourceBody437_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_31 sourceBody437_43

def sourceBody437_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 36)

def sourceBody437_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_45 sourceBody437_0

def sourceBody437_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_46 sourceBody437_0

def sourceBody437_48 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody437_44 sourceBody437_47

def sourceBody437_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_48 sourceBody437_4

def sourceBody437_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_49 sourceBody437_0

def sourceBody437_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_23 sourceBody437_50

def sourceBody437_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_22 sourceBody437_51

def sourceBody437_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_18 sourceBody437_52

def sourceBody437_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_17 sourceBody437_53

def sourceBody437_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 20)

def sourceBody437_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 40#64)

def sourceBody437_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody437_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody437_0, 437, 10)) (some 436) ([26, 38, 16]) (some (26, sourceBody437_35, 437, 11))

def sourceBody437_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_58 sourceBody437_4

def sourceBody437_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_59 sourceBody437_0

def sourceBody437_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_57 sourceBody437_60

def sourceBody437_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_56 sourceBody437_61

def sourceBody437_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_55 sourceBody437_62

def sourceBody437_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody437_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 8)

def sourceBody437_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody437_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 12)

def sourceBody437_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody437_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 38)

def sourceBody437_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 26) 34

def sourceBody437_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_70 sourceBody437_0

def sourceBody437_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_69 sourceBody437_71

def sourceBody437_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody437_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 8#64])
  34

def sourceBody437_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_74 sourceBody437_0

def sourceBody437_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_73 sourceBody437_75

def sourceBody437_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 28)

def sourceBody437_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 16#64])
  34

def sourceBody437_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_78 sourceBody437_0

def sourceBody437_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_77 sourceBody437_79

def sourceBody437_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 22)

def sourceBody437_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 24#64])
  34

def sourceBody437_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_82 sourceBody437_0

def sourceBody437_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_81 sourceBody437_83

def sourceBody437_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_84 sourceBody437_0

def sourceBody437_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_80 sourceBody437_85

def sourceBody437_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_76 sourceBody437_86

def sourceBody437_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_72 sourceBody437_87

def sourceBody437_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_68 sourceBody437_88

def sourceBody437_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_89

def sourceBody437_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_67 sourceBody437_90

def sourceBody437_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_91

def sourceBody437_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_66 sourceBody437_92

def sourceBody437_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_93

def sourceBody437_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_65 sourceBody437_94

def sourceBody437_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_95

def sourceBody437_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_64 sourceBody437_96

def sourceBody437_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_97

def sourceBody437_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody437_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_99 sourceBody437_0

def sourceBody437_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_20 sourceBody437_100

def sourceBody437_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_98 sourceBody437_101

def sourceBody437_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_63 sourceBody437_102

def sourceBody437_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_103

def sourceBody437_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_104

def sourceBody437_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_54 sourceBody437_105

def sourceBody437_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_106

def sourceBody437_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_107

def sourceBody437_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_16 sourceBody437_108

def sourceBody437_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_109

def sourceBody437_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_110

def sourceBody437_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_111

def sourceBody437_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_112

def sourceBody437_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_8 sourceBody437_113

def sourceBody437_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_114

def sourceBody437_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_7 sourceBody437_115

def sourceBody437_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_116

def sourceBody437_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody437_0 sourceBody437_117

def source437 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (437, 8, sourceBody437_118)
end InitECandidate.Proofs.WordStages
