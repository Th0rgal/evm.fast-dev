import InitECandidate.Proofs.WordStages.Source675
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody691_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody691_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 2)

def sourceBody691_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody691_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 56

def sourceBody691_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([48, 12, 40, 26]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody691_0, 691, 2)) (some 146) ([56, 8]) (some (56, sourceBody691_3, 691, 3))

def sourceBody691_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody691_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_4 sourceBody691_5

def sourceBody691_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_6 sourceBody691_0

def sourceBody691_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_2 sourceBody691_7

def sourceBody691_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_1 sourceBody691_8

def sourceBody691_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody691_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody691_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 52

def sourceBody691_13 : WordLangProgHOL (BitVec 64) :=
.call (some (([56, 8, 36, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody691_0, 691, 4)) (some 146) ([52, 16]) (some (52, sourceBody691_12, 691, 5))

def sourceBody691_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_13 sourceBody691_5

def sourceBody691_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_14 sourceBody691_0

def sourceBody691_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_11 sourceBody691_15

def sourceBody691_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_10 sourceBody691_16

def sourceBody691_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 48)

def sourceBody691_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 12)

def sourceBody691_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 40)

def sourceBody691_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 26)

def sourceBody691_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 4332616871279656263#64)

def sourceBody691_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 10917124144477883021#64)

def sourceBody691_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 13281191951274694749#64)

def sourceBody691_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 3486998266802970665#64)

def sourceBody691_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody691_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody691_0, 691, 6)) (some 106) ([16, 44, 30, 60, 6, 34, 20, 50]) (some (16, sourceBody691_26, 691, 7))

def sourceBody691_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_27 sourceBody691_5

def sourceBody691_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_28 sourceBody691_0

def sourceBody691_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_25 sourceBody691_29

def sourceBody691_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_24 sourceBody691_30

def sourceBody691_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_23 sourceBody691_31

def sourceBody691_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_22 sourceBody691_32

def sourceBody691_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_21 sourceBody691_33

def sourceBody691_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_20 sourceBody691_34

def sourceBody691_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_19 sourceBody691_35

def sourceBody691_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_18 sourceBody691_36

def sourceBody691_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 52)

def sourceBody691_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody691_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody691_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody691_42 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 44 (Flapjack.WordRegImm.reg 30) sourceBody691_40 sourceBody691_41

def sourceBody691_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_42 sourceBody691_5

def sourceBody691_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 44)

def sourceBody691_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody691_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody691_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_46 sourceBody691_0

def sourceBody691_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_45 sourceBody691_47

def sourceBody691_49 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 60 (Flapjack.WordRegImm.imm 0#64) sourceBody691_48 sourceBody691_0

def sourceBody691_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_49 sourceBody691_5

def sourceBody691_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_50 sourceBody691_0

def sourceBody691_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_44 sourceBody691_51

def sourceBody691_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_43 sourceBody691_52

def sourceBody691_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_39 sourceBody691_53

def sourceBody691_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_38 sourceBody691_54

def sourceBody691_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 56)

def sourceBody691_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 8)

def sourceBody691_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 36)

def sourceBody691_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 22)

def sourceBody691_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 4332616871279656263#64)

def sourceBody691_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 10917124144477883021#64)

def sourceBody691_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 13281191951274694749#64)

def sourceBody691_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 3486998266802970665#64)

def sourceBody691_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody691_65 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody691_0, 691, 8)) (some 106) ([44, 30, 60, 6, 34, 20, 50, 14]) (some (44, sourceBody691_64, 691, 9))

def sourceBody691_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_65 sourceBody691_5

def sourceBody691_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_66 sourceBody691_0

def sourceBody691_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_63 sourceBody691_67

def sourceBody691_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_62 sourceBody691_68

def sourceBody691_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_61 sourceBody691_69

def sourceBody691_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_60 sourceBody691_70

def sourceBody691_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_59 sourceBody691_71

def sourceBody691_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_58 sourceBody691_72

def sourceBody691_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_57 sourceBody691_73

def sourceBody691_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_56 sourceBody691_74

def sourceBody691_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 16)

def sourceBody691_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody691_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody691_79 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 30 (Flapjack.WordRegImm.reg 60) sourceBody691_78 sourceBody691_39

def sourceBody691_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_79 sourceBody691_5

def sourceBody691_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 30)

def sourceBody691_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [44]

def sourceBody691_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_82 sourceBody691_0

def sourceBody691_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_40 sourceBody691_83

def sourceBody691_85 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody691_84 sourceBody691_0

def sourceBody691_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_85 sourceBody691_5

def sourceBody691_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_86 sourceBody691_0

def sourceBody691_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_81 sourceBody691_87

def sourceBody691_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_80 sourceBody691_88

def sourceBody691_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_77 sourceBody691_89

def sourceBody691_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_76 sourceBody691_90

def sourceBody691_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 48)

def sourceBody691_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 12)

def sourceBody691_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 40)

def sourceBody691_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 26)

def sourceBody691_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody691_97 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody691_0, 691, 10)) (some 102) ([30, 60, 6, 34]) (some (30, sourceBody691_96, 691, 11))

def sourceBody691_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_97 sourceBody691_5

def sourceBody691_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_98 sourceBody691_0

def sourceBody691_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_95 sourceBody691_99

def sourceBody691_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_94 sourceBody691_100

def sourceBody691_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_93 sourceBody691_101

def sourceBody691_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_92 sourceBody691_102

def sourceBody691_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 56)

def sourceBody691_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody691_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 36)

def sourceBody691_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 22)

def sourceBody691_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 60

def sourceBody691_109 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody691_0, 691, 12)) (some 102) ([60, 6, 34, 20]) (some (60, sourceBody691_108, 691, 13))

def sourceBody691_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_109 sourceBody691_5

def sourceBody691_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_110 sourceBody691_0

def sourceBody691_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_107 sourceBody691_111

def sourceBody691_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_106 sourceBody691_112

def sourceBody691_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_105 sourceBody691_113

def sourceBody691_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_104 sourceBody691_114

def sourceBody691_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 44, Flapjack.WordLangExpHOL.var 30])

def sourceBody691_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody691_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody691_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody691_120 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.WordRegImm.reg 34) sourceBody691_118 sourceBody691_119

def sourceBody691_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_120 sourceBody691_5

def sourceBody691_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 6)

def sourceBody691_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 4)

def sourceBody691_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody691_125 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody691_0, 691, 14)) (some 676) ([6, 34]) (some (6, sourceBody691_124, 691, 15))

def sourceBody691_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_125 sourceBody691_5

def sourceBody691_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_126 sourceBody691_0

def sourceBody691_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_123 sourceBody691_127

def sourceBody691_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_118 sourceBody691_128

def sourceBody691_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_129

def sourceBody691_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_130

def sourceBody691_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [60]

def sourceBody691_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_132 sourceBody691_0

def sourceBody691_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_77 sourceBody691_133

def sourceBody691_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_131 sourceBody691_134

def sourceBody691_136 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody691_135 sourceBody691_0

def sourceBody691_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_136 sourceBody691_5

def sourceBody691_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_137 sourceBody691_0

def sourceBody691_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_122 sourceBody691_138

def sourceBody691_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_121 sourceBody691_139

def sourceBody691_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_117 sourceBody691_140

def sourceBody691_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_116 sourceBody691_141

def sourceBody691_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 48)

def sourceBody691_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody691_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 40)

def sourceBody691_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 26)

def sourceBody691_147 : WordLangProgHOL (BitVec 64) :=
.call (some (([48, 12, 40, 26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody691_0, 691, 16)) (some 658) ([60, 6, 34, 20]) (some (60, sourceBody691_108, 691, 17))

def sourceBody691_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_147 sourceBody691_5

def sourceBody691_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_148 sourceBody691_0

def sourceBody691_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_146 sourceBody691_149

def sourceBody691_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_145 sourceBody691_150

def sourceBody691_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_144 sourceBody691_151

def sourceBody691_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_143 sourceBody691_152

def sourceBody691_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_142 sourceBody691_153

def sourceBody691_155 : WordLangProgHOL (BitVec 64) :=
.call (some (([56, 8, 36, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody691_0, 691, 18)) (some 658) ([60, 6, 34, 20]) (some (60, sourceBody691_108, 691, 19))

def sourceBody691_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_155 sourceBody691_5

def sourceBody691_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_156 sourceBody691_0

def sourceBody691_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_107 sourceBody691_157

def sourceBody691_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_106 sourceBody691_158

def sourceBody691_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_105 sourceBody691_159

def sourceBody691_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_104 sourceBody691_160

def sourceBody691_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_154 sourceBody691_161

def sourceBody691_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 56)

def sourceBody691_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody691_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 36)

def sourceBody691_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 22)

def sourceBody691_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 56)

def sourceBody691_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody691_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 36)

def sourceBody691_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 22)

def sourceBody691_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 50

def sourceBody691_172 : WordLangProgHOL (BitVec 64) :=
.call (some (([60, 6, 34, 20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody691_0, 691, 20)) (some 657) ([50, 14, 42, 28, 58, 10, 38, 24]) (some (50, sourceBody691_171, 691, 21))

def sourceBody691_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_172 sourceBody691_5

def sourceBody691_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_173 sourceBody691_0

def sourceBody691_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_170 sourceBody691_174

def sourceBody691_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_169 sourceBody691_175

def sourceBody691_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_168 sourceBody691_176

def sourceBody691_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_167 sourceBody691_177

def sourceBody691_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_166 sourceBody691_178

def sourceBody691_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_165 sourceBody691_179

def sourceBody691_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_164 sourceBody691_180

def sourceBody691_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_163 sourceBody691_181

def sourceBody691_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 48)

def sourceBody691_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody691_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 40)

def sourceBody691_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody691_187 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 48)

def sourceBody691_188 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody691_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 40)

def sourceBody691_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 26)

def sourceBody691_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 58

def sourceBody691_192 : WordLangProgHOL (BitVec 64) :=
.call (some (([50, 14, 42, 28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody691_0, 691, 22)) (some 657) ([58, 10, 38, 24, 54, 18, 46, 32]) (some (58, sourceBody691_191, 691, 23))

def sourceBody691_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_192 sourceBody691_5

def sourceBody691_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_193 sourceBody691_0

def sourceBody691_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_190 sourceBody691_194

def sourceBody691_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_189 sourceBody691_195

def sourceBody691_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_188 sourceBody691_196

def sourceBody691_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_187 sourceBody691_197

def sourceBody691_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_186 sourceBody691_198

def sourceBody691_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_185 sourceBody691_199

def sourceBody691_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_184 sourceBody691_200

def sourceBody691_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_183 sourceBody691_201

def sourceBody691_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 50)

def sourceBody691_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody691_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 42)

def sourceBody691_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 28)

def sourceBody691_207 : WordLangProgHOL (BitVec 64) :=
.call (some (([50, 14, 42, 28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody691_0, 691, 24)) (some 657) ([58, 10, 38, 24, 54, 18, 46, 32]) (some (58, sourceBody691_191, 691, 25))

def sourceBody691_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_207 sourceBody691_5

def sourceBody691_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_208 sourceBody691_0

def sourceBody691_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_190 sourceBody691_209

def sourceBody691_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_189 sourceBody691_210

def sourceBody691_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_188 sourceBody691_211

def sourceBody691_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_187 sourceBody691_212

def sourceBody691_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_206 sourceBody691_213

def sourceBody691_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_205 sourceBody691_214

def sourceBody691_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_204 sourceBody691_215

def sourceBody691_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_203 sourceBody691_216

def sourceBody691_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 8797723225643362519#64)

def sourceBody691_219 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 2263834496217719225#64)

def sourceBody691_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 3696305541684646532#64)

def sourceBody691_221 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 3035258219084094862#64)

def sourceBody691_222 : WordLangProgHOL (BitVec 64) :=
.call (some (([50, 14, 42, 28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody691_0, 691, 26)) (some 654) ([58, 10, 38, 24, 54, 18, 46, 32]) (some (58, sourceBody691_191, 691, 27))

def sourceBody691_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_222 sourceBody691_5

def sourceBody691_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_223 sourceBody691_0

def sourceBody691_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_221 sourceBody691_224

def sourceBody691_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_220 sourceBody691_225

def sourceBody691_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_219 sourceBody691_226

def sourceBody691_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_218 sourceBody691_227

def sourceBody691_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_206 sourceBody691_228

def sourceBody691_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_205 sourceBody691_229

def sourceBody691_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_204 sourceBody691_230

def sourceBody691_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_203 sourceBody691_231

def sourceBody691_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_217 sourceBody691_232

def sourceBody691_234 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 60)

def sourceBody691_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 6)

def sourceBody691_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 34)

def sourceBody691_237 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 20)

def sourceBody691_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 50)

def sourceBody691_239 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 14)

def sourceBody691_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 42)

def sourceBody691_241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 28)

def sourceBody691_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody691_243 : WordLangProgHOL (BitVec 64) :=
.call (some (([58]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody691_0, 691, 28)) (some 105) ([10, 38, 24, 54, 18, 46, 32, 62]) (some (10, sourceBody691_242, 691, 29))

def sourceBody691_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_243 sourceBody691_5

def sourceBody691_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_244 sourceBody691_0

def sourceBody691_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_241 sourceBody691_245

def sourceBody691_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_240 sourceBody691_246

def sourceBody691_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_239 sourceBody691_247

def sourceBody691_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_238 sourceBody691_248

def sourceBody691_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_237 sourceBody691_249

def sourceBody691_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_236 sourceBody691_250

def sourceBody691_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_235 sourceBody691_251

def sourceBody691_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_234 sourceBody691_252

def sourceBody691_254 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 58)

def sourceBody691_255 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody691_256 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody691_257 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody691_258 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 38 (Flapjack.WordRegImm.reg 24) sourceBody691_256 sourceBody691_257

def sourceBody691_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_258 sourceBody691_5

def sourceBody691_260 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 38)

def sourceBody691_261 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody691_262 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody691_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_262 sourceBody691_0

def sourceBody691_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_261 sourceBody691_263

def sourceBody691_265 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 54 (Flapjack.WordRegImm.imm 0#64) sourceBody691_264 sourceBody691_0

def sourceBody691_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_265 sourceBody691_5

def sourceBody691_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_266 sourceBody691_0

def sourceBody691_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_260 sourceBody691_267

def sourceBody691_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_259 sourceBody691_268

def sourceBody691_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_255 sourceBody691_269

def sourceBody691_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_254 sourceBody691_270

def sourceBody691_272 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody691_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 48)

def sourceBody691_274 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody691_275 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 40)

def sourceBody691_276 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 26)

def sourceBody691_277 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 38)

def sourceBody691_278 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 46

def sourceBody691_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_278 sourceBody691_0

def sourceBody691_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_277 sourceBody691_279

def sourceBody691_281 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 24)

def sourceBody691_282 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 8#64])
  46

def sourceBody691_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_282 sourceBody691_0

def sourceBody691_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_281 sourceBody691_283

def sourceBody691_285 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 54)

def sourceBody691_286 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 16#64])
  46

def sourceBody691_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_286 sourceBody691_0

def sourceBody691_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_285 sourceBody691_287

def sourceBody691_289 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 18)

def sourceBody691_290 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 24#64])
  46

def sourceBody691_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_290 sourceBody691_0

def sourceBody691_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_289 sourceBody691_291

def sourceBody691_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_292 sourceBody691_0

def sourceBody691_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_288 sourceBody691_293

def sourceBody691_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_284 sourceBody691_294

def sourceBody691_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_280 sourceBody691_295

def sourceBody691_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_276 sourceBody691_296

def sourceBody691_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_297

def sourceBody691_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_275 sourceBody691_298

def sourceBody691_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_299

def sourceBody691_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_274 sourceBody691_300

def sourceBody691_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_301

def sourceBody691_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_273 sourceBody691_302

def sourceBody691_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_303

def sourceBody691_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_272 sourceBody691_304

def sourceBody691_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_305

def sourceBody691_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_271 sourceBody691_306

def sourceBody691_308 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody691_309 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 56)

def sourceBody691_310 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody691_311 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 36)

def sourceBody691_312 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 22)

def sourceBody691_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_312 sourceBody691_296

def sourceBody691_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_313

def sourceBody691_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_311 sourceBody691_314

def sourceBody691_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_315

def sourceBody691_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_310 sourceBody691_316

def sourceBody691_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_317

def sourceBody691_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_309 sourceBody691_318

def sourceBody691_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_319

def sourceBody691_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_308 sourceBody691_320

def sourceBody691_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_321

def sourceBody691_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_307 sourceBody691_322

def sourceBody691_324 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody691_325 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 15230403791020821917#64)

def sourceBody691_326 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 754611498739239741#64)

def sourceBody691_327 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 7381016538464732716#64)

def sourceBody691_328 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1011752739694698287#64)

def sourceBody691_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_328 sourceBody691_296

def sourceBody691_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_329

def sourceBody691_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_327 sourceBody691_330

def sourceBody691_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_331

def sourceBody691_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_326 sourceBody691_332

def sourceBody691_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_333

def sourceBody691_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_325 sourceBody691_334

def sourceBody691_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_335

def sourceBody691_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_324 sourceBody691_336

def sourceBody691_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_337

def sourceBody691_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_323 sourceBody691_338

def sourceBody691_340 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody691_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_340 sourceBody691_263

def sourceBody691_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_339 sourceBody691_341

def sourceBody691_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_253 sourceBody691_342

def sourceBody691_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_343

def sourceBody691_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_344

def sourceBody691_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_233 sourceBody691_345

def sourceBody691_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_202 sourceBody691_346

def sourceBody691_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_347

def sourceBody691_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_348

def sourceBody691_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_349

def sourceBody691_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_350

def sourceBody691_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_351

def sourceBody691_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_352

def sourceBody691_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_353

def sourceBody691_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_354

def sourceBody691_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_182 sourceBody691_355

def sourceBody691_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_356

def sourceBody691_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_357

def sourceBody691_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_358

def sourceBody691_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_359

def sourceBody691_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_360

def sourceBody691_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_361

def sourceBody691_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_362

def sourceBody691_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_363

def sourceBody691_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_162 sourceBody691_364

def sourceBody691_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_115 sourceBody691_365

def sourceBody691_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_366

def sourceBody691_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_367

def sourceBody691_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_103 sourceBody691_368

def sourceBody691_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_369

def sourceBody691_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_370

def sourceBody691_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_91 sourceBody691_371

def sourceBody691_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_75 sourceBody691_372

def sourceBody691_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_373

def sourceBody691_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_374

def sourceBody691_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_55 sourceBody691_375

def sourceBody691_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_37 sourceBody691_376

def sourceBody691_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_377

def sourceBody691_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_378

def sourceBody691_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_17 sourceBody691_379

def sourceBody691_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_380

def sourceBody691_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_381

def sourceBody691_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_382

def sourceBody691_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_383

def sourceBody691_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_384

def sourceBody691_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_385

def sourceBody691_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_386

def sourceBody691_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_387

def sourceBody691_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_9 sourceBody691_388

def sourceBody691_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_389

def sourceBody691_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_390

def sourceBody691_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_391

def sourceBody691_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_392

def sourceBody691_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_393

def sourceBody691_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_394

def sourceBody691_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_395

def sourceBody691_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody691_0 sourceBody691_396

def source691 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (691, 3, sourceBody691_397)
end InitECandidate.Proofs.WordStages
