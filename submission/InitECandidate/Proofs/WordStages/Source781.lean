import InitECandidate.Proofs.WordStages.Source765
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody781_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody781_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody781_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody781_0, 781, 2)) (some 69) ([]) (some (8, sourceBody781_1, 781, 3))

def sourceBody781_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody781_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_2 sourceBody781_3

def sourceBody781_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_4 sourceBody781_0

def sourceBody781_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody781_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody781_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody781_0, 781, 4)) (some 68) ([14]) (some (14, sourceBody781_7, 781, 5))

def sourceBody781_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_8 sourceBody781_3

def sourceBody781_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_9 sourceBody781_0

def sourceBody781_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_6 sourceBody781_10

def sourceBody781_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody781_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody781_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody781_0, 781, 6)) (some 775) ([10]) (some (10, sourceBody781_13, 781, 7))

def sourceBody781_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_14 sourceBody781_3

def sourceBody781_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_15 sourceBody781_0

def sourceBody781_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_12 sourceBody781_16

def sourceBody781_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody781_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody781_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody781_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody781_22 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 18 (Flapjack.WordRegImm.reg 6) sourceBody781_20 sourceBody781_21

def sourceBody781_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_22 sourceBody781_3

def sourceBody781_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody781_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody781_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 192#64)

def sourceBody781_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody781_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody781_0, 781, 8)) (some 78) ([18, 6]) (some (18, sourceBody781_27, 781, 9))

def sourceBody781_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_28 sourceBody781_3

def sourceBody781_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_29 sourceBody781_0

def sourceBody781_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_26 sourceBody781_30

def sourceBody781_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_25 sourceBody781_31

def sourceBody781_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_32

def sourceBody781_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_33

def sourceBody781_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody781_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody781_0, 781, 10)) (some 70) ([18]) (some (18, sourceBody781_27, 781, 11))

def sourceBody781_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_36 sourceBody781_3

def sourceBody781_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_37 sourceBody781_0

def sourceBody781_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_35 sourceBody781_38

def sourceBody781_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_39

def sourceBody781_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_40

def sourceBody781_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_34 sourceBody781_41

def sourceBody781_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody781_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody781_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_44 sourceBody781_0

def sourceBody781_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_43 sourceBody781_45

def sourceBody781_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_42 sourceBody781_46

def sourceBody781_48 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody781_47 sourceBody781_0

def sourceBody781_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_48 sourceBody781_3

def sourceBody781_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_49 sourceBody781_0

def sourceBody781_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_24 sourceBody781_50

def sourceBody781_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_23 sourceBody781_51

def sourceBody781_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_19 sourceBody781_52

def sourceBody781_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_18 sourceBody781_53

def sourceBody781_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody781_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody781_57 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody781_0, 781, 12)) (some 739) ([18, 6]) (some (18, sourceBody781_27, 781, 13))

def sourceBody781_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_57 sourceBody781_3

def sourceBody781_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_58 sourceBody781_0

def sourceBody781_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_56 sourceBody781_59

def sourceBody781_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_55 sourceBody781_60

def sourceBody781_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_61

def sourceBody781_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_62

def sourceBody781_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_54 sourceBody781_63

def sourceBody781_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody781_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody781_67 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody781_0, 781, 14)) (some 735) ([18, 6, 12]) (some (18, sourceBody781_27, 781, 15))

def sourceBody781_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_67 sourceBody781_3

def sourceBody781_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_68 sourceBody781_0

def sourceBody781_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_66 sourceBody781_69

def sourceBody781_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_65 sourceBody781_70

def sourceBody781_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_25 sourceBody781_71

def sourceBody781_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_72

def sourceBody781_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_73

def sourceBody781_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_64 sourceBody781_74

def sourceBody781_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody781_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody781_78 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody781_0, 781, 16)) (some 735) ([18, 6, 12]) (some (18, sourceBody781_27, 781, 17))

def sourceBody781_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_78 sourceBody781_3

def sourceBody781_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_79 sourceBody781_0

def sourceBody781_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_66 sourceBody781_80

def sourceBody781_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_77 sourceBody781_81

def sourceBody781_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_76 sourceBody781_82

def sourceBody781_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_83

def sourceBody781_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_84

def sourceBody781_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_75 sourceBody781_85

def sourceBody781_87 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody781_0, 781, 18)) (some 70) ([18]) (some (18, sourceBody781_27, 781, 19))

def sourceBody781_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_87 sourceBody781_3

def sourceBody781_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_88 sourceBody781_0

def sourceBody781_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_35 sourceBody781_89

def sourceBody781_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_90

def sourceBody781_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_91

def sourceBody781_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_86 sourceBody781_92

def sourceBody781_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody781_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_94 sourceBody781_45

def sourceBody781_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_93 sourceBody781_95

def sourceBody781_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_17 sourceBody781_96

def sourceBody781_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_97

def sourceBody781_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_98

def sourceBody781_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_11 sourceBody781_99

def sourceBody781_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_100

def sourceBody781_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_101

def sourceBody781_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_5 sourceBody781_102

def sourceBody781_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_103

def sourceBody781_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody781_0 sourceBody781_104

def source781 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (781, 3, sourceBody781_105)
end InitECandidate.Proofs.WordStages
