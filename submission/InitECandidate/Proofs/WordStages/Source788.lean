import InitECandidate.Proofs.WordStages.Source772
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody788_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody788_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody788_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([50]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody788_0, 788, 2)) (some 69) ([]) (some (30, sourceBody788_1, 788, 3))

def sourceBody788_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody788_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_2 sourceBody788_3

def sourceBody788_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_4 sourceBody788_0

def sourceBody788_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 576#64)

def sourceBody788_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody788_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody788_0, 788, 4)) (some 68) ([40]) (some (40, sourceBody788_7, 788, 5))

def sourceBody788_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_8 sourceBody788_3

def sourceBody788_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_9 sourceBody788_0

def sourceBody788_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_6 sourceBody788_10

def sourceBody788_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 30)

def sourceBody788_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 576#64)

def sourceBody788_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody788_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody788_0, 788, 6)) (some 78) ([36, 46]) (some (36, sourceBody788_14, 788, 7))

def sourceBody788_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_15 sourceBody788_3

def sourceBody788_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_16 sourceBody788_0

def sourceBody788_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_13 sourceBody788_17

def sourceBody788_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_12 sourceBody788_18

def sourceBody788_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_0 sourceBody788_19

def sourceBody788_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_0 sourceBody788_20

def sourceBody788_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody788_23 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody788_0, 788, 8)) (some 725) ([36, 46]) (some (36, sourceBody788_14, 788, 9))

def sourceBody788_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_23 sourceBody788_3

def sourceBody788_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_24 sourceBody788_0

def sourceBody788_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_22 sourceBody788_25

def sourceBody788_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_12 sourceBody788_26

def sourceBody788_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_0 sourceBody788_27

def sourceBody788_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_0 sourceBody788_28

def sourceBody788_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_21 sourceBody788_29

def sourceBody788_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody788_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody788_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 6)

def sourceBody788_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 8)

def sourceBody788_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 10)

def sourceBody788_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 12)

def sourceBody788_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 14)

def sourceBody788_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 16)

def sourceBody788_39 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody788_0, 788, 10)) (some 738) ([36, 46, 34, 44, 38, 48, 32, 42]) (some (36, sourceBody788_14, 788, 11))

def sourceBody788_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_39 sourceBody788_3

def sourceBody788_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_40 sourceBody788_0

def sourceBody788_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_38 sourceBody788_41

def sourceBody788_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_37 sourceBody788_42

def sourceBody788_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_36 sourceBody788_43

def sourceBody788_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_35 sourceBody788_44

def sourceBody788_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_34 sourceBody788_45

def sourceBody788_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_33 sourceBody788_46

def sourceBody788_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_32 sourceBody788_47

def sourceBody788_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_31 sourceBody788_48

def sourceBody788_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_0 sourceBody788_49

def sourceBody788_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_0 sourceBody788_50

def sourceBody788_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_30 sourceBody788_51

def sourceBody788_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody788_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 4)

def sourceBody788_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 18)

def sourceBody788_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 20)

def sourceBody788_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 22)

def sourceBody788_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 24)

def sourceBody788_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 26)

def sourceBody788_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 28)

def sourceBody788_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody788_0, 788, 12)) (some 738) ([36, 46, 34, 44, 38, 48, 32, 42]) (some (36, sourceBody788_14, 788, 13))

def sourceBody788_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_61 sourceBody788_3

def sourceBody788_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_62 sourceBody788_0

def sourceBody788_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_60 sourceBody788_63

def sourceBody788_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_59 sourceBody788_64

def sourceBody788_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_58 sourceBody788_65

def sourceBody788_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_57 sourceBody788_66

def sourceBody788_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_56 sourceBody788_67

def sourceBody788_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_55 sourceBody788_68

def sourceBody788_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_54 sourceBody788_69

def sourceBody788_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_53 sourceBody788_70

def sourceBody788_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_0 sourceBody788_71

def sourceBody788_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_0 sourceBody788_72

def sourceBody788_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_52 sourceBody788_73

def sourceBody788_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 2)

def sourceBody788_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 2)

def sourceBody788_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 30)

def sourceBody788_78 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody788_0, 788, 14)) (some 754) ([36, 46, 34]) (some (36, sourceBody788_14, 788, 15))

def sourceBody788_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_78 sourceBody788_3

def sourceBody788_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_79 sourceBody788_0

def sourceBody788_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_77 sourceBody788_80

def sourceBody788_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_76 sourceBody788_81

def sourceBody788_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_75 sourceBody788_82

def sourceBody788_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_0 sourceBody788_83

def sourceBody788_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_0 sourceBody788_84

def sourceBody788_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_74 sourceBody788_85

def sourceBody788_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 50)

def sourceBody788_88 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody788_0, 788, 16)) (some 70) ([36]) (some (36, sourceBody788_14, 788, 17))

def sourceBody788_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_88 sourceBody788_3

def sourceBody788_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_89 sourceBody788_0

def sourceBody788_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_87 sourceBody788_90

def sourceBody788_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_0 sourceBody788_91

def sourceBody788_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_0 sourceBody788_92

def sourceBody788_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_86 sourceBody788_93

def sourceBody788_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody788_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [40]

def sourceBody788_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_96 sourceBody788_0

def sourceBody788_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_95 sourceBody788_97

def sourceBody788_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_94 sourceBody788_98

def sourceBody788_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_11 sourceBody788_99

def sourceBody788_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_0 sourceBody788_100

def sourceBody788_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_0 sourceBody788_101

def sourceBody788_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_5 sourceBody788_102

def sourceBody788_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_0 sourceBody788_103

def sourceBody788_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody788_0 sourceBody788_104

def source788 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (788, 15, sourceBody788_105)
end InitECandidate.Proofs.WordStages
