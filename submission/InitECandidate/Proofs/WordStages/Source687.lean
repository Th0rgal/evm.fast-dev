import InitECandidate.Proofs.WordStages.Source671
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody687_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody687_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody687_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([56]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 2)) (some 69) ([]) (some (14, sourceBody687_1, 687, 3))

def sourceBody687_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody687_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_2 sourceBody687_3

def sourceBody687_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_4 sourceBody687_0

def sourceBody687_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 416#64)

def sourceBody687_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 48

def sourceBody687_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 4)) (some 68) ([48]) (some (48, sourceBody687_7, 687, 5))

def sourceBody687_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_8 sourceBody687_3

def sourceBody687_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_9 sourceBody687_0

def sourceBody687_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_6 sourceBody687_10

def sourceBody687_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 416#64)

def sourceBody687_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody687_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 6)) (some 68) ([32]) (some (32, sourceBody687_13, 687, 7))

def sourceBody687_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_14 sourceBody687_3

def sourceBody687_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_15 sourceBody687_0

def sourceBody687_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_12 sourceBody687_16

def sourceBody687_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 416#64)

def sourceBody687_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 66

def sourceBody687_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 8)) (some 68) ([66]) (some (66, sourceBody687_19, 687, 9))

def sourceBody687_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_20 sourceBody687_3

def sourceBody687_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_21 sourceBody687_0

def sourceBody687_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_18 sourceBody687_22

def sourceBody687_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 416#64)

def sourceBody687_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody687_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([66]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 10)) (some 68) ([10]) (some (10, sourceBody687_25, 687, 11))

def sourceBody687_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_26 sourceBody687_3

def sourceBody687_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_27 sourceBody687_0

def sourceBody687_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_24 sourceBody687_28

def sourceBody687_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 416#64)

def sourceBody687_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody687_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 12)) (some 68) ([44]) (some (44, sourceBody687_31, 687, 13))

def sourceBody687_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_32 sourceBody687_3

def sourceBody687_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_33 sourceBody687_0

def sourceBody687_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_30 sourceBody687_34

def sourceBody687_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 416#64)

def sourceBody687_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody687_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 14)) (some 68) ([28]) (some (28, sourceBody687_37, 687, 15))

def sourceBody687_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_38 sourceBody687_3

def sourceBody687_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_39 sourceBody687_0

def sourceBody687_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_36 sourceBody687_40

def sourceBody687_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 14)

def sourceBody687_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 416#64)

def sourceBody687_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 62

def sourceBody687_45 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 16)) (some 78) ([62, 20]) (some (62, sourceBody687_44, 687, 17))

def sourceBody687_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_45 sourceBody687_3

def sourceBody687_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_46 sourceBody687_0

def sourceBody687_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_43 sourceBody687_47

def sourceBody687_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_42 sourceBody687_48

def sourceBody687_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_49

def sourceBody687_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_50

def sourceBody687_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 14)

def sourceBody687_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 5544790254283102953#64)

def sourceBody687_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 13698472384431417117#64)

def sourceBody687_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 4628036095437277618#64)

def sourceBody687_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 2762764518496934255#64)

def sourceBody687_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 62)

def sourceBody687_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 28) 70

def sourceBody687_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_58 sourceBody687_0

def sourceBody687_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_57 sourceBody687_59

def sourceBody687_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 20)

def sourceBody687_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 8#64])
  70

def sourceBody687_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_62 sourceBody687_0

def sourceBody687_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_61 sourceBody687_63

def sourceBody687_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 52)

def sourceBody687_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 16#64])
  70

def sourceBody687_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_66 sourceBody687_0

def sourceBody687_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_65 sourceBody687_67

def sourceBody687_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 36)

def sourceBody687_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 24#64])
  70

def sourceBody687_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_70 sourceBody687_0

def sourceBody687_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_69 sourceBody687_71

def sourceBody687_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_72 sourceBody687_0

def sourceBody687_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_68 sourceBody687_73

def sourceBody687_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_64 sourceBody687_74

def sourceBody687_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_60 sourceBody687_75

def sourceBody687_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_56 sourceBody687_76

def sourceBody687_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_77

def sourceBody687_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_55 sourceBody687_78

def sourceBody687_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_79

def sourceBody687_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_54 sourceBody687_80

def sourceBody687_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_81

def sourceBody687_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_53 sourceBody687_82

def sourceBody687_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_83

def sourceBody687_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_52 sourceBody687_84

def sourceBody687_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_85

def sourceBody687_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_51 sourceBody687_86

def sourceBody687_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody687_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 10102850021236865696#64)

def sourceBody687_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 15026249742141879542#64)

def sourceBody687_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 2169086236411634456#64)

def sourceBody687_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 2710440286313254821#64)

def sourceBody687_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_92 sourceBody687_76

def sourceBody687_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_93

def sourceBody687_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_91 sourceBody687_94

def sourceBody687_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_95

def sourceBody687_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_90 sourceBody687_96

def sourceBody687_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_97

def sourceBody687_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_89 sourceBody687_98

def sourceBody687_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_99

def sourceBody687_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_88 sourceBody687_100

def sourceBody687_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_101

def sourceBody687_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_87 sourceBody687_102

def sourceBody687_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody687_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 15230403791020821917#64)

def sourceBody687_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 754611498739239741#64)

def sourceBody687_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 7381016538464732716#64)

def sourceBody687_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 1011752739694698287#64)

def sourceBody687_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_108 sourceBody687_76

def sourceBody687_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_109

def sourceBody687_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_107 sourceBody687_110

def sourceBody687_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_111

def sourceBody687_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_106 sourceBody687_112

def sourceBody687_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_113

def sourceBody687_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_105 sourceBody687_114

def sourceBody687_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_115

def sourceBody687_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_104 sourceBody687_116

def sourceBody687_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_117

def sourceBody687_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_103 sourceBody687_118

def sourceBody687_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 48)

def sourceBody687_121 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 18)) (some 78) ([62, 20]) (some (62, sourceBody687_44, 687, 19))

def sourceBody687_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_121 sourceBody687_3

def sourceBody687_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_122 sourceBody687_0

def sourceBody687_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_43 sourceBody687_123

def sourceBody687_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_120 sourceBody687_124

def sourceBody687_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_125

def sourceBody687_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_126

def sourceBody687_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_119 sourceBody687_127

def sourceBody687_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody687_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 384#64)

def sourceBody687_131 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 20)) (some 77) ([62, 20, 52]) (some (62, sourceBody687_44, 687, 21))

def sourceBody687_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_131 sourceBody687_3

def sourceBody687_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_132 sourceBody687_0

def sourceBody687_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_130 sourceBody687_133

def sourceBody687_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_129 sourceBody687_134

def sourceBody687_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_120 sourceBody687_135

def sourceBody687_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_136

def sourceBody687_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_137

def sourceBody687_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_128 sourceBody687_138

def sourceBody687_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 32)

def sourceBody687_141 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 22)) (some 78) ([62, 20]) (some (62, sourceBody687_44, 687, 23))

def sourceBody687_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_141 sourceBody687_3

def sourceBody687_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_142 sourceBody687_0

def sourceBody687_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_43 sourceBody687_143

def sourceBody687_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_140 sourceBody687_144

def sourceBody687_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_145

def sourceBody687_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_146

def sourceBody687_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_139 sourceBody687_147

def sourceBody687_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 66)

def sourceBody687_150 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 24)) (some 78) ([62, 20]) (some (62, sourceBody687_44, 687, 25))

def sourceBody687_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_150 sourceBody687_3

def sourceBody687_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_151 sourceBody687_0

def sourceBody687_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_43 sourceBody687_152

def sourceBody687_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_149 sourceBody687_153

def sourceBody687_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_154

def sourceBody687_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_155

def sourceBody687_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_148 sourceBody687_156

def sourceBody687_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 66)

def sourceBody687_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_158 sourceBody687_116

def sourceBody687_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_159

def sourceBody687_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_157 sourceBody687_160

def sourceBody687_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody687_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 13#64)

def sourceBody687_164 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 26)) (some 685) ([62, 20]) (some (62, sourceBody687_44, 687, 27))

def sourceBody687_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_164 sourceBody687_3

def sourceBody687_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_165 sourceBody687_0

def sourceBody687_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_163 sourceBody687_166

def sourceBody687_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_120 sourceBody687_167

def sourceBody687_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody687_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 28)

def sourceBody687_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody687_172 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLess) 20 (Flapjack.WordRegImm.reg 52) sourceBody687_171 sourceBody687_169

def sourceBody687_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_172 sourceBody687_3

def sourceBody687_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 20)

def sourceBody687_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody687_176 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody687_175 sourceBody687_0

def sourceBody687_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_176 sourceBody687_3

def sourceBody687_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_177 sourceBody687_0

def sourceBody687_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_174 sourceBody687_178

def sourceBody687_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_173 sourceBody687_179

def sourceBody687_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_170 sourceBody687_180

def sourceBody687_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_169 sourceBody687_181

def sourceBody687_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody687_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 13#64)

def sourceBody687_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody687_186 : WordLangProgHOL (BitVec 64) :=
.call (some (([62]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 28)) (some 685) ([20, 52]) (some (20, sourceBody687_185, 687, 29))

def sourceBody687_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_186 sourceBody687_3

def sourceBody687_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_187 sourceBody687_0

def sourceBody687_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_184 sourceBody687_188

def sourceBody687_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_183 sourceBody687_189

def sourceBody687_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 10)

def sourceBody687_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 416#64)

def sourceBody687_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 52

def sourceBody687_194 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 30)) (some 78) ([52, 36]) (some (52, sourceBody687_193, 687, 31))

def sourceBody687_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_194 sourceBody687_3

def sourceBody687_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_195 sourceBody687_0

def sourceBody687_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_192 sourceBody687_196

def sourceBody687_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_191 sourceBody687_197

def sourceBody687_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_198

def sourceBody687_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_199

def sourceBody687_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 48,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 28)
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody687_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 48,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 28)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody687_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 48,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 28)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody687_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 48,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 28)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody687_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody687_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 52)

def sourceBody687_207 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 36)

def sourceBody687_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 70)

def sourceBody687_209 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody687_210 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 42, 26, 60]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 32)) (some 660) ([18, 50, 34, 68]) (some (18, sourceBody687_209, 687, 33))

def sourceBody687_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_210 sourceBody687_3

def sourceBody687_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_211 sourceBody687_0

def sourceBody687_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_208 sourceBody687_212

def sourceBody687_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_207 sourceBody687_213

def sourceBody687_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_206 sourceBody687_214

def sourceBody687_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_205 sourceBody687_215

def sourceBody687_217 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 62)

def sourceBody687_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 28)

def sourceBody687_219 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody687_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody687_221 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLess) 50 (Flapjack.WordRegImm.reg 34) sourceBody687_219 sourceBody687_220

def sourceBody687_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_221 sourceBody687_3

def sourceBody687_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 50)

def sourceBody687_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 62)
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody687_225 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 14,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 62)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody687_226 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 14,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 62)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody687_227 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 14,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 62)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody687_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody687_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 50)

def sourceBody687_230 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 34)

def sourceBody687_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 68)

def sourceBody687_232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody687_233 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 42)

def sourceBody687_234 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody687_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 60)

def sourceBody687_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody687_237 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 46, 30, 64]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 34)) (some 657) ([22, 54, 38, 72, 6, 40, 24, 58]) (some (22, sourceBody687_236, 687, 35))

def sourceBody687_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_237 sourceBody687_3

def sourceBody687_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_238 sourceBody687_0

def sourceBody687_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_235 sourceBody687_239

def sourceBody687_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_234 sourceBody687_240

def sourceBody687_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_233 sourceBody687_241

def sourceBody687_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_232 sourceBody687_242

def sourceBody687_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_231 sourceBody687_243

def sourceBody687_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_230 sourceBody687_244

def sourceBody687_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_229 sourceBody687_245

def sourceBody687_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_228 sourceBody687_246

def sourceBody687_248 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 62, Flapjack.WordLangExpHOL.var 28])
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody687_249 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 12)

def sourceBody687_250 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 46)

def sourceBody687_251 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 30)

def sourceBody687_252 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 64)

def sourceBody687_253 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 54)

def sourceBody687_254 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 22) 40

def sourceBody687_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_254 sourceBody687_0

def sourceBody687_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_253 sourceBody687_255

def sourceBody687_257 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 38)

def sourceBody687_258 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 8#64])
  40

def sourceBody687_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_258 sourceBody687_0

def sourceBody687_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_257 sourceBody687_259

def sourceBody687_261 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 72)

def sourceBody687_262 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 16#64])
  40

def sourceBody687_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_262 sourceBody687_0

def sourceBody687_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_261 sourceBody687_263

def sourceBody687_265 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 6)

def sourceBody687_266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 24#64])
  40

def sourceBody687_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_266 sourceBody687_0

def sourceBody687_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_265 sourceBody687_267

def sourceBody687_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_268 sourceBody687_0

def sourceBody687_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_264 sourceBody687_269

def sourceBody687_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_260 sourceBody687_270

def sourceBody687_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_256 sourceBody687_271

def sourceBody687_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_252 sourceBody687_272

def sourceBody687_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_273

def sourceBody687_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_251 sourceBody687_274

def sourceBody687_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_275

def sourceBody687_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_250 sourceBody687_276

def sourceBody687_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_277

def sourceBody687_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_249 sourceBody687_278

def sourceBody687_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_279

def sourceBody687_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_248 sourceBody687_280

def sourceBody687_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_281

def sourceBody687_283 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 14)

def sourceBody687_284 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 48)

def sourceBody687_285 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 12)

def sourceBody687_286 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 46)

def sourceBody687_287 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 30)

def sourceBody687_288 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 64)

def sourceBody687_289 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 62, Flapjack.WordLangExpHOL.var 28])

def sourceBody687_290 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 28)

def sourceBody687_291 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 54

def sourceBody687_292 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 36)) (some 686) ([54, 38, 72, 6, 40, 24, 58, 16]) (some (54, sourceBody687_291, 687, 37))

def sourceBody687_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_292 sourceBody687_3

def sourceBody687_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_293 sourceBody687_0

def sourceBody687_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_290 sourceBody687_294

def sourceBody687_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_289 sourceBody687_295

def sourceBody687_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_288 sourceBody687_296

def sourceBody687_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_287 sourceBody687_297

def sourceBody687_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_286 sourceBody687_298

def sourceBody687_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_285 sourceBody687_299

def sourceBody687_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_284 sourceBody687_300

def sourceBody687_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_283 sourceBody687_301

def sourceBody687_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_302

def sourceBody687_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_303

def sourceBody687_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_282 sourceBody687_304

def sourceBody687_306 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody687_307 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 13#64)

def sourceBody687_308 : WordLangProgHOL (BitVec 64) :=
.call (some (([62]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 38)) (some 685) ([22, 54]) (some (22, sourceBody687_236, 687, 39))

def sourceBody687_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_308 sourceBody687_3

def sourceBody687_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_309 sourceBody687_0

def sourceBody687_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_307 sourceBody687_310

def sourceBody687_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_306 sourceBody687_311

def sourceBody687_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_305 sourceBody687_312

def sourceBody687_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_247 sourceBody687_313

def sourceBody687_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_314

def sourceBody687_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_315

def sourceBody687_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_316

def sourceBody687_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_317

def sourceBody687_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_318

def sourceBody687_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_319

def sourceBody687_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_320

def sourceBody687_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_321

def sourceBody687_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_227 sourceBody687_322

def sourceBody687_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_323

def sourceBody687_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_226 sourceBody687_324

def sourceBody687_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_325

def sourceBody687_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_225 sourceBody687_326

def sourceBody687_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_327

def sourceBody687_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_224 sourceBody687_328

def sourceBody687_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_329

def sourceBody687_331 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody687_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_330 sourceBody687_331

def sourceBody687_333 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 68 (Flapjack.WordRegImm.imm 0#64) sourceBody687_332 sourceBody687_175

def sourceBody687_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_333 sourceBody687_3

def sourceBody687_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_334 sourceBody687_0

def sourceBody687_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_223 sourceBody687_335

def sourceBody687_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_222 sourceBody687_336

def sourceBody687_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_218 sourceBody687_337

def sourceBody687_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_217 sourceBody687_338

def sourceBody687_340 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody687_339 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody687_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_340 sourceBody687_3

def sourceBody687_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_3 sourceBody687_341

def sourceBody687_343 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 44)

def sourceBody687_344 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 32)

def sourceBody687_345 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.const 416#64)

def sourceBody687_346 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 50

def sourceBody687_347 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 40)) (some 77) ([50, 34, 68]) (some (50, sourceBody687_346, 687, 41))

def sourceBody687_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_347 sourceBody687_3

def sourceBody687_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_348 sourceBody687_0

def sourceBody687_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_345 sourceBody687_349

def sourceBody687_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_344 sourceBody687_350

def sourceBody687_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_343 sourceBody687_351

def sourceBody687_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_352

def sourceBody687_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_353

def sourceBody687_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_342 sourceBody687_354

def sourceBody687_356 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody687_357 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 18)

def sourceBody687_358 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.const 13#64)

def sourceBody687_359 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody687_360 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody687_361 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 34 (Flapjack.WordRegImm.reg 68) sourceBody687_359 sourceBody687_360

def sourceBody687_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_361 sourceBody687_3

def sourceBody687_363 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 34)

def sourceBody687_364 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 18)
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody687_365 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 10,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 18)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody687_366 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 10,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 18)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody687_367 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 10,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 18)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody687_368 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 50)

def sourceBody687_369 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 34)

def sourceBody687_370 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 68)

def sourceBody687_371 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody687_372 : WordLangProgHOL (BitVec 64) :=
.call (some (([46]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 42)) (some 102) ([30, 64, 22, 54]) (some (30, sourceBody687_371, 687, 43))

def sourceBody687_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_372 sourceBody687_3

def sourceBody687_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_373 sourceBody687_0

def sourceBody687_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_249 sourceBody687_374

def sourceBody687_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_370 sourceBody687_375

def sourceBody687_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_369 sourceBody687_376

def sourceBody687_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_368 sourceBody687_377

def sourceBody687_379 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 46)

def sourceBody687_380 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody687_381 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody687_382 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody687_383 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 64 (Flapjack.WordRegImm.reg 22) sourceBody687_381 sourceBody687_382

def sourceBody687_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_383 sourceBody687_3

def sourceBody687_385 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 64)

def sourceBody687_386 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 44)

def sourceBody687_387 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 66)

def sourceBody687_388 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody687_389 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 18)

def sourceBody687_390 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.const 12#64, Flapjack.WordLangExpHOL.var 18])

def sourceBody687_391 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 64

def sourceBody687_392 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 44)) (some 686) ([64, 22, 54, 38, 72, 6, 40, 24]) (some (64, sourceBody687_391, 687, 45))

def sourceBody687_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_392 sourceBody687_3

def sourceBody687_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_393 sourceBody687_0

def sourceBody687_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_390 sourceBody687_394

def sourceBody687_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_389 sourceBody687_395

def sourceBody687_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_388 sourceBody687_396

def sourceBody687_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_231 sourceBody687_397

def sourceBody687_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_230 sourceBody687_398

def sourceBody687_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_229 sourceBody687_399

def sourceBody687_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_387 sourceBody687_400

def sourceBody687_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_386 sourceBody687_401

def sourceBody687_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_402

def sourceBody687_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_403

def sourceBody687_405 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 54 (Flapjack.WordRegImm.imm 0#64) sourceBody687_404 sourceBody687_0

def sourceBody687_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_405 sourceBody687_3

def sourceBody687_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_406 sourceBody687_0

def sourceBody687_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_385 sourceBody687_407

def sourceBody687_409 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_384 sourceBody687_408

def sourceBody687_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_380 sourceBody687_409

def sourceBody687_411 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_379 sourceBody687_410

def sourceBody687_412 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody687_413 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 30)

def sourceBody687_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_413 sourceBody687_0

def sourceBody687_415 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_414 sourceBody687_0

def sourceBody687_416 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_412 sourceBody687_415

def sourceBody687_417 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_416

def sourceBody687_418 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_411 sourceBody687_417

def sourceBody687_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_378 sourceBody687_418

def sourceBody687_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_419

def sourceBody687_421 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_420

def sourceBody687_422 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_367 sourceBody687_421

def sourceBody687_423 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_422

def sourceBody687_424 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_366 sourceBody687_423

def sourceBody687_425 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_424

def sourceBody687_426 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_365 sourceBody687_425

def sourceBody687_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_426

def sourceBody687_428 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_364 sourceBody687_427

def sourceBody687_429 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_428

def sourceBody687_430 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_429 sourceBody687_331

def sourceBody687_431 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody687_430 sourceBody687_175

def sourceBody687_432 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_431 sourceBody687_3

def sourceBody687_433 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_432 sourceBody687_0

def sourceBody687_434 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_363 sourceBody687_433

def sourceBody687_435 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_362 sourceBody687_434

def sourceBody687_436 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_358 sourceBody687_435

def sourceBody687_437 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_357 sourceBody687_436

def sourceBody687_438 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody687_437 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody687_439 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_438 sourceBody687_3

def sourceBody687_440 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_3 sourceBody687_439

def sourceBody687_441 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 14)

def sourceBody687_442 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 48)

def sourceBody687_443 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_442 sourceBody687_0

def sourceBody687_444 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_443 sourceBody687_0

def sourceBody687_445 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 50)

def sourceBody687_446 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_445 sourceBody687_0

def sourceBody687_447 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_446 sourceBody687_0

def sourceBody687_448 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_444 sourceBody687_447

def sourceBody687_449 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 32)

def sourceBody687_450 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_449 sourceBody687_0

def sourceBody687_451 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_450 sourceBody687_0

def sourceBody687_452 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_448 sourceBody687_451

def sourceBody687_453 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 66)

def sourceBody687_454 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_453 sourceBody687_0

def sourceBody687_455 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_454 sourceBody687_0

def sourceBody687_456 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_452 sourceBody687_455

def sourceBody687_457 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 44)

def sourceBody687_458 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_457 sourceBody687_0

def sourceBody687_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_458 sourceBody687_0

def sourceBody687_460 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_456 sourceBody687_459

def sourceBody687_461 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 50)

def sourceBody687_462 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_461 sourceBody687_0

def sourceBody687_463 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_462 sourceBody687_0

def sourceBody687_464 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_460 sourceBody687_463

def sourceBody687_465 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_441 sourceBody687_464

def sourceBody687_466 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_465

def sourceBody687_467 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_440 sourceBody687_466

def sourceBody687_468 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_356 sourceBody687_467

def sourceBody687_469 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_468

def sourceBody687_470 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_355 sourceBody687_469

def sourceBody687_471 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_216 sourceBody687_470

def sourceBody687_472 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_471

def sourceBody687_473 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_472

def sourceBody687_474 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_473

def sourceBody687_475 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_474

def sourceBody687_476 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_475

def sourceBody687_477 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_476

def sourceBody687_478 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_477

def sourceBody687_479 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_478

def sourceBody687_480 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_204 sourceBody687_479

def sourceBody687_481 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_480

def sourceBody687_482 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_203 sourceBody687_481

def sourceBody687_483 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_482

def sourceBody687_484 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_202 sourceBody687_483

def sourceBody687_485 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_484

def sourceBody687_486 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_201 sourceBody687_485

def sourceBody687_487 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_486

def sourceBody687_488 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_200 sourceBody687_487

def sourceBody687_489 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_190 sourceBody687_488

def sourceBody687_490 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_489

def sourceBody687_491 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_490

def sourceBody687_492 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_182 sourceBody687_491

def sourceBody687_493 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_168 sourceBody687_492

def sourceBody687_494 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_493

def sourceBody687_495 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_494

def sourceBody687_496 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_495 sourceBody687_331

def sourceBody687_497 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody687_496 sourceBody687_175

def sourceBody687_498 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_497 sourceBody687_3

def sourceBody687_499 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_498 sourceBody687_0

def sourceBody687_500 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_162 sourceBody687_499

def sourceBody687_501 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody687_500 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody687_502 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_501 sourceBody687_3

def sourceBody687_503 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_3 sourceBody687_502

def sourceBody687_504 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_161 sourceBody687_503

def sourceBody687_505 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 46)) (some 685) ([62, 20]) (some (62, sourceBody687_44, 687, 47))

def sourceBody687_506 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_505 sourceBody687_3

def sourceBody687_507 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_506 sourceBody687_0

def sourceBody687_508 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_163 sourceBody687_507

def sourceBody687_509 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_120 sourceBody687_508

def sourceBody687_510 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 28)

def sourceBody687_511 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody687_512 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 20 (Flapjack.WordRegImm.reg 52) sourceBody687_171 sourceBody687_169

def sourceBody687_513 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_512 sourceBody687_3

def sourceBody687_514 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody687_515 : WordLangProgHOL (BitVec 64) :=
.call (some (([62]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 48)) (some 78) ([20, 52]) (some (20, sourceBody687_185, 687, 49))

def sourceBody687_516 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_515 sourceBody687_3

def sourceBody687_517 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_516 sourceBody687_0

def sourceBody687_518 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_130 sourceBody687_517

def sourceBody687_519 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_514 sourceBody687_518

def sourceBody687_520 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_519

def sourceBody687_521 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_520

def sourceBody687_522 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 56)

def sourceBody687_523 : WordLangProgHOL (BitVec 64) :=
.call (some (([62]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody687_0, 687, 50)) (some 70) ([20]) (some (20, sourceBody687_185, 687, 51))

def sourceBody687_524 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_523 sourceBody687_3

def sourceBody687_525 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_524 sourceBody687_0

def sourceBody687_526 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_522 sourceBody687_525

def sourceBody687_527 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_526

def sourceBody687_528 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_527

def sourceBody687_529 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_521 sourceBody687_528

def sourceBody687_530 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody687_531 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [62]

def sourceBody687_532 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_531 sourceBody687_0

def sourceBody687_533 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_530 sourceBody687_532

def sourceBody687_534 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_529 sourceBody687_533

def sourceBody687_535 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody687_534 sourceBody687_0

def sourceBody687_536 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_535 sourceBody687_3

def sourceBody687_537 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_536 sourceBody687_0

def sourceBody687_538 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_174 sourceBody687_537

def sourceBody687_539 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_513 sourceBody687_538

def sourceBody687_540 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_511 sourceBody687_539

def sourceBody687_541 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_510 sourceBody687_540

def sourceBody687_542 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 48))

def sourceBody687_543 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody687_544 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody687_545 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody687_546 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 62)

def sourceBody687_547 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 60

def sourceBody687_548 : WordLangProgHOL (BitVec 64) :=
.call (some (([70, 8, 42, 26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 52)) (some 660) ([60, 18, 50, 34]) (some (60, sourceBody687_547, 687, 53))

def sourceBody687_549 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_548 sourceBody687_3

def sourceBody687_550 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_549 sourceBody687_0

def sourceBody687_551 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_207 sourceBody687_550

def sourceBody687_552 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_206 sourceBody687_551

def sourceBody687_553 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_205 sourceBody687_552

def sourceBody687_554 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_546 sourceBody687_553

def sourceBody687_555 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody687_556 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 60)

def sourceBody687_557 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody687_558 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 50 (Flapjack.WordRegImm.reg 34) sourceBody687_219 sourceBody687_220

def sourceBody687_559 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_558 sourceBody687_3

def sourceBody687_560 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 66,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 60)
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody687_561 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 66,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 60)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody687_562 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 66,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 60)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody687_563 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 66,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 60)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody687_564 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 70)

def sourceBody687_565 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 8)

def sourceBody687_566 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 42)

def sourceBody687_567 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 26)

def sourceBody687_568 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 46, 30, 64]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody687_0, 687, 54)) (some 657) ([22, 54, 38, 72, 6, 40, 24, 58]) (some (22, sourceBody687_236, 687, 55))

def sourceBody687_569 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_568 sourceBody687_3

def sourceBody687_570 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_569 sourceBody687_0

def sourceBody687_571 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_567 sourceBody687_570

def sourceBody687_572 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_566 sourceBody687_571

def sourceBody687_573 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_565 sourceBody687_572

def sourceBody687_574 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_564 sourceBody687_573

def sourceBody687_575 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_231 sourceBody687_574

def sourceBody687_576 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_230 sourceBody687_575

def sourceBody687_577 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_229 sourceBody687_576

def sourceBody687_578 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_228 sourceBody687_577

def sourceBody687_579 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 60)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody687_580 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_579 sourceBody687_280

def sourceBody687_581 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_580

def sourceBody687_582 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 60, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody687_583 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 22)

def sourceBody687_584 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_583 sourceBody687_0

def sourceBody687_585 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_584 sourceBody687_0

def sourceBody687_586 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_582 sourceBody687_585

def sourceBody687_587 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_586

def sourceBody687_588 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_581 sourceBody687_587

def sourceBody687_589 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_578 sourceBody687_588

def sourceBody687_590 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_589

def sourceBody687_591 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_590

def sourceBody687_592 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_591

def sourceBody687_593 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_592

def sourceBody687_594 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_593

def sourceBody687_595 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_594

def sourceBody687_596 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_595

def sourceBody687_597 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_596

def sourceBody687_598 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_563 sourceBody687_597

def sourceBody687_599 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_598

def sourceBody687_600 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_562 sourceBody687_599

def sourceBody687_601 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_600

def sourceBody687_602 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_561 sourceBody687_601

def sourceBody687_603 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_602

def sourceBody687_604 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_560 sourceBody687_603

def sourceBody687_605 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_604

def sourceBody687_606 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_605 sourceBody687_331

def sourceBody687_607 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 68 (Flapjack.WordRegImm.imm 0#64) sourceBody687_606 sourceBody687_175

def sourceBody687_608 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_607 sourceBody687_3

def sourceBody687_609 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_608 sourceBody687_0

def sourceBody687_610 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_223 sourceBody687_609

def sourceBody687_611 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_559 sourceBody687_610

def sourceBody687_612 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_557 sourceBody687_611

def sourceBody687_613 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_556 sourceBody687_612

def sourceBody687_614 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody687_613 (Flapjack.Spt.bs
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody687_615 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_614 sourceBody687_3

def sourceBody687_616 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_3 sourceBody687_615

def sourceBody687_617 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 56)

def sourceBody687_618 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody687_0, 687, 56)) (some 70) ([50]) (some (50, sourceBody687_346, 687, 57))

def sourceBody687_619 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_618 sourceBody687_3

def sourceBody687_620 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_619 sourceBody687_0

def sourceBody687_621 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_617 sourceBody687_620

def sourceBody687_622 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_621

def sourceBody687_623 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_622

def sourceBody687_624 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_616 sourceBody687_623

def sourceBody687_625 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody687_626 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_625 sourceBody687_0

def sourceBody687_627 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_356 sourceBody687_626

def sourceBody687_628 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_624 sourceBody687_627

def sourceBody687_629 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_555 sourceBody687_628

def sourceBody687_630 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_629

def sourceBody687_631 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_554 sourceBody687_630

def sourceBody687_632 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_631

def sourceBody687_633 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_632

def sourceBody687_634 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_633

def sourceBody687_635 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_634

def sourceBody687_636 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_635

def sourceBody687_637 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_636

def sourceBody687_638 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_637

def sourceBody687_639 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_638

def sourceBody687_640 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_545 sourceBody687_639

def sourceBody687_641 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_640

def sourceBody687_642 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_544 sourceBody687_641

def sourceBody687_643 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_642

def sourceBody687_644 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_543 sourceBody687_643

def sourceBody687_645 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_644

def sourceBody687_646 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_542 sourceBody687_645

def sourceBody687_647 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_646

def sourceBody687_648 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_541 sourceBody687_647

def sourceBody687_649 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_509 sourceBody687_648

def sourceBody687_650 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_649

def sourceBody687_651 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_650

def sourceBody687_652 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_504 sourceBody687_651

def sourceBody687_653 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_41 sourceBody687_652

def sourceBody687_654 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_653

def sourceBody687_655 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_654

def sourceBody687_656 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_35 sourceBody687_655

def sourceBody687_657 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_656

def sourceBody687_658 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_657

def sourceBody687_659 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_29 sourceBody687_658

def sourceBody687_660 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_659

def sourceBody687_661 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_660

def sourceBody687_662 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_23 sourceBody687_661

def sourceBody687_663 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_662

def sourceBody687_664 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_663

def sourceBody687_665 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_17 sourceBody687_664

def sourceBody687_666 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_665

def sourceBody687_667 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_666

def sourceBody687_668 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_11 sourceBody687_667

def sourceBody687_669 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_668

def sourceBody687_670 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_669

def sourceBody687_671 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_5 sourceBody687_670

def sourceBody687_672 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_671

def sourceBody687_673 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody687_0 sourceBody687_672

def source687 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (687, 3, sourceBody687_673)
end InitECandidate.Proofs.WordStages
