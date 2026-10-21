import InitECandidate.Proofs.WordStages.Source770
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody786_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody786_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody786_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 2)) (some 69) ([]) (some (10, sourceBody786_1, 786, 3))

def sourceBody786_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody786_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_2 sourceBody786_3

def sourceBody786_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_4 sourceBody786_0

def sourceBody786_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 864#64)

def sourceBody786_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody786_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 4)) (some 68) ([28]) (some (28, sourceBody786_7, 786, 5))

def sourceBody786_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_8 sourceBody786_3

def sourceBody786_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_9 sourceBody786_0

def sourceBody786_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_6 sourceBody786_10

def sourceBody786_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 10)

def sourceBody786_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody786_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody786_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody786_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody786_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 480#64])

def sourceBody786_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 576#64])

def sourceBody786_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 672#64])

def sourceBody786_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 768#64])

def sourceBody786_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 2)

def sourceBody786_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody786_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody786_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 28)

def sourceBody786_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 22)

def sourceBody786_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody786_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 6)) (some 736) ([16, 34]) (some (16, sourceBody786_26, 786, 7))

def sourceBody786_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_27 sourceBody786_3

def sourceBody786_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_28 sourceBody786_0

def sourceBody786_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_25 sourceBody786_29

def sourceBody786_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_24 sourceBody786_30

def sourceBody786_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_31

def sourceBody786_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_32

def sourceBody786_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody786_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 40)

def sourceBody786_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 8)) (some 736) ([16, 34]) (some (16, sourceBody786_26, 786, 9))

def sourceBody786_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_36 sourceBody786_3

def sourceBody786_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_37 sourceBody786_0

def sourceBody786_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_35 sourceBody786_38

def sourceBody786_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_34 sourceBody786_39

def sourceBody786_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_40

def sourceBody786_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_41

def sourceBody786_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_33 sourceBody786_42

def sourceBody786_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 38)

def sourceBody786_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 20)

def sourceBody786_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 10)) (some 736) ([16, 34]) (some (16, sourceBody786_26, 786, 11))

def sourceBody786_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_46 sourceBody786_3

def sourceBody786_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_47 sourceBody786_0

def sourceBody786_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_45 sourceBody786_48

def sourceBody786_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_44 sourceBody786_49

def sourceBody786_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_50

def sourceBody786_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_51

def sourceBody786_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_43 sourceBody786_52

def sourceBody786_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody786_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 22)

def sourceBody786_56 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 12)) (some 730) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 13))

def sourceBody786_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_56 sourceBody786_3

def sourceBody786_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_57 sourceBody786_0

def sourceBody786_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_55 sourceBody786_58

def sourceBody786_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_45 sourceBody786_59

def sourceBody786_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_54 sourceBody786_60

def sourceBody786_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_61

def sourceBody786_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_62

def sourceBody786_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_53 sourceBody786_63

def sourceBody786_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 8)

def sourceBody786_66 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 14)) (some 736) ([16, 34]) (some (16, sourceBody786_26, 786, 15))

def sourceBody786_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_66 sourceBody786_3

def sourceBody786_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_67 sourceBody786_0

def sourceBody786_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_65 sourceBody786_68

def sourceBody786_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_54 sourceBody786_69

def sourceBody786_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_70

def sourceBody786_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_71

def sourceBody786_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_64 sourceBody786_72

def sourceBody786_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 28)

def sourceBody786_75 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 16)) (some 731) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 17))

def sourceBody786_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_75 sourceBody786_3

def sourceBody786_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_76 sourceBody786_0

def sourceBody786_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_74 sourceBody786_77

def sourceBody786_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_65 sourceBody786_78

def sourceBody786_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_54 sourceBody786_79

def sourceBody786_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_80

def sourceBody786_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_81

def sourceBody786_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_73 sourceBody786_82

def sourceBody786_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 38)

def sourceBody786_85 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 18)) (some 731) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 19))

def sourceBody786_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_85 sourceBody786_3

def sourceBody786_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_86 sourceBody786_0

def sourceBody786_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_84 sourceBody786_87

def sourceBody786_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_65 sourceBody786_88

def sourceBody786_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_54 sourceBody786_89

def sourceBody786_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_90

def sourceBody786_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_91

def sourceBody786_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_83 sourceBody786_92

def sourceBody786_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody786_95 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 20)) (some 730) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 21))

def sourceBody786_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_95 sourceBody786_3

def sourceBody786_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_96 sourceBody786_0

def sourceBody786_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_94 sourceBody786_97

def sourceBody786_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_65 sourceBody786_98

def sourceBody786_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_54 sourceBody786_99

def sourceBody786_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_100

def sourceBody786_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_101

def sourceBody786_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_93 sourceBody786_102

def sourceBody786_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 26)

def sourceBody786_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 28)

def sourceBody786_106 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 22)) (some 730) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 23))

def sourceBody786_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_106 sourceBody786_3

def sourceBody786_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_107 sourceBody786_0

def sourceBody786_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_74 sourceBody786_108

def sourceBody786_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_105 sourceBody786_109

def sourceBody786_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_104 sourceBody786_110

def sourceBody786_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_111

def sourceBody786_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_112

def sourceBody786_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_103 sourceBody786_113

def sourceBody786_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 26)

def sourceBody786_116 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 24)) (some 730) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 25))

def sourceBody786_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_116 sourceBody786_3

def sourceBody786_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_117 sourceBody786_0

def sourceBody786_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_74 sourceBody786_118

def sourceBody786_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_115 sourceBody786_119

def sourceBody786_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_104 sourceBody786_120

def sourceBody786_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_121

def sourceBody786_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_122

def sourceBody786_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_114 sourceBody786_123

def sourceBody786_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 36)

def sourceBody786_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 26)

def sourceBody786_127 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 26)) (some 730) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 27))

def sourceBody786_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_127 sourceBody786_3

def sourceBody786_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_128 sourceBody786_0

def sourceBody786_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_126 sourceBody786_129

def sourceBody786_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_25 sourceBody786_130

def sourceBody786_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_125 sourceBody786_131

def sourceBody786_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_132

def sourceBody786_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_133

def sourceBody786_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_124 sourceBody786_134

def sourceBody786_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody786_137 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 28)) (some 736) ([16, 34]) (some (16, sourceBody786_26, 786, 29))

def sourceBody786_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_137 sourceBody786_3

def sourceBody786_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_138 sourceBody786_0

def sourceBody786_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_115 sourceBody786_139

def sourceBody786_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_136 sourceBody786_140

def sourceBody786_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_141

def sourceBody786_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_142

def sourceBody786_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_135 sourceBody786_143

def sourceBody786_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody786_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 6)

def sourceBody786_147 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 30)) (some 736) ([16, 34]) (some (16, sourceBody786_26, 786, 31))

def sourceBody786_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_147 sourceBody786_3

def sourceBody786_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_148 sourceBody786_0

def sourceBody786_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_146 sourceBody786_149

def sourceBody786_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_145 sourceBody786_150

def sourceBody786_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_151

def sourceBody786_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_152

def sourceBody786_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_144 sourceBody786_153

def sourceBody786_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 30)

def sourceBody786_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 18)

def sourceBody786_157 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 32)) (some 731) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 33))

def sourceBody786_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_157 sourceBody786_3

def sourceBody786_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_158 sourceBody786_0

def sourceBody786_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_94 sourceBody786_159

def sourceBody786_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_156 sourceBody786_160

def sourceBody786_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_155 sourceBody786_161

def sourceBody786_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_162

def sourceBody786_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_163

def sourceBody786_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_154 sourceBody786_164

def sourceBody786_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 30)

def sourceBody786_167 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 34)) (some 731) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 35))

def sourceBody786_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_167 sourceBody786_3

def sourceBody786_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_168 sourceBody786_0

def sourceBody786_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_94 sourceBody786_169

def sourceBody786_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_166 sourceBody786_170

def sourceBody786_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_155 sourceBody786_171

def sourceBody786_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_172

def sourceBody786_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_173

def sourceBody786_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_165 sourceBody786_174

def sourceBody786_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody786_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 40)

def sourceBody786_178 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 36)) (some 730) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 37))

def sourceBody786_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_178 sourceBody786_3

def sourceBody786_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_179 sourceBody786_0

def sourceBody786_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_177 sourceBody786_180

def sourceBody786_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_146 sourceBody786_181

def sourceBody786_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_176 sourceBody786_182

def sourceBody786_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_183

def sourceBody786_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_184

def sourceBody786_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_175 sourceBody786_185

def sourceBody786_187 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 38)) (some 736) ([16, 34]) (some (16, sourceBody786_26, 786, 39))

def sourceBody786_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_187 sourceBody786_3

def sourceBody786_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_188 sourceBody786_0

def sourceBody786_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_146 sourceBody786_189

def sourceBody786_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_176 sourceBody786_190

def sourceBody786_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_191

def sourceBody786_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_192

def sourceBody786_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_186 sourceBody786_193

def sourceBody786_195 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 20)

def sourceBody786_196 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 40)) (some 731) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 41))

def sourceBody786_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_196 sourceBody786_3

def sourceBody786_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_197 sourceBody786_0

def sourceBody786_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_195 sourceBody786_198

def sourceBody786_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_146 sourceBody786_199

def sourceBody786_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_176 sourceBody786_200

def sourceBody786_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_201

def sourceBody786_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_202

def sourceBody786_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_194 sourceBody786_203

def sourceBody786_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody786_206 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 42)) (some 731) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 43))

def sourceBody786_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_206 sourceBody786_3

def sourceBody786_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_207 sourceBody786_0

def sourceBody786_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_205 sourceBody786_208

def sourceBody786_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_146 sourceBody786_209

def sourceBody786_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_176 sourceBody786_210

def sourceBody786_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_211

def sourceBody786_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_212

def sourceBody786_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_204 sourceBody786_213

def sourceBody786_215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 40)

def sourceBody786_216 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 30)

def sourceBody786_217 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 44)) (some 731) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 45))

def sourceBody786_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_217 sourceBody786_3

def sourceBody786_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_218 sourceBody786_0

def sourceBody786_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_216 sourceBody786_219

def sourceBody786_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_65 sourceBody786_220

def sourceBody786_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_215 sourceBody786_221

def sourceBody786_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_222

def sourceBody786_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_223

def sourceBody786_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_214 sourceBody786_224

def sourceBody786_226 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 46)) (some 735) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 47))

def sourceBody786_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_226 sourceBody786_3

def sourceBody786_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_227 sourceBody786_0

def sourceBody786_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_126 sourceBody786_228

def sourceBody786_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_35 sourceBody786_229

def sourceBody786_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_215 sourceBody786_230

def sourceBody786_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_231

def sourceBody786_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_232

def sourceBody786_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_225 sourceBody786_233

def sourceBody786_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 38)

def sourceBody786_236 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 48)) (some 730) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 49))

def sourceBody786_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_236 sourceBody786_3

def sourceBody786_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_237 sourceBody786_0

def sourceBody786_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_84 sourceBody786_238

def sourceBody786_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_235 sourceBody786_239

def sourceBody786_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_44 sourceBody786_240

def sourceBody786_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_241

def sourceBody786_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_242

def sourceBody786_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_234 sourceBody786_243

def sourceBody786_245 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 50)) (some 730) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 51))

def sourceBody786_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_245 sourceBody786_3

def sourceBody786_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_246 sourceBody786_0

def sourceBody786_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_84 sourceBody786_247

def sourceBody786_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_235 sourceBody786_248

def sourceBody786_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_44 sourceBody786_249

def sourceBody786_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_250

def sourceBody786_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_251

def sourceBody786_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_244 sourceBody786_252

def sourceBody786_254 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 52)) (some 730) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 53))

def sourceBody786_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_254 sourceBody786_3

def sourceBody786_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_255 sourceBody786_0

def sourceBody786_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_84 sourceBody786_256

def sourceBody786_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_235 sourceBody786_257

def sourceBody786_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_44 sourceBody786_258

def sourceBody786_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_259

def sourceBody786_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_260

def sourceBody786_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_253 sourceBody786_261

def sourceBody786_263 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 54)) (some 731) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 55))

def sourceBody786_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_263 sourceBody786_3

def sourceBody786_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_264 sourceBody786_0

def sourceBody786_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_84 sourceBody786_265

def sourceBody786_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_35 sourceBody786_266

def sourceBody786_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_215 sourceBody786_267

def sourceBody786_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_268

def sourceBody786_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_269

def sourceBody786_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_262 sourceBody786_270

def sourceBody786_272 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody786_273 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 56)) (some 725) ([16, 34]) (some (16, sourceBody786_26, 786, 57))

def sourceBody786_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_273 sourceBody786_3

def sourceBody786_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_274 sourceBody786_0

def sourceBody786_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_166 sourceBody786_275

def sourceBody786_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_272 sourceBody786_276

def sourceBody786_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_277

def sourceBody786_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_278

def sourceBody786_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_271 sourceBody786_279

def sourceBody786_281 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 58)) (some 735) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 59))

def sourceBody786_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_281 sourceBody786_3

def sourceBody786_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_282 sourceBody786_0

def sourceBody786_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_205 sourceBody786_283

def sourceBody786_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_115 sourceBody786_284

def sourceBody786_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_54 sourceBody786_285

def sourceBody786_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_286

def sourceBody786_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_287

def sourceBody786_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_280 sourceBody786_288

def sourceBody786_290 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 60)) (some 730) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 61))

def sourceBody786_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_290 sourceBody786_3

def sourceBody786_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_291 sourceBody786_0

def sourceBody786_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_94 sourceBody786_292

def sourceBody786_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_65 sourceBody786_293

def sourceBody786_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_54 sourceBody786_294

def sourceBody786_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_295

def sourceBody786_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_296

def sourceBody786_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_289 sourceBody786_297

def sourceBody786_299 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody786_300 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 62)) (some 732) ([16, 34]) (some (16, sourceBody786_26, 786, 63))

def sourceBody786_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_300 sourceBody786_3

def sourceBody786_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_301 sourceBody786_0

def sourceBody786_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_65 sourceBody786_302

def sourceBody786_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_299 sourceBody786_303

def sourceBody786_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_304

def sourceBody786_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_305

def sourceBody786_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_298 sourceBody786_306

def sourceBody786_308 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 36)

def sourceBody786_309 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 64)) (some 736) ([16, 34]) (some (16, sourceBody786_26, 786, 65))

def sourceBody786_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_309 sourceBody786_3

def sourceBody786_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_310 sourceBody786_0

def sourceBody786_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_308 sourceBody786_311

def sourceBody786_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_125 sourceBody786_312

def sourceBody786_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_313

def sourceBody786_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_314

def sourceBody786_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_307 sourceBody786_315

def sourceBody786_317 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 66)) (some 731) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 67))

def sourceBody786_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_317 sourceBody786_3

def sourceBody786_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_318 sourceBody786_0

def sourceBody786_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_74 sourceBody786_319

def sourceBody786_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_308 sourceBody786_320

def sourceBody786_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_125 sourceBody786_321

def sourceBody786_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_322

def sourceBody786_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_323

def sourceBody786_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_316 sourceBody786_324

def sourceBody786_326 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody786_327 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 68)) (some 731) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 69))

def sourceBody786_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_327 sourceBody786_3

def sourceBody786_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_328 sourceBody786_0

def sourceBody786_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_326 sourceBody786_329

def sourceBody786_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_308 sourceBody786_330

def sourceBody786_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_125 sourceBody786_331

def sourceBody786_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_332

def sourceBody786_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_333

def sourceBody786_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_325 sourceBody786_334

def sourceBody786_336 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 70)) (some 730) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 71))

def sourceBody786_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_336 sourceBody786_3

def sourceBody786_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_337 sourceBody786_0

def sourceBody786_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_195 sourceBody786_338

def sourceBody786_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_45 sourceBody786_339

def sourceBody786_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_34 sourceBody786_340

def sourceBody786_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_341

def sourceBody786_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_342

def sourceBody786_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_335 sourceBody786_343

def sourceBody786_345 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 72)) (some 730) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 73))

def sourceBody786_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_345 sourceBody786_3

def sourceBody786_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_346 sourceBody786_0

def sourceBody786_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_195 sourceBody786_347

def sourceBody786_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_45 sourceBody786_348

def sourceBody786_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_34 sourceBody786_349

def sourceBody786_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_350

def sourceBody786_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_351

def sourceBody786_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_344 sourceBody786_352

def sourceBody786_354 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody786_355 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 74)) (some 731) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 75))

def sourceBody786_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_355 sourceBody786_3

def sourceBody786_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_356 sourceBody786_0

def sourceBody786_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_195 sourceBody786_357

def sourceBody786_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_308 sourceBody786_358

def sourceBody786_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_354 sourceBody786_359

def sourceBody786_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_360

def sourceBody786_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_361

def sourceBody786_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_353 sourceBody786_362

def sourceBody786_364 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 76)) (some 735) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 77))

def sourceBody786_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_364 sourceBody786_3

def sourceBody786_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_365 sourceBody786_0

def sourceBody786_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_205 sourceBody786_366

def sourceBody786_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_146 sourceBody786_367

def sourceBody786_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_24 sourceBody786_368

def sourceBody786_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_369

def sourceBody786_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_370

def sourceBody786_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_363 sourceBody786_371

def sourceBody786_373 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody786_374 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody786_0, 786, 78)) (some 730) ([16, 34, 12]) (some (16, sourceBody786_26, 786, 79))

def sourceBody786_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_374 sourceBody786_3

def sourceBody786_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_375 sourceBody786_0

def sourceBody786_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_74 sourceBody786_376

def sourceBody786_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_105 sourceBody786_377

def sourceBody786_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_373 sourceBody786_378

def sourceBody786_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_379

def sourceBody786_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_380

def sourceBody786_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_372 sourceBody786_381

def sourceBody786_383 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 32)

def sourceBody786_384 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody786_0, 786, 80)) (some 70) ([16]) (some (16, sourceBody786_26, 786, 81))

def sourceBody786_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_384 sourceBody786_3

def sourceBody786_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_385 sourceBody786_0

def sourceBody786_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_383 sourceBody786_386

def sourceBody786_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_387

def sourceBody786_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_388

def sourceBody786_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_382 sourceBody786_389

def sourceBody786_391 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody786_392 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody786_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_392 sourceBody786_0

def sourceBody786_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_391 sourceBody786_393

def sourceBody786_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_390 sourceBody786_394

def sourceBody786_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_23 sourceBody786_395

def sourceBody786_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_396

def sourceBody786_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_22 sourceBody786_397

def sourceBody786_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_398

def sourceBody786_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_21 sourceBody786_399

def sourceBody786_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_400

def sourceBody786_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_20 sourceBody786_401

def sourceBody786_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_402

def sourceBody786_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_19 sourceBody786_403

def sourceBody786_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_404

def sourceBody786_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_18 sourceBody786_405

def sourceBody786_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_406

def sourceBody786_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_17 sourceBody786_407

def sourceBody786_409 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_408

def sourceBody786_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_16 sourceBody786_409

def sourceBody786_411 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_410

def sourceBody786_412 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_15 sourceBody786_411

def sourceBody786_413 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_412

def sourceBody786_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_14 sourceBody786_413

def sourceBody786_415 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_414

def sourceBody786_416 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_13 sourceBody786_415

def sourceBody786_417 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_416

def sourceBody786_418 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_12 sourceBody786_417

def sourceBody786_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_418

def sourceBody786_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_11 sourceBody786_419

def sourceBody786_421 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_420

def sourceBody786_422 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_421

def sourceBody786_423 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_5 sourceBody786_422

def sourceBody786_424 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_423

def sourceBody786_425 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody786_0 sourceBody786_424

def source786 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (786, 3, sourceBody786_425)
end InitECandidate.Proofs.WordStages
