import InitECandidate.Proofs.WordStages.Source632
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody648_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody648_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 2)

def sourceBody648_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 76

def sourceBody648_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([62]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody648_0, 648, 2)) (some 644) ([76]) (some (76, sourceBody648_2, 648, 3))

def sourceBody648_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody648_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_3 sourceBody648_4

def sourceBody648_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_5 sourceBody648_0

def sourceBody648_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_1 sourceBody648_6

def sourceBody648_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_7

def sourceBody648_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_8

def sourceBody648_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 4)

def sourceBody648_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 6)

def sourceBody648_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 8)

def sourceBody648_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 10)

def sourceBody648_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([62]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody648_0, 648, 4)) (some 138) ([76, 58, 72, 66]) (some (76, sourceBody648_2, 648, 5))

def sourceBody648_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_14 sourceBody648_4

def sourceBody648_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_15 sourceBody648_0

def sourceBody648_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_13 sourceBody648_16

def sourceBody648_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_12 sourceBody648_17

def sourceBody648_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_11 sourceBody648_18

def sourceBody648_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_10 sourceBody648_19

def sourceBody648_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 28)

def sourceBody648_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 30)

def sourceBody648_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 32)

def sourceBody648_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 34)

def sourceBody648_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 58

def sourceBody648_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([76]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody648_0, 648, 6)) (some 138) ([58, 72, 66, 80]) (some (58, sourceBody648_25, 648, 7))

def sourceBody648_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_26 sourceBody648_4

def sourceBody648_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_27 sourceBody648_0

def sourceBody648_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_24 sourceBody648_28

def sourceBody648_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_23 sourceBody648_29

def sourceBody648_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_22 sourceBody648_30

def sourceBody648_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_21 sourceBody648_31

def sourceBody648_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 62)

def sourceBody648_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 76)

def sourceBody648_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 72

def sourceBody648_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([58]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody648_0, 648, 8)) (some 93) ([72, 66]) (some (72, sourceBody648_35, 648, 9))

def sourceBody648_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_36 sourceBody648_4

def sourceBody648_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_37 sourceBody648_0

def sourceBody648_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_34 sourceBody648_38

def sourceBody648_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_33 sourceBody648_39

def sourceBody648_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody648_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 58)

def sourceBody648_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody648_44 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 66 (Flapjack.WordRegImm.reg 80) sourceBody648_43 sourceBody648_41

def sourceBody648_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_44 sourceBody648_4

def sourceBody648_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 66)

def sourceBody648_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 58, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody648_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 72)

def sourceBody648_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_48 sourceBody648_0

def sourceBody648_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_49 sourceBody648_0

def sourceBody648_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_47 sourceBody648_50

def sourceBody648_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_51

def sourceBody648_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 2)

def sourceBody648_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 66

def sourceBody648_55 : WordLangProgHOL (BitVec 64) :=
.call (some (([72]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody648_0, 648, 10)) (some 646) ([66]) (some (66, sourceBody648_54, 648, 11))

def sourceBody648_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_55 sourceBody648_4

def sourceBody648_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_56 sourceBody648_0

def sourceBody648_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_53 sourceBody648_57

def sourceBody648_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_58

def sourceBody648_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_59

def sourceBody648_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_52 sourceBody648_60

def sourceBody648_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 4)

def sourceBody648_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 6)

def sourceBody648_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 8)

def sourceBody648_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 10)

def sourceBody648_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 58)

def sourceBody648_67 : WordLangProgHOL (BitVec 64) :=
.call (some (([72]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody648_0, 648, 12)) (some 104) ([66, 80, 52, 68, 60]) (some (66, sourceBody648_54, 648, 13))

def sourceBody648_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_67 sourceBody648_4

def sourceBody648_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_68 sourceBody648_0

def sourceBody648_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_66 sourceBody648_69

def sourceBody648_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_65 sourceBody648_70

def sourceBody648_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_64 sourceBody648_71

def sourceBody648_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_63 sourceBody648_72

def sourceBody648_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_62 sourceBody648_73

def sourceBody648_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 72)

def sourceBody648_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody648_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody648_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody648_79 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 80 (Flapjack.WordRegImm.reg 52) sourceBody648_77 sourceBody648_78

def sourceBody648_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_79 sourceBody648_4

def sourceBody648_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 80)

def sourceBody648_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 2)

def sourceBody648_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 12)

def sourceBody648_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 14)

def sourceBody648_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 16)

def sourceBody648_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 18)

def sourceBody648_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 20)

def sourceBody648_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 22)

def sourceBody648_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 24)

def sourceBody648_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 26)

def sourceBody648_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 80

def sourceBody648_92 : WordLangProgHOL (BitVec 64) :=
.call (some (([66]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody648_0, 648, 14)) (some 647) ([80, 52, 68, 60, 74, 56, 70, 64, 78]) (some (80, sourceBody648_91, 648, 15))

def sourceBody648_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_92 sourceBody648_4

def sourceBody648_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_93 sourceBody648_0

def sourceBody648_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_90 sourceBody648_94

def sourceBody648_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_89 sourceBody648_95

def sourceBody648_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_88 sourceBody648_96

def sourceBody648_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_87 sourceBody648_97

def sourceBody648_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_86 sourceBody648_98

def sourceBody648_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_85 sourceBody648_99

def sourceBody648_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_84 sourceBody648_100

def sourceBody648_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_83 sourceBody648_101

def sourceBody648_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_82 sourceBody648_102

def sourceBody648_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_103

def sourceBody648_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_104

def sourceBody648_106 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 68 (Flapjack.WordRegImm.imm 0#64) sourceBody648_105 sourceBody648_0

def sourceBody648_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_106 sourceBody648_4

def sourceBody648_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_107 sourceBody648_0

def sourceBody648_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_81 sourceBody648_108

def sourceBody648_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_80 sourceBody648_109

def sourceBody648_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_76 sourceBody648_110

def sourceBody648_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_75 sourceBody648_111

def sourceBody648_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 28)

def sourceBody648_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 30)

def sourceBody648_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 32)

def sourceBody648_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 34)

def sourceBody648_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 58)

def sourceBody648_118 : WordLangProgHOL (BitVec 64) :=
.call (some (([66]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody648_0, 648, 16)) (some 104) ([80, 52, 68, 60, 74]) (some (80, sourceBody648_91, 648, 17))

def sourceBody648_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_118 sourceBody648_4

def sourceBody648_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_119 sourceBody648_0

def sourceBody648_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_117 sourceBody648_120

def sourceBody648_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_116 sourceBody648_121

def sourceBody648_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_115 sourceBody648_122

def sourceBody648_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_114 sourceBody648_123

def sourceBody648_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_113 sourceBody648_124

def sourceBody648_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody648_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody648_128 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 52 (Flapjack.WordRegImm.reg 68) sourceBody648_76 sourceBody648_127

def sourceBody648_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_128 sourceBody648_4

def sourceBody648_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 52)

def sourceBody648_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 2)

def sourceBody648_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 36)

def sourceBody648_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 38)

def sourceBody648_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 40)

def sourceBody648_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 42)

def sourceBody648_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 44)

def sourceBody648_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 46)

def sourceBody648_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 48)

def sourceBody648_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 50)

def sourceBody648_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 52

def sourceBody648_141 : WordLangProgHOL (BitVec 64) :=
.call (some (([80]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody648_0, 648, 18)) (some 647) ([52, 68, 60, 74, 56, 70, 64, 78, 54]) (some (52, sourceBody648_140, 648, 19))

def sourceBody648_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_141 sourceBody648_4

def sourceBody648_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_142 sourceBody648_0

def sourceBody648_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_139 sourceBody648_143

def sourceBody648_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_138 sourceBody648_144

def sourceBody648_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_137 sourceBody648_145

def sourceBody648_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_136 sourceBody648_146

def sourceBody648_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_135 sourceBody648_147

def sourceBody648_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_134 sourceBody648_148

def sourceBody648_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_133 sourceBody648_149

def sourceBody648_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_132 sourceBody648_150

def sourceBody648_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_131 sourceBody648_151

def sourceBody648_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_152

def sourceBody648_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_153

def sourceBody648_155 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 60 (Flapjack.WordRegImm.imm 0#64) sourceBody648_154 sourceBody648_0

def sourceBody648_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_155 sourceBody648_4

def sourceBody648_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_156 sourceBody648_0

def sourceBody648_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_130 sourceBody648_157

def sourceBody648_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_129 sourceBody648_158

def sourceBody648_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_126 sourceBody648_159

def sourceBody648_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_46 sourceBody648_160

def sourceBody648_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_125 sourceBody648_161

def sourceBody648_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_162

def sourceBody648_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_163

def sourceBody648_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_112 sourceBody648_164

def sourceBody648_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_74 sourceBody648_165

def sourceBody648_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_166

def sourceBody648_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_167

def sourceBody648_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_61 sourceBody648_168

def sourceBody648_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody648_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_169 sourceBody648_170

def sourceBody648_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody648_173 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 52 (Flapjack.WordRegImm.imm 0#64) sourceBody648_171 sourceBody648_172

def sourceBody648_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_173 sourceBody648_4

def sourceBody648_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_174 sourceBody648_0

def sourceBody648_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_46 sourceBody648_175

def sourceBody648_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_45 sourceBody648_176

def sourceBody648_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_42 sourceBody648_177

def sourceBody648_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_41 sourceBody648_178

def sourceBody648_180 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody648_179 (Flapjack.Spt.ls PUnit.unit)

def sourceBody648_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_180 sourceBody648_4

def sourceBody648_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_4 sourceBody648_181

def sourceBody648_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody648_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [72]

def sourceBody648_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_184 sourceBody648_0

def sourceBody648_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_183 sourceBody648_185

def sourceBody648_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_182 sourceBody648_186

def sourceBody648_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_40 sourceBody648_187

def sourceBody648_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_188

def sourceBody648_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_189

def sourceBody648_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_32 sourceBody648_190

def sourceBody648_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_191

def sourceBody648_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_192

def sourceBody648_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_20 sourceBody648_193

def sourceBody648_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_194

def sourceBody648_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_0 sourceBody648_195

def sourceBody648_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody648_9 sourceBody648_196

def source648 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (648, 26, sourceBody648_197)
end InitECandidate.Proofs.WordStages
