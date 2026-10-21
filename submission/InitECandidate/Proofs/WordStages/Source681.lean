import InitECandidate.Proofs.WordStages.Source665
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody681_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody681_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 2)
    (Flapjack.WordLangExpHOL.const 5#64))

def sourceBody681_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody681_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 2)) (some 69) ([]) (some (38, sourceBody681_2, 681, 3))

def sourceBody681_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody681_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_3 sourceBody681_4

def sourceBody681_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_5 sourceBody681_0

def sourceBody681_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 8)

def sourceBody681_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 52])

def sourceBody681_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 8,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 52)
        (Flapjack.WordLangExpHOL.const 1#64)])

def sourceBody681_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody681_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 52])

def sourceBody681_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 52)
        (Flapjack.WordLangExpHOL.const 1#64)])

def sourceBody681_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 12)

def sourceBody681_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.var 52])

def sourceBody681_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 12,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 52)
        (Flapjack.WordLangExpHOL.const 1#64)])

def sourceBody681_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 52)

def sourceBody681_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody681_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 4)) (some 68) ([46]) (some (46, sourceBody681_17, 681, 5))

def sourceBody681_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_18 sourceBody681_4

def sourceBody681_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_19 sourceBody681_0

def sourceBody681_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_16 sourceBody681_20

def sourceBody681_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 52)

def sourceBody681_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody681_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([46]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 6)) (some 68) ([20]) (some (20, sourceBody681_23, 681, 7))

def sourceBody681_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_24 sourceBody681_4

def sourceBody681_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_25 sourceBody681_0

def sourceBody681_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_22 sourceBody681_26

def sourceBody681_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 52)

def sourceBody681_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody681_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 8)) (some 68) ([42]) (some (42, sourceBody681_29, 681, 9))

def sourceBody681_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_30 sourceBody681_4

def sourceBody681_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_31 sourceBody681_0

def sourceBody681_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_28 sourceBody681_32

def sourceBody681_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 52)

def sourceBody681_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody681_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 10)) (some 68) ([32]) (some (32, sourceBody681_35, 681, 11))

def sourceBody681_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_36 sourceBody681_4

def sourceBody681_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_37 sourceBody681_0

def sourceBody681_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_34 sourceBody681_38

def sourceBody681_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 8)

def sourceBody681_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody681_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody681_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody681_44 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 54 (Flapjack.WordRegImm.reg 18) sourceBody681_42 sourceBody681_43

def sourceBody681_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_44 sourceBody681_4

def sourceBody681_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 54)

def sourceBody681_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 2)

def sourceBody681_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 26)

def sourceBody681_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 54

def sourceBody681_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 12)) (some 674) ([54, 18]) (some (54, sourceBody681_49, 681, 13))

def sourceBody681_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_50 sourceBody681_4

def sourceBody681_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_51 sourceBody681_0

def sourceBody681_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_48 sourceBody681_52

def sourceBody681_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_47 sourceBody681_53

def sourceBody681_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_54

def sourceBody681_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_55

def sourceBody681_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 46)

def sourceBody681_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 14)) (some 674) ([54, 18]) (some (54, sourceBody681_49, 681, 15))

def sourceBody681_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_58 sourceBody681_4

def sourceBody681_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_59 sourceBody681_0

def sourceBody681_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_57 sourceBody681_60

def sourceBody681_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_47 sourceBody681_61

def sourceBody681_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_62

def sourceBody681_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_63

def sourceBody681_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_56 sourceBody681_64

def sourceBody681_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 44)

def sourceBody681_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 48)

def sourceBody681_68 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 16)) (some 666) ([54, 18, 40, 30]) (some (54, sourceBody681_49, 681, 17))

def sourceBody681_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_68 sourceBody681_4

def sourceBody681_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_69 sourceBody681_0

def sourceBody681_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_67 sourceBody681_70

def sourceBody681_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_66 sourceBody681_71

def sourceBody681_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_48 sourceBody681_72

def sourceBody681_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_47 sourceBody681_73

def sourceBody681_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_74

def sourceBody681_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_75

def sourceBody681_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody681_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 28)

def sourceBody681_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 34)

def sourceBody681_80 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 18)) (some 666) ([54, 18, 40, 30]) (some (54, sourceBody681_49, 681, 19))

def sourceBody681_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_80 sourceBody681_4

def sourceBody681_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_81 sourceBody681_0

def sourceBody681_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_79 sourceBody681_82

def sourceBody681_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_78 sourceBody681_83

def sourceBody681_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_77 sourceBody681_84

def sourceBody681_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_47 sourceBody681_85

def sourceBody681_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_86

def sourceBody681_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_87

def sourceBody681_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_76 sourceBody681_88

def sourceBody681_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 26)

def sourceBody681_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 20)

def sourceBody681_92 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 20)) (some 669) ([54, 18, 40, 30]) (some (54, sourceBody681_49, 681, 21))

def sourceBody681_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_92 sourceBody681_4

def sourceBody681_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_93 sourceBody681_0

def sourceBody681_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_91 sourceBody681_94

def sourceBody681_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_90 sourceBody681_95

def sourceBody681_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_48 sourceBody681_96

def sourceBody681_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_47 sourceBody681_97

def sourceBody681_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_98

def sourceBody681_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_99

def sourceBody681_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_89 sourceBody681_100

def sourceBody681_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 22)

def sourceBody681_103 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 22)) (some 666) ([54, 18, 40, 30]) (some (54, sourceBody681_49, 681, 23))

def sourceBody681_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_103 sourceBody681_4

def sourceBody681_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_104 sourceBody681_0

def sourceBody681_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_67 sourceBody681_105

def sourceBody681_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_102 sourceBody681_106

def sourceBody681_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_57 sourceBody681_107

def sourceBody681_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_47 sourceBody681_108

def sourceBody681_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_109

def sourceBody681_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_110

def sourceBody681_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_101 sourceBody681_111

def sourceBody681_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 38)

def sourceBody681_114 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 24)) (some 666) ([54, 18, 40, 30]) (some (54, sourceBody681_49, 681, 25))

def sourceBody681_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_114 sourceBody681_4

def sourceBody681_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_115 sourceBody681_0

def sourceBody681_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_79 sourceBody681_116

def sourceBody681_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_113 sourceBody681_117

def sourceBody681_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_77 sourceBody681_118

def sourceBody681_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_47 sourceBody681_119

def sourceBody681_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_120

def sourceBody681_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_121

def sourceBody681_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_112 sourceBody681_122

def sourceBody681_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 46)

def sourceBody681_125 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 26)) (some 669) ([54, 18, 40, 30]) (some (54, sourceBody681_49, 681, 27))

def sourceBody681_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_125 sourceBody681_4

def sourceBody681_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_126 sourceBody681_0

def sourceBody681_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_91 sourceBody681_127

def sourceBody681_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_124 sourceBody681_128

def sourceBody681_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_57 sourceBody681_129

def sourceBody681_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_47 sourceBody681_130

def sourceBody681_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_131

def sourceBody681_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_132

def sourceBody681_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_123 sourceBody681_133

def sourceBody681_135 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.imm 0#64) sourceBody681_65 sourceBody681_134

def sourceBody681_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_135 sourceBody681_4

def sourceBody681_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_136 sourceBody681_0

def sourceBody681_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_46 sourceBody681_137

def sourceBody681_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_45 sourceBody681_138

def sourceBody681_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_41 sourceBody681_139

def sourceBody681_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_40 sourceBody681_140

def sourceBody681_142 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 28)) (some 672) ([54, 18]) (some (54, sourceBody681_49, 681, 29))

def sourceBody681_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_142 sourceBody681_4

def sourceBody681_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_143 sourceBody681_0

def sourceBody681_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_57 sourceBody681_144

def sourceBody681_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_47 sourceBody681_145

def sourceBody681_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 32)

def sourceBody681_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody681_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody681_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody681_151 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 18 (Flapjack.WordRegImm.reg 40) sourceBody681_149 sourceBody681_150

def sourceBody681_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_151 sourceBody681_4

def sourceBody681_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 18)

def sourceBody681_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody681_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody681_156 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 30)) (some 672) ([18, 40]) (some (18, sourceBody681_155, 681, 31))

def sourceBody681_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_156 sourceBody681_4

def sourceBody681_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_157 sourceBody681_0

def sourceBody681_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_90 sourceBody681_158

def sourceBody681_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_154 sourceBody681_159

def sourceBody681_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody681_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody681_163 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 40 (Flapjack.WordRegImm.reg 30) sourceBody681_148 sourceBody681_162

def sourceBody681_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_163 sourceBody681_4

def sourceBody681_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 40)

def sourceBody681_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 2)

def sourceBody681_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 38)

def sourceBody681_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody681_169 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 32)) (some 667) ([40, 30, 50]) (some (40, sourceBody681_168, 681, 33))

def sourceBody681_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_169 sourceBody681_4

def sourceBody681_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_170 sourceBody681_0

def sourceBody681_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_167 sourceBody681_171

def sourceBody681_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_91 sourceBody681_172

def sourceBody681_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_166 sourceBody681_173

def sourceBody681_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_174

def sourceBody681_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_175

def sourceBody681_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 26)

def sourceBody681_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 20)

def sourceBody681_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody681_180 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 34)) (some 671) ([40, 30, 50, 24]) (some (40, sourceBody681_168, 681, 35))

def sourceBody681_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_180 sourceBody681_4

def sourceBody681_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_181 sourceBody681_0

def sourceBody681_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_179 sourceBody681_182

def sourceBody681_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_178 sourceBody681_183

def sourceBody681_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_177 sourceBody681_184

def sourceBody681_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_166 sourceBody681_185

def sourceBody681_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_186

def sourceBody681_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_187

def sourceBody681_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_176 sourceBody681_188

def sourceBody681_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 46)

def sourceBody681_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 28)

def sourceBody681_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 48)

def sourceBody681_193 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 36)) (some 666) ([40, 30, 50, 24]) (some (40, sourceBody681_168, 681, 37))

def sourceBody681_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_193 sourceBody681_4

def sourceBody681_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_194 sourceBody681_0

def sourceBody681_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_192 sourceBody681_195

def sourceBody681_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_191 sourceBody681_196

def sourceBody681_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_190 sourceBody681_197

def sourceBody681_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_166 sourceBody681_198

def sourceBody681_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_199

def sourceBody681_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_200

def sourceBody681_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_189 sourceBody681_201

def sourceBody681_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 46)

def sourceBody681_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody681_205 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 38)) (some 671) ([40, 30, 50, 24]) (some (40, sourceBody681_168, 681, 39))

def sourceBody681_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_205 sourceBody681_4

def sourceBody681_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_206 sourceBody681_0

def sourceBody681_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_204 sourceBody681_207

def sourceBody681_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_203 sourceBody681_208

def sourceBody681_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_190 sourceBody681_209

def sourceBody681_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_166 sourceBody681_210

def sourceBody681_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_211

def sourceBody681_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_212

def sourceBody681_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_202 sourceBody681_213

def sourceBody681_215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 4)

def sourceBody681_216 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 56)

def sourceBody681_217 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 40)) (some 666) ([40, 30, 50, 24]) (some (40, sourceBody681_168, 681, 41))

def sourceBody681_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_217 sourceBody681_4

def sourceBody681_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_218 sourceBody681_0

def sourceBody681_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_192 sourceBody681_219

def sourceBody681_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_216 sourceBody681_220

def sourceBody681_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_215 sourceBody681_221

def sourceBody681_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_166 sourceBody681_222

def sourceBody681_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_223

def sourceBody681_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_224

def sourceBody681_226 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 36)

def sourceBody681_227 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 42)) (some 666) ([40, 30, 50, 24]) (some (40, sourceBody681_168, 681, 43))

def sourceBody681_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_227 sourceBody681_4

def sourceBody681_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_228 sourceBody681_0

def sourceBody681_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_226 sourceBody681_229

def sourceBody681_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_167 sourceBody681_230

def sourceBody681_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_91 sourceBody681_231

def sourceBody681_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_166 sourceBody681_232

def sourceBody681_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_233

def sourceBody681_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_234

def sourceBody681_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_225 sourceBody681_235

def sourceBody681_237 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 4)

def sourceBody681_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 20)

def sourceBody681_239 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 44)) (some 669) ([40, 30, 50, 24]) (some (40, sourceBody681_168, 681, 45))

def sourceBody681_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_239 sourceBody681_4

def sourceBody681_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_240 sourceBody681_0

def sourceBody681_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_238 sourceBody681_241

def sourceBody681_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_237 sourceBody681_242

def sourceBody681_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_215 sourceBody681_243

def sourceBody681_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_166 sourceBody681_244

def sourceBody681_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_245

def sourceBody681_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_246

def sourceBody681_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_236 sourceBody681_247

def sourceBody681_249 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 6)

def sourceBody681_250 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 48)

def sourceBody681_251 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 46)) (some 666) ([40, 30, 50, 24]) (some (40, sourceBody681_168, 681, 47))

def sourceBody681_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_251 sourceBody681_4

def sourceBody681_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_252 sourceBody681_0

def sourceBody681_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_226 sourceBody681_253

def sourceBody681_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_250 sourceBody681_254

def sourceBody681_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_249 sourceBody681_255

def sourceBody681_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_166 sourceBody681_256

def sourceBody681_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_257

def sourceBody681_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_258

def sourceBody681_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_248 sourceBody681_259

def sourceBody681_261 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 16)

def sourceBody681_262 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody681_0, 681, 48)) (some 70) ([40]) (some (40, sourceBody681_168, 681, 49))

def sourceBody681_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_262 sourceBody681_4

def sourceBody681_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_263 sourceBody681_0

def sourceBody681_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_261 sourceBody681_264

def sourceBody681_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_265

def sourceBody681_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_266

def sourceBody681_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_260 sourceBody681_267

def sourceBody681_269 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody681_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_269 sourceBody681_0

def sourceBody681_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_150 sourceBody681_270

def sourceBody681_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_268 sourceBody681_271

def sourceBody681_273 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 50 (Flapjack.WordRegImm.imm 0#64) sourceBody681_214 sourceBody681_272

def sourceBody681_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_273 sourceBody681_4

def sourceBody681_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_274 sourceBody681_0

def sourceBody681_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_165 sourceBody681_275

def sourceBody681_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_164 sourceBody681_276

def sourceBody681_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_161 sourceBody681_277

def sourceBody681_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_46 sourceBody681_278

def sourceBody681_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_160 sourceBody681_279

def sourceBody681_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_280

def sourceBody681_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_281

def sourceBody681_283 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody681_282 sourceBody681_0

def sourceBody681_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_283 sourceBody681_4

def sourceBody681_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_284 sourceBody681_0

def sourceBody681_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_153 sourceBody681_285

def sourceBody681_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_152 sourceBody681_286

def sourceBody681_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_148 sourceBody681_287

def sourceBody681_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_147 sourceBody681_288

def sourceBody681_290 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 20)

def sourceBody681_291 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 56)

def sourceBody681_292 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 50)) (some 666) ([18, 40, 30, 50]) (some (18, sourceBody681_155, 681, 51))

def sourceBody681_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_292 sourceBody681_4

def sourceBody681_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_293 sourceBody681_0

def sourceBody681_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_250 sourceBody681_294

def sourceBody681_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_291 sourceBody681_295

def sourceBody681_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_290 sourceBody681_296

def sourceBody681_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_154 sourceBody681_297

def sourceBody681_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_298

def sourceBody681_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_299

def sourceBody681_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_289 sourceBody681_300

def sourceBody681_302 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 42)

def sourceBody681_303 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 38)

def sourceBody681_304 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 36)

def sourceBody681_305 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 52)) (some 666) ([18, 40, 30, 50]) (some (18, sourceBody681_155, 681, 53))

def sourceBody681_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_305 sourceBody681_4

def sourceBody681_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_306 sourceBody681_0

def sourceBody681_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_304 sourceBody681_307

def sourceBody681_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_303 sourceBody681_308

def sourceBody681_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_302 sourceBody681_309

def sourceBody681_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_154 sourceBody681_310

def sourceBody681_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_311

def sourceBody681_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_312

def sourceBody681_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_301 sourceBody681_313

def sourceBody681_315 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 42)

def sourceBody681_316 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 54)) (some 669) ([18, 40, 30, 50]) (some (18, sourceBody681_155, 681, 55))

def sourceBody681_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_316 sourceBody681_4

def sourceBody681_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_317 sourceBody681_0

def sourceBody681_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_315 sourceBody681_318

def sourceBody681_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_91 sourceBody681_319

def sourceBody681_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_290 sourceBody681_320

def sourceBody681_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_154 sourceBody681_321

def sourceBody681_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_322

def sourceBody681_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_323

def sourceBody681_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_314 sourceBody681_324

def sourceBody681_326 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 56)) (some 666) ([18, 40, 30, 50]) (some (18, sourceBody681_155, 681, 57))

def sourceBody681_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_326 sourceBody681_4

def sourceBody681_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_327 sourceBody681_0

def sourceBody681_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_178 sourceBody681_328

def sourceBody681_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_177 sourceBody681_329

def sourceBody681_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_290 sourceBody681_330

def sourceBody681_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_154 sourceBody681_331

def sourceBody681_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_332

def sourceBody681_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_333

def sourceBody681_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_325 sourceBody681_334

def sourceBody681_336 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 14)

def sourceBody681_337 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 58)) (some 666) ([18, 40, 30, 50]) (some (18, sourceBody681_155, 681, 59))

def sourceBody681_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_337 sourceBody681_4

def sourceBody681_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_338 sourceBody681_0

def sourceBody681_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_250 sourceBody681_339

def sourceBody681_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_336 sourceBody681_340

def sourceBody681_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_302 sourceBody681_341

def sourceBody681_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_154 sourceBody681_342

def sourceBody681_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_343

def sourceBody681_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_344

def sourceBody681_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_335 sourceBody681_345

def sourceBody681_347 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 4)

def sourceBody681_348 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 28)

def sourceBody681_349 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 60)) (some 666) ([18, 40, 30, 50]) (some (18, sourceBody681_155, 681, 61))

def sourceBody681_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_349 sourceBody681_4

def sourceBody681_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_350 sourceBody681_0

def sourceBody681_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_304 sourceBody681_351

def sourceBody681_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_348 sourceBody681_352

def sourceBody681_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_347 sourceBody681_353

def sourceBody681_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_154 sourceBody681_354

def sourceBody681_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_355

def sourceBody681_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_356

def sourceBody681_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_346 sourceBody681_357

def sourceBody681_359 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 42)

def sourceBody681_360 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 62)) (some 669) ([18, 40, 30, 50]) (some (18, sourceBody681_155, 681, 63))

def sourceBody681_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_360 sourceBody681_4

def sourceBody681_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_361 sourceBody681_0

def sourceBody681_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_237 sourceBody681_362

def sourceBody681_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_359 sourceBody681_363

def sourceBody681_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_302 sourceBody681_364

def sourceBody681_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_154 sourceBody681_365

def sourceBody681_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_366

def sourceBody681_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_367

def sourceBody681_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_358 sourceBody681_368

def sourceBody681_370 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 64)) (some 666) ([18, 40, 30, 50]) (some (18, sourceBody681_155, 681, 65))

def sourceBody681_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_370 sourceBody681_4

def sourceBody681_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_371 sourceBody681_0

def sourceBody681_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_315 sourceBody681_372

def sourceBody681_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_190 sourceBody681_373

def sourceBody681_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_302 sourceBody681_374

def sourceBody681_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_154 sourceBody681_375

def sourceBody681_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_376

def sourceBody681_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_377

def sourceBody681_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_369 sourceBody681_378

def sourceBody681_380 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 66)) (some 669) ([18, 40, 30, 50]) (some (18, sourceBody681_155, 681, 67))

def sourceBody681_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_380 sourceBody681_4

def sourceBody681_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_381 sourceBody681_0

def sourceBody681_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_315 sourceBody681_382

def sourceBody681_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_91 sourceBody681_383

def sourceBody681_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_347 sourceBody681_384

def sourceBody681_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_154 sourceBody681_385

def sourceBody681_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_386

def sourceBody681_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_387

def sourceBody681_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_379 sourceBody681_388

def sourceBody681_390 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 6)

def sourceBody681_391 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 68)) (some 666) ([18, 40, 30, 50]) (some (18, sourceBody681_155, 681, 69))

def sourceBody681_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_391 sourceBody681_4

def sourceBody681_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_392 sourceBody681_0

def sourceBody681_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_304 sourceBody681_393

def sourceBody681_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_190 sourceBody681_394

def sourceBody681_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_390 sourceBody681_395

def sourceBody681_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_154 sourceBody681_396

def sourceBody681_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_397

def sourceBody681_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_398

def sourceBody681_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_389 sourceBody681_399

def sourceBody681_401 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody681_0, 681, 70)) (some 666) ([18, 40, 30, 50]) (some (18, sourceBody681_155, 681, 71))

def sourceBody681_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_401 sourceBody681_4

def sourceBody681_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_402 sourceBody681_0

def sourceBody681_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_250 sourceBody681_403

def sourceBody681_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_249 sourceBody681_404

def sourceBody681_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_390 sourceBody681_405

def sourceBody681_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_154 sourceBody681_406

def sourceBody681_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_407

def sourceBody681_409 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_408

def sourceBody681_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_400 sourceBody681_409

def sourceBody681_411 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody681_412 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody681_0, 681, 72)) (some 70) ([18]) (some (18, sourceBody681_155, 681, 73))

def sourceBody681_413 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_412 sourceBody681_4

def sourceBody681_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_413 sourceBody681_0

def sourceBody681_415 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_411 sourceBody681_414

def sourceBody681_416 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_415

def sourceBody681_417 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_416

def sourceBody681_418 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_410 sourceBody681_417

def sourceBody681_419 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [54]

def sourceBody681_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_419 sourceBody681_0

def sourceBody681_421 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_43 sourceBody681_420

def sourceBody681_422 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_418 sourceBody681_421

def sourceBody681_423 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_146 sourceBody681_422

def sourceBody681_424 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_423

def sourceBody681_425 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_424

def sourceBody681_426 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_141 sourceBody681_425

def sourceBody681_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_39 sourceBody681_426

def sourceBody681_428 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_427

def sourceBody681_429 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_428

def sourceBody681_430 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_33 sourceBody681_429

def sourceBody681_431 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_430

def sourceBody681_432 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_431

def sourceBody681_433 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_27 sourceBody681_432

def sourceBody681_434 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_433

def sourceBody681_435 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_434

def sourceBody681_436 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_21 sourceBody681_435

def sourceBody681_437 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_436

def sourceBody681_438 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_437

def sourceBody681_439 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_15 sourceBody681_438

def sourceBody681_440 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_439

def sourceBody681_441 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_14 sourceBody681_440

def sourceBody681_442 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_441

def sourceBody681_443 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_13 sourceBody681_442

def sourceBody681_444 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_443

def sourceBody681_445 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_12 sourceBody681_444

def sourceBody681_446 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_445

def sourceBody681_447 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_11 sourceBody681_446

def sourceBody681_448 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_447

def sourceBody681_449 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_10 sourceBody681_448

def sourceBody681_450 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_449

def sourceBody681_451 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_9 sourceBody681_450

def sourceBody681_452 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_451

def sourceBody681_453 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_8 sourceBody681_452

def sourceBody681_454 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_453

def sourceBody681_455 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_7 sourceBody681_454

def sourceBody681_456 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_455

def sourceBody681_457 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_6 sourceBody681_456

def sourceBody681_458 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_457

def sourceBody681_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_458

def sourceBody681_460 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_1 sourceBody681_459

def sourceBody681_461 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody681_0 sourceBody681_460

def source681 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (681, 7, sourceBody681_461)
end InitECandidate.Proofs.WordStages
