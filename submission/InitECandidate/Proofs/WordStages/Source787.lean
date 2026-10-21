import InitECandidate.Proofs.WordStages.Source771
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody787_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody787_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody787_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 2)) (some 69) ([]) (some (24, sourceBody787_1, 787, 3))

def sourceBody787_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody787_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_2 sourceBody787_3

def sourceBody787_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_4 sourceBody787_0

def sourceBody787_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 1152#64)

def sourceBody787_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody787_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 4)) (some 68) ([46]) (some (46, sourceBody787_7, 787, 5))

def sourceBody787_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_8 sourceBody787_3

def sourceBody787_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_9 sourceBody787_0

def sourceBody787_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_6 sourceBody787_10

def sourceBody787_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 24)

def sourceBody787_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody787_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody787_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody787_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody787_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 480#64])

def sourceBody787_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 576#64])

def sourceBody787_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 672#64])

def sourceBody787_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 768#64])

def sourceBody787_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 864#64])

def sourceBody787_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 960#64])

def sourceBody787_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 1056#64])

def sourceBody787_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 2)

def sourceBody787_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody787_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody787_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 46)

def sourceBody787_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 38)

def sourceBody787_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 48

def sourceBody787_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 6)) (some 736) ([48, 14]) (some (48, sourceBody787_29, 787, 7))

def sourceBody787_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_30 sourceBody787_3

def sourceBody787_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_31 sourceBody787_0

def sourceBody787_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_28 sourceBody787_32

def sourceBody787_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_27 sourceBody787_33

def sourceBody787_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_34

def sourceBody787_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_35

def sourceBody787_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 12)

def sourceBody787_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody787_39 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 8)) (some 736) ([48, 14]) (some (48, sourceBody787_29, 787, 9))

def sourceBody787_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_39 sourceBody787_3

def sourceBody787_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_40 sourceBody787_0

def sourceBody787_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_38 sourceBody787_41

def sourceBody787_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_37 sourceBody787_42

def sourceBody787_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_43

def sourceBody787_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_44

def sourceBody787_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_36 sourceBody787_45

def sourceBody787_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 32)

def sourceBody787_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 46)

def sourceBody787_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 4)

def sourceBody787_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 10)) (some 735) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 11))

def sourceBody787_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_50 sourceBody787_3

def sourceBody787_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_51 sourceBody787_0

def sourceBody787_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_49 sourceBody787_52

def sourceBody787_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_48 sourceBody787_53

def sourceBody787_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_47 sourceBody787_54

def sourceBody787_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_55

def sourceBody787_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_56

def sourceBody787_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_46 sourceBody787_57

def sourceBody787_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 22)

def sourceBody787_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 38)

def sourceBody787_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 12)) (some 730) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 13))

def sourceBody787_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_61 sourceBody787_3

def sourceBody787_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_62 sourceBody787_0

def sourceBody787_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_60 sourceBody787_63

def sourceBody787_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_38 sourceBody787_64

def sourceBody787_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_59 sourceBody787_65

def sourceBody787_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_66

def sourceBody787_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_67

def sourceBody787_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_58 sourceBody787_68

def sourceBody787_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 22)

def sourceBody787_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 14)) (some 736) ([48, 14]) (some (48, sourceBody787_29, 787, 15))

def sourceBody787_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_71 sourceBody787_3

def sourceBody787_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_72 sourceBody787_0

def sourceBody787_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_70 sourceBody787_73

def sourceBody787_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_59 sourceBody787_74

def sourceBody787_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_75

def sourceBody787_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_76

def sourceBody787_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_69 sourceBody787_77

def sourceBody787_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 12)

def sourceBody787_80 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 16)) (some 731) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 17))

def sourceBody787_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_80 sourceBody787_3

def sourceBody787_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_81 sourceBody787_0

def sourceBody787_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_79 sourceBody787_82

def sourceBody787_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_70 sourceBody787_83

def sourceBody787_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_59 sourceBody787_84

def sourceBody787_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_85

def sourceBody787_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_86

def sourceBody787_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_78 sourceBody787_87

def sourceBody787_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 46)

def sourceBody787_90 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 18)) (some 731) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 19))

def sourceBody787_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_90 sourceBody787_3

def sourceBody787_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_91 sourceBody787_0

def sourceBody787_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_89 sourceBody787_92

def sourceBody787_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_70 sourceBody787_93

def sourceBody787_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_59 sourceBody787_94

def sourceBody787_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_95

def sourceBody787_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_96

def sourceBody787_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_88 sourceBody787_97

def sourceBody787_99 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 20)) (some 735) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 21))

def sourceBody787_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_99 sourceBody787_3

def sourceBody787_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_100 sourceBody787_0

def sourceBody787_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_89 sourceBody787_101

def sourceBody787_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_70 sourceBody787_102

def sourceBody787_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_59 sourceBody787_103

def sourceBody787_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_104

def sourceBody787_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_105

def sourceBody787_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_98 sourceBody787_106

def sourceBody787_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 44)

def sourceBody787_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 32)

def sourceBody787_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 42)

def sourceBody787_111 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 22)) (some 731) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 23))

def sourceBody787_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_111 sourceBody787_3

def sourceBody787_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_112 sourceBody787_0

def sourceBody787_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_110 sourceBody787_113

def sourceBody787_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_109 sourceBody787_114

def sourceBody787_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_108 sourceBody787_115

def sourceBody787_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_116

def sourceBody787_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_117

def sourceBody787_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_107 sourceBody787_118

def sourceBody787_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 18)

def sourceBody787_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 44)

def sourceBody787_122 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 24)) (some 736) ([48, 14]) (some (48, sourceBody787_29, 787, 25))

def sourceBody787_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_122 sourceBody787_3

def sourceBody787_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_123 sourceBody787_0

def sourceBody787_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_121 sourceBody787_124

def sourceBody787_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_120 sourceBody787_125

def sourceBody787_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_126

def sourceBody787_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_127

def sourceBody787_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_119 sourceBody787_128

def sourceBody787_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 40)

def sourceBody787_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody787_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 18)

def sourceBody787_133 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 26)) (some 730) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 27))

def sourceBody787_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_133 sourceBody787_3

def sourceBody787_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_134 sourceBody787_0

def sourceBody787_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_132 sourceBody787_135

def sourceBody787_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_131 sourceBody787_136

def sourceBody787_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_130 sourceBody787_137

def sourceBody787_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_138

def sourceBody787_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_139

def sourceBody787_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_129 sourceBody787_140

def sourceBody787_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 40)

def sourceBody787_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 40)

def sourceBody787_144 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 28)) (some 730) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 29))

def sourceBody787_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_144 sourceBody787_3

def sourceBody787_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_145 sourceBody787_0

def sourceBody787_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_143 sourceBody787_146

def sourceBody787_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_142 sourceBody787_147

def sourceBody787_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_130 sourceBody787_148

def sourceBody787_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_149

def sourceBody787_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_150

def sourceBody787_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_141 sourceBody787_151

def sourceBody787_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 28)

def sourceBody787_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 44)

def sourceBody787_155 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 30)) (some 735) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 31))

def sourceBody787_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_155 sourceBody787_3

def sourceBody787_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_156 sourceBody787_0

def sourceBody787_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_154 sourceBody787_157

def sourceBody787_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_142 sourceBody787_158

def sourceBody787_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_153 sourceBody787_159

def sourceBody787_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_160

def sourceBody787_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_161

def sourceBody787_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_152 sourceBody787_162

def sourceBody787_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 50)

def sourceBody787_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody787_166 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 32)) (some 731) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 33))

def sourceBody787_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_166 sourceBody787_3

def sourceBody787_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_167 sourceBody787_0

def sourceBody787_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_165 sourceBody787_168

def sourceBody787_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_70 sourceBody787_169

def sourceBody787_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_164 sourceBody787_170

def sourceBody787_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_171

def sourceBody787_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_172

def sourceBody787_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_163 sourceBody787_173

def sourceBody787_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 50)

def sourceBody787_176 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 34)) (some 731) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 35))

def sourceBody787_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_176 sourceBody787_3

def sourceBody787_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_177 sourceBody787_0

def sourceBody787_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_165 sourceBody787_178

def sourceBody787_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_175 sourceBody787_179

def sourceBody787_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_164 sourceBody787_180

def sourceBody787_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_181

def sourceBody787_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_182

def sourceBody787_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_174 sourceBody787_183

def sourceBody787_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 30)

def sourceBody787_186 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 36)) (some 735) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 37))

def sourceBody787_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_186 sourceBody787_3

def sourceBody787_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_187 sourceBody787_0

def sourceBody787_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_49 sourceBody787_188

def sourceBody787_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_175 sourceBody787_189

def sourceBody787_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_185 sourceBody787_190

def sourceBody787_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_191

def sourceBody787_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_192

def sourceBody787_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_184 sourceBody787_193

def sourceBody787_195 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 10)

def sourceBody787_196 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 38)) (some 735) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 39))

def sourceBody787_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_196 sourceBody787_3

def sourceBody787_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_197 sourceBody787_0

def sourceBody787_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_110 sourceBody787_198

def sourceBody787_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_142 sourceBody787_199

def sourceBody787_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_195 sourceBody787_200

def sourceBody787_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_201

def sourceBody787_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_202

def sourceBody787_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_194 sourceBody787_203

def sourceBody787_205 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 40)) (some 736) ([48, 14]) (some (48, sourceBody787_29, 787, 41))

def sourceBody787_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_205 sourceBody787_3

def sourceBody787_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_206 sourceBody787_0

def sourceBody787_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_175 sourceBody787_207

def sourceBody787_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_47 sourceBody787_208

def sourceBody787_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_209

def sourceBody787_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_210

def sourceBody787_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_204 sourceBody787_211

def sourceBody787_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 28)

def sourceBody787_214 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 42)) (some 731) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 43))

def sourceBody787_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_214 sourceBody787_3

def sourceBody787_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_215 sourceBody787_0

def sourceBody787_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_213 sourceBody787_216

def sourceBody787_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_109 sourceBody787_217

def sourceBody787_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_47 sourceBody787_218

def sourceBody787_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_219

def sourceBody787_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_220

def sourceBody787_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_212 sourceBody787_221

def sourceBody787_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 10)

def sourceBody787_224 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 44)) (some 731) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 45))

def sourceBody787_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_224 sourceBody787_3

def sourceBody787_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_225 sourceBody787_0

def sourceBody787_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_223 sourceBody787_226

def sourceBody787_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_109 sourceBody787_227

def sourceBody787_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_47 sourceBody787_228

def sourceBody787_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_229

def sourceBody787_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_230

def sourceBody787_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_222 sourceBody787_231

def sourceBody787_233 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 46)) (some 731) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 47))

def sourceBody787_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_233 sourceBody787_3

def sourceBody787_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_234 sourceBody787_0

def sourceBody787_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_223 sourceBody787_235

def sourceBody787_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_109 sourceBody787_236

def sourceBody787_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_47 sourceBody787_237

def sourceBody787_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_238

def sourceBody787_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_239

def sourceBody787_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_232 sourceBody787_240

def sourceBody787_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 38)

def sourceBody787_243 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 48)) (some 730) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 49))

def sourceBody787_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_243 sourceBody787_3

def sourceBody787_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_244 sourceBody787_0

def sourceBody787_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_154 sourceBody787_245

def sourceBody787_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_28 sourceBody787_246

def sourceBody787_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_242 sourceBody787_247

def sourceBody787_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_248

def sourceBody787_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_249

def sourceBody787_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_241 sourceBody787_250

def sourceBody787_252 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 50)) (some 736) ([48, 14]) (some (48, sourceBody787_29, 787, 51))

def sourceBody787_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_252 sourceBody787_3

def sourceBody787_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_253 sourceBody787_0

def sourceBody787_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_28 sourceBody787_254

def sourceBody787_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_242 sourceBody787_255

def sourceBody787_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_256

def sourceBody787_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_257

def sourceBody787_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_251 sourceBody787_258

def sourceBody787_260 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 52)) (some 731) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 53))

def sourceBody787_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_260 sourceBody787_3

def sourceBody787_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_261 sourceBody787_0

def sourceBody787_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_89 sourceBody787_262

def sourceBody787_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_28 sourceBody787_263

def sourceBody787_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_242 sourceBody787_264

def sourceBody787_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_265

def sourceBody787_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_266

def sourceBody787_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_259 sourceBody787_267

def sourceBody787_269 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 54)) (some 731) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 55))

def sourceBody787_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_269 sourceBody787_3

def sourceBody787_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_270 sourceBody787_0

def sourceBody787_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_132 sourceBody787_271

def sourceBody787_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_28 sourceBody787_272

def sourceBody787_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_242 sourceBody787_273

def sourceBody787_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_274

def sourceBody787_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_275

def sourceBody787_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_268 sourceBody787_276

def sourceBody787_278 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 20)

def sourceBody787_279 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 56)) (some 730) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 57))

def sourceBody787_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_279 sourceBody787_3

def sourceBody787_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_280 sourceBody787_0

def sourceBody787_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_60 sourceBody787_281

def sourceBody787_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_38 sourceBody787_282

def sourceBody787_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_278 sourceBody787_283

def sourceBody787_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_284

def sourceBody787_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_285

def sourceBody787_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_277 sourceBody787_286

def sourceBody787_288 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody787_289 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 32)

def sourceBody787_290 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 58)) (some 731) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 59))

def sourceBody787_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_290 sourceBody787_3

def sourceBody787_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_291 sourceBody787_0

def sourceBody787_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_289 sourceBody787_292

def sourceBody787_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_288 sourceBody787_293

def sourceBody787_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_195 sourceBody787_294

def sourceBody787_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_295

def sourceBody787_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_296

def sourceBody787_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_287 sourceBody787_297

def sourceBody787_299 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 50)

def sourceBody787_300 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 60)) (some 735) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 61))

def sourceBody787_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_300 sourceBody787_3

def sourceBody787_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_301 sourceBody787_0

def sourceBody787_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_299 sourceBody787_302

def sourceBody787_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_288 sourceBody787_303

def sourceBody787_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_195 sourceBody787_304

def sourceBody787_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_305

def sourceBody787_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_306

def sourceBody787_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_298 sourceBody787_307

def sourceBody787_309 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody787_310 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 62)) (some 735) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 63))

def sourceBody787_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_310 sourceBody787_3

def sourceBody787_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_311 sourceBody787_0

def sourceBody787_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_213 sourceBody787_312

def sourceBody787_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_309 sourceBody787_313

def sourceBody787_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_59 sourceBody787_314

def sourceBody787_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_315

def sourceBody787_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_316

def sourceBody787_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_308 sourceBody787_317

def sourceBody787_319 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 22)

def sourceBody787_320 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 64)) (some 730) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 65))

def sourceBody787_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_320 sourceBody787_3

def sourceBody787_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_321 sourceBody787_0

def sourceBody787_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_319 sourceBody787_322

def sourceBody787_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_70 sourceBody787_323

def sourceBody787_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_59 sourceBody787_324

def sourceBody787_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_325

def sourceBody787_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_326

def sourceBody787_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_318 sourceBody787_327

def sourceBody787_329 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 16)

def sourceBody787_330 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 66)) (some 731) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 67))

def sourceBody787_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_330 sourceBody787_3

def sourceBody787_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_331 sourceBody787_0

def sourceBody787_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_319 sourceBody787_332

def sourceBody787_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_288 sourceBody787_333

def sourceBody787_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_329 sourceBody787_334

def sourceBody787_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_335

def sourceBody787_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_336

def sourceBody787_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_328 sourceBody787_337

def sourceBody787_339 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 42)

def sourceBody787_340 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 68)) (some 725) ([48, 14]) (some (48, sourceBody787_29, 787, 69))

def sourceBody787_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_340 sourceBody787_3

def sourceBody787_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_341 sourceBody787_0

def sourceBody787_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_109 sourceBody787_342

def sourceBody787_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_339 sourceBody787_343

def sourceBody787_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_344

def sourceBody787_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_345

def sourceBody787_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_338 sourceBody787_346

def sourceBody787_348 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody787_349 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 70)) (some 736) ([48, 14]) (some (48, sourceBody787_29, 787, 71))

def sourceBody787_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_349 sourceBody787_3

def sourceBody787_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_350 sourceBody787_0

def sourceBody787_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_348 sourceBody787_351

def sourceBody787_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_278 sourceBody787_352

def sourceBody787_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_353

def sourceBody787_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_354

def sourceBody787_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_347 sourceBody787_355

def sourceBody787_357 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 72)) (some 731) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 73))

def sourceBody787_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_357 sourceBody787_3

def sourceBody787_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_358 sourceBody787_0

def sourceBody787_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_79 sourceBody787_359

def sourceBody787_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_348 sourceBody787_360

def sourceBody787_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_278 sourceBody787_361

def sourceBody787_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_362

def sourceBody787_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_363

def sourceBody787_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_356 sourceBody787_364

def sourceBody787_366 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 74)) (some 736) ([48, 14]) (some (48, sourceBody787_29, 787, 75))

def sourceBody787_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_366 sourceBody787_3

def sourceBody787_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_367 sourceBody787_0

def sourceBody787_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_28 sourceBody787_368

def sourceBody787_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_59 sourceBody787_369

def sourceBody787_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_370

def sourceBody787_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_371

def sourceBody787_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_365 sourceBody787_372

def sourceBody787_374 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 76)) (some 731) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 77))

def sourceBody787_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_374 sourceBody787_3

def sourceBody787_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_375 sourceBody787_0

def sourceBody787_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_319 sourceBody787_376

def sourceBody787_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_348 sourceBody787_377

def sourceBody787_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_278 sourceBody787_378

def sourceBody787_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_379

def sourceBody787_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_380

def sourceBody787_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_373 sourceBody787_381

def sourceBody787_383 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 30)

def sourceBody787_384 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 30)

def sourceBody787_385 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 78)) (some 730) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 79))

def sourceBody787_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_385 sourceBody787_3

def sourceBody787_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_386 sourceBody787_0

def sourceBody787_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_384 sourceBody787_387

def sourceBody787_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_383 sourceBody787_388

def sourceBody787_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_185 sourceBody787_389

def sourceBody787_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_390

def sourceBody787_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_391

def sourceBody787_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_382 sourceBody787_392

def sourceBody787_394 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody787_395 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 20)

def sourceBody787_396 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 80)) (some 731) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 81))

def sourceBody787_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_396 sourceBody787_3

def sourceBody787_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_397 sourceBody787_0

def sourceBody787_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_395 sourceBody787_398

def sourceBody787_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_383 sourceBody787_399

def sourceBody787_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_394 sourceBody787_400

def sourceBody787_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_401

def sourceBody787_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_402

def sourceBody787_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_393 sourceBody787_403

def sourceBody787_405 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 8)

def sourceBody787_406 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 82)) (some 730) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 83))

def sourceBody787_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_406 sourceBody787_3

def sourceBody787_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_407 sourceBody787_0

def sourceBody787_409 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_60 sourceBody787_408

def sourceBody787_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_28 sourceBody787_409

def sourceBody787_411 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_405 sourceBody787_410

def sourceBody787_412 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_411

def sourceBody787_413 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_412

def sourceBody787_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_404 sourceBody787_413

def sourceBody787_415 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 84)) (some 732) ([48, 14]) (some (48, sourceBody787_29, 787, 85))

def sourceBody787_416 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_415 sourceBody787_3

def sourceBody787_417 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_416 sourceBody787_0

def sourceBody787_418 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_175 sourceBody787_417

def sourceBody787_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_164 sourceBody787_418

def sourceBody787_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_419

def sourceBody787_421 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_420

def sourceBody787_422 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_414 sourceBody787_421

def sourceBody787_423 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody787_424 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody787_0, 787, 86)) (some 730) ([48, 14, 34]) (some (48, sourceBody787_29, 787, 87))

def sourceBody787_425 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_424 sourceBody787_3

def sourceBody787_426 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_425 sourceBody787_0

def sourceBody787_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_299 sourceBody787_426

def sourceBody787_428 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_175 sourceBody787_427

def sourceBody787_429 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_423 sourceBody787_428

def sourceBody787_430 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_429

def sourceBody787_431 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_430

def sourceBody787_432 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_422 sourceBody787_431

def sourceBody787_433 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 36)

def sourceBody787_434 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody787_0, 787, 88)) (some 70) ([48]) (some (48, sourceBody787_29, 787, 89))

def sourceBody787_435 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_434 sourceBody787_3

def sourceBody787_436 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_435 sourceBody787_0

def sourceBody787_437 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_433 sourceBody787_436

def sourceBody787_438 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_437

def sourceBody787_439 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_438

def sourceBody787_440 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_432 sourceBody787_439

def sourceBody787_441 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody787_442 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody787_443 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_442 sourceBody787_0

def sourceBody787_444 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_441 sourceBody787_443

def sourceBody787_445 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_440 sourceBody787_444

def sourceBody787_446 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_26 sourceBody787_445

def sourceBody787_447 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_446

def sourceBody787_448 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_25 sourceBody787_447

def sourceBody787_449 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_448

def sourceBody787_450 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_24 sourceBody787_449

def sourceBody787_451 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_450

def sourceBody787_452 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_23 sourceBody787_451

def sourceBody787_453 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_452

def sourceBody787_454 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_22 sourceBody787_453

def sourceBody787_455 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_454

def sourceBody787_456 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_21 sourceBody787_455

def sourceBody787_457 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_456

def sourceBody787_458 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_20 sourceBody787_457

def sourceBody787_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_458

def sourceBody787_460 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_19 sourceBody787_459

def sourceBody787_461 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_460

def sourceBody787_462 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_18 sourceBody787_461

def sourceBody787_463 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_462

def sourceBody787_464 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_17 sourceBody787_463

def sourceBody787_465 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_464

def sourceBody787_466 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_16 sourceBody787_465

def sourceBody787_467 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_466

def sourceBody787_468 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_15 sourceBody787_467

def sourceBody787_469 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_468

def sourceBody787_470 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_14 sourceBody787_469

def sourceBody787_471 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_470

def sourceBody787_472 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_13 sourceBody787_471

def sourceBody787_473 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_472

def sourceBody787_474 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_12 sourceBody787_473

def sourceBody787_475 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_474

def sourceBody787_476 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_11 sourceBody787_475

def sourceBody787_477 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_476

def sourceBody787_478 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_477

def sourceBody787_479 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_5 sourceBody787_478

def sourceBody787_480 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_479

def sourceBody787_481 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody787_0 sourceBody787_480

def source787 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (787, 5, sourceBody787_481)
end InitECandidate.Proofs.WordStages
