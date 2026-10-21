import InitECandidate.Proofs.WordStages.Source781
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody797_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody797_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody797_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 2)) (some 69) ([]) (some (14, sourceBody797_1, 797, 3))

def sourceBody797_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody797_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_2 sourceBody797_3

def sourceBody797_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_4 sourceBody797_0

def sourceBody797_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 1056#64)

def sourceBody797_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody797_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 4)) (some 68) ([44]) (some (44, sourceBody797_7, 797, 5))

def sourceBody797_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_8 sourceBody797_3

def sourceBody797_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_9 sourceBody797_0

def sourceBody797_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_6 sourceBody797_10

def sourceBody797_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 14)

def sourceBody797_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody797_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody797_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody797_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody797_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 480#64])

def sourceBody797_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 576#64])

def sourceBody797_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 672#64])

def sourceBody797_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 768#64])

def sourceBody797_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 864#64])

def sourceBody797_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 960#64])

def sourceBody797_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 44)

def sourceBody797_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody797_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody797_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 6)) (some 736) ([38, 24]) (some (38, sourceBody797_25, 797, 7))

def sourceBody797_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_26 sourceBody797_3

def sourceBody797_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_27 sourceBody797_0

def sourceBody797_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_24 sourceBody797_28

def sourceBody797_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_23 sourceBody797_29

def sourceBody797_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_30

def sourceBody797_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_31

def sourceBody797_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 30)

def sourceBody797_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 4736#64])

def sourceBody797_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 44)

def sourceBody797_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 8)) (some 735) ([38, 24, 58]) (some (38, sourceBody797_25, 797, 9))

def sourceBody797_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_36 sourceBody797_3

def sourceBody797_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_37 sourceBody797_0

def sourceBody797_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_35 sourceBody797_38

def sourceBody797_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_34 sourceBody797_39

def sourceBody797_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_33 sourceBody797_40

def sourceBody797_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_41

def sourceBody797_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_42

def sourceBody797_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_32 sourceBody797_43

def sourceBody797_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 62)

def sourceBody797_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 30)

def sourceBody797_47 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 10)) (some 736) ([38, 24]) (some (38, sourceBody797_25, 797, 11))

def sourceBody797_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_47 sourceBody797_3

def sourceBody797_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_48 sourceBody797_0

def sourceBody797_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_46 sourceBody797_49

def sourceBody797_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_45 sourceBody797_50

def sourceBody797_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_51

def sourceBody797_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_52

def sourceBody797_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_44 sourceBody797_53

def sourceBody797_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 62)

def sourceBody797_56 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 12)) (some 730) ([38, 24, 58]) (some (38, sourceBody797_25, 797, 13))

def sourceBody797_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_56 sourceBody797_3

def sourceBody797_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_57 sourceBody797_0

def sourceBody797_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_55 sourceBody797_58

def sourceBody797_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_46 sourceBody797_59

def sourceBody797_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_45 sourceBody797_60

def sourceBody797_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_61

def sourceBody797_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_62

def sourceBody797_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_54 sourceBody797_63

def sourceBody797_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 10)

def sourceBody797_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 4544#64])

def sourceBody797_67 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 14)) (some 735) ([38, 24, 58]) (some (38, sourceBody797_25, 797, 15))

def sourceBody797_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_67 sourceBody797_3

def sourceBody797_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_68 sourceBody797_0

def sourceBody797_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_55 sourceBody797_69

def sourceBody797_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_66 sourceBody797_70

def sourceBody797_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_65 sourceBody797_71

def sourceBody797_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_72

def sourceBody797_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_73

def sourceBody797_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_64 sourceBody797_74

def sourceBody797_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody797_77 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 16)) (some 732) ([38, 24]) (some (38, sourceBody797_25, 797, 17))

def sourceBody797_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_77 sourceBody797_3

def sourceBody797_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_78 sourceBody797_0

def sourceBody797_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_76 sourceBody797_79

def sourceBody797_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_65 sourceBody797_80

def sourceBody797_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_81

def sourceBody797_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_82

def sourceBody797_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_75 sourceBody797_83

def sourceBody797_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 36)

def sourceBody797_86 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 18)) (some 727) ([38]) (some (38, sourceBody797_25, 797, 19))

def sourceBody797_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_86 sourceBody797_3

def sourceBody797_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_87 sourceBody797_0

def sourceBody797_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_85 sourceBody797_88

def sourceBody797_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_89

def sourceBody797_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_90

def sourceBody797_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_84 sourceBody797_91

def sourceBody797_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 62)

def sourceBody797_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 36)

def sourceBody797_95 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 20)) (some 730) ([38, 24, 58]) (some (38, sourceBody797_25, 797, 21))

def sourceBody797_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_95 sourceBody797_3

def sourceBody797_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_96 sourceBody797_0

def sourceBody797_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_94 sourceBody797_97

def sourceBody797_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_93 sourceBody797_98

def sourceBody797_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_45 sourceBody797_99

def sourceBody797_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_100

def sourceBody797_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_101

def sourceBody797_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_92 sourceBody797_102

def sourceBody797_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 40)

def sourceBody797_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 4640#64])

def sourceBody797_106 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 22)) (some 735) ([38, 24, 58]) (some (38, sourceBody797_25, 797, 23))

def sourceBody797_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_106 sourceBody797_3

def sourceBody797_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_107 sourceBody797_0

def sourceBody797_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_55 sourceBody797_108

def sourceBody797_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_105 sourceBody797_109

def sourceBody797_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_104 sourceBody797_110

def sourceBody797_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_111

def sourceBody797_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_112

def sourceBody797_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_103 sourceBody797_113

def sourceBody797_115 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 24)) (some 728) ([38]) (some (38, sourceBody797_25, 797, 25))

def sourceBody797_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_115 sourceBody797_3

def sourceBody797_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_116 sourceBody797_0

def sourceBody797_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_65 sourceBody797_117

def sourceBody797_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody797_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody797_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody797_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody797_123 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 58) sourceBody797_121 sourceBody797_122

def sourceBody797_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_123 sourceBody797_3

def sourceBody797_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody797_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 4736#64])

def sourceBody797_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 4544#64])

def sourceBody797_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody797_129 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 26)) (some 735) ([24, 58, 16]) (some (24, sourceBody797_128, 797, 27))

def sourceBody797_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_129 sourceBody797_3

def sourceBody797_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_130 sourceBody797_0

def sourceBody797_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_127 sourceBody797_131

def sourceBody797_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_126 sourceBody797_132

def sourceBody797_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_76 sourceBody797_133

def sourceBody797_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_134

def sourceBody797_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_135

def sourceBody797_137 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody797_136 sourceBody797_0

def sourceBody797_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_137 sourceBody797_3

def sourceBody797_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_138 sourceBody797_0

def sourceBody797_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_125 sourceBody797_139

def sourceBody797_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_124 sourceBody797_140

def sourceBody797_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_120 sourceBody797_141

def sourceBody797_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_119 sourceBody797_142

def sourceBody797_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 36)

def sourceBody797_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 10)

def sourceBody797_146 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 28)) (some 736) ([24, 58]) (some (24, sourceBody797_128, 797, 29))

def sourceBody797_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_146 sourceBody797_3

def sourceBody797_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_147 sourceBody797_0

def sourceBody797_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_145 sourceBody797_148

def sourceBody797_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_144 sourceBody797_149

def sourceBody797_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_150

def sourceBody797_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_151

def sourceBody797_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_143 sourceBody797_152

def sourceBody797_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody797_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody797_156 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 30)) (some 735) ([24, 58, 16]) (some (24, sourceBody797_128, 797, 31))

def sourceBody797_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_156 sourceBody797_3

def sourceBody797_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_157 sourceBody797_0

def sourceBody797_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_155 sourceBody797_158

def sourceBody797_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_94 sourceBody797_159

def sourceBody797_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_154 sourceBody797_160

def sourceBody797_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_161

def sourceBody797_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_162

def sourceBody797_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_153 sourceBody797_163

def sourceBody797_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 60)

def sourceBody797_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 4544#64])

def sourceBody797_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 40)

def sourceBody797_168 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 32)) (some 735) ([24, 58, 16]) (some (24, sourceBody797_128, 797, 33))

def sourceBody797_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_168 sourceBody797_3

def sourceBody797_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_169 sourceBody797_0

def sourceBody797_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_167 sourceBody797_170

def sourceBody797_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_166 sourceBody797_171

def sourceBody797_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_165 sourceBody797_172

def sourceBody797_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_173

def sourceBody797_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_174

def sourceBody797_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_164 sourceBody797_175

def sourceBody797_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 60)

def sourceBody797_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 36)

def sourceBody797_179 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 34)) (some 735) ([24, 58, 16]) (some (24, sourceBody797_128, 797, 35))

def sourceBody797_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_179 sourceBody797_3

def sourceBody797_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_180 sourceBody797_0

def sourceBody797_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_178 sourceBody797_181

def sourceBody797_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_177 sourceBody797_182

def sourceBody797_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_165 sourceBody797_183

def sourceBody797_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_184

def sourceBody797_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_185

def sourceBody797_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_176 sourceBody797_186

def sourceBody797_188 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 40)

def sourceBody797_189 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 36)) (some 736) ([24, 58]) (some (24, sourceBody797_128, 797, 37))

def sourceBody797_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_189 sourceBody797_3

def sourceBody797_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_190 sourceBody797_0

def sourceBody797_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_188 sourceBody797_191

def sourceBody797_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_144 sourceBody797_192

def sourceBody797_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_193

def sourceBody797_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_194

def sourceBody797_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_187 sourceBody797_195

def sourceBody797_197 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 38)) (some 735) ([24, 58, 16]) (some (24, sourceBody797_128, 797, 39))

def sourceBody797_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_197 sourceBody797_3

def sourceBody797_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_198 sourceBody797_0

def sourceBody797_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_167 sourceBody797_199

def sourceBody797_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_94 sourceBody797_200

def sourceBody797_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_144 sourceBody797_201

def sourceBody797_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_202

def sourceBody797_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_203

def sourceBody797_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_196 sourceBody797_204

def sourceBody797_206 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 40)) (some 730) ([24, 58, 16]) (some (24, sourceBody797_128, 797, 41))

def sourceBody797_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_206 sourceBody797_3

def sourceBody797_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_207 sourceBody797_0

def sourceBody797_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_178 sourceBody797_208

def sourceBody797_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_177 sourceBody797_209

def sourceBody797_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_165 sourceBody797_210

def sourceBody797_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_211

def sourceBody797_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_212

def sourceBody797_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_205 sourceBody797_213

def sourceBody797_215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 4640#64])

def sourceBody797_216 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 26)

def sourceBody797_217 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 42)) (some 735) ([24, 58, 16]) (some (24, sourceBody797_128, 797, 43))

def sourceBody797_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_217 sourceBody797_3

def sourceBody797_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_218 sourceBody797_0

def sourceBody797_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_216 sourceBody797_219

def sourceBody797_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_215 sourceBody797_220

def sourceBody797_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_144 sourceBody797_221

def sourceBody797_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_222

def sourceBody797_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_223

def sourceBody797_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_214 sourceBody797_224

def sourceBody797_226 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 44)) (some 730) ([24, 58, 16]) (some (24, sourceBody797_128, 797, 45))

def sourceBody797_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_226 sourceBody797_3

def sourceBody797_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_227 sourceBody797_0

def sourceBody797_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_178 sourceBody797_228

def sourceBody797_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_177 sourceBody797_229

def sourceBody797_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_165 sourceBody797_230

def sourceBody797_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_231

def sourceBody797_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_232

def sourceBody797_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_225 sourceBody797_233

def sourceBody797_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody797_236 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 46)) (some 796) ([24, 58, 16]) (some (24, sourceBody797_128, 797, 47))

def sourceBody797_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_236 sourceBody797_3

def sourceBody797_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_237 sourceBody797_0

def sourceBody797_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_216 sourceBody797_238

def sourceBody797_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_177 sourceBody797_239

def sourceBody797_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_235 sourceBody797_240

def sourceBody797_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 50)

def sourceBody797_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 44)

def sourceBody797_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 4)

def sourceBody797_245 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 58

def sourceBody797_246 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 48)) (some 735) ([58, 16, 48]) (some (58, sourceBody797_245, 797, 49))

def sourceBody797_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_246 sourceBody797_3

def sourceBody797_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_247 sourceBody797_0

def sourceBody797_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_244 sourceBody797_248

def sourceBody797_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_243 sourceBody797_249

def sourceBody797_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_242 sourceBody797_250

def sourceBody797_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_251

def sourceBody797_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_252

def sourceBody797_254 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody797_255 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 50)

def sourceBody797_256 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 50)) (some 735) ([58, 16, 48]) (some (58, sourceBody797_245, 797, 51))

def sourceBody797_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_256 sourceBody797_3

def sourceBody797_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_257 sourceBody797_0

def sourceBody797_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_255 sourceBody797_258

def sourceBody797_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_254 sourceBody797_259

def sourceBody797_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_242 sourceBody797_260

def sourceBody797_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_261

def sourceBody797_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_262

def sourceBody797_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_253 sourceBody797_263

def sourceBody797_265 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 30)

def sourceBody797_266 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 52)) (some 736) ([58, 16]) (some (58, sourceBody797_245, 797, 53))

def sourceBody797_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_266 sourceBody797_3

def sourceBody797_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_267 sourceBody797_0

def sourceBody797_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_265 sourceBody797_268

def sourceBody797_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_94 sourceBody797_269

def sourceBody797_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_270

def sourceBody797_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_271

def sourceBody797_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_264 sourceBody797_272

def sourceBody797_274 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 30)

def sourceBody797_275 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 54)) (some 735) ([58, 16, 48]) (some (58, sourceBody797_245, 797, 55))

def sourceBody797_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_275 sourceBody797_3

def sourceBody797_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_276 sourceBody797_0

def sourceBody797_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_274 sourceBody797_277

def sourceBody797_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_178 sourceBody797_278

def sourceBody797_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_94 sourceBody797_279

def sourceBody797_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_280

def sourceBody797_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_281

def sourceBody797_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_273 sourceBody797_282

def sourceBody797_284 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 68)

def sourceBody797_285 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 60)

def sourceBody797_286 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 56)) (some 735) ([58, 16, 48]) (some (58, sourceBody797_245, 797, 57))

def sourceBody797_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_286 sourceBody797_3

def sourceBody797_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_287 sourceBody797_0

def sourceBody797_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_285 sourceBody797_288

def sourceBody797_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_178 sourceBody797_289

def sourceBody797_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_284 sourceBody797_290

def sourceBody797_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_291

def sourceBody797_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_292

def sourceBody797_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_283 sourceBody797_293

def sourceBody797_295 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody797_296 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 58)

def sourceBody797_297 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody797_298 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody797_299 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody797_300 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 48 (Flapjack.WordRegImm.reg 34) sourceBody797_298 sourceBody797_299

def sourceBody797_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_300 sourceBody797_3

def sourceBody797_302 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 48)

def sourceBody797_303 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody797_304 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 66 66 48 34))

def sourceBody797_305 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 36)

def sourceBody797_306 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 4832#64, Flapjack.WordLangExpHOL.var 66])

def sourceBody797_307 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 50)

def sourceBody797_308 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 48

def sourceBody797_309 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 58)) (some 735) ([12, 42, 28]) (some (48, sourceBody797_308, 797, 59))

def sourceBody797_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_309 sourceBody797_3

def sourceBody797_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_310 sourceBody797_0

def sourceBody797_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_307 sourceBody797_311

def sourceBody797_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_306 sourceBody797_312

def sourceBody797_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_305 sourceBody797_313

def sourceBody797_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_304 sourceBody797_314

def sourceBody797_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_303 sourceBody797_315

def sourceBody797_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_296 sourceBody797_316

def sourceBody797_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_317

def sourceBody797_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_318

def sourceBody797_320 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 62)

def sourceBody797_321 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 36)

def sourceBody797_322 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 60)) (some 736) ([48, 34]) (some (48, sourceBody797_308, 797, 61))

def sourceBody797_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_322 sourceBody797_3

def sourceBody797_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_323 sourceBody797_0

def sourceBody797_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_321 sourceBody797_324

def sourceBody797_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_320 sourceBody797_325

def sourceBody797_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_326

def sourceBody797_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_327

def sourceBody797_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_319 sourceBody797_328

def sourceBody797_330 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 62)

def sourceBody797_331 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 26)

def sourceBody797_332 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 62)) (some 735) ([48, 34, 66]) (some (48, sourceBody797_308, 797, 63))

def sourceBody797_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_332 sourceBody797_3

def sourceBody797_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_333 sourceBody797_0

def sourceBody797_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_331 sourceBody797_334

def sourceBody797_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_330 sourceBody797_335

def sourceBody797_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_320 sourceBody797_336

def sourceBody797_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_337

def sourceBody797_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_338

def sourceBody797_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_329 sourceBody797_339

def sourceBody797_341 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 68)

def sourceBody797_342 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 64)) (some 731) ([48, 34, 66]) (some (48, sourceBody797_308, 797, 65))

def sourceBody797_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_342 sourceBody797_3

def sourceBody797_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_343 sourceBody797_0

def sourceBody797_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_341 sourceBody797_344

def sourceBody797_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_330 sourceBody797_345

def sourceBody797_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_320 sourceBody797_346

def sourceBody797_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_347

def sourceBody797_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_348

def sourceBody797_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_340 sourceBody797_349

def sourceBody797_351 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 66)) (some 728) ([48]) (some (48, sourceBody797_308, 797, 67))

def sourceBody797_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_351 sourceBody797_3

def sourceBody797_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_352 sourceBody797_0

def sourceBody797_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_320 sourceBody797_353

def sourceBody797_355 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody797_356 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody797_357 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody797_358 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody797_359 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 34 (Flapjack.WordRegImm.reg 66) sourceBody797_357 sourceBody797_358

def sourceBody797_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_359 sourceBody797_3

def sourceBody797_361 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody797_362 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 34)

def sourceBody797_363 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody797_364 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.reg 28) sourceBody797_363 sourceBody797_361

def sourceBody797_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_364 sourceBody797_3

def sourceBody797_366 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 38)

def sourceBody797_367 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody797_368 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody797_369 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody797_370 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 20 (Flapjack.WordRegImm.reg 52) sourceBody797_368 sourceBody797_369

def sourceBody797_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_370 sourceBody797_3

def sourceBody797_372 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody797_373 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 20)

def sourceBody797_374 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody797_375 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 70 (Flapjack.WordRegImm.reg 6) sourceBody797_374 sourceBody797_372

def sourceBody797_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_375 sourceBody797_3

def sourceBody797_377 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 24)

def sourceBody797_378 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody797_379 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody797_380 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody797_381 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 22 (Flapjack.WordRegImm.reg 56) sourceBody797_379 sourceBody797_380

def sourceBody797_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_381 sourceBody797_3

def sourceBody797_383 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody797_384 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 22)

def sourceBody797_385 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody797_386 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 46 (Flapjack.WordRegImm.reg 32) sourceBody797_385 sourceBody797_383

def sourceBody797_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_386 sourceBody797_3

def sourceBody797_388 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.var 70, Flapjack.WordLangExpHOL.var 46])

def sourceBody797_389 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 18)

def sourceBody797_390 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 36)

def sourceBody797_391 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody797_392 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 68)) (some 725) ([34, 66]) (some (34, sourceBody797_391, 797, 69))

def sourceBody797_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_392 sourceBody797_3

def sourceBody797_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_393 sourceBody797_0

def sourceBody797_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_390 sourceBody797_394

def sourceBody797_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_389 sourceBody797_395

def sourceBody797_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_396

def sourceBody797_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_397

def sourceBody797_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_121 sourceBody797_0

def sourceBody797_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_399 sourceBody797_0

def sourceBody797_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_398 sourceBody797_400

def sourceBody797_402 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 64 (Flapjack.WordRegImm.imm 0#64) sourceBody797_401 sourceBody797_0

def sourceBody797_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_402 sourceBody797_3

def sourceBody797_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_403 sourceBody797_0

def sourceBody797_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_388 sourceBody797_404

def sourceBody797_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_387 sourceBody797_405

def sourceBody797_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_384 sourceBody797_406

def sourceBody797_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_383 sourceBody797_407

def sourceBody797_409 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_382 sourceBody797_408

def sourceBody797_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_378 sourceBody797_409

def sourceBody797_411 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_377 sourceBody797_410

def sourceBody797_412 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_376 sourceBody797_411

def sourceBody797_413 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_373 sourceBody797_412

def sourceBody797_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_372 sourceBody797_413

def sourceBody797_415 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_371 sourceBody797_414

def sourceBody797_416 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_367 sourceBody797_415

def sourceBody797_417 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_366 sourceBody797_416

def sourceBody797_418 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_365 sourceBody797_417

def sourceBody797_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_362 sourceBody797_418

def sourceBody797_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_361 sourceBody797_419

def sourceBody797_421 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_360 sourceBody797_420

def sourceBody797_422 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_356 sourceBody797_421

def sourceBody797_423 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_355 sourceBody797_422

def sourceBody797_424 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 58, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody797_425 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 48)

def sourceBody797_426 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_425 sourceBody797_0

def sourceBody797_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_426 sourceBody797_0

def sourceBody797_428 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_424 sourceBody797_427

def sourceBody797_429 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_428

def sourceBody797_430 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_423 sourceBody797_429

def sourceBody797_431 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_354 sourceBody797_430

def sourceBody797_432 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_431

def sourceBody797_433 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_432

def sourceBody797_434 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_350 sourceBody797_433

def sourceBody797_435 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody797_436 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_434 sourceBody797_435

def sourceBody797_437 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody797_438 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 66 (Flapjack.WordRegImm.imm 0#64) sourceBody797_436 sourceBody797_437

def sourceBody797_439 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_438 sourceBody797_3

def sourceBody797_440 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_439 sourceBody797_0

def sourceBody797_441 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_302 sourceBody797_440

def sourceBody797_442 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_301 sourceBody797_441

def sourceBody797_443 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_297 sourceBody797_442

def sourceBody797_444 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_296 sourceBody797_443

def sourceBody797_445 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody797_444 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody797_446 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_445 sourceBody797_3

def sourceBody797_447 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_3 sourceBody797_446

def sourceBody797_448 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 38)

def sourceBody797_449 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 48 (Flapjack.WordRegImm.reg 34) sourceBody797_298 sourceBody797_299

def sourceBody797_450 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_449 sourceBody797_3

def sourceBody797_451 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 40)

def sourceBody797_452 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 40)

def sourceBody797_453 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 30)

def sourceBody797_454 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 70)) (some 735) ([48, 34, 66]) (some (48, sourceBody797_308, 797, 71))

def sourceBody797_455 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_454 sourceBody797_3

def sourceBody797_456 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_455 sourceBody797_0

def sourceBody797_457 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_453 sourceBody797_456

def sourceBody797_458 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_452 sourceBody797_457

def sourceBody797_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_451 sourceBody797_458

def sourceBody797_460 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_459

def sourceBody797_461 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_460

def sourceBody797_462 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 66 (Flapjack.WordRegImm.imm 0#64) sourceBody797_461 sourceBody797_0

def sourceBody797_463 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_462 sourceBody797_3

def sourceBody797_464 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_463 sourceBody797_0

def sourceBody797_465 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_302 sourceBody797_464

def sourceBody797_466 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_450 sourceBody797_465

def sourceBody797_467 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_358 sourceBody797_466

def sourceBody797_468 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_448 sourceBody797_467

def sourceBody797_469 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_447 sourceBody797_468

def sourceBody797_470 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 72)) (some 741) ([48]) (some (48, sourceBody797_308, 797, 73))

def sourceBody797_471 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_470 sourceBody797_3

def sourceBody797_472 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_471 sourceBody797_0

def sourceBody797_473 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_244 sourceBody797_472

def sourceBody797_474 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 74)) (some 741) ([34]) (some (34, sourceBody797_391, 797, 75))

def sourceBody797_475 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_474 sourceBody797_3

def sourceBody797_476 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_475 sourceBody797_0

def sourceBody797_477 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_389 sourceBody797_476

def sourceBody797_478 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 16)

def sourceBody797_479 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 48)

def sourceBody797_480 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody797_481 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 66 (Flapjack.WordRegImm.reg 12) sourceBody797_356 sourceBody797_480

def sourceBody797_482 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_481 sourceBody797_3

def sourceBody797_483 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 66)

def sourceBody797_484 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 18)

def sourceBody797_485 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody797_486 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 66

def sourceBody797_487 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 76)) (some 732) ([66, 12]) (some (66, sourceBody797_486, 797, 77))

def sourceBody797_488 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_487 sourceBody797_3

def sourceBody797_489 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_488 sourceBody797_0

def sourceBody797_490 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_485 sourceBody797_489

def sourceBody797_491 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_484 sourceBody797_490

def sourceBody797_492 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_491

def sourceBody797_493 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_492

def sourceBody797_494 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.imm 0#64) sourceBody797_493 sourceBody797_0

def sourceBody797_495 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_494 sourceBody797_3

def sourceBody797_496 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_495 sourceBody797_0

def sourceBody797_497 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_483 sourceBody797_496

def sourceBody797_498 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_482 sourceBody797_497

def sourceBody797_499 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_479 sourceBody797_498

def sourceBody797_500 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_478 sourceBody797_499

def sourceBody797_501 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 10)

def sourceBody797_502 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 78)) (some 735) ([66, 12, 42]) (some (66, sourceBody797_486, 797, 79))

def sourceBody797_503 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_502 sourceBody797_3

def sourceBody797_504 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_503 sourceBody797_0

def sourceBody797_505 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_501 sourceBody797_504

def sourceBody797_506 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_485 sourceBody797_505

def sourceBody797_507 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_484 sourceBody797_506

def sourceBody797_508 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_507

def sourceBody797_509 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_508

def sourceBody797_510 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_500 sourceBody797_509

def sourceBody797_511 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 2)

def sourceBody797_512 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 40)

def sourceBody797_513 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 80)) (some 725) ([66, 12]) (some (66, sourceBody797_486, 797, 81))

def sourceBody797_514 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_513 sourceBody797_3

def sourceBody797_515 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_514 sourceBody797_0

def sourceBody797_516 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_512 sourceBody797_515

def sourceBody797_517 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_511 sourceBody797_516

def sourceBody797_518 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_517

def sourceBody797_519 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_518

def sourceBody797_520 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_510 sourceBody797_519

def sourceBody797_521 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody797_522 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 82)) (some 725) ([66, 12]) (some (66, sourceBody797_486, 797, 83))

def sourceBody797_523 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_522 sourceBody797_3

def sourceBody797_524 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_523 sourceBody797_0

def sourceBody797_525 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_485 sourceBody797_524

def sourceBody797_526 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_521 sourceBody797_525

def sourceBody797_527 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_526

def sourceBody797_528 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_527

def sourceBody797_529 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_520 sourceBody797_528

def sourceBody797_530 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody797_531 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody797_532 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody797_0, 797, 84)) (some 725) ([66, 12]) (some (66, sourceBody797_486, 797, 85))

def sourceBody797_533 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_532 sourceBody797_3

def sourceBody797_534 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_533 sourceBody797_0

def sourceBody797_535 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_531 sourceBody797_534

def sourceBody797_536 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_530 sourceBody797_535

def sourceBody797_537 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_536

def sourceBody797_538 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_537

def sourceBody797_539 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_529 sourceBody797_538

def sourceBody797_540 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 54)

def sourceBody797_541 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody797_0, 797, 86)) (some 70) ([66]) (some (66, sourceBody797_486, 797, 87))

def sourceBody797_542 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_541 sourceBody797_3

def sourceBody797_543 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_542 sourceBody797_0

def sourceBody797_544 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_540 sourceBody797_543

def sourceBody797_545 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_544

def sourceBody797_546 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_545

def sourceBody797_547 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_539 sourceBody797_546

def sourceBody797_548 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [34]

def sourceBody797_549 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_548 sourceBody797_0

def sourceBody797_550 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_358 sourceBody797_549

def sourceBody797_551 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_547 sourceBody797_550

def sourceBody797_552 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_477 sourceBody797_551

def sourceBody797_553 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_552

def sourceBody797_554 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_553

def sourceBody797_555 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_473 sourceBody797_554

def sourceBody797_556 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_555

def sourceBody797_557 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_556

def sourceBody797_558 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_469 sourceBody797_557

def sourceBody797_559 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_295 sourceBody797_558

def sourceBody797_560 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_559

def sourceBody797_561 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_122 sourceBody797_560

def sourceBody797_562 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_561

def sourceBody797_563 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_294 sourceBody797_562

def sourceBody797_564 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_241 sourceBody797_563

def sourceBody797_565 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_564

def sourceBody797_566 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_565

def sourceBody797_567 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_234 sourceBody797_566

def sourceBody797_568 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_118 sourceBody797_567

def sourceBody797_569 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_568

def sourceBody797_570 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_569

def sourceBody797_571 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_114 sourceBody797_570

def sourceBody797_572 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_22 sourceBody797_571

def sourceBody797_573 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_572

def sourceBody797_574 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_21 sourceBody797_573

def sourceBody797_575 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_574

def sourceBody797_576 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_20 sourceBody797_575

def sourceBody797_577 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_576

def sourceBody797_578 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_19 sourceBody797_577

def sourceBody797_579 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_578

def sourceBody797_580 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_18 sourceBody797_579

def sourceBody797_581 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_580

def sourceBody797_582 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_17 sourceBody797_581

def sourceBody797_583 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_582

def sourceBody797_584 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_16 sourceBody797_583

def sourceBody797_585 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_584

def sourceBody797_586 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_15 sourceBody797_585

def sourceBody797_587 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_586

def sourceBody797_588 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_14 sourceBody797_587

def sourceBody797_589 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_588

def sourceBody797_590 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_13 sourceBody797_589

def sourceBody797_591 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_590

def sourceBody797_592 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_12 sourceBody797_591

def sourceBody797_593 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_592

def sourceBody797_594 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_11 sourceBody797_593

def sourceBody797_595 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_594

def sourceBody797_596 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_595

def sourceBody797_597 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_5 sourceBody797_596

def sourceBody797_598 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_597

def sourceBody797_599 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody797_0 sourceBody797_598

def source797 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (797, 3, sourceBody797_599)
end InitECandidate.Proofs.WordStages
