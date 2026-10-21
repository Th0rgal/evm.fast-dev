import InitECandidate.Proofs.WordStages.Source773
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody789_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody789_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody789_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([66]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody789_0, 789, 2)) (some 69) ([]) (some (32, sourceBody789_1, 789, 3))

def sourceBody789_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody789_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_2 sourceBody789_3

def sourceBody789_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_4 sourceBody789_0

def sourceBody789_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody789_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 52

def sourceBody789_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody789_0, 789, 4)) (some 68) ([52]) (some (52, sourceBody789_7, 789, 5))

def sourceBody789_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_8 sourceBody789_3

def sourceBody789_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_9 sourceBody789_0

def sourceBody789_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_6 sourceBody789_10

def sourceBody789_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody789_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody789_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody789_0, 789, 6)) (some 68) ([42]) (some (42, sourceBody789_13, 789, 7))

def sourceBody789_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_14 sourceBody789_3

def sourceBody789_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_15 sourceBody789_0

def sourceBody789_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_12 sourceBody789_16

def sourceBody789_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 32)

def sourceBody789_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 28)

def sourceBody789_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 60

def sourceBody789_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody789_0, 789, 8)) (some 725) ([60, 36]) (some (60, sourceBody789_20, 789, 9))

def sourceBody789_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_21 sourceBody789_3

def sourceBody789_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_22 sourceBody789_0

def sourceBody789_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_19 sourceBody789_23

def sourceBody789_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_18 sourceBody789_24

def sourceBody789_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_25

def sourceBody789_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_26

def sourceBody789_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody789_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody789_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody789_0, 789, 10)) (some 725) ([60, 36]) (some (60, sourceBody789_20, 789, 11))

def sourceBody789_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_30 sourceBody789_3

def sourceBody789_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_31 sourceBody789_0

def sourceBody789_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_29 sourceBody789_32

def sourceBody789_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_28 sourceBody789_33

def sourceBody789_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_34

def sourceBody789_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_35

def sourceBody789_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_27 sourceBody789_36

def sourceBody789_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody789_39 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody789_0, 789, 12)) (some 727) ([60]) (some (60, sourceBody789_20, 789, 13))

def sourceBody789_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_39 sourceBody789_3

def sourceBody789_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_40 sourceBody789_0

def sourceBody789_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_38 sourceBody789_41

def sourceBody789_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_42

def sourceBody789_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_43

def sourceBody789_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_37 sourceBody789_44

def sourceBody789_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 2)

def sourceBody789_47 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody789_0, 789, 14)) (some 752) ([60]) (some (60, sourceBody789_20, 789, 15))

def sourceBody789_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_47 sourceBody789_3

def sourceBody789_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_48 sourceBody789_0

def sourceBody789_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_46 sourceBody789_49

def sourceBody789_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_50

def sourceBody789_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_51

def sourceBody789_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_45 sourceBody789_52

def sourceBody789_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 392#64]),
        Flapjack.WordLangExpHOL.const 1376#64]))

def sourceBody789_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.const 63#64)

def sourceBody789_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody789_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 60)

def sourceBody789_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody789_59 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 56 (Flapjack.WordRegImm.reg 46) sourceBody789_58 sourceBody789_56

def sourceBody789_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_59 sourceBody789_3

def sourceBody789_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 56)

def sourceBody789_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 60, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody789_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 36)

def sourceBody789_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_63 sourceBody789_0

def sourceBody789_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_64 sourceBody789_0

def sourceBody789_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_62 sourceBody789_65

def sourceBody789_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_66

def sourceBody789_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 2)

def sourceBody789_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 2)

def sourceBody789_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 2)

def sourceBody789_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 56

def sourceBody789_72 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody789_0, 789, 16)) (some 754) ([56, 46, 64]) (some (56, sourceBody789_71, 789, 17))

def sourceBody789_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_72 sourceBody789_3

def sourceBody789_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_73 sourceBody789_0

def sourceBody789_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_70 sourceBody789_74

def sourceBody789_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_69 sourceBody789_75

def sourceBody789_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_68 sourceBody789_76

def sourceBody789_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_77

def sourceBody789_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_78

def sourceBody789_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_67 sourceBody789_79

def sourceBody789_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 32)

def sourceBody789_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 52)

def sourceBody789_83 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody789_0, 789, 18)) (some 786) ([56, 46]) (some (56, sourceBody789_71, 789, 19))

def sourceBody789_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_83 sourceBody789_3

def sourceBody789_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_84 sourceBody789_0

def sourceBody789_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_82 sourceBody789_85

def sourceBody789_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_81 sourceBody789_86

def sourceBody789_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_87

def sourceBody789_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_88

def sourceBody789_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_80 sourceBody789_89

def sourceBody789_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 4)

def sourceBody789_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 6)

def sourceBody789_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 8)

def sourceBody789_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 10)

def sourceBody789_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 12)

def sourceBody789_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 14)

def sourceBody789_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 16)

def sourceBody789_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 18)

def sourceBody789_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 20)

def sourceBody789_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 22)

def sourceBody789_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 24)

def sourceBody789_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 26)

def sourceBody789_103 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody789_0, 789, 20)) (some 788) ([56, 46, 64, 34, 54, 44, 62, 38, 58, 48, 68, 30, 50, 40]) (some (56, sourceBody789_71, 789, 21))

def sourceBody789_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_103 sourceBody789_3

def sourceBody789_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_104 sourceBody789_0

def sourceBody789_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_102 sourceBody789_105

def sourceBody789_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_101 sourceBody789_106

def sourceBody789_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_100 sourceBody789_107

def sourceBody789_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_99 sourceBody789_108

def sourceBody789_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_98 sourceBody789_109

def sourceBody789_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_97 sourceBody789_110

def sourceBody789_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_96 sourceBody789_111

def sourceBody789_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_95 sourceBody789_112

def sourceBody789_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_94 sourceBody789_113

def sourceBody789_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_93 sourceBody789_114

def sourceBody789_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_92 sourceBody789_115

def sourceBody789_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_91 sourceBody789_116

def sourceBody789_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_82 sourceBody789_117

def sourceBody789_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_68 sourceBody789_118

def sourceBody789_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_119

def sourceBody789_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_120

def sourceBody789_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_90 sourceBody789_121

def sourceBody789_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 42) (Flapjack.WordLangExpHOL.var 60),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody789_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody789_125 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 56 (Flapjack.WordRegImm.reg 46) sourceBody789_58 sourceBody789_56

def sourceBody789_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_125 sourceBody789_3

def sourceBody789_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 28)

def sourceBody789_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody789_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 52)

def sourceBody789_130 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody789_0, 789, 22)) (some 787) ([56, 46, 64, 34]) (some (56, sourceBody789_71, 789, 23))

def sourceBody789_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_130 sourceBody789_3

def sourceBody789_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_131 sourceBody789_0

def sourceBody789_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_129 sourceBody789_132

def sourceBody789_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_128 sourceBody789_133

def sourceBody789_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_127 sourceBody789_134

def sourceBody789_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_81 sourceBody789_135

def sourceBody789_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_136

def sourceBody789_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_137

def sourceBody789_139 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody789_0, 789, 24)) (some 788) ([56, 46, 64, 34, 54, 44, 62, 38, 58, 48, 68, 30, 50, 40]) (some (56, sourceBody789_71, 789, 25))

def sourceBody789_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_139 sourceBody789_3

def sourceBody789_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_140 sourceBody789_0

def sourceBody789_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_102 sourceBody789_141

def sourceBody789_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_101 sourceBody789_142

def sourceBody789_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_100 sourceBody789_143

def sourceBody789_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_99 sourceBody789_144

def sourceBody789_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_98 sourceBody789_145

def sourceBody789_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_97 sourceBody789_146

def sourceBody789_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_96 sourceBody789_147

def sourceBody789_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_95 sourceBody789_148

def sourceBody789_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_94 sourceBody789_149

def sourceBody789_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_93 sourceBody789_150

def sourceBody789_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_92 sourceBody789_151

def sourceBody789_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_91 sourceBody789_152

def sourceBody789_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_82 sourceBody789_153

def sourceBody789_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_68 sourceBody789_154

def sourceBody789_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_155

def sourceBody789_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_156

def sourceBody789_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_138 sourceBody789_157

def sourceBody789_159 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 64 (Flapjack.WordRegImm.imm 0#64) sourceBody789_158 sourceBody789_0

def sourceBody789_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_159 sourceBody789_3

def sourceBody789_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_160 sourceBody789_0

def sourceBody789_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_61 sourceBody789_161

def sourceBody789_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_126 sourceBody789_162

def sourceBody789_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_124 sourceBody789_163

def sourceBody789_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_123 sourceBody789_164

def sourceBody789_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_122 sourceBody789_165

def sourceBody789_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody789_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_166 sourceBody789_167

def sourceBody789_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody789_170 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 64 (Flapjack.WordRegImm.imm 0#64) sourceBody789_168 sourceBody789_169

def sourceBody789_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_170 sourceBody789_3

def sourceBody789_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_171 sourceBody789_0

def sourceBody789_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_61 sourceBody789_172

def sourceBody789_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_60 sourceBody789_173

def sourceBody789_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_57 sourceBody789_174

def sourceBody789_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_56 sourceBody789_175

def sourceBody789_177 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody789_176 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln)
  PUnit.unit Flapjack.Spt.ln)

def sourceBody789_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_177 sourceBody789_3

def sourceBody789_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_3 sourceBody789_178

def sourceBody789_180 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody789_0, 789, 26)) (some 756) ([56, 46]) (some (56, sourceBody789_71, 789, 27))

def sourceBody789_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_180 sourceBody789_3

def sourceBody789_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_181 sourceBody789_0

def sourceBody789_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_69 sourceBody789_182

def sourceBody789_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_68 sourceBody789_183

def sourceBody789_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_184

def sourceBody789_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_185

def sourceBody789_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_179 sourceBody789_186

def sourceBody789_188 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 66)

def sourceBody789_189 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody789_0, 789, 28)) (some 70) ([56]) (some (56, sourceBody789_71, 789, 29))

def sourceBody789_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_189 sourceBody789_3

def sourceBody789_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_190 sourceBody789_0

def sourceBody789_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_188 sourceBody789_191

def sourceBody789_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_192

def sourceBody789_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_193

def sourceBody789_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_187 sourceBody789_194

def sourceBody789_196 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody789_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [36]

def sourceBody789_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_197 sourceBody789_0

def sourceBody789_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_196 sourceBody789_198

def sourceBody789_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_195 sourceBody789_199

def sourceBody789_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_55 sourceBody789_200

def sourceBody789_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_201

def sourceBody789_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_54 sourceBody789_202

def sourceBody789_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_203

def sourceBody789_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_53 sourceBody789_204

def sourceBody789_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_17 sourceBody789_205

def sourceBody789_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_206

def sourceBody789_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_207

def sourceBody789_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_11 sourceBody789_208

def sourceBody789_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_209

def sourceBody789_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_210

def sourceBody789_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_5 sourceBody789_211

def sourceBody789_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_212

def sourceBody789_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody789_0 sourceBody789_213

def source789 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (789, 15, sourceBody789_214)
end InitECandidate.Proofs.WordStages
