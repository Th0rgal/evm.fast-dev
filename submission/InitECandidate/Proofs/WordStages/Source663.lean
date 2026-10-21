import InitECandidate.Proofs.WordStages.Source647
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody663_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody663_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 11#64)

def sourceBody663_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody663_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody663_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 18)

def sourceBody663_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody663_6 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 40) sourceBody663_5 sourceBody663_3

def sourceBody663_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_6 sourceBody663_2

def sourceBody663_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody663_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody663_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 48)

def sourceBody663_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_10 sourceBody663_0

def sourceBody663_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_11 sourceBody663_0

def sourceBody663_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_9 sourceBody663_12

def sourceBody663_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_13

def sourceBody663_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 12#64])
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody663_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 12#64])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody663_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 12#64])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody663_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 12#64])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody663_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 48)

def sourceBody663_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody663_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 40)

def sourceBody663_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 26)

def sourceBody663_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.const 82#64)

def sourceBody663_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 52

def sourceBody663_25 : WordLangProgHOL (BitVec 64) :=
.call (some (([56, 6, 36, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody663_0, 663, 2)) (some 661) ([52, 14, 44, 30, 60]) (some (52, sourceBody663_24, 663, 3))

def sourceBody663_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_25 sourceBody663_2

def sourceBody663_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_26 sourceBody663_0

def sourceBody663_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_23 sourceBody663_27

def sourceBody663_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_22 sourceBody663_28

def sourceBody663_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_21 sourceBody663_29

def sourceBody663_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_20 sourceBody663_30

def sourceBody663_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_19 sourceBody663_31

def sourceBody663_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 48)

def sourceBody663_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody663_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 40)

def sourceBody663_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 26)

def sourceBody663_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 18#64)

def sourceBody663_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 60

def sourceBody663_39 : WordLangProgHOL (BitVec 64) :=
.call (some (([52, 14, 44, 30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody663_0, 663, 4)) (some 661) ([60, 4, 34, 20, 50]) (some (60, sourceBody663_38, 663, 5))

def sourceBody663_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_39 sourceBody663_2

def sourceBody663_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_40 sourceBody663_0

def sourceBody663_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_37 sourceBody663_41

def sourceBody663_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_36 sourceBody663_42

def sourceBody663_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_35 sourceBody663_43

def sourceBody663_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_34 sourceBody663_44

def sourceBody663_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_33 sourceBody663_45

def sourceBody663_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 18)
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody663_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 18)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody663_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 18)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody663_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 18)
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody663_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 60)

def sourceBody663_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody663_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 34)

def sourceBody663_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 20)

def sourceBody663_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 56)

def sourceBody663_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody663_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 36)

def sourceBody663_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 22)

def sourceBody663_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 50

def sourceBody663_60 : WordLangProgHOL (BitVec 64) :=
.call (some (([60, 4, 34, 20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody663_0, 663, 6)) (some 655) ([50, 12, 42, 28, 58, 8, 38, 24]) (some (50, sourceBody663_59, 663, 7))

def sourceBody663_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_60 sourceBody663_2

def sourceBody663_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_61 sourceBody663_0

def sourceBody663_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_58 sourceBody663_62

def sourceBody663_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_57 sourceBody663_63

def sourceBody663_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_56 sourceBody663_64

def sourceBody663_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_55 sourceBody663_65

def sourceBody663_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_54 sourceBody663_66

def sourceBody663_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_53 sourceBody663_67

def sourceBody663_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_52 sourceBody663_68

def sourceBody663_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_51 sourceBody663_69

def sourceBody663_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 18)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody663_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 60)

def sourceBody663_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 4)

def sourceBody663_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 34)

def sourceBody663_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 20)

def sourceBody663_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody663_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 50) 8

def sourceBody663_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_77 sourceBody663_0

def sourceBody663_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_76 sourceBody663_78

def sourceBody663_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 42)

def sourceBody663_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 8#64]) 8

def sourceBody663_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_81 sourceBody663_0

def sourceBody663_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_80 sourceBody663_82

def sourceBody663_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody663_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 16#64])
  8

def sourceBody663_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_85 sourceBody663_0

def sourceBody663_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_84 sourceBody663_86

def sourceBody663_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 58)

def sourceBody663_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 24#64])
  8

def sourceBody663_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_89 sourceBody663_0

def sourceBody663_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_88 sourceBody663_90

def sourceBody663_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_91 sourceBody663_0

def sourceBody663_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_87 sourceBody663_92

def sourceBody663_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_83 sourceBody663_93

def sourceBody663_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_79 sourceBody663_94

def sourceBody663_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_75 sourceBody663_95

def sourceBody663_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_96

def sourceBody663_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_74 sourceBody663_97

def sourceBody663_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_98

def sourceBody663_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_73 sourceBody663_99

def sourceBody663_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_100

def sourceBody663_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_72 sourceBody663_101

def sourceBody663_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_102

def sourceBody663_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_71 sourceBody663_103

def sourceBody663_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_104

def sourceBody663_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_70 sourceBody663_105

def sourceBody663_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 6#64])
          (Flapjack.WordLangExpHOL.const 5#64)]))

def sourceBody663_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 6#64])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody663_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 6#64])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody663_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 6#64])
              (Flapjack.WordLangExpHOL.const 5#64)],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody663_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 50)

def sourceBody663_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 42)

def sourceBody663_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 28)

def sourceBody663_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 52)

def sourceBody663_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody663_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 44)

def sourceBody663_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 30)

def sourceBody663_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 58

def sourceBody663_119 : WordLangProgHOL (BitVec 64) :=
.call (some (([50, 12, 42, 28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody663_0, 663, 8)) (some 654) ([58, 8, 38, 24, 54, 16, 46, 32]) (some (58, sourceBody663_118, 663, 9))

def sourceBody663_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_119 sourceBody663_2

def sourceBody663_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_120 sourceBody663_0

def sourceBody663_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_117 sourceBody663_121

def sourceBody663_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_116 sourceBody663_122

def sourceBody663_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_115 sourceBody663_123

def sourceBody663_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_114 sourceBody663_124

def sourceBody663_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_113 sourceBody663_125

def sourceBody663_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_112 sourceBody663_126

def sourceBody663_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_76 sourceBody663_127

def sourceBody663_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_111 sourceBody663_128

def sourceBody663_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 6#64])
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody663_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 50)

def sourceBody663_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 12)

def sourceBody663_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 42)

def sourceBody663_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 28)

def sourceBody663_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody663_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 58) 16

def sourceBody663_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_136 sourceBody663_0

def sourceBody663_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_135 sourceBody663_137

def sourceBody663_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 38)

def sourceBody663_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 58, Flapjack.WordLangExpHOL.const 8#64])
  16

def sourceBody663_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_140 sourceBody663_0

def sourceBody663_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_139 sourceBody663_141

def sourceBody663_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody663_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 58, Flapjack.WordLangExpHOL.const 16#64])
  16

def sourceBody663_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_144 sourceBody663_0

def sourceBody663_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_143 sourceBody663_145

def sourceBody663_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 54)

def sourceBody663_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 58, Flapjack.WordLangExpHOL.const 24#64])
  16

def sourceBody663_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_148 sourceBody663_0

def sourceBody663_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_147 sourceBody663_149

def sourceBody663_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_150 sourceBody663_0

def sourceBody663_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_146 sourceBody663_151

def sourceBody663_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_142 sourceBody663_152

def sourceBody663_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_138 sourceBody663_153

def sourceBody663_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_134 sourceBody663_154

def sourceBody663_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_155

def sourceBody663_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_133 sourceBody663_156

def sourceBody663_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_157

def sourceBody663_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_132 sourceBody663_158

def sourceBody663_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_159

def sourceBody663_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_131 sourceBody663_160

def sourceBody663_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_161

def sourceBody663_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_130 sourceBody663_162

def sourceBody663_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_163

def sourceBody663_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_129 sourceBody663_164

def sourceBody663_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_110 sourceBody663_165

def sourceBody663_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_166

def sourceBody663_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_109 sourceBody663_167

def sourceBody663_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_168

def sourceBody663_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_108 sourceBody663_169

def sourceBody663_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_170

def sourceBody663_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_107 sourceBody663_171

def sourceBody663_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_172

def sourceBody663_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_106 sourceBody663_173

def sourceBody663_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_50 sourceBody663_174

def sourceBody663_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_175

def sourceBody663_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_49 sourceBody663_176

def sourceBody663_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_177

def sourceBody663_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_48 sourceBody663_178

def sourceBody663_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_179

def sourceBody663_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_47 sourceBody663_180

def sourceBody663_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_181

def sourceBody663_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_46 sourceBody663_182

def sourceBody663_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_183

def sourceBody663_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_184

def sourceBody663_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_185

def sourceBody663_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_186

def sourceBody663_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_187

def sourceBody663_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_188

def sourceBody663_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_189

def sourceBody663_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_190

def sourceBody663_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_32 sourceBody663_191

def sourceBody663_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_192

def sourceBody663_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_193

def sourceBody663_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_194

def sourceBody663_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_195

def sourceBody663_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_196

def sourceBody663_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_197

def sourceBody663_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_198

def sourceBody663_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_199

def sourceBody663_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_18 sourceBody663_200

def sourceBody663_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_201

def sourceBody663_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_17 sourceBody663_202

def sourceBody663_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_203

def sourceBody663_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_16 sourceBody663_204

def sourceBody663_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_205

def sourceBody663_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_15 sourceBody663_206

def sourceBody663_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_207

def sourceBody663_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_14 sourceBody663_208

def sourceBody663_210 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody663_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_209 sourceBody663_210

def sourceBody663_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody663_213 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody663_211 sourceBody663_212

def sourceBody663_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_213 sourceBody663_2

def sourceBody663_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_214 sourceBody663_0

def sourceBody663_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_8 sourceBody663_215

def sourceBody663_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_7 sourceBody663_216

def sourceBody663_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_4 sourceBody663_217

def sourceBody663_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_3 sourceBody663_218

def sourceBody663_220 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln)
  PUnit.unit Flapjack.Spt.ln) sourceBody663_219 (Flapjack.Spt.ls PUnit.unit)

def sourceBody663_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_220 sourceBody663_2

def sourceBody663_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_2 sourceBody663_221

def sourceBody663_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody663_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [48]

def sourceBody663_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_224 sourceBody663_0

def sourceBody663_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_223 sourceBody663_225

def sourceBody663_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_222 sourceBody663_226

def sourceBody663_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_1 sourceBody663_227

def sourceBody663_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody663_0 sourceBody663_228

def source663 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (663, 2, sourceBody663_229)
end InitECandidate.Proofs.WordStages
