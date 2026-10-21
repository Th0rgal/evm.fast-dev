import InitECandidate.Proofs.WordStages.Source343
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody359_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody359_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody359_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody359_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody359_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody359_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody359_6 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody359_0, 359, 2)) (some 354) ([18, 6, 16, 12]) (some (18, sourceBody359_5, 359, 3))

def sourceBody359_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody359_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_6 sourceBody359_7

def sourceBody359_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_8 sourceBody359_0

def sourceBody359_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_4 sourceBody359_9

def sourceBody359_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_3 sourceBody359_10

def sourceBody359_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_2 sourceBody359_11

def sourceBody359_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_1 sourceBody359_12

def sourceBody359_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody359_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody359_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody359_0, 359, 4)) (some 181) ([6]) (some (6, sourceBody359_15, 359, 5))

def sourceBody359_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_16 sourceBody359_7

def sourceBody359_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_17 sourceBody359_0

def sourceBody359_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_14 sourceBody359_18

def sourceBody359_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody359_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody359_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody359_0, 359, 6)) (some 181) ([16]) (some (16, sourceBody359_21, 359, 7))

def sourceBody359_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_22 sourceBody359_7

def sourceBody359_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_23 sourceBody359_0

def sourceBody359_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_20 sourceBody359_24

def sourceBody359_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody359_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 56#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody359_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 56#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody359_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 56#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody359_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody359_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody359_0, 359, 8)) (some 354) ([12, 20, 4, 14]) (some (12, sourceBody359_30, 359, 9))

def sourceBody359_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_31 sourceBody359_7

def sourceBody359_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_32 sourceBody359_0

def sourceBody359_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_29 sourceBody359_33

def sourceBody359_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_28 sourceBody359_34

def sourceBody359_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_27 sourceBody359_35

def sourceBody359_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_26 sourceBody359_36

def sourceBody359_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody359_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 88#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody359_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 88#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody359_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 88#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody359_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody359_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody359_0, 359, 10)) (some 354) ([20, 4, 14, 10]) (some (20, sourceBody359_42, 359, 11))

def sourceBody359_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_43 sourceBody359_7

def sourceBody359_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_44 sourceBody359_0

def sourceBody359_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_41 sourceBody359_45

def sourceBody359_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_40 sourceBody359_46

def sourceBody359_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_39 sourceBody359_47

def sourceBody359_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_38 sourceBody359_48

def sourceBody359_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 21#64, Flapjack.WordLangExpHOL.var 18,
      Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.var 12])

def sourceBody359_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody359_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_51 sourceBody359_0

def sourceBody359_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_50 sourceBody359_52

def sourceBody359_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_49 sourceBody359_53

def sourceBody359_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_0 sourceBody359_54

def sourceBody359_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_0 sourceBody359_55

def sourceBody359_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_37 sourceBody359_56

def sourceBody359_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_0 sourceBody359_57

def sourceBody359_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_0 sourceBody359_58

def sourceBody359_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_25 sourceBody359_59

def sourceBody359_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_0 sourceBody359_60

def sourceBody359_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_0 sourceBody359_61

def sourceBody359_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_19 sourceBody359_62

def sourceBody359_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_0 sourceBody359_63

def sourceBody359_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_0 sourceBody359_64

def sourceBody359_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_13 sourceBody359_65

def sourceBody359_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_0 sourceBody359_66

def sourceBody359_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody359_0 sourceBody359_67

def source359 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (359, 2, sourceBody359_68)
end InitECandidate.Proofs.WordStages
