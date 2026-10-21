import InitECandidate.Proofs.WordStages.Source667
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody683_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody683_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody683_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1152#64)

def sourceBody683_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody683_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody683_0, 683, 2)) (some 78) ([8, 12]) (some (8, sourceBody683_3, 683, 3))

def sourceBody683_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody683_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_4 sourceBody683_5

def sourceBody683_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_6 sourceBody683_0

def sourceBody683_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_2 sourceBody683_7

def sourceBody683_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_1 sourceBody683_8

def sourceBody683_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_0 sourceBody683_9

def sourceBody683_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_0 sourceBody683_10

def sourceBody683_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody683_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 4))

def sourceBody683_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody683_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody683_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody683_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody683_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 14) 6

def sourceBody683_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_18 sourceBody683_0

def sourceBody683_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_17 sourceBody683_19

def sourceBody683_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody683_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 8#64]) 6

def sourceBody683_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_22 sourceBody683_0

def sourceBody683_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_21 sourceBody683_23

def sourceBody683_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody683_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 16#64])
  6

def sourceBody683_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_26 sourceBody683_0

def sourceBody683_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_25 sourceBody683_27

def sourceBody683_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody683_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 24#64])
  6

def sourceBody683_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_30 sourceBody683_0

def sourceBody683_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_29 sourceBody683_31

def sourceBody683_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_32 sourceBody683_0

def sourceBody683_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_28 sourceBody683_33

def sourceBody683_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_24 sourceBody683_34

def sourceBody683_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_20 sourceBody683_35

def sourceBody683_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_16 sourceBody683_36

def sourceBody683_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_0 sourceBody683_37

def sourceBody683_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_15 sourceBody683_38

def sourceBody683_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_0 sourceBody683_39

def sourceBody683_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_14 sourceBody683_40

def sourceBody683_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_0 sourceBody683_41

def sourceBody683_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_13 sourceBody683_42

def sourceBody683_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_0 sourceBody683_43

def sourceBody683_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_12 sourceBody683_44

def sourceBody683_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_0 sourceBody683_45

def sourceBody683_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_11 sourceBody683_46

def sourceBody683_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody683_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody683_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 32#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody683_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 32#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody683_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 32#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody683_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_52 sourceBody683_36

def sourceBody683_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_0 sourceBody683_53

def sourceBody683_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_51 sourceBody683_54

def sourceBody683_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_0 sourceBody683_55

def sourceBody683_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_50 sourceBody683_56

def sourceBody683_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_0 sourceBody683_57

def sourceBody683_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_49 sourceBody683_58

def sourceBody683_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_0 sourceBody683_59

def sourceBody683_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_48 sourceBody683_60

def sourceBody683_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_0 sourceBody683_61

def sourceBody683_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_47 sourceBody683_62

def sourceBody683_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 768#64])

def sourceBody683_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody683_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 64#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody683_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 64#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody683_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 64#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody683_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_68 sourceBody683_36

def sourceBody683_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_0 sourceBody683_69

def sourceBody683_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_67 sourceBody683_70

def sourceBody683_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_0 sourceBody683_71

def sourceBody683_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_66 sourceBody683_72

def sourceBody683_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_0 sourceBody683_73

def sourceBody683_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_65 sourceBody683_74

def sourceBody683_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_0 sourceBody683_75

def sourceBody683_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_64 sourceBody683_76

def sourceBody683_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_0 sourceBody683_77

def sourceBody683_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_63 sourceBody683_78

def sourceBody683_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody683_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody683_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_81 sourceBody683_0

def sourceBody683_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_80 sourceBody683_82

def sourceBody683_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody683_79 sourceBody683_83

def source683 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (683, 3, sourceBody683_84)
end InitECandidate.Proofs.WordStages
