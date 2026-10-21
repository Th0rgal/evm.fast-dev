import InitECandidate.Proofs.WordStages.Source708
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody724_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody724_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 2))

def sourceBody724_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody724_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody724_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody724_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody724_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody724_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 36)

def sourceBody724_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody724_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody724_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody724_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 42)

def sourceBody724_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody724_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody724_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([28, 18, 40, 14, 34, 24]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody724_0, 724, 2)) (some 713) ([44, 6, 26, 16, 38, 12]) (some (44, sourceBody724_13, 724, 3))

def sourceBody724_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody724_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_14 sourceBody724_15

def sourceBody724_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_16 sourceBody724_0

def sourceBody724_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_12 sourceBody724_17

def sourceBody724_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_11 sourceBody724_18

def sourceBody724_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_10 sourceBody724_19

def sourceBody724_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_9 sourceBody724_20

def sourceBody724_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_8 sourceBody724_21

def sourceBody724_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_7 sourceBody724_22

def sourceBody724_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody724_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody724_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody724_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody724_0, 724, 4)) (some 78) ([6, 26]) (some (6, sourceBody724_26, 724, 5))

def sourceBody724_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_27 sourceBody724_15

def sourceBody724_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_28 sourceBody724_0

def sourceBody724_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_25 sourceBody724_29

def sourceBody724_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_24 sourceBody724_30

def sourceBody724_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_31

def sourceBody724_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_32

def sourceBody724_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 28)

def sourceBody724_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 18)

def sourceBody724_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 40)

def sourceBody724_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 14)

def sourceBody724_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 34)

def sourceBody724_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 24)

def sourceBody724_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody724_41 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody724_0, 724, 6)) (some 722) ([6, 26, 16, 38, 12, 32, 22]) (some (6, sourceBody724_26, 724, 7))

def sourceBody724_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_41 sourceBody724_15

def sourceBody724_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_42 sourceBody724_0

def sourceBody724_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_40 sourceBody724_43

def sourceBody724_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_39 sourceBody724_44

def sourceBody724_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_38 sourceBody724_45

def sourceBody724_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_37 sourceBody724_46

def sourceBody724_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_36 sourceBody724_47

def sourceBody724_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_35 sourceBody724_48

def sourceBody724_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_34 sourceBody724_49

def sourceBody724_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_50

def sourceBody724_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_51

def sourceBody724_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_33 sourceBody724_52

def sourceBody724_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody724_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [44]

def sourceBody724_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_55 sourceBody724_0

def sourceBody724_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_54 sourceBody724_56

def sourceBody724_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_53 sourceBody724_57

def sourceBody724_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_23 sourceBody724_58

def sourceBody724_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_59

def sourceBody724_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_60

def sourceBody724_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_61

def sourceBody724_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_62

def sourceBody724_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_63

def sourceBody724_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_64

def sourceBody724_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_65

def sourceBody724_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_66

def sourceBody724_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_67

def sourceBody724_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_68

def sourceBody724_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_69

def sourceBody724_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_70

def sourceBody724_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_6 sourceBody724_71

def sourceBody724_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_72

def sourceBody724_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_5 sourceBody724_73

def sourceBody724_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_74

def sourceBody724_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_4 sourceBody724_75

def sourceBody724_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_76

def sourceBody724_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_3 sourceBody724_77

def sourceBody724_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_78

def sourceBody724_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_2 sourceBody724_79

def sourceBody724_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_80

def sourceBody724_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_1 sourceBody724_81

def sourceBody724_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody724_0 sourceBody724_82

def source724 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (724, 3, sourceBody724_83)
end InitECandidate.Proofs.WordStages
