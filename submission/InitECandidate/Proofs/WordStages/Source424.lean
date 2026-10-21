import InitECandidate.Proofs.WordStages.Source408
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody424_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody424_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 2)

def sourceBody424_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody424_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody424_0, 424, 2)) (some 403) ([34]) (some (34, sourceBody424_2, 424, 3))

def sourceBody424_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody424_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_3 sourceBody424_4

def sourceBody424_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_5 sourceBody424_0

def sourceBody424_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_1 sourceBody424_6

def sourceBody424_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 22)

def sourceBody424_9 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody424_0, 424, 4)) (some 391) ([34]) (some (34, sourceBody424_2, 424, 5))

def sourceBody424_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_9 sourceBody424_4

def sourceBody424_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_10 sourceBody424_0

def sourceBody424_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_8 sourceBody424_11

def sourceBody424_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody424_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody424_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody424_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody424_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 4)

def sourceBody424_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody424_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 8)

def sourceBody424_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody424_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody424_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([34, 14, 28, 20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody424_0, 424, 6)) (some 116) ([32, 16, 30, 24, 36, 12, 26, 18]) (some (32, sourceBody424_21, 424, 7))

def sourceBody424_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_22 sourceBody424_4

def sourceBody424_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_23 sourceBody424_0

def sourceBody424_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_20 sourceBody424_24

def sourceBody424_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_19 sourceBody424_25

def sourceBody424_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_18 sourceBody424_26

def sourceBody424_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_17 sourceBody424_27

def sourceBody424_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_16 sourceBody424_28

def sourceBody424_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_15 sourceBody424_29

def sourceBody424_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_14 sourceBody424_30

def sourceBody424_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_13 sourceBody424_31

def sourceBody424_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody424_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 34)

def sourceBody424_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 14)

def sourceBody424_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 28)

def sourceBody424_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 20)

def sourceBody424_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody424_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 32) 12

def sourceBody424_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_39 sourceBody424_0

def sourceBody424_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_38 sourceBody424_40

def sourceBody424_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 30)

def sourceBody424_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 8#64])
  12

def sourceBody424_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_43 sourceBody424_0

def sourceBody424_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_42 sourceBody424_44

def sourceBody424_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 24)

def sourceBody424_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 16#64])
  12

def sourceBody424_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_47 sourceBody424_0

def sourceBody424_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_46 sourceBody424_48

def sourceBody424_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 36)

def sourceBody424_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 24#64])
  12

def sourceBody424_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_51 sourceBody424_0

def sourceBody424_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_50 sourceBody424_52

def sourceBody424_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_53 sourceBody424_0

def sourceBody424_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_49 sourceBody424_54

def sourceBody424_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_45 sourceBody424_55

def sourceBody424_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_41 sourceBody424_56

def sourceBody424_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_37 sourceBody424_57

def sourceBody424_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_0 sourceBody424_58

def sourceBody424_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_36 sourceBody424_59

def sourceBody424_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_0 sourceBody424_60

def sourceBody424_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_35 sourceBody424_61

def sourceBody424_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_0 sourceBody424_62

def sourceBody424_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_34 sourceBody424_63

def sourceBody424_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_0 sourceBody424_64

def sourceBody424_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_33 sourceBody424_65

def sourceBody424_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_0 sourceBody424_66

def sourceBody424_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody424_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 22)

def sourceBody424_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody424_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody424_0, 424, 8)) (some 419) ([16, 30]) (some (16, sourceBody424_70, 424, 9))

def sourceBody424_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_71 sourceBody424_4

def sourceBody424_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_72 sourceBody424_0

def sourceBody424_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_69 sourceBody424_73

def sourceBody424_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_68 sourceBody424_74

def sourceBody424_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_0 sourceBody424_75

def sourceBody424_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_0 sourceBody424_76

def sourceBody424_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_67 sourceBody424_77

def sourceBody424_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody424_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [32]

def sourceBody424_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_80 sourceBody424_0

def sourceBody424_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_79 sourceBody424_81

def sourceBody424_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_78 sourceBody424_82

def sourceBody424_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_32 sourceBody424_83

def sourceBody424_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_0 sourceBody424_84

def sourceBody424_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_0 sourceBody424_85

def sourceBody424_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_0 sourceBody424_86

def sourceBody424_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_0 sourceBody424_87

def sourceBody424_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_0 sourceBody424_88

def sourceBody424_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_0 sourceBody424_89

def sourceBody424_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_0 sourceBody424_90

def sourceBody424_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_0 sourceBody424_91

def sourceBody424_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_12 sourceBody424_92

def sourceBody424_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_7 sourceBody424_93

def sourceBody424_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_0 sourceBody424_94

def sourceBody424_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody424_0 sourceBody424_95

def source424 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (424, 6, sourceBody424_96)
end InitECandidate.Proofs.WordStages
