import InitECandidate.Proofs.WordStages.Source359
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody375_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody375_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody375_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody375_0, 375, 2)) (some 69) ([]) (some (28, sourceBody375_1, 375, 3))

def sourceBody375_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody375_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_2 sourceBody375_3

def sourceBody375_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_4 sourceBody375_0

def sourceBody375_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody375_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody375_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody375_0, 375, 4)) (some 68) ([20]) (some (20, sourceBody375_7, 375, 5))

def sourceBody375_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_8 sourceBody375_3

def sourceBody375_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_9 sourceBody375_0

def sourceBody375_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_6 sourceBody375_10

def sourceBody375_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 2)

def sourceBody375_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody375_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody375_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody375_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody375_0, 375, 6)) (some 374) ([34, 10, 26]) (some (34, sourceBody375_15, 375, 7))

def sourceBody375_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_16 sourceBody375_3

def sourceBody375_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_17 sourceBody375_0

def sourceBody375_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_14 sourceBody375_18

def sourceBody375_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_13 sourceBody375_19

def sourceBody375_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_12 sourceBody375_20

def sourceBody375_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 28)

def sourceBody375_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 320#64]))

def sourceBody375_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 320#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody375_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 320#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody375_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 320#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody375_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 352#64]))

def sourceBody375_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 352#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody375_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 352#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody375_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 352#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody375_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 20)

def sourceBody375_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody375_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody375_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody375_0, 375, 8)) (some 231) ([10, 26, 18, 32, 14, 30, 22, 36, 8, 24, 16]) (some (10, sourceBody375_33, 375, 9))

def sourceBody375_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_34 sourceBody375_3

def sourceBody375_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_35 sourceBody375_0

def sourceBody375_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_32 sourceBody375_36

def sourceBody375_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_31 sourceBody375_37

def sourceBody375_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_30 sourceBody375_38

def sourceBody375_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_29 sourceBody375_39

def sourceBody375_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_28 sourceBody375_40

def sourceBody375_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_27 sourceBody375_41

def sourceBody375_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_26 sourceBody375_42

def sourceBody375_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_25 sourceBody375_43

def sourceBody375_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_24 sourceBody375_44

def sourceBody375_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_23 sourceBody375_45

def sourceBody375_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_22 sourceBody375_46

def sourceBody375_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 12)

def sourceBody375_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody375_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody375_0, 375, 10)) (some 70) ([26]) (some (26, sourceBody375_49, 375, 11))

def sourceBody375_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_50 sourceBody375_3

def sourceBody375_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_51 sourceBody375_0

def sourceBody375_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_48 sourceBody375_52

def sourceBody375_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_0 sourceBody375_53

def sourceBody375_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_0 sourceBody375_54

def sourceBody375_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 34)

def sourceBody375_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody375_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody375_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody375_60 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 26 (Flapjack.WordRegImm.reg 18) sourceBody375_58 sourceBody375_59

def sourceBody375_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_60 sourceBody375_3

def sourceBody375_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 26)

def sourceBody375_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 46#64)

def sourceBody375_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 10)

def sourceBody375_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_64 sourceBody375_0

def sourceBody375_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_65 sourceBody375_0

def sourceBody375_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_63 sourceBody375_66

def sourceBody375_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_0 sourceBody375_67

def sourceBody375_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody375_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_69 sourceBody375_33

def sourceBody375_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_68 sourceBody375_70

def sourceBody375_72 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody375_71 sourceBody375_0

def sourceBody375_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_72 sourceBody375_3

def sourceBody375_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_73 sourceBody375_0

def sourceBody375_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_62 sourceBody375_74

def sourceBody375_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_61 sourceBody375_75

def sourceBody375_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_57 sourceBody375_76

def sourceBody375_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_56 sourceBody375_77

def sourceBody375_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_55 sourceBody375_78

def sourceBody375_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody375_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody375_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_81 sourceBody375_0

def sourceBody375_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_80 sourceBody375_82

def sourceBody375_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_79 sourceBody375_83

def sourceBody375_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_47 sourceBody375_84

def sourceBody375_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_0 sourceBody375_85

def sourceBody375_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_0 sourceBody375_86

def sourceBody375_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_21 sourceBody375_87

def sourceBody375_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_0 sourceBody375_88

def sourceBody375_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_0 sourceBody375_89

def sourceBody375_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_11 sourceBody375_90

def sourceBody375_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_0 sourceBody375_91

def sourceBody375_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_0 sourceBody375_92

def sourceBody375_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_5 sourceBody375_93

def sourceBody375_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_0 sourceBody375_94

def sourceBody375_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody375_0 sourceBody375_95

def source375 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (375, 4, sourceBody375_96)
end InitECandidate.Proofs.WordStages
