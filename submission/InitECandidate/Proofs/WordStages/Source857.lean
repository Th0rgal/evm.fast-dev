import InitECandidate.Proofs.WordStages.Source841
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody857_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody857_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody857_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody857_0, 857, 2)) (some 383) ([]) (some (16, sourceBody857_1, 857, 3))

def sourceBody857_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody857_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_2 sourceBody857_3

def sourceBody857_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_4 sourceBody857_0

def sourceBody857_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_0 sourceBody857_5

def sourceBody857_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_0 sourceBody857_6

def sourceBody857_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody857_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody857_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 16]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody857_0, 857, 4)) (some 561) ([6]) (some (6, sourceBody857_9, 857, 5))

def sourceBody857_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_10 sourceBody857_3

def sourceBody857_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_11 sourceBody857_0

def sourceBody857_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_8 sourceBody857_12

def sourceBody857_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody857_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody857_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody857_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody857_18 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 10) sourceBody857_16 sourceBody857_17

def sourceBody857_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_18 sourceBody857_3

def sourceBody857_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody857_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 70#64)

def sourceBody857_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 6)

def sourceBody857_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_22 sourceBody857_0

def sourceBody857_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_23 sourceBody857_0

def sourceBody857_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_21 sourceBody857_24

def sourceBody857_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_0 sourceBody857_25

def sourceBody857_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody857_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_27 sourceBody857_9

def sourceBody857_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_26 sourceBody857_28

def sourceBody857_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody857_29 sourceBody857_0

def sourceBody857_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_30 sourceBody857_3

def sourceBody857_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_31 sourceBody857_0

def sourceBody857_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_20 sourceBody857_32

def sourceBody857_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_19 sourceBody857_33

def sourceBody857_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_15 sourceBody857_34

def sourceBody857_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_14 sourceBody857_35

def sourceBody857_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody857_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody857_39 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody857_0, 857, 6)) (some 68) ([14]) (some (14, sourceBody857_38, 857, 7))

def sourceBody857_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_39 sourceBody857_3

def sourceBody857_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_40 sourceBody857_0

def sourceBody857_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_37 sourceBody857_41

def sourceBody857_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody857_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody857_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody857_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody857_47 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody857_0, 857, 8)) (some 856) ([10, 18, 4]) (some (10, sourceBody857_46, 857, 9))

def sourceBody857_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_47 sourceBody857_3

def sourceBody857_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_48 sourceBody857_0

def sourceBody857_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_45 sourceBody857_49

def sourceBody857_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_44 sourceBody857_50

def sourceBody857_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_43 sourceBody857_51

def sourceBody857_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody857_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody857_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody857_56 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.reg 4) sourceBody857_54 sourceBody857_55

def sourceBody857_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_56 sourceBody857_3

def sourceBody857_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody857_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 71#64)

def sourceBody857_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 10)

def sourceBody857_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_60 sourceBody857_0

def sourceBody857_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_61 sourceBody857_0

def sourceBody857_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_59 sourceBody857_62

def sourceBody857_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_0 sourceBody857_63

def sourceBody857_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody857_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_65 sourceBody857_46

def sourceBody857_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_64 sourceBody857_66

def sourceBody857_68 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody857_67 sourceBody857_0

def sourceBody857_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_68 sourceBody857_3

def sourceBody857_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_69 sourceBody857_0

def sourceBody857_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_58 sourceBody857_70

def sourceBody857_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_57 sourceBody857_71

def sourceBody857_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_45 sourceBody857_72

def sourceBody857_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_53 sourceBody857_73

def sourceBody857_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody857_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody857_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_76 sourceBody857_0

def sourceBody857_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_75 sourceBody857_77

def sourceBody857_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_74 sourceBody857_78

def sourceBody857_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_52 sourceBody857_79

def sourceBody857_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_0 sourceBody857_80

def sourceBody857_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_0 sourceBody857_81

def sourceBody857_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_42 sourceBody857_82

def sourceBody857_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_0 sourceBody857_83

def sourceBody857_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_0 sourceBody857_84

def sourceBody857_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_36 sourceBody857_85

def sourceBody857_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_13 sourceBody857_86

def sourceBody857_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_0 sourceBody857_87

def sourceBody857_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_0 sourceBody857_88

def sourceBody857_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_0 sourceBody857_89

def sourceBody857_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_0 sourceBody857_90

def sourceBody857_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody857_7 sourceBody857_91

def source857 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (857, 2, sourceBody857_92)
end InitECandidate.Proofs.WordStages
