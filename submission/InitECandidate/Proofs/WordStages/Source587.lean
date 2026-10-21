import InitECandidate.Proofs.WordStages.Source571
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody587_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody587_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody587_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody587_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 18]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody587_0, 587, 2)) (some 561) ([6]) (some (6, sourceBody587_2, 587, 3))

def sourceBody587_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody587_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_3 sourceBody587_4

def sourceBody587_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_5 sourceBody587_0

def sourceBody587_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_1 sourceBody587_6

def sourceBody587_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody587_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody587_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody587_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody587_0, 587, 4)) (some 464) ([16, 12]) (some (16, sourceBody587_10, 587, 5))

def sourceBody587_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_11 sourceBody587_4

def sourceBody587_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_12 sourceBody587_0

def sourceBody587_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_9 sourceBody587_13

def sourceBody587_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_8 sourceBody587_14

def sourceBody587_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody587_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody587_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody587_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody587_20 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.WordRegImm.reg 20) sourceBody587_18 sourceBody587_19

def sourceBody587_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_20 sourceBody587_4

def sourceBody587_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 12)

def sourceBody587_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody587_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody587_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16, 12, 20]

def sourceBody587_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_25 sourceBody587_0

def sourceBody587_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_17 sourceBody587_26

def sourceBody587_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_24 sourceBody587_27

def sourceBody587_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_23 sourceBody587_28

def sourceBody587_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody587_29 sourceBody587_0

def sourceBody587_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_30 sourceBody587_4

def sourceBody587_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_31 sourceBody587_0

def sourceBody587_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_22 sourceBody587_32

def sourceBody587_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_21 sourceBody587_33

def sourceBody587_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_17 sourceBody587_34

def sourceBody587_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_16 sourceBody587_35

def sourceBody587_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody587_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody587_39 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody587_0, 587, 6)) (some 68) ([12]) (some (12, sourceBody587_38, 587, 7))

def sourceBody587_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_39 sourceBody587_4

def sourceBody587_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_40 sourceBody587_0

def sourceBody587_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_37 sourceBody587_41

def sourceBody587_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody587_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody587_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody587_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody587_47 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody587_0, 587, 8)) (some 77) ([20, 4, 14]) (some (20, sourceBody587_46, 587, 9))

def sourceBody587_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_47 sourceBody587_4

def sourceBody587_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_48 sourceBody587_0

def sourceBody587_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_45 sourceBody587_49

def sourceBody587_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_44 sourceBody587_50

def sourceBody587_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_43 sourceBody587_51

def sourceBody587_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_0 sourceBody587_52

def sourceBody587_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_0 sourceBody587_53

def sourceBody587_55 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody587_0, 587, 10)) (some 489) ([20]) (some (20, sourceBody587_46, 587, 11))

def sourceBody587_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_55 sourceBody587_4

def sourceBody587_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_56 sourceBody587_0

def sourceBody587_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_43 sourceBody587_57

def sourceBody587_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody587_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody587_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody587_62 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.reg 14) sourceBody587_60 sourceBody587_61

def sourceBody587_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_62 sourceBody587_4

def sourceBody587_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody587_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody587_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 16)

def sourceBody587_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 100#64)

def sourceBody587_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20, 4, 14]

def sourceBody587_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_68 sourceBody587_0

def sourceBody587_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_67 sourceBody587_69

def sourceBody587_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_66 sourceBody587_70

def sourceBody587_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_65 sourceBody587_71

def sourceBody587_73 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody587_72 sourceBody587_0

def sourceBody587_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_73 sourceBody587_4

def sourceBody587_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_74 sourceBody587_0

def sourceBody587_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_64 sourceBody587_75

def sourceBody587_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_63 sourceBody587_76

def sourceBody587_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_59 sourceBody587_77

def sourceBody587_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_22 sourceBody587_78

def sourceBody587_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 3000#64)

def sourceBody587_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_80 sourceBody587_69

def sourceBody587_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_66 sourceBody587_81

def sourceBody587_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_65 sourceBody587_82

def sourceBody587_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_79 sourceBody587_83

def sourceBody587_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_58 sourceBody587_84

def sourceBody587_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_0 sourceBody587_85

def sourceBody587_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_0 sourceBody587_86

def sourceBody587_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_54 sourceBody587_87

def sourceBody587_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_42 sourceBody587_88

def sourceBody587_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_0 sourceBody587_89

def sourceBody587_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_0 sourceBody587_90

def sourceBody587_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_36 sourceBody587_91

def sourceBody587_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_15 sourceBody587_92

def sourceBody587_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_0 sourceBody587_93

def sourceBody587_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_0 sourceBody587_94

def sourceBody587_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_7 sourceBody587_95

def sourceBody587_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_0 sourceBody587_96

def sourceBody587_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_0 sourceBody587_97

def sourceBody587_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_0 sourceBody587_98

def sourceBody587_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody587_0 sourceBody587_99

def source587 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (587, 2, sourceBody587_100)
end InitECandidate.Proofs.WordStages
