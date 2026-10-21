import InitECandidate.Proofs.WordStages.Source300
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody316_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody316_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody316_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody316_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 6)

def sourceBody316_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody316_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([22, 34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody316_0, 316, 2)) (some 306) ([14, 28, 20]) (some (14, sourceBody316_4, 316, 3))

def sourceBody316_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody316_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_5 sourceBody316_6

def sourceBody316_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_7 sourceBody316_0

def sourceBody316_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_3 sourceBody316_8

def sourceBody316_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_2 sourceBody316_9

def sourceBody316_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_1 sourceBody316_10

def sourceBody316_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody316_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody316_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody316_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody316_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody316_17 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 20 (Flapjack.WordRegImm.reg 32) sourceBody316_15 sourceBody316_16

def sourceBody316_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_17 sourceBody316_6

def sourceBody316_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 10)

def sourceBody316_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody316_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody316_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody316_23 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 30 (Flapjack.WordRegImm.reg 24) sourceBody316_21 sourceBody316_22

def sourceBody316_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_23 sourceBody316_6

def sourceBody316_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody316_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.var 30])

def sourceBody316_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody316_28 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 26) sourceBody316_27 sourceBody316_25

def sourceBody316_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_28 sourceBody316_6

def sourceBody316_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody316_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 14)

def sourceBody316_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 22)

def sourceBody316_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 34)

def sourceBody316_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody316_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody316_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody316_0, 316, 4)) (some 315) ([28, 20, 32, 16]) (some (28, sourceBody316_35, 316, 5))

def sourceBody316_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_36 sourceBody316_6

def sourceBody316_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_37 sourceBody316_0

def sourceBody316_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_34 sourceBody316_38

def sourceBody316_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_33 sourceBody316_39

def sourceBody316_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_32 sourceBody316_40

def sourceBody316_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_31 sourceBody316_41

def sourceBody316_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 8)

def sourceBody316_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody316_45 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody316_0, 316, 6)) (some 311) ([28, 20, 32, 16, 30, 24]) (some (28, sourceBody316_35, 316, 7))

def sourceBody316_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_45 sourceBody316_6

def sourceBody316_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_46 sourceBody316_0

def sourceBody316_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_44 sourceBody316_47

def sourceBody316_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_43 sourceBody316_48

def sourceBody316_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_34 sourceBody316_49

def sourceBody316_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_33 sourceBody316_50

def sourceBody316_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_32 sourceBody316_51

def sourceBody316_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_31 sourceBody316_52

def sourceBody316_54 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody316_42 sourceBody316_53

def sourceBody316_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_54 sourceBody316_6

def sourceBody316_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_55 sourceBody316_0

def sourceBody316_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_30 sourceBody316_56

def sourceBody316_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_29 sourceBody316_57

def sourceBody316_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_26 sourceBody316_58

def sourceBody316_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_25 sourceBody316_59

def sourceBody316_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_24 sourceBody316_60

def sourceBody316_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_20 sourceBody316_61

def sourceBody316_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_19 sourceBody316_62

def sourceBody316_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_18 sourceBody316_63

def sourceBody316_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_14 sourceBody316_64

def sourceBody316_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_13 sourceBody316_65

def sourceBody316_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody316_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody316_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 20)

def sourceBody316_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 28) 32

def sourceBody316_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_70 sourceBody316_0

def sourceBody316_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_69 sourceBody316_71

def sourceBody316_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_72 sourceBody316_0

def sourceBody316_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_68 sourceBody316_73

def sourceBody316_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_0 sourceBody316_74

def sourceBody316_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_67 sourceBody316_75

def sourceBody316_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_0 sourceBody316_76

def sourceBody316_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_66 sourceBody316_77

def sourceBody316_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody316_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [28]

def sourceBody316_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_80 sourceBody316_0

def sourceBody316_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_79 sourceBody316_81

def sourceBody316_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_78 sourceBody316_82

def sourceBody316_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_12 sourceBody316_83

def sourceBody316_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_0 sourceBody316_84

def sourceBody316_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_11 sourceBody316_85

def sourceBody316_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_0 sourceBody316_86

def sourceBody316_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_0 sourceBody316_87

def sourceBody316_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_0 sourceBody316_88

def sourceBody316_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody316_0 sourceBody316_89

def source316 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (316, 6, sourceBody316_90)
end InitECandidate.Proofs.WordStages
