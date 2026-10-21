import InitECandidate.Proofs.WordStages.Source420
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody436_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody436_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody436_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody436_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody436_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody436_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 16)

def sourceBody436_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody436_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody436_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody436_9 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 8 (Flapjack.WordRegImm.reg 18) sourceBody436_7 sourceBody436_8

def sourceBody436_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_9 sourceBody436_4

def sourceBody436_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody436_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 16)

def sourceBody436_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody436_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 18 18 26 8))

def sourceBody436_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.var 18]))

def sourceBody436_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody436_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody436_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody436_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 12) sourceBody436_17 sourceBody436_18

def sourceBody436_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_19 sourceBody436_4

def sourceBody436_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 24)

def sourceBody436_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.var 18])

def sourceBody436_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody436_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_23 sourceBody436_0

def sourceBody436_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_22 sourceBody436_24

def sourceBody436_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_14 sourceBody436_25

def sourceBody436_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_13 sourceBody436_26

def sourceBody436_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_12 sourceBody436_27

def sourceBody436_29 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody436_28 sourceBody436_0

def sourceBody436_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_29 sourceBody436_4

def sourceBody436_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_30 sourceBody436_0

def sourceBody436_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_21 sourceBody436_31

def sourceBody436_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_20 sourceBody436_32

def sourceBody436_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_16 sourceBody436_33

def sourceBody436_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_15 sourceBody436_34

def sourceBody436_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_14 sourceBody436_35

def sourceBody436_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_13 sourceBody436_36

def sourceBody436_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_12 sourceBody436_37

def sourceBody436_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody436_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 26)

def sourceBody436_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_40 sourceBody436_0

def sourceBody436_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_41 sourceBody436_0

def sourceBody436_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_39 sourceBody436_42

def sourceBody436_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_0 sourceBody436_43

def sourceBody436_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_38 sourceBody436_44

def sourceBody436_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody436_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_45 sourceBody436_46

def sourceBody436_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody436_49 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody436_47 sourceBody436_48

def sourceBody436_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_49 sourceBody436_4

def sourceBody436_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_50 sourceBody436_0

def sourceBody436_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_11 sourceBody436_51

def sourceBody436_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_10 sourceBody436_52

def sourceBody436_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_6 sourceBody436_53

def sourceBody436_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_5 sourceBody436_54

def sourceBody436_56 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody436_55 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  Flapjack.Spt.ln)

def sourceBody436_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_56 sourceBody436_4

def sourceBody436_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_4 sourceBody436_57

def sourceBody436_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody436_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody436_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody436_62 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody436_0, 436, 2)) (some 433) ([8, 18]) (some (8, sourceBody436_61, 436, 3))

def sourceBody436_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_62 sourceBody436_4

def sourceBody436_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_63 sourceBody436_0

def sourceBody436_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_60 sourceBody436_64

def sourceBody436_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_59 sourceBody436_65

def sourceBody436_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 26)

def sourceBody436_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody436_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody436_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 14

def sourceBody436_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_70 sourceBody436_0

def sourceBody436_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_69 sourceBody436_71

def sourceBody436_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_72 sourceBody436_0

def sourceBody436_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_68 sourceBody436_73

def sourceBody436_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_0 sourceBody436_74

def sourceBody436_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_67 sourceBody436_75

def sourceBody436_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_0 sourceBody436_76

def sourceBody436_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody436_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_78 sourceBody436_0

def sourceBody436_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_67 sourceBody436_79

def sourceBody436_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_77 sourceBody436_80

def sourceBody436_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_66 sourceBody436_81

def sourceBody436_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_0 sourceBody436_82

def sourceBody436_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_0 sourceBody436_83

def sourceBody436_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_58 sourceBody436_84

def sourceBody436_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_3 sourceBody436_85

def sourceBody436_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_0 sourceBody436_86

def sourceBody436_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_2 sourceBody436_87

def sourceBody436_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_0 sourceBody436_88

def sourceBody436_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_1 sourceBody436_89

def sourceBody436_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody436_0 sourceBody436_90

def source436 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (436, 4, sourceBody436_91)
end InitECandidate.Proofs.WordStages
