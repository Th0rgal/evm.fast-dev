import InitECandidate.Proofs.WordStages.Source431
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody447_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody447_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody447_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody447_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody447_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody447_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody447_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 12)

def sourceBody447_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody447_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody447_9 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 10 (Flapjack.WordRegImm.reg 22) sourceBody447_7 sourceBody447_8

def sourceBody447_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_9 sourceBody447_4

def sourceBody447_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody447_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 18)

def sourceBody447_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody447_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 22 22 30 10))

def sourceBody447_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.var 22]))

def sourceBody447_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody447_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody447_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody447_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 28 (Flapjack.WordRegImm.reg 14) sourceBody447_17 sourceBody447_18

def sourceBody447_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_19 sourceBody447_4

def sourceBody447_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody447_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody447_23 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 22) sourceBody447_7 sourceBody447_8

def sourceBody447_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_23 sourceBody447_4

def sourceBody447_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 4)

def sourceBody447_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 16 16 10 22))

def sourceBody447_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody447_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody447_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 26 26 28 14))

def sourceBody447_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.var 16])

def sourceBody447_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.var 26])

def sourceBody447_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody447_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody447_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody447_0, 447, 2)) (some 77) ([20, 32, 8]) (some (10, sourceBody447_33, 447, 3))

def sourceBody447_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_34 sourceBody447_4

def sourceBody447_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_35 sourceBody447_0

def sourceBody447_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_32 sourceBody447_36

def sourceBody447_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_31 sourceBody447_37

def sourceBody447_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_30 sourceBody447_38

def sourceBody447_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_29 sourceBody447_39

def sourceBody447_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_28 sourceBody447_40

def sourceBody447_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_27 sourceBody447_41

def sourceBody447_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_26 sourceBody447_42

def sourceBody447_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_25 sourceBody447_43

def sourceBody447_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_5 sourceBody447_44

def sourceBody447_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_0 sourceBody447_45

def sourceBody447_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_0 sourceBody447_46

def sourceBody447_48 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody447_47 sourceBody447_0

def sourceBody447_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_48 sourceBody447_4

def sourceBody447_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_49 sourceBody447_0

def sourceBody447_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_11 sourceBody447_50

def sourceBody447_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_24 sourceBody447_51

def sourceBody447_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_22 sourceBody447_52

def sourceBody447_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_5 sourceBody447_53

def sourceBody447_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody447_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody447_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody447_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 30) 22

def sourceBody447_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_58 sourceBody447_0

def sourceBody447_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_57 sourceBody447_59

def sourceBody447_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_60 sourceBody447_0

def sourceBody447_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_56 sourceBody447_61

def sourceBody447_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_0 sourceBody447_62

def sourceBody447_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_55 sourceBody447_63

def sourceBody447_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_0 sourceBody447_64

def sourceBody447_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_54 sourceBody447_65

def sourceBody447_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody447_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30]

def sourceBody447_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_68 sourceBody447_0

def sourceBody447_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_67 sourceBody447_69

def sourceBody447_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_66 sourceBody447_70

def sourceBody447_72 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody447_71 sourceBody447_0

def sourceBody447_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_72 sourceBody447_4

def sourceBody447_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_73 sourceBody447_0

def sourceBody447_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_21 sourceBody447_74

def sourceBody447_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_20 sourceBody447_75

def sourceBody447_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_16 sourceBody447_76

def sourceBody447_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_15 sourceBody447_77

def sourceBody447_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_14 sourceBody447_78

def sourceBody447_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_13 sourceBody447_79

def sourceBody447_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_12 sourceBody447_80

def sourceBody447_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody447_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 30)

def sourceBody447_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_83 sourceBody447_0

def sourceBody447_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_84 sourceBody447_0

def sourceBody447_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_82 sourceBody447_85

def sourceBody447_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_0 sourceBody447_86

def sourceBody447_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_81 sourceBody447_87

def sourceBody447_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody447_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_88 sourceBody447_89

def sourceBody447_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody447_92 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody447_90 sourceBody447_91

def sourceBody447_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_92 sourceBody447_4

def sourceBody447_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_93 sourceBody447_0

def sourceBody447_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_11 sourceBody447_94

def sourceBody447_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_10 sourceBody447_95

def sourceBody447_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_6 sourceBody447_96

def sourceBody447_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_5 sourceBody447_97

def sourceBody447_99 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody447_98 (Flapjack.Spt.ls PUnit.unit)

def sourceBody447_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_99 sourceBody447_4

def sourceBody447_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_4 sourceBody447_100

def sourceBody447_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_101 sourceBody447_70

def sourceBody447_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_3 sourceBody447_102

def sourceBody447_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_0 sourceBody447_103

def sourceBody447_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_2 sourceBody447_104

def sourceBody447_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_0 sourceBody447_105

def sourceBody447_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_1 sourceBody447_106

def sourceBody447_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody447_0 sourceBody447_107

def source447 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (447, 4, sourceBody447_108)
end InitECandidate.Proofs.WordStages
