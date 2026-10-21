import InitECandidate.Proofs.WordStages.Source269
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody285_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody285_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody285_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody285_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody285_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 8 (Flapjack.WordRegImm.reg 18) sourceBody285_2 sourceBody285_3

def sourceBody285_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody285_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_4 sourceBody285_5

def sourceBody285_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody285_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody285_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody285_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody285_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody285_8, 285, 2)) (some 282) ([8]) (some (8, sourceBody285_10, 285, 3))

def sourceBody285_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_11 sourceBody285_5

def sourceBody285_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_12 sourceBody285_8

def sourceBody285_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_9 sourceBody285_13

def sourceBody285_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_8 sourceBody285_14

def sourceBody285_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_8 sourceBody285_15

def sourceBody285_17 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody285_16 sourceBody285_8

def sourceBody285_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_17 sourceBody285_5

def sourceBody285_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_18 sourceBody285_8

def sourceBody285_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_7 sourceBody285_19

def sourceBody285_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_6 sourceBody285_20

def sourceBody285_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_1 sourceBody285_21

def sourceBody285_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_0 sourceBody285_22

def sourceBody285_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 2)

def sourceBody285_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 22 (Flapjack.WordLangAddr.addr 22 0#64))

def sourceBody285_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_25 sourceBody285_8

def sourceBody285_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_24 sourceBody285_26

def sourceBody285_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 22)

def sourceBody285_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 8)
    (Flapjack.WordLangExpHOL.const 4#64))

def sourceBody285_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 18)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody285_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody285_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
    (Flapjack.WordLangExpHOL.const 1#64))

def sourceBody285_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody285_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody285_8, 285, 4)) (some 68) ([16]) (some (16, sourceBody285_33, 285, 5))

def sourceBody285_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_34 sourceBody285_5

def sourceBody285_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_35 sourceBody285_8

def sourceBody285_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_32 sourceBody285_36

def sourceBody285_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody285_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody285_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody285_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody285_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody285_43 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.reg 10) sourceBody285_41 sourceBody285_42

def sourceBody285_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_43 sourceBody285_5

def sourceBody285_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody285_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody285_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 15#64])

def sourceBody285_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 24 (Flapjack.WordLangAddr.addr 12 0#64))

def sourceBody285_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_48 sourceBody285_8

def sourceBody285_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_47 sourceBody285_49

def sourceBody285_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_46 sourceBody285_50

def sourceBody285_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody285_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_52 sourceBody285_8

def sourceBody285_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_53 sourceBody285_8

def sourceBody285_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_51 sourceBody285_54

def sourceBody285_56 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody285_55 sourceBody285_8

def sourceBody285_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_56 sourceBody285_5

def sourceBody285_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_57 sourceBody285_8

def sourceBody285_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_45 sourceBody285_58

def sourceBody285_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_44 sourceBody285_59

def sourceBody285_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_40 sourceBody285_60

def sourceBody285_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_39 sourceBody285_61

def sourceBody285_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody285_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody285_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 16])

def sourceBody285_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody285_67 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody285_8, 285, 6)) (some 284) ([24, 10, 20]) (some (24, sourceBody285_66, 285, 7))

def sourceBody285_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_67 sourceBody285_5

def sourceBody285_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_68 sourceBody285_8

def sourceBody285_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_65 sourceBody285_69

def sourceBody285_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_64 sourceBody285_70

def sourceBody285_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_63 sourceBody285_71

def sourceBody285_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_8 sourceBody285_72

def sourceBody285_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_8 sourceBody285_73

def sourceBody285_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_62 sourceBody285_74

def sourceBody285_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 16,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64])
        (Flapjack.WordLangExpHOL.const 1#64)])

def sourceBody285_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody285_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12, 24, 10]

def sourceBody285_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_78 sourceBody285_8

def sourceBody285_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_77 sourceBody285_79

def sourceBody285_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_76 sourceBody285_80

def sourceBody285_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_46 sourceBody285_81

def sourceBody285_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_75 sourceBody285_82

def sourceBody285_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_38 sourceBody285_83

def sourceBody285_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_8 sourceBody285_84

def sourceBody285_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_37 sourceBody285_85

def sourceBody285_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_8 sourceBody285_86

def sourceBody285_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_8 sourceBody285_87

def sourceBody285_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_31 sourceBody285_88

def sourceBody285_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_8 sourceBody285_89

def sourceBody285_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_30 sourceBody285_90

def sourceBody285_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_8 sourceBody285_91

def sourceBody285_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_29 sourceBody285_92

def sourceBody285_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_8 sourceBody285_93

def sourceBody285_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_28 sourceBody285_94

def sourceBody285_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_27 sourceBody285_95

def sourceBody285_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody285_23 sourceBody285_96

def source285 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (285, 3, sourceBody285_97)
end InitECandidate.Proofs.WordStages
