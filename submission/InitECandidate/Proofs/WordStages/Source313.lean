import InitECandidate.Proofs.WordStages.Source297
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody313_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody313_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody313_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody313_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody313_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 22) sourceBody313_2 sourceBody313_3

def sourceBody313_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody313_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_4 sourceBody313_5

def sourceBody313_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody313_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody313_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody313_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody313_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_9 sourceBody313_10

def sourceBody313_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_8 sourceBody313_11

def sourceBody313_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody313_12 sourceBody313_10

def sourceBody313_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_13 sourceBody313_5

def sourceBody313_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_14 sourceBody313_10

def sourceBody313_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_7 sourceBody313_15

def sourceBody313_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_6 sourceBody313_16

def sourceBody313_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_1 sourceBody313_17

def sourceBody313_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_0 sourceBody313_18

def sourceBody313_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody313_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody313_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody313_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody313_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 22 (Flapjack.WordRegImm.reg 10) sourceBody313_23 sourceBody313_1

def sourceBody313_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_24 sourceBody313_5

def sourceBody313_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody313_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody313_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 8)

def sourceBody313_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 22)

def sourceBody313_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 14) 10

def sourceBody313_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_30 sourceBody313_10

def sourceBody313_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_29 sourceBody313_31

def sourceBody313_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_32 sourceBody313_10

def sourceBody313_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_28 sourceBody313_33

def sourceBody313_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_10 sourceBody313_34

def sourceBody313_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_27 sourceBody313_35

def sourceBody313_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_10 sourceBody313_36

def sourceBody313_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody313_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody313_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_39 sourceBody313_10

def sourceBody313_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_38 sourceBody313_40

def sourceBody313_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_37 sourceBody313_41

def sourceBody313_43 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody313_42 sourceBody313_10

def sourceBody313_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_43 sourceBody313_5

def sourceBody313_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_44 sourceBody313_10

def sourceBody313_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_26 sourceBody313_45

def sourceBody313_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_25 sourceBody313_46

def sourceBody313_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_22 sourceBody313_47

def sourceBody313_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_21 sourceBody313_48

def sourceBody313_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody313_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody313_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody313_53 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody313_10, 313, 2)) (some 282) ([22]) (some (22, sourceBody313_52, 313, 3))

def sourceBody313_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_53 sourceBody313_5

def sourceBody313_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_54 sourceBody313_10

def sourceBody313_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_51 sourceBody313_55

def sourceBody313_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_10 sourceBody313_56

def sourceBody313_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_10 sourceBody313_57

def sourceBody313_59 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody313_58 sourceBody313_10

def sourceBody313_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_59 sourceBody313_5

def sourceBody313_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_60 sourceBody313_10

def sourceBody313_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_26 sourceBody313_61

def sourceBody313_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_25 sourceBody313_62

def sourceBody313_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_50 sourceBody313_63

def sourceBody313_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_21 sourceBody313_64

def sourceBody313_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_49 sourceBody313_65

def sourceBody313_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 4)

def sourceBody313_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody313_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody313_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody313_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody313_10, 313, 4)) (some 288) ([22, 10, 16, 12]) (some (22, sourceBody313_52, 313, 5))

def sourceBody313_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_71 sourceBody313_5

def sourceBody313_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_72 sourceBody313_10

def sourceBody313_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_70 sourceBody313_73

def sourceBody313_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_69 sourceBody313_74

def sourceBody313_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_68 sourceBody313_75

def sourceBody313_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_67 sourceBody313_76

def sourceBody313_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 40#64])])

def sourceBody313_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody313_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody313_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody313_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody313_83 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 12) sourceBody313_81 sourceBody313_82

def sourceBody313_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_83 sourceBody313_5

def sourceBody313_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody313_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody313_87 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 293) ([0, 10, 16, 12]) (none)

def sourceBody313_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_87 sourceBody313_10

def sourceBody313_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_86 sourceBody313_88

def sourceBody313_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_26 sourceBody313_89

def sourceBody313_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_7 sourceBody313_90

def sourceBody313_92 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody313_91 sourceBody313_10

def sourceBody313_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_92 sourceBody313_5

def sourceBody313_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_93 sourceBody313_10

def sourceBody313_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_85 sourceBody313_94

def sourceBody313_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_84 sourceBody313_95

def sourceBody313_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_80 sourceBody313_96

def sourceBody313_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_79 sourceBody313_97

def sourceBody313_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody313_100 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 292) ([0, 10, 16, 12, 20]) (none)

def sourceBody313_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_100 sourceBody313_10

def sourceBody313_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_99 sourceBody313_101

def sourceBody313_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_86 sourceBody313_102

def sourceBody313_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_26 sourceBody313_103

def sourceBody313_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_7 sourceBody313_104

def sourceBody313_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_98 sourceBody313_105

def sourceBody313_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_78 sourceBody313_106

def sourceBody313_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_10 sourceBody313_107

def sourceBody313_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_77 sourceBody313_108

def sourceBody313_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_10 sourceBody313_109

def sourceBody313_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_10 sourceBody313_110

def sourceBody313_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_66 sourceBody313_111

def sourceBody313_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_20 sourceBody313_112

def sourceBody313_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_10 sourceBody313_113

def sourceBody313_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody313_19 sourceBody313_114

def source313 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (313, 5, sourceBody313_115)
end InitECandidate.Proofs.WordStages
