import InitECandidate.Proofs.WordStages.Source294
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody310_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody310_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody310_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody310_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody310_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody310_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody310_0, 310, 2)) (some 294) ([]) (some (34, sourceBody310_4, 310, 3))

def sourceBody310_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody310_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_5 sourceBody310_6

def sourceBody310_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_7 sourceBody310_0

def sourceBody310_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.var 12])

def sourceBody310_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 34)

def sourceBody310_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody310_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody310_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody310_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 30 (Flapjack.WordRegImm.reg 24) sourceBody310_12 sourceBody310_13

def sourceBody310_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_14 sourceBody310_6

def sourceBody310_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 30)

def sourceBody310_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.var 12])

def sourceBody310_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 18 (Flapjack.WordLangAddr.addr 18 0#64))

def sourceBody310_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_18 sourceBody310_0

def sourceBody310_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_17 sourceBody310_19

def sourceBody310_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 32#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 18)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody310_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 28)

def sourceBody310_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 24)

def sourceBody310_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 30) 38

def sourceBody310_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_24 sourceBody310_0

def sourceBody310_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_23 sourceBody310_25

def sourceBody310_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_26 sourceBody310_0

def sourceBody310_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_22 sourceBody310_27

def sourceBody310_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_28

def sourceBody310_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_21 sourceBody310_29

def sourceBody310_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_20 sourceBody310_30

def sourceBody310_32 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.imm 0#64) sourceBody310_31 sourceBody310_0

def sourceBody310_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_32 sourceBody310_6

def sourceBody310_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_33 sourceBody310_0

def sourceBody310_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_16 sourceBody310_34

def sourceBody310_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_15 sourceBody310_35

def sourceBody310_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_11 sourceBody310_36

def sourceBody310_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_10 sourceBody310_37

def sourceBody310_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 34)

def sourceBody310_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 30 (Flapjack.WordRegImm.reg 24) sourceBody310_12 sourceBody310_13

def sourceBody310_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_40 sourceBody310_6

def sourceBody310_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody310_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody310_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 28)

def sourceBody310_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody310_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody310_0, 310, 4)) (some 293) ([30, 24, 38]) (some (30, sourceBody310_45, 310, 5))

def sourceBody310_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_46 sourceBody310_6

def sourceBody310_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_47 sourceBody310_0

def sourceBody310_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_44 sourceBody310_48

def sourceBody310_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_43 sourceBody310_49

def sourceBody310_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_42 sourceBody310_50

def sourceBody310_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.var 12])

def sourceBody310_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 30 (Flapjack.WordLangAddr.addr 30 0#64))

def sourceBody310_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_53 sourceBody310_0

def sourceBody310_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_52 sourceBody310_54

def sourceBody310_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 32#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 30)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody310_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 18)

def sourceBody310_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 38)

def sourceBody310_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 24) 14

def sourceBody310_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_59 sourceBody310_0

def sourceBody310_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_58 sourceBody310_60

def sourceBody310_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_61 sourceBody310_0

def sourceBody310_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_57 sourceBody310_62

def sourceBody310_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_63

def sourceBody310_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_56 sourceBody310_64

def sourceBody310_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_55 sourceBody310_65

def sourceBody310_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_51 sourceBody310_66

def sourceBody310_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_67

def sourceBody310_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_68

def sourceBody310_70 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.imm 0#64) sourceBody310_69 sourceBody310_0

def sourceBody310_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_70 sourceBody310_6

def sourceBody310_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_71 sourceBody310_0

def sourceBody310_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_16 sourceBody310_72

def sourceBody310_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_41 sourceBody310_73

def sourceBody310_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_39 sourceBody310_74

def sourceBody310_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_12 sourceBody310_75

def sourceBody310_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_38 sourceBody310_76

def sourceBody310_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 12])

def sourceBody310_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody310_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody310_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody310_82 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 38) sourceBody310_11 sourceBody310_81

def sourceBody310_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_82 sourceBody310_6

def sourceBody310_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 24)

def sourceBody310_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 160#64])

def sourceBody310_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody310_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_86 sourceBody310_27

def sourceBody310_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_87

def sourceBody310_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_85 sourceBody310_88

def sourceBody310_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_89

def sourceBody310_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 168#64])

def sourceBody310_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody310_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_92 sourceBody310_27

def sourceBody310_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_93

def sourceBody310_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_91 sourceBody310_94

def sourceBody310_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_95

def sourceBody310_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_90 sourceBody310_96

def sourceBody310_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 12])

def sourceBody310_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_98 sourceBody310_54

def sourceBody310_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 30)

def sourceBody310_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 32#64,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody310_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody310_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody310_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody310_105 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.reg 26) sourceBody310_103 sourceBody310_104

def sourceBody310_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_105 sourceBody310_6

def sourceBody310_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody310_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 11#64)

def sourceBody310_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody310_110 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody310_0, 310, 6)) (some 282) ([14]) (some (14, sourceBody310_109, 310, 7))

def sourceBody310_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_110 sourceBody310_6

def sourceBody310_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_111 sourceBody310_0

def sourceBody310_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_108 sourceBody310_112

def sourceBody310_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_113

def sourceBody310_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_114

def sourceBody310_116 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody310_115 sourceBody310_0

def sourceBody310_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_116 sourceBody310_6

def sourceBody310_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_117 sourceBody310_0

def sourceBody310_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_107 sourceBody310_118

def sourceBody310_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_106 sourceBody310_119

def sourceBody310_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_102 sourceBody310_120

def sourceBody310_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_101 sourceBody310_121

def sourceBody310_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody310_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody310_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody310_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody310_127 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody310_0, 310, 8)) (some 292) ([14, 26, 20, 32]) (some (14, sourceBody310_109, 310, 9))

def sourceBody310_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_127 sourceBody310_6

def sourceBody310_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_128 sourceBody310_0

def sourceBody310_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_126 sourceBody310_129

def sourceBody310_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_125 sourceBody310_130

def sourceBody310_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_124 sourceBody310_131

def sourceBody310_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_123 sourceBody310_132

def sourceBody310_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 32#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody310_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 38)

def sourceBody310_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 26)

def sourceBody310_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 14) 20

def sourceBody310_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_137 sourceBody310_0

def sourceBody310_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_136 sourceBody310_138

def sourceBody310_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_139 sourceBody310_0

def sourceBody310_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_135 sourceBody310_140

def sourceBody310_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_141

def sourceBody310_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_134 sourceBody310_142

def sourceBody310_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_143

def sourceBody310_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_133 sourceBody310_144

def sourceBody310_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_145

def sourceBody310_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_146

def sourceBody310_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_122 sourceBody310_147

def sourceBody310_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_100 sourceBody310_148

def sourceBody310_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_99 sourceBody310_149

def sourceBody310_151 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody310_97 sourceBody310_150

def sourceBody310_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_151 sourceBody310_6

def sourceBody310_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_152 sourceBody310_0

def sourceBody310_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_84 sourceBody310_153

def sourceBody310_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_83 sourceBody310_154

def sourceBody310_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_80 sourceBody310_155

def sourceBody310_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_79 sourceBody310_156

def sourceBody310_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 22)

def sourceBody310_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30]

def sourceBody310_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_159 sourceBody310_0

def sourceBody310_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_158 sourceBody310_160

def sourceBody310_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_157 sourceBody310_161

def sourceBody310_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_78 sourceBody310_162

def sourceBody310_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_163

def sourceBody310_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_77 sourceBody310_164

def sourceBody310_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_9 sourceBody310_165

def sourceBody310_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_166

def sourceBody310_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_8 sourceBody310_167

def sourceBody310_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_168

def sourceBody310_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_169

def sourceBody310_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_3 sourceBody310_170

def sourceBody310_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_171

def sourceBody310_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_2 sourceBody310_172

def sourceBody310_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_173

def sourceBody310_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_1 sourceBody310_174

def sourceBody310_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody310_0 sourceBody310_175

def source310 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (310, 7, sourceBody310_176)
end InitECandidate.Proofs.WordStages
