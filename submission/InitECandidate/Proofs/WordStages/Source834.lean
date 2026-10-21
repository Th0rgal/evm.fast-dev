import InitECandidate.Proofs.WordStages.Source818
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody834_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody834_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody834_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody834_0, 834, 2)) (some 69) ([]) (some (22, sourceBody834_1, 834, 3))

def sourceBody834_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody834_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_2 sourceBody834_3

def sourceBody834_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_4 sourceBody834_0

def sourceBody834_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody834_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody834_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody834_0, 834, 4)) (some 68) ([16]) (some (16, sourceBody834_7, 834, 5))

def sourceBody834_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_8 sourceBody834_3

def sourceBody834_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_9 sourceBody834_0

def sourceBody834_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_6 sourceBody834_10

def sourceBody834_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody834_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody834_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 22)

def sourceBody834_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody834_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody834_0, 834, 6)) (some 158) ([28, 8, 20]) (some (28, sourceBody834_15, 834, 7))

def sourceBody834_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_16 sourceBody834_3

def sourceBody834_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_17 sourceBody834_0

def sourceBody834_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_14 sourceBody834_18

def sourceBody834_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_13 sourceBody834_19

def sourceBody834_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_12 sourceBody834_20

def sourceBody834_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_0 sourceBody834_21

def sourceBody834_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_0 sourceBody834_22

def sourceBody834_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody834_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 16)

def sourceBody834_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody834_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody834_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody834_29 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 8 (Flapjack.WordRegImm.reg 20) sourceBody834_27 sourceBody834_28

def sourceBody834_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_29 sourceBody834_3

def sourceBody834_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody834_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.var 16])

def sourceBody834_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 28 (Flapjack.WordLangAddr.addr 28 0#64))

def sourceBody834_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody834_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 8 (Flapjack.WordLangAddr.addr 8 0#64))

def sourceBody834_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_35 sourceBody834_0

def sourceBody834_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_34 sourceBody834_36

def sourceBody834_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_33 sourceBody834_37

def sourceBody834_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_32 sourceBody834_38

def sourceBody834_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
        [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 28)
            (Flapjack.WordLangExpHOL.const 8#64),
          Flapjack.WordLangExpHOL.var 8],
      Flapjack.WordLangExpHOL.const 2047#64])

def sourceBody834_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.const 2047#64, Flapjack.WordLangExpHOL.var 20])

def sourceBody834_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 14)
    (Flapjack.WordLangExpHOL.const 3#64))

def sourceBody834_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.const 1#64)
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.const 7#64,
        Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
          [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 7#64]]))

def sourceBody834_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 26])

def sourceBody834_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 24 (Flapjack.WordLangAddr.addr 24 0#64))

def sourceBody834_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 26])

def sourceBody834_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.var 12])

def sourceBody834_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 30 (Flapjack.WordLangAddr.addr 18 0#64))

def sourceBody834_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_48 sourceBody834_0

def sourceBody834_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_47 sourceBody834_49

def sourceBody834_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_46 sourceBody834_50

def sourceBody834_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_45 sourceBody834_51

def sourceBody834_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_44 sourceBody834_52

def sourceBody834_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody834_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody834_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_55 sourceBody834_0

def sourceBody834_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_56 sourceBody834_0

def sourceBody834_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_54 sourceBody834_57

def sourceBody834_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_0 sourceBody834_58

def sourceBody834_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_53 sourceBody834_59

def sourceBody834_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_43 sourceBody834_60

def sourceBody834_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_0 sourceBody834_61

def sourceBody834_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_42 sourceBody834_62

def sourceBody834_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_0 sourceBody834_63

def sourceBody834_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_41 sourceBody834_64

def sourceBody834_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_0 sourceBody834_65

def sourceBody834_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_40 sourceBody834_66

def sourceBody834_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_39 sourceBody834_67

def sourceBody834_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody834_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_68 sourceBody834_69

def sourceBody834_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody834_72 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody834_70 sourceBody834_71

def sourceBody834_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_72 sourceBody834_3

def sourceBody834_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_73 sourceBody834_0

def sourceBody834_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_31 sourceBody834_74

def sourceBody834_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_30 sourceBody834_75

def sourceBody834_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_26 sourceBody834_76

def sourceBody834_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_25 sourceBody834_77

def sourceBody834_79 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody834_78 (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
  PUnit.unit Flapjack.Spt.ln)

def sourceBody834_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_79 sourceBody834_3

def sourceBody834_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_3 sourceBody834_80

def sourceBody834_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody834_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody834_84 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody834_0, 834, 8)) (some 70) ([8]) (some (8, sourceBody834_83, 834, 9))

def sourceBody834_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_84 sourceBody834_3

def sourceBody834_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_85 sourceBody834_0

def sourceBody834_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_82 sourceBody834_86

def sourceBody834_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_0 sourceBody834_87

def sourceBody834_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_0 sourceBody834_88

def sourceBody834_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_81 sourceBody834_89

def sourceBody834_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody834_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [28]

def sourceBody834_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_92 sourceBody834_0

def sourceBody834_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_91 sourceBody834_93

def sourceBody834_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_90 sourceBody834_94

def sourceBody834_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_24 sourceBody834_95

def sourceBody834_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_0 sourceBody834_96

def sourceBody834_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_23 sourceBody834_97

def sourceBody834_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_11 sourceBody834_98

def sourceBody834_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_0 sourceBody834_99

def sourceBody834_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_0 sourceBody834_100

def sourceBody834_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_5 sourceBody834_101

def sourceBody834_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_0 sourceBody834_102

def sourceBody834_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody834_0 sourceBody834_103

def source834 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (834, 4, sourceBody834_104)
end InitECandidate.Proofs.WordStages
