import InitECandidate.Proofs.WordStages.Source465
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody481_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody481_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 63#64])
          (Flapjack.WordLangExpHOL.const 6#64))
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody481_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody481_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody481_0, 481, 2)) (some 74) ([10]) (some (10, sourceBody481_2, 481, 3))

def sourceBody481_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody481_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_3 sourceBody481_4

def sourceBody481_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_5 sourceBody481_0

def sourceBody481_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_1 sourceBody481_6

def sourceBody481_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 36)

def sourceBody481_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 63#64])
          (Flapjack.WordLangExpHOL.const 6#64))
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody481_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody481_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody481_0, 481, 4)) (some 78) ([30, 20]) (some (30, sourceBody481_10, 481, 5))

def sourceBody481_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_11 sourceBody481_4

def sourceBody481_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_12 sourceBody481_0

def sourceBody481_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_9 sourceBody481_13

def sourceBody481_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_8 sourceBody481_14

def sourceBody481_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_0 sourceBody481_15

def sourceBody481_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_0 sourceBody481_16

def sourceBody481_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody481_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 10)

def sourceBody481_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 4)

def sourceBody481_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody481_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody481_23 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 20 (Flapjack.WordRegImm.reg 42) sourceBody481_21 sourceBody481_22

def sourceBody481_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_23 sourceBody481_4

def sourceBody481_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 20)

def sourceBody481_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 10])

def sourceBody481_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 30 (Flapjack.WordLangAddr.addr 30 0#64))

def sourceBody481_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_27 sourceBody481_0

def sourceBody481_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_26 sourceBody481_28

def sourceBody481_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 30)

def sourceBody481_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody481_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 20)

def sourceBody481_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 91#64)

def sourceBody481_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody481_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody481_36 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 28 (Flapjack.WordRegImm.reg 18) sourceBody481_34 sourceBody481_35

def sourceBody481_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_36 sourceBody481_4

def sourceBody481_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 28)

def sourceBody481_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 36,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 10)
          (Flapjack.WordLangExpHOL.const 6#64))
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody481_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 36,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 10)
                (Flapjack.WordLangExpHOL.const 6#64))
              (Flapjack.WordLangExpHOL.const 3#64)]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.const 1#64)
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
          [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 63#64])])

def sourceBody481_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody481_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 18

def sourceBody481_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_42 sourceBody481_0

def sourceBody481_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_41 sourceBody481_43

def sourceBody481_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_44 sourceBody481_0

def sourceBody481_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_40 sourceBody481_45

def sourceBody481_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_0 sourceBody481_46

def sourceBody481_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_39 sourceBody481_47

def sourceBody481_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_0 sourceBody481_48

def sourceBody481_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody481_51 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 28 (Flapjack.WordRegImm.reg 18) sourceBody481_34 sourceBody481_35

def sourceBody481_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_51 sourceBody481_4

def sourceBody481_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody481_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 28)

def sourceBody481_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody481_56 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.reg 34) sourceBody481_55 sourceBody481_53

def sourceBody481_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_56 sourceBody481_4

def sourceBody481_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 127#64)

def sourceBody481_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 20)

def sourceBody481_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody481_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody481_62 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 44 (Flapjack.WordRegImm.reg 6) sourceBody481_60 sourceBody481_61

def sourceBody481_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_62 sourceBody481_4

def sourceBody481_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody481_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 44)

def sourceBody481_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody481_67 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 38) sourceBody481_66 sourceBody481_64

def sourceBody481_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_67 sourceBody481_4

def sourceBody481_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.var 16])

def sourceBody481_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
        [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 96#64],
      Flapjack.WordLangExpHOL.const 2#64])

def sourceBody481_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_70 sourceBody481_0

def sourceBody481_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_71 sourceBody481_0

def sourceBody481_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 230#64)

def sourceBody481_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody481_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 231#64)

def sourceBody481_76 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 34) sourceBody481_55 sourceBody481_53

def sourceBody481_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_76 sourceBody481_4

def sourceBody481_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.var 14])

def sourceBody481_79 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 44 (Flapjack.WordRegImm.reg 6) sourceBody481_60 sourceBody481_61

def sourceBody481_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_79 sourceBody481_4

def sourceBody481_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 44)

def sourceBody481_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody481_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_82 sourceBody481_0

def sourceBody481_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_83 sourceBody481_0

def sourceBody481_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody481_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody481_87 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 28 (Flapjack.WordRegImm.reg 18) sourceBody481_34 sourceBody481_35

def sourceBody481_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_87 sourceBody481_4

def sourceBody481_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody481_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 8 (Flapjack.WordLangAddr.addr 8 0#64))

def sourceBody481_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_90 sourceBody481_0

def sourceBody481_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_89 sourceBody481_91

def sourceBody481_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 8)

def sourceBody481_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 91#64)

def sourceBody481_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody481_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody481_97 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 40 (Flapjack.WordRegImm.reg 14) sourceBody481_95 sourceBody481_96

def sourceBody481_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_97 sourceBody481_4

def sourceBody481_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody481_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 40)

def sourceBody481_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody481_102 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.reg 44) sourceBody481_101 sourceBody481_99

def sourceBody481_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_102 sourceBody481_4

def sourceBody481_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 127#64)

def sourceBody481_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 28)

def sourceBody481_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody481_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody481_108 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 26 (Flapjack.WordRegImm.reg 16) sourceBody481_106 sourceBody481_107

def sourceBody481_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_108 sourceBody481_4

def sourceBody481_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody481_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 26)

def sourceBody481_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody481_113 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 32) sourceBody481_112 sourceBody481_110

def sourceBody481_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_113 sourceBody481_4

def sourceBody481_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.var 12])

def sourceBody481_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_31 sourceBody481_0

def sourceBody481_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_116 sourceBody481_0

def sourceBody481_118 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody481_117 sourceBody481_0

def sourceBody481_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_118 sourceBody481_4

def sourceBody481_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_119 sourceBody481_0

def sourceBody481_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_115 sourceBody481_120

def sourceBody481_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_114 sourceBody481_121

def sourceBody481_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_111 sourceBody481_122

def sourceBody481_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_110 sourceBody481_123

def sourceBody481_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_109 sourceBody481_124

def sourceBody481_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_105 sourceBody481_125

def sourceBody481_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_104 sourceBody481_126

def sourceBody481_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_103 sourceBody481_127

def sourceBody481_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_100 sourceBody481_128

def sourceBody481_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_99 sourceBody481_129

def sourceBody481_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_98 sourceBody481_130

def sourceBody481_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_94 sourceBody481_131

def sourceBody481_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_38 sourceBody481_132

def sourceBody481_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_93 sourceBody481_133

def sourceBody481_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_92 sourceBody481_134

def sourceBody481_136 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.imm 0#64) sourceBody481_135 sourceBody481_0

def sourceBody481_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_136 sourceBody481_4

def sourceBody481_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_137 sourceBody481_0

def sourceBody481_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_38 sourceBody481_138

def sourceBody481_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_88 sourceBody481_139

def sourceBody481_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_86 sourceBody481_140

def sourceBody481_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_85 sourceBody481_141

def sourceBody481_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_84 sourceBody481_142

def sourceBody481_144 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody481_143 sourceBody481_0

def sourceBody481_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_144 sourceBody481_4

def sourceBody481_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_145 sourceBody481_0

def sourceBody481_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_81 sourceBody481_146

def sourceBody481_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_80 sourceBody481_147

def sourceBody481_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_78 sourceBody481_148

def sourceBody481_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_61 sourceBody481_149

def sourceBody481_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_77 sourceBody481_150

def sourceBody481_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_75 sourceBody481_151

def sourceBody481_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_74 sourceBody481_152

def sourceBody481_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_37 sourceBody481_153

def sourceBody481_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_73 sourceBody481_154

def sourceBody481_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_32 sourceBody481_155

def sourceBody481_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 232#64)

def sourceBody481_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 82#64)

def sourceBody481_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_158 sourceBody481_131

def sourceBody481_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_38 sourceBody481_159

def sourceBody481_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_93 sourceBody481_160

def sourceBody481_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_92 sourceBody481_161

def sourceBody481_163 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.imm 0#64) sourceBody481_162 sourceBody481_0

def sourceBody481_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_163 sourceBody481_4

def sourceBody481_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_164 sourceBody481_0

def sourceBody481_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_38 sourceBody481_165

def sourceBody481_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_88 sourceBody481_166

def sourceBody481_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_86 sourceBody481_167

def sourceBody481_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_85 sourceBody481_168

def sourceBody481_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_84 sourceBody481_169

def sourceBody481_171 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.imm 0#64) sourceBody481_170 sourceBody481_0

def sourceBody481_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_171 sourceBody481_4

def sourceBody481_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_172 sourceBody481_0

def sourceBody481_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_38 sourceBody481_173

def sourceBody481_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_37 sourceBody481_174

def sourceBody481_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_157 sourceBody481_175

def sourceBody481_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_32 sourceBody481_176

def sourceBody481_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_156 sourceBody481_177

def sourceBody481_179 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody481_72 sourceBody481_178

def sourceBody481_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_179 sourceBody481_4

def sourceBody481_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_180 sourceBody481_0

def sourceBody481_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_69 sourceBody481_181

def sourceBody481_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_68 sourceBody481_182

def sourceBody481_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_65 sourceBody481_183

def sourceBody481_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_64 sourceBody481_184

def sourceBody481_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_63 sourceBody481_185

def sourceBody481_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_59 sourceBody481_186

def sourceBody481_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_58 sourceBody481_187

def sourceBody481_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_57 sourceBody481_188

def sourceBody481_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_54 sourceBody481_189

def sourceBody481_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_53 sourceBody481_190

def sourceBody481_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_52 sourceBody481_191

def sourceBody481_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_50 sourceBody481_192

def sourceBody481_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_32 sourceBody481_193

def sourceBody481_195 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.imm 0#64) sourceBody481_49 sourceBody481_194

def sourceBody481_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_195 sourceBody481_4

def sourceBody481_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_196 sourceBody481_0

def sourceBody481_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_38 sourceBody481_197

def sourceBody481_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_37 sourceBody481_198

def sourceBody481_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_33 sourceBody481_199

def sourceBody481_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_32 sourceBody481_200

def sourceBody481_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 42])

def sourceBody481_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody481_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_203 sourceBody481_0

def sourceBody481_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_204 sourceBody481_0

def sourceBody481_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_202 sourceBody481_205

def sourceBody481_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_0 sourceBody481_206

def sourceBody481_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_201 sourceBody481_207

def sourceBody481_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_31 sourceBody481_208

def sourceBody481_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_0 sourceBody481_209

def sourceBody481_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_30 sourceBody481_210

def sourceBody481_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_29 sourceBody481_211

def sourceBody481_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody481_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_212 sourceBody481_213

def sourceBody481_215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody481_216 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody481_214 sourceBody481_215

def sourceBody481_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_216 sourceBody481_4

def sourceBody481_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_217 sourceBody481_0

def sourceBody481_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_25 sourceBody481_218

def sourceBody481_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_24 sourceBody481_219

def sourceBody481_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_20 sourceBody481_220

def sourceBody481_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_19 sourceBody481_221

def sourceBody481_223 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln) sourceBody481_222 (Flapjack.Spt.bs
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody481_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_223 sourceBody481_4

def sourceBody481_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_4 sourceBody481_224

def sourceBody481_226 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30]

def sourceBody481_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_226 sourceBody481_0

def sourceBody481_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_8 sourceBody481_227

def sourceBody481_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_225 sourceBody481_228

def sourceBody481_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_18 sourceBody481_229

def sourceBody481_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_0 sourceBody481_230

def sourceBody481_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_17 sourceBody481_231

def sourceBody481_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_7 sourceBody481_232

def sourceBody481_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_0 sourceBody481_233

def sourceBody481_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody481_0 sourceBody481_234

def source481 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (481, 3, sourceBody481_235)
end InitECandidate.Proofs.WordStages
