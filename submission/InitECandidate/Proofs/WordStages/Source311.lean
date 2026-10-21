import InitECandidate.Proofs.WordStages.Source295
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody311_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody311_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody311_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody311_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody311_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody311_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 34)

def sourceBody311_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody311_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody311_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody311_9 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.reg 22) sourceBody311_7 sourceBody311_8

def sourceBody311_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_9 sourceBody311_4

def sourceBody311_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 42)

def sourceBody311_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody311_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody311_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_13 sourceBody311_0

def sourceBody311_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_14 sourceBody311_0

def sourceBody311_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 2)

def sourceBody311_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody311_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody311_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody311_20 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 48 (Flapjack.WordRegImm.reg 14) sourceBody311_18 sourceBody311_19

def sourceBody311_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_20 sourceBody311_4

def sourceBody311_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 48)

def sourceBody311_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 8])

def sourceBody311_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 8])

def sourceBody311_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody311_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 12)

def sourceBody311_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody311_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody311_0, 311, 2)) (some 292) ([30, 48, 14, 32]) (some (30, sourceBody311_27, 311, 3))

def sourceBody311_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_28 sourceBody311_4

def sourceBody311_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_29 sourceBody311_0

def sourceBody311_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_26 sourceBody311_30

def sourceBody311_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_25 sourceBody311_31

def sourceBody311_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_24 sourceBody311_32

def sourceBody311_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_23 sourceBody311_33

def sourceBody311_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody311_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 30)

def sourceBody311_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody311_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody311_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 32) sourceBody311_38 sourceBody311_17

def sourceBody311_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_39 sourceBody311_4

def sourceBody311_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody311_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody311_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody311_44 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody311_0, 311, 4)) (some 282) ([14]) (some (14, sourceBody311_43, 311, 5))

def sourceBody311_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_44 sourceBody311_4

def sourceBody311_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_45 sourceBody311_0

def sourceBody311_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_42 sourceBody311_46

def sourceBody311_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_47

def sourceBody311_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_48

def sourceBody311_50 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody311_49 sourceBody311_0

def sourceBody311_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_50 sourceBody311_4

def sourceBody311_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_51 sourceBody311_0

def sourceBody311_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_41 sourceBody311_52

def sourceBody311_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_40 sourceBody311_53

def sourceBody311_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_37 sourceBody311_54

def sourceBody311_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_36 sourceBody311_55

def sourceBody311_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody311_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody311_0, 311, 6)) (some 295) ([14]) (some (14, sourceBody311_43, 311, 7))

def sourceBody311_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_58 sourceBody311_4

def sourceBody311_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_59 sourceBody311_0

def sourceBody311_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_57 sourceBody311_60

def sourceBody311_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_61

def sourceBody311_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_62

def sourceBody311_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_56 sourceBody311_63

def sourceBody311_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody311_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 8])

def sourceBody311_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 8])

def sourceBody311_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody311_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 12)

def sourceBody311_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 48

def sourceBody311_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody311_0, 311, 8)) (some 309) ([48, 14, 32, 24, 40]) (some (48, sourceBody311_70, 311, 9))

def sourceBody311_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_71 sourceBody311_4

def sourceBody311_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_72 sourceBody311_0

def sourceBody311_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_69 sourceBody311_73

def sourceBody311_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_68 sourceBody311_74

def sourceBody311_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_67 sourceBody311_75

def sourceBody311_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_66 sourceBody311_76

def sourceBody311_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_16 sourceBody311_77

def sourceBody311_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody311_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody311_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody311_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 48)

def sourceBody311_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 14)

def sourceBody311_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 8])

def sourceBody311_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 8])

def sourceBody311_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody311_87 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody311_0, 311, 10)) (some 287) ([24, 40, 20, 36]) (some (24, sourceBody311_86, 311, 11))

def sourceBody311_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_87 sourceBody311_4

def sourceBody311_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_88 sourceBody311_0

def sourceBody311_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_85 sourceBody311_89

def sourceBody311_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_84 sourceBody311_90

def sourceBody311_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_83 sourceBody311_91

def sourceBody311_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_82 sourceBody311_92

def sourceBody311_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 32)

def sourceBody311_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody311_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody311_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody311_98 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 40 (Flapjack.WordRegImm.reg 20) sourceBody311_96 sourceBody311_97

def sourceBody311_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_98 sourceBody311_4

def sourceBody311_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 40)

def sourceBody311_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 2)

def sourceBody311_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_101 sourceBody311_0

def sourceBody311_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_102 sourceBody311_0

def sourceBody311_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody311_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_104 sourceBody311_0

def sourceBody311_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_105 sourceBody311_0

def sourceBody311_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_103 sourceBody311_106

def sourceBody311_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody311_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_108 sourceBody311_0

def sourceBody311_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_109 sourceBody311_0

def sourceBody311_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_107 sourceBody311_110

def sourceBody311_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 32])

def sourceBody311_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_112 sourceBody311_0

def sourceBody311_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_113 sourceBody311_0

def sourceBody311_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_111 sourceBody311_114

def sourceBody311_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_3 sourceBody311_0

def sourceBody311_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_116 sourceBody311_0

def sourceBody311_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_115 sourceBody311_117

def sourceBody311_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 2)

def sourceBody311_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 10)

def sourceBody311_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 12)

def sourceBody311_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 32)

def sourceBody311_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody311_124 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody311_0, 311, 12)) (some 310) ([40, 20, 36, 28, 46, 18]) (some (40, sourceBody311_123, 311, 13))

def sourceBody311_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_124 sourceBody311_4

def sourceBody311_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_125 sourceBody311_0

def sourceBody311_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_122 sourceBody311_126

def sourceBody311_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_121 sourceBody311_127

def sourceBody311_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_120 sourceBody311_128

def sourceBody311_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_85 sourceBody311_129

def sourceBody311_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_84 sourceBody311_130

def sourceBody311_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_119 sourceBody311_131

def sourceBody311_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody311_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 32)

def sourceBody311_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody311_136 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 20 (Flapjack.WordRegImm.reg 36) sourceBody311_135 sourceBody311_133

def sourceBody311_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_136 sourceBody311_4

def sourceBody311_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 20)

def sourceBody311_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 48)

def sourceBody311_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 32)

def sourceBody311_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 24)

def sourceBody311_142 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody311_0, 311, 14)) (some 293) ([40, 20, 36]) (some (40, sourceBody311_123, 311, 15))

def sourceBody311_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_142 sourceBody311_4

def sourceBody311_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_143 sourceBody311_0

def sourceBody311_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_141 sourceBody311_144

def sourceBody311_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_140 sourceBody311_145

def sourceBody311_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_139 sourceBody311_146

def sourceBody311_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 24)

def sourceBody311_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_148 sourceBody311_0

def sourceBody311_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_149 sourceBody311_0

def sourceBody311_151 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody311_147 sourceBody311_150

def sourceBody311_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_151 sourceBody311_4

def sourceBody311_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_152 sourceBody311_0

def sourceBody311_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_138 sourceBody311_153

def sourceBody311_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_137 sourceBody311_154

def sourceBody311_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_134 sourceBody311_155

def sourceBody311_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_133 sourceBody311_156

def sourceBody311_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_132 sourceBody311_157

def sourceBody311_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_158

def sourceBody311_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_159

def sourceBody311_161 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody311_118 sourceBody311_160

def sourceBody311_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_161 sourceBody311_4

def sourceBody311_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_162 sourceBody311_0

def sourceBody311_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_100 sourceBody311_163

def sourceBody311_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_99 sourceBody311_164

def sourceBody311_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_95 sourceBody311_165

def sourceBody311_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_94 sourceBody311_166

def sourceBody311_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_93 sourceBody311_167

def sourceBody311_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_168

def sourceBody311_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_169

def sourceBody311_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_81 sourceBody311_170

def sourceBody311_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_171

def sourceBody311_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_80 sourceBody311_172

def sourceBody311_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_173

def sourceBody311_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody311_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 6)

def sourceBody311_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64])

def sourceBody311_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 14)

def sourceBody311_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 48) 32

def sourceBody311_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_179 sourceBody311_0

def sourceBody311_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_178 sourceBody311_180

def sourceBody311_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_181 sourceBody311_0

def sourceBody311_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_25 sourceBody311_182

def sourceBody311_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_183

def sourceBody311_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_177 sourceBody311_184

def sourceBody311_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_185

def sourceBody311_187 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 168#64])

def sourceBody311_188 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody311_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_188 sourceBody311_182

def sourceBody311_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_189

def sourceBody311_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_187 sourceBody311_190

def sourceBody311_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_191

def sourceBody311_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_186 sourceBody311_192

def sourceBody311_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_193 sourceBody311_103

def sourceBody311_195 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 8])

def sourceBody311_196 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 48 (Flapjack.WordLangAddr.addr 48 0#64))

def sourceBody311_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_196 sourceBody311_0

def sourceBody311_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_195 sourceBody311_197

def sourceBody311_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 48)

def sourceBody311_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody311_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_200 sourceBody311_0

def sourceBody311_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_201 sourceBody311_0

def sourceBody311_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_103 sourceBody311_202

def sourceBody311_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody311_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_204 sourceBody311_0

def sourceBody311_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_205 sourceBody311_0

def sourceBody311_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_203 sourceBody311_206

def sourceBody311_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody311_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_208 sourceBody311_0

def sourceBody311_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_209 sourceBody311_0

def sourceBody311_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_207 sourceBody311_210

def sourceBody311_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_211 sourceBody311_117

def sourceBody311_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_199 sourceBody311_212

def sourceBody311_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_198 sourceBody311_213

def sourceBody311_215 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody311_194 sourceBody311_214

def sourceBody311_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_215 sourceBody311_4

def sourceBody311_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_216 sourceBody311_0

def sourceBody311_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_41 sourceBody311_217

def sourceBody311_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_40 sourceBody311_218

def sourceBody311_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_176 sourceBody311_219

def sourceBody311_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_175 sourceBody311_220

def sourceBody311_222 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody311_174 sourceBody311_221

def sourceBody311_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_222 sourceBody311_4

def sourceBody311_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_223 sourceBody311_0

def sourceBody311_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_41 sourceBody311_224

def sourceBody311_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_40 sourceBody311_225

def sourceBody311_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_79 sourceBody311_226

def sourceBody311_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_36 sourceBody311_227

def sourceBody311_229 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody311_78 sourceBody311_228

def sourceBody311_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_229 sourceBody311_4

def sourceBody311_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_230 sourceBody311_0

def sourceBody311_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_41 sourceBody311_231

def sourceBody311_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_40 sourceBody311_232

def sourceBody311_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_65 sourceBody311_233

def sourceBody311_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_36 sourceBody311_234

def sourceBody311_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_64 sourceBody311_235

def sourceBody311_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_35 sourceBody311_236

def sourceBody311_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_237

def sourceBody311_239 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody311_34 sourceBody311_238

def sourceBody311_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_239 sourceBody311_4

def sourceBody311_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_240 sourceBody311_0

def sourceBody311_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_22 sourceBody311_241

def sourceBody311_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_21 sourceBody311_242

def sourceBody311_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_17 sourceBody311_243

def sourceBody311_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_16 sourceBody311_244

def sourceBody311_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_15 sourceBody311_245

def sourceBody311_247 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 16)

def sourceBody311_248 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 26)

def sourceBody311_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_248 sourceBody311_0

def sourceBody311_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_249 sourceBody311_0

def sourceBody311_251 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 16)

def sourceBody311_252 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 26)

def sourceBody311_253 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 30) 14

def sourceBody311_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_253 sourceBody311_0

def sourceBody311_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_199 sourceBody311_254

def sourceBody311_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_255 sourceBody311_0

def sourceBody311_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_252 sourceBody311_256

def sourceBody311_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_257

def sourceBody311_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_251 sourceBody311_258

def sourceBody311_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_259

def sourceBody311_261 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody311_250 sourceBody311_260

def sourceBody311_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_261 sourceBody311_4

def sourceBody311_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_262 sourceBody311_0

def sourceBody311_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_22 sourceBody311_263

def sourceBody311_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_21 sourceBody311_264

def sourceBody311_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_17 sourceBody311_265

def sourceBody311_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_247 sourceBody311_266

def sourceBody311_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_246 sourceBody311_267

def sourceBody311_269 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 42)

def sourceBody311_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_269 sourceBody311_0

def sourceBody311_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_270 sourceBody311_0

def sourceBody311_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_268 sourceBody311_271

def sourceBody311_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody311_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_273 sourceBody311_0

def sourceBody311_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_274 sourceBody311_0

def sourceBody311_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_272 sourceBody311_275

def sourceBody311_277 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 38)

def sourceBody311_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_277 sourceBody311_0

def sourceBody311_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_278 sourceBody311_0

def sourceBody311_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_276 sourceBody311_279

def sourceBody311_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_12 sourceBody311_280

def sourceBody311_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_281

def sourceBody311_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_6 sourceBody311_282

def sourceBody311_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_283

def sourceBody311_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_8 sourceBody311_284

def sourceBody311_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_285

def sourceBody311_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_286

def sourceBody311_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_287

def sourceBody311_289 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody311_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_288 sourceBody311_289

def sourceBody311_291 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody311_292 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.imm 0#64) sourceBody311_290 sourceBody311_291

def sourceBody311_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_292 sourceBody311_4

def sourceBody311_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_293 sourceBody311_0

def sourceBody311_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_11 sourceBody311_294

def sourceBody311_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_10 sourceBody311_295

def sourceBody311_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_6 sourceBody311_296

def sourceBody311_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_5 sourceBody311_297

def sourceBody311_299 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody311_298 (Flapjack.Spt.bs
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody311_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_299 sourceBody311_4

def sourceBody311_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_4 sourceBody311_300

def sourceBody311_302 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 44)

def sourceBody311_303 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody311_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_303 sourceBody311_0

def sourceBody311_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_302 sourceBody311_304

def sourceBody311_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_301 sourceBody311_305

def sourceBody311_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_3 sourceBody311_306

def sourceBody311_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_307

def sourceBody311_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_2 sourceBody311_308

def sourceBody311_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_309

def sourceBody311_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_1 sourceBody311_310

def sourceBody311_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody311_0 sourceBody311_311

def source311 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (311, 7, sourceBody311_312)
end InitECandidate.Proofs.WordStages
