import InitECandidate.Proofs.WordStages.Source313
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody329_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody329_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody329_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody329_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody329_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody329_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody329_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 2)

def sourceBody329_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody329_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody329_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody329_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.lookup (Flapjack.WordStore.temp 0#5))

def sourceBody329_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_10 sourceBody329_0

def sourceBody329_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_11 sourceBody329_0

def sourceBody329_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody329_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody329_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody329_0, 329, 3)) (some 282) ([28]) (some (28, sourceBody329_14, 329, 4))

def sourceBody329_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_15 sourceBody329_9

def sourceBody329_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_16 sourceBody329_0

def sourceBody329_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_13 sourceBody329_17

def sourceBody329_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_18

def sourceBody329_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_19

def sourceBody329_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_12 sourceBody329_20

def sourceBody329_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_9 sourceBody329_21

def sourceBody329_23 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 44 (Flapjack.WordRegImm.imm 1#64) sourceBody329_8 sourceBody329_22

def sourceBody329_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_23 sourceBody329_9

def sourceBody329_25 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 48, 32, 64]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody329_0, 329, 2)) (some 162) ([44, 28]) (some (44, sourceBody329_24, 329, 5))

def sourceBody329_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_25 sourceBody329_9

def sourceBody329_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_26 sourceBody329_0

def sourceBody329_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_7 sourceBody329_27

def sourceBody329_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_6 sourceBody329_28

def sourceBody329_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 16)

def sourceBody329_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody329_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody329_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody329_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.reg 60) sourceBody329_32 sourceBody329_33

def sourceBody329_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_34 sourceBody329_9

def sourceBody329_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 28)

def sourceBody329_37 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody329_0, 329, 6)) (some 282) ([28]) (some (28, sourceBody329_14, 329, 7))

def sourceBody329_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_37 sourceBody329_9

def sourceBody329_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_38 sourceBody329_0

def sourceBody329_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_13 sourceBody329_39

def sourceBody329_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_40

def sourceBody329_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_41

def sourceBody329_43 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody329_42 sourceBody329_0

def sourceBody329_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_43 sourceBody329_9

def sourceBody329_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_44 sourceBody329_0

def sourceBody329_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_36 sourceBody329_45

def sourceBody329_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_35 sourceBody329_46

def sourceBody329_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_31 sourceBody329_47

def sourceBody329_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_30 sourceBody329_48

def sourceBody329_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_29 sourceBody329_49

def sourceBody329_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 48)

def sourceBody329_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 32)

def sourceBody329_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 60

def sourceBody329_54 : WordLangProgHOL (BitVec 64) :=
.call (some (([44, 28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody329_0, 329, 8)) (some 169) ([60, 20]) (some (60, sourceBody329_53, 329, 9))

def sourceBody329_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_54 sourceBody329_9

def sourceBody329_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_55 sourceBody329_0

def sourceBody329_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_52 sourceBody329_56

def sourceBody329_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_51 sourceBody329_57

def sourceBody329_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody329_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody329_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody329_62 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.reg 52) sourceBody329_60 sourceBody329_61

def sourceBody329_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_62 sourceBody329_9

def sourceBody329_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 20)

def sourceBody329_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody329_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody329_67 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody329_0, 329, 10)) (some 282) ([20]) (some (20, sourceBody329_66, 329, 11))

def sourceBody329_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_67 sourceBody329_9

def sourceBody329_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_68 sourceBody329_0

def sourceBody329_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_65 sourceBody329_69

def sourceBody329_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_70

def sourceBody329_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_71

def sourceBody329_73 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody329_72 sourceBody329_0

def sourceBody329_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_73 sourceBody329_9

def sourceBody329_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_74 sourceBody329_0

def sourceBody329_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_64 sourceBody329_75

def sourceBody329_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_63 sourceBody329_76

def sourceBody329_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_59 sourceBody329_77

def sourceBody329_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_36 sourceBody329_78

def sourceBody329_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 44)

def sourceBody329_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 60, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody329_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 60, Flapjack.WordLangExpHOL.const 0#64, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody329_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody329_84 : WordLangProgHOL (BitVec 64) :=
.call (some (([20, 52, 36, 68]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody329_0, 329, 12)) (some 161) ([10, 42]) (some (10, sourceBody329_83, 329, 13))

def sourceBody329_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_84 sourceBody329_9

def sourceBody329_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_85 sourceBody329_0

def sourceBody329_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_82 sourceBody329_86

def sourceBody329_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_81 sourceBody329_87

def sourceBody329_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 60, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody329_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 60, Flapjack.WordLangExpHOL.const 16#64, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody329_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody329_92 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 42, 26, 58]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody329_0, 329, 14)) (some 161) ([18, 50]) (some (18, sourceBody329_91, 329, 15))

def sourceBody329_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_92 sourceBody329_9

def sourceBody329_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_93 sourceBody329_0

def sourceBody329_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_90 sourceBody329_94

def sourceBody329_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_89 sourceBody329_95

def sourceBody329_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 60, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody329_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 60, Flapjack.WordLangExpHOL.const 32#64, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody329_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody329_100 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 50, 34, 66]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody329_0, 329, 16)) (some 161) ([14, 46]) (some (14, sourceBody329_99, 329, 17))

def sourceBody329_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_100 sourceBody329_9

def sourceBody329_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_101 sourceBody329_0

def sourceBody329_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_98 sourceBody329_102

def sourceBody329_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_97 sourceBody329_103

def sourceBody329_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 60, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody329_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 60, Flapjack.WordLangExpHOL.const 48#64, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody329_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody329_108 : WordLangProgHOL (BitVec 64) :=
.call (some (([14, 46, 30, 62]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody329_0, 329, 18)) (some 161) ([22, 54]) (some (22, sourceBody329_107, 329, 19))

def sourceBody329_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_108 sourceBody329_9

def sourceBody329_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_109 sourceBody329_0

def sourceBody329_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_106 sourceBody329_110

def sourceBody329_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_105 sourceBody329_111

def sourceBody329_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 18,
      Flapjack.WordLangExpHOL.var 14])

def sourceBody329_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody329_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody329_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody329_117 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 54 (Flapjack.WordRegImm.reg 38) sourceBody329_115 sourceBody329_116

def sourceBody329_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_117 sourceBody329_9

def sourceBody329_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 54)

def sourceBody329_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody329_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 54

def sourceBody329_122 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody329_0, 329, 20)) (some 282) ([54]) (some (54, sourceBody329_121, 329, 21))

def sourceBody329_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_122 sourceBody329_9

def sourceBody329_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_123 sourceBody329_0

def sourceBody329_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_120 sourceBody329_124

def sourceBody329_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_125

def sourceBody329_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_126

def sourceBody329_128 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 70 (Flapjack.WordRegImm.imm 0#64) sourceBody329_127 sourceBody329_0

def sourceBody329_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_128 sourceBody329_9

def sourceBody329_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_129 sourceBody329_0

def sourceBody329_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_119 sourceBody329_130

def sourceBody329_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_118 sourceBody329_131

def sourceBody329_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_114 sourceBody329_132

def sourceBody329_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_113 sourceBody329_133

def sourceBody329_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody329_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 36)

def sourceBody329_137 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 54 (Flapjack.WordRegImm.reg 38) sourceBody329_115 sourceBody329_116

def sourceBody329_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_137 sourceBody329_9

def sourceBody329_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 21#64)

def sourceBody329_140 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody329_0, 329, 22)) (some 282) ([54]) (some (54, sourceBody329_121, 329, 23))

def sourceBody329_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_140 sourceBody329_9

def sourceBody329_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_141 sourceBody329_0

def sourceBody329_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_139 sourceBody329_142

def sourceBody329_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_143

def sourceBody329_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_144

def sourceBody329_146 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 70 (Flapjack.WordRegImm.imm 0#64) sourceBody329_145 sourceBody329_0

def sourceBody329_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_146 sourceBody329_9

def sourceBody329_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_147 sourceBody329_0

def sourceBody329_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_119 sourceBody329_148

def sourceBody329_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_138 sourceBody329_149

def sourceBody329_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_136 sourceBody329_150

def sourceBody329_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_135 sourceBody329_151

def sourceBody329_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_134 sourceBody329_152

def sourceBody329_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody329_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 36)

def sourceBody329_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody329_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody329_158 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 70 (Flapjack.WordRegImm.reg 8) sourceBody329_156 sourceBody329_157

def sourceBody329_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_158 sourceBody329_9

def sourceBody329_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 70)

def sourceBody329_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 52, Flapjack.WordLangExpHOL.var 54])

def sourceBody329_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 38 (Flapjack.WordLangAddr.addr 38 0#64))

def sourceBody329_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_162 sourceBody329_0

def sourceBody329_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_161 sourceBody329_163

def sourceBody329_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 22)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.var 38])

def sourceBody329_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 70)

def sourceBody329_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_166 sourceBody329_0

def sourceBody329_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_167 sourceBody329_0

def sourceBody329_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_165 sourceBody329_168

def sourceBody329_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_164 sourceBody329_169

def sourceBody329_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 54, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody329_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 38)

def sourceBody329_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_172 sourceBody329_0

def sourceBody329_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_173 sourceBody329_0

def sourceBody329_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_171 sourceBody329_174

def sourceBody329_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_175

def sourceBody329_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_170 sourceBody329_176

def sourceBody329_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody329_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_177 sourceBody329_178

def sourceBody329_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody329_181 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.imm 0#64) sourceBody329_179 sourceBody329_180

def sourceBody329_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_181 sourceBody329_9

def sourceBody329_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_182 sourceBody329_0

def sourceBody329_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_160 sourceBody329_183

def sourceBody329_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_159 sourceBody329_184

def sourceBody329_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_155 sourceBody329_185

def sourceBody329_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_119 sourceBody329_186

def sourceBody329_188 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
  PUnit.unit Flapjack.Spt.ln) sourceBody329_187 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody329_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_188 sourceBody329_9

def sourceBody329_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_9 sourceBody329_189

def sourceBody329_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody329_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 22)

def sourceBody329_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 70)

def sourceBody329_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 38) 8

def sourceBody329_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_194 sourceBody329_0

def sourceBody329_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_193 sourceBody329_195

def sourceBody329_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_196 sourceBody329_0

def sourceBody329_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_192 sourceBody329_197

def sourceBody329_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_198

def sourceBody329_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_191 sourceBody329_199

def sourceBody329_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_200

def sourceBody329_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_190 sourceBody329_201

def sourceBody329_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody329_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 26)

def sourceBody329_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.const 22#64)

def sourceBody329_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 70

def sourceBody329_207 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody329_0, 329, 24)) (some 282) ([70]) (some (70, sourceBody329_206, 329, 25))

def sourceBody329_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_207 sourceBody329_9

def sourceBody329_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_208 sourceBody329_0

def sourceBody329_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_205 sourceBody329_209

def sourceBody329_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_210

def sourceBody329_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_211

def sourceBody329_213 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.imm 0#64) sourceBody329_212 sourceBody329_0

def sourceBody329_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_213 sourceBody329_9

def sourceBody329_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_214 sourceBody329_0

def sourceBody329_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_160 sourceBody329_215

def sourceBody329_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_159 sourceBody329_216

def sourceBody329_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_204 sourceBody329_217

def sourceBody329_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_203 sourceBody329_218

def sourceBody329_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_202 sourceBody329_219

def sourceBody329_221 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody329_222 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody329_223 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody329_0, 329, 26)) (some 78) ([70, 8]) (some (70, sourceBody329_206, 329, 27))

def sourceBody329_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_223 sourceBody329_9

def sourceBody329_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_224 sourceBody329_0

def sourceBody329_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_222 sourceBody329_225

def sourceBody329_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_221 sourceBody329_226

def sourceBody329_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_227

def sourceBody329_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_228

def sourceBody329_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_220 sourceBody329_229

def sourceBody329_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_116 sourceBody329_0

def sourceBody329_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_231 sourceBody329_0

def sourceBody329_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_230 sourceBody329_232

def sourceBody329_234 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 1#64],
      Flapjack.WordLangExpHOL.var 54])

def sourceBody329_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 8#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 38)
          (Flapjack.WordLangExpHOL.const 3#64))
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody329_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.var 54])

def sourceBody329_237 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 40 (Flapjack.WordLangAddr.addr 40 0#64))

def sourceBody329_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_237 sourceBody329_0

def sourceBody329_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_236 sourceBody329_238

def sourceBody329_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 70),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
        (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
            [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 7#64])
          (Flapjack.WordLangExpHOL.const 3#64))])

def sourceBody329_241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 24)

def sourceBody329_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 56

def sourceBody329_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_242 sourceBody329_0

def sourceBody329_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_241 sourceBody329_243

def sourceBody329_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_244 sourceBody329_0

def sourceBody329_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_240 sourceBody329_245

def sourceBody329_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_239 sourceBody329_246

def sourceBody329_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_193 sourceBody329_247

def sourceBody329_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_248

def sourceBody329_250 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 54, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody329_251 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 8)

def sourceBody329_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_251 sourceBody329_0

def sourceBody329_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_252 sourceBody329_0

def sourceBody329_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_250 sourceBody329_253

def sourceBody329_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_254

def sourceBody329_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_249 sourceBody329_255

def sourceBody329_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_235 sourceBody329_256

def sourceBody329_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_257

def sourceBody329_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_234 sourceBody329_258

def sourceBody329_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_259

def sourceBody329_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_260 sourceBody329_178

def sourceBody329_262 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.imm 0#64) sourceBody329_261 sourceBody329_180

def sourceBody329_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_262 sourceBody329_9

def sourceBody329_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_263 sourceBody329_0

def sourceBody329_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_160 sourceBody329_264

def sourceBody329_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_159 sourceBody329_265

def sourceBody329_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_204 sourceBody329_266

def sourceBody329_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_119 sourceBody329_267

def sourceBody329_269 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
  PUnit.unit Flapjack.Spt.ln) sourceBody329_268 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
    Flapjack.Spt.ln)
  PUnit.unit Flapjack.Spt.ln)

def sourceBody329_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_269 sourceBody329_9

def sourceBody329_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_9 sourceBody329_270

def sourceBody329_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_233 sourceBody329_271

def sourceBody329_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 34)

def sourceBody329_274 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody329_275 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 70 (Flapjack.WordRegImm.reg 8) sourceBody329_156 sourceBody329_157

def sourceBody329_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_275 sourceBody329_9

def sourceBody329_277 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody329_278 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 128#64]))

def sourceBody329_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_278 sourceBody329_197

def sourceBody329_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_279

def sourceBody329_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_277 sourceBody329_280

def sourceBody329_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_281

def sourceBody329_283 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 70 (Flapjack.WordRegImm.reg 8) sourceBody329_156 sourceBody329_157

def sourceBody329_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_283 sourceBody329_9

def sourceBody329_285 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.const 23#64)

def sourceBody329_286 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody329_0, 329, 28)) (some 282) ([70]) (some (70, sourceBody329_206, 329, 29))

def sourceBody329_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_286 sourceBody329_9

def sourceBody329_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_287 sourceBody329_0

def sourceBody329_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_285 sourceBody329_288

def sourceBody329_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_289

def sourceBody329_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_290

def sourceBody329_292 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.imm 0#64) sourceBody329_291 sourceBody329_0

def sourceBody329_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_292 sourceBody329_9

def sourceBody329_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_293 sourceBody329_0

def sourceBody329_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_160 sourceBody329_294

def sourceBody329_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_284 sourceBody329_295

def sourceBody329_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_222 sourceBody329_296

def sourceBody329_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_273 sourceBody329_297

def sourceBody329_299 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 50)

def sourceBody329_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_299 sourceBody329_197

def sourceBody329_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_300

def sourceBody329_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_277 sourceBody329_301

def sourceBody329_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_302

def sourceBody329_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_298 sourceBody329_303

def sourceBody329_305 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.imm 0#64) sourceBody329_282 sourceBody329_304

def sourceBody329_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_305 sourceBody329_9

def sourceBody329_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_306 sourceBody329_0

def sourceBody329_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_160 sourceBody329_307

def sourceBody329_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_276 sourceBody329_308

def sourceBody329_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_274 sourceBody329_309

def sourceBody329_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_273 sourceBody329_310

def sourceBody329_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_272 sourceBody329_311

def sourceBody329_313 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 30)

def sourceBody329_314 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody329_315 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 136#64]))

def sourceBody329_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_315 sourceBody329_197

def sourceBody329_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_316

def sourceBody329_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_314 sourceBody329_317

def sourceBody329_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_318

def sourceBody329_320 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody329_321 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody329_0, 329, 30)) (some 282) ([70]) (some (70, sourceBody329_206, 329, 31))

def sourceBody329_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_321 sourceBody329_9

def sourceBody329_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_322 sourceBody329_0

def sourceBody329_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_320 sourceBody329_323

def sourceBody329_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_324

def sourceBody329_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_325

def sourceBody329_327 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.imm 0#64) sourceBody329_326 sourceBody329_0

def sourceBody329_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_327 sourceBody329_9

def sourceBody329_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_328 sourceBody329_0

def sourceBody329_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_160 sourceBody329_329

def sourceBody329_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_284 sourceBody329_330

def sourceBody329_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_222 sourceBody329_331

def sourceBody329_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_313 sourceBody329_332

def sourceBody329_334 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 46)

def sourceBody329_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_334 sourceBody329_197

def sourceBody329_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_335

def sourceBody329_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_314 sourceBody329_336

def sourceBody329_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_337

def sourceBody329_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_333 sourceBody329_338

def sourceBody329_340 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.imm 0#64) sourceBody329_319 sourceBody329_339

def sourceBody329_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_340 sourceBody329_9

def sourceBody329_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_341 sourceBody329_0

def sourceBody329_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_160 sourceBody329_342

def sourceBody329_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_276 sourceBody329_343

def sourceBody329_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_274 sourceBody329_344

def sourceBody329_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_313 sourceBody329_345

def sourceBody329_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_312 sourceBody329_346

def sourceBody329_348 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [38]

def sourceBody329_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_348 sourceBody329_0

def sourceBody329_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_114 sourceBody329_349

def sourceBody329_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_347 sourceBody329_350

def sourceBody329_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_116 sourceBody329_351

def sourceBody329_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_352

def sourceBody329_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_154 sourceBody329_353

def sourceBody329_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_354

def sourceBody329_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_153 sourceBody329_355

def sourceBody329_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_112 sourceBody329_356

def sourceBody329_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_357

def sourceBody329_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_358

def sourceBody329_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_359

def sourceBody329_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_360

def sourceBody329_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_361

def sourceBody329_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_362

def sourceBody329_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_363

def sourceBody329_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_364

def sourceBody329_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_104 sourceBody329_365

def sourceBody329_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_366

def sourceBody329_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_367

def sourceBody329_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_368

def sourceBody329_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_369

def sourceBody329_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_370

def sourceBody329_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_371

def sourceBody329_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_372

def sourceBody329_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_373

def sourceBody329_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_96 sourceBody329_374

def sourceBody329_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_375

def sourceBody329_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_376

def sourceBody329_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_377

def sourceBody329_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_378

def sourceBody329_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_379

def sourceBody329_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_380

def sourceBody329_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_381

def sourceBody329_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_382

def sourceBody329_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_88 sourceBody329_383

def sourceBody329_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_384

def sourceBody329_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_385

def sourceBody329_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_386

def sourceBody329_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_387

def sourceBody329_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_388

def sourceBody329_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_389

def sourceBody329_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_390

def sourceBody329_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_391

def sourceBody329_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_80 sourceBody329_392

def sourceBody329_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_393

def sourceBody329_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_79 sourceBody329_394

def sourceBody329_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_58 sourceBody329_395

def sourceBody329_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_396

def sourceBody329_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_397

def sourceBody329_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_398

def sourceBody329_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_399

def sourceBody329_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_50 sourceBody329_400

def sourceBody329_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_5 sourceBody329_401

def sourceBody329_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_402

def sourceBody329_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_4 sourceBody329_403

def sourceBody329_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_404

def sourceBody329_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_3 sourceBody329_405

def sourceBody329_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_406

def sourceBody329_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_2 sourceBody329_407

def sourceBody329_409 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_408

def sourceBody329_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_1 sourceBody329_409

def sourceBody329_411 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody329_0 sourceBody329_410

def source329 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (329, 4, sourceBody329_411)
end InitECandidate.Proofs.WordStages
