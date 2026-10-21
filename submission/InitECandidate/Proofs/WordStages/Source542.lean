import InitECandidate.Proofs.WordStages.Source526
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody542_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody542_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody542_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 42, 10, 36]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody542_0, 542, 2)) (some 471) ([]) (some (24, sourceBody542_1, 542, 3))

def sourceBody542_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody542_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_2 sourceBody542_3

def sourceBody542_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_4 sourceBody542_0

def sourceBody542_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody542_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([24, 50, 6, 32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 4)) (some 471) ([]) (some (20, sourceBody542_6, 542, 5))

def sourceBody542_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_7 sourceBody542_3

def sourceBody542_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_8 sourceBody542_0

def sourceBody542_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody542_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody542_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody542_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody542_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 46 (Flapjack.WordRegImm.reg 14) sourceBody542_12 sourceBody542_13

def sourceBody542_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_14 sourceBody542_3

def sourceBody542_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 46)

def sourceBody542_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody542_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 20)

def sourceBody542_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_18 sourceBody542_0

def sourceBody542_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_19 sourceBody542_0

def sourceBody542_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_17 sourceBody542_20

def sourceBody542_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_21

def sourceBody542_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody542_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_23 sourceBody542_6

def sourceBody542_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_22 sourceBody542_24

def sourceBody542_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.imm 0#64) sourceBody542_25 sourceBody542_0

def sourceBody542_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_26 sourceBody542_3

def sourceBody542_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_27 sourceBody542_0

def sourceBody542_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_16 sourceBody542_28

def sourceBody542_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_15 sourceBody542_29

def sourceBody542_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_11 sourceBody542_30

def sourceBody542_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_10 sourceBody542_31

def sourceBody542_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 24)

def sourceBody542_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 50)

def sourceBody542_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 6)

def sourceBody542_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 32)

def sourceBody542_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody542_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 6)) (some 458) ([46, 14, 40, 28]) (some (46, sourceBody542_37, 542, 7))

def sourceBody542_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_38 sourceBody542_3

def sourceBody542_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_39 sourceBody542_0

def sourceBody542_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_36 sourceBody542_40

def sourceBody542_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_35 sourceBody542_41

def sourceBody542_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_34 sourceBody542_42

def sourceBody542_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_33 sourceBody542_43

def sourceBody542_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 16)

def sourceBody542_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 42)

def sourceBody542_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 10)

def sourceBody542_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 36)

def sourceBody542_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 24)

def sourceBody542_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 50)

def sourceBody542_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 6)

def sourceBody542_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 32)

def sourceBody542_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody542_54 : WordLangProgHOL (BitVec 64) :=
.call (some (([46, 14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 8)) (some 476) ([40, 28, 54, 4, 30, 18, 44, 12]) (some (40, sourceBody542_53, 542, 9))

def sourceBody542_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_54 sourceBody542_3

def sourceBody542_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_55 sourceBody542_0

def sourceBody542_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_52 sourceBody542_56

def sourceBody542_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_51 sourceBody542_57

def sourceBody542_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_50 sourceBody542_58

def sourceBody542_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_49 sourceBody542_59

def sourceBody542_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_48 sourceBody542_60

def sourceBody542_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_47 sourceBody542_61

def sourceBody542_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_46 sourceBody542_62

def sourceBody542_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_45 sourceBody542_63

def sourceBody542_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody542_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 20)

def sourceBody542_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 54

def sourceBody542_68 : WordLangProgHOL (BitVec 64) :=
.call (some (([40, 28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 10)) (some 119) ([54, 4]) (some (54, sourceBody542_67, 542, 11))

def sourceBody542_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_68 sourceBody542_3

def sourceBody542_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_69 sourceBody542_0

def sourceBody542_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_66 sourceBody542_70

def sourceBody542_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_65 sourceBody542_71

def sourceBody542_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody542_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 375#64)

def sourceBody542_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 18 18 4 30))

def sourceBody542_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.const 375#64, Flapjack.WordLangExpHOL.var 18])

def sourceBody542_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 46)

def sourceBody542_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody542_79 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 12)) (some 459) ([44, 12]) (some (4, sourceBody542_78, 542, 13))

def sourceBody542_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_79 sourceBody542_3

def sourceBody542_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_80 sourceBody542_0

def sourceBody542_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_77 sourceBody542_81

def sourceBody542_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_76 sourceBody542_82

def sourceBody542_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_75 sourceBody542_83

def sourceBody542_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_74 sourceBody542_84

def sourceBody542_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_73 sourceBody542_85

def sourceBody542_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 28)

def sourceBody542_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody542_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody542_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody542_91 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.reg 18) sourceBody542_89 sourceBody542_90

def sourceBody542_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_91 sourceBody542_3

def sourceBody542_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 30)

def sourceBody542_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 18446744073709551615#64)

def sourceBody542_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_94 sourceBody542_0

def sourceBody542_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_95 sourceBody542_0

def sourceBody542_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 54)

def sourceBody542_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 40)

def sourceBody542_99 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 14)) (some 459) ([4, 30]) (some (4, sourceBody542_78, 542, 15))

def sourceBody542_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_99 sourceBody542_3

def sourceBody542_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_100 sourceBody542_0

def sourceBody542_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_98 sourceBody542_101

def sourceBody542_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_97 sourceBody542_102

def sourceBody542_104 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 44 (Flapjack.WordRegImm.imm 0#64) sourceBody542_96 sourceBody542_103

def sourceBody542_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_104 sourceBody542_3

def sourceBody542_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_105 sourceBody542_0

def sourceBody542_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_93 sourceBody542_106

def sourceBody542_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_92 sourceBody542_107

def sourceBody542_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_88 sourceBody542_108

def sourceBody542_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_87 sourceBody542_109

def sourceBody542_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 54)

def sourceBody542_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody542_113 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 16)) (some 466) ([30]) (some (30, sourceBody542_112, 542, 17))

def sourceBody542_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_113 sourceBody542_3

def sourceBody542_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_114 sourceBody542_0

def sourceBody542_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_111 sourceBody542_115

def sourceBody542_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_116

def sourceBody542_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_117

def sourceBody542_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_110 sourceBody542_118

def sourceBody542_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 2)
        (Flapjack.WordLangExpHOL.const 5#64),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody542_121 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 18)) (some 68) ([30]) (some (30, sourceBody542_112, 542, 19))

def sourceBody542_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_121 sourceBody542_3

def sourceBody542_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_122 sourceBody542_0

def sourceBody542_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_120 sourceBody542_123

def sourceBody542_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody542_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody542_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody542_128 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 44 (Flapjack.WordRegImm.reg 12) sourceBody542_126 sourceBody542_127

def sourceBody542_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_128 sourceBody542_3

def sourceBody542_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 44)

def sourceBody542_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody542_132 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 44, 12, 38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 20)) (some 471) ([]) (some (26, sourceBody542_131, 542, 21))

def sourceBody542_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_132 sourceBody542_3

def sourceBody542_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_133 sourceBody542_0

def sourceBody542_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 18)

def sourceBody542_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 44)

def sourceBody542_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 12)

def sourceBody542_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 38)

def sourceBody542_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 4,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 30)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody542_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 52

def sourceBody542_141 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 22)) (some 147) ([52, 8, 34, 22, 48]) (some (52, sourceBody542_140, 542, 23))

def sourceBody542_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_141 sourceBody542_3

def sourceBody542_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_142 sourceBody542_0

def sourceBody542_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_139 sourceBody542_143

def sourceBody542_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_138 sourceBody542_144

def sourceBody542_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_137 sourceBody542_145

def sourceBody542_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_136 sourceBody542_146

def sourceBody542_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_135 sourceBody542_147

def sourceBody542_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_148

def sourceBody542_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_149

def sourceBody542_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody542_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 26)

def sourceBody542_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_152 sourceBody542_0

def sourceBody542_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_153 sourceBody542_0

def sourceBody542_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_151 sourceBody542_154

def sourceBody542_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_155

def sourceBody542_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_150 sourceBody542_156

def sourceBody542_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_134 sourceBody542_157

def sourceBody542_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_158

def sourceBody542_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_159

def sourceBody542_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_160

def sourceBody542_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_161

def sourceBody542_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_162

def sourceBody542_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_163

def sourceBody542_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_164

def sourceBody542_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_165

def sourceBody542_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody542_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_166 sourceBody542_167

def sourceBody542_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody542_170 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.imm 0#64) sourceBody542_168 sourceBody542_169

def sourceBody542_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_170 sourceBody542_3

def sourceBody542_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_171 sourceBody542_0

def sourceBody542_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_130 sourceBody542_172

def sourceBody542_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_129 sourceBody542_173

def sourceBody542_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_125 sourceBody542_174

def sourceBody542_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_93 sourceBody542_175

def sourceBody542_177 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody542_176 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody542_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_177 sourceBody542_3

def sourceBody542_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_3 sourceBody542_178

def sourceBody542_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 14)

def sourceBody542_181 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody542_182 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 24)) (some 478) ([44]) (some (44, sourceBody542_181, 542, 25))

def sourceBody542_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_182 sourceBody542_3

def sourceBody542_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_183 sourceBody542_0

def sourceBody542_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_180 sourceBody542_184

def sourceBody542_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_185

def sourceBody542_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_186

def sourceBody542_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_179 sourceBody542_187

def sourceBody542_189 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 26)) (some 488) ([]) (some (44, sourceBody542_181, 542, 27))

def sourceBody542_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_189 sourceBody542_3

def sourceBody542_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_190 sourceBody542_0

def sourceBody542_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_191

def sourceBody542_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_192

def sourceBody542_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_188 sourceBody542_193

def sourceBody542_195 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 40#64)

def sourceBody542_196 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 28)) (some 68) ([44]) (some (44, sourceBody542_181, 542, 29))

def sourceBody542_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_196 sourceBody542_3

def sourceBody542_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_197 sourceBody542_0

def sourceBody542_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_195 sourceBody542_198

def sourceBody542_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody542_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody542_202 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 30)) (some 68) ([12]) (some (12, sourceBody542_201, 542, 31))

def sourceBody542_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_202 sourceBody542_3

def sourceBody542_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_203 sourceBody542_0

def sourceBody542_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_200 sourceBody542_204

def sourceBody542_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.load
                (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                  [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                      [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                          (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                          (Flapjack.WordLangExpHOL.const 1#64)],
                    Flapjack.WordLangExpHOL.const 256#64]),
              Flapjack.WordLangExpHOL.const 112#64]),
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody542_207 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody542_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody542_209 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 32)) (some 77) ([38, 26, 52]) (some (38, sourceBody542_208, 542, 33))

def sourceBody542_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_209 sourceBody542_3

def sourceBody542_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_210 sourceBody542_0

def sourceBody542_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_207 sourceBody542_211

def sourceBody542_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_206 sourceBody542_212

def sourceBody542_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_130 sourceBody542_213

def sourceBody542_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_214

def sourceBody542_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_215

def sourceBody542_217 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody542_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 38)

def sourceBody542_219 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 12) 26

def sourceBody542_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_219 sourceBody542_0

def sourceBody542_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_218 sourceBody542_220

def sourceBody542_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_221 sourceBody542_0

def sourceBody542_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_130 sourceBody542_222

def sourceBody542_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_223

def sourceBody542_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_217 sourceBody542_224

def sourceBody542_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_225

def sourceBody542_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_216 sourceBody542_226

def sourceBody542_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody542_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 4)

def sourceBody542_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_229 sourceBody542_222

def sourceBody542_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_230

def sourceBody542_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_228 sourceBody542_231

def sourceBody542_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_232

def sourceBody542_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_227 sourceBody542_233

def sourceBody542_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody542_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 2)

def sourceBody542_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_236 sourceBody542_222

def sourceBody542_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_237

def sourceBody542_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_235 sourceBody542_238

def sourceBody542_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_239

def sourceBody542_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_234 sourceBody542_240

def sourceBody542_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody542_243 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 34)) (some 68) ([38]) (some (38, sourceBody542_208, 542, 35))

def sourceBody542_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_243 sourceBody542_3

def sourceBody542_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_244 sourceBody542_0

def sourceBody542_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_242 sourceBody542_245

def sourceBody542_247 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 16)

def sourceBody542_248 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 42)

def sourceBody542_249 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody542_250 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 36)

def sourceBody542_251 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 36)) (some 458) ([26, 52, 8, 34]) (some (26, sourceBody542_131, 542, 37))

def sourceBody542_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_251 sourceBody542_3

def sourceBody542_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_252 sourceBody542_0

def sourceBody542_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_250 sourceBody542_253

def sourceBody542_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_249 sourceBody542_254

def sourceBody542_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_248 sourceBody542_255

def sourceBody542_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_247 sourceBody542_256

def sourceBody542_258 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 12)

def sourceBody542_259 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 256#64]),
            Flapjack.WordLangExpHOL.const 24#64]),
      Flapjack.WordLangExpHOL.var 38])

def sourceBody542_260 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 20)

def sourceBody542_261 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody542_0, 542, 38)) (some 77) ([52, 8, 34]) (some (52, sourceBody542_140, 542, 39))

def sourceBody542_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_261 sourceBody542_3

def sourceBody542_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_262 sourceBody542_0

def sourceBody542_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_260 sourceBody542_263

def sourceBody542_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_259 sourceBody542_264

def sourceBody542_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_258 sourceBody542_265

def sourceBody542_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_266

def sourceBody542_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_267

def sourceBody542_269 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody542_270 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 52)

def sourceBody542_271 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 26) 8

def sourceBody542_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_271 sourceBody542_0

def sourceBody542_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_270 sourceBody542_272

def sourceBody542_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_273 sourceBody542_0

def sourceBody542_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_258 sourceBody542_274

def sourceBody542_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_275

def sourceBody542_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_269 sourceBody542_276

def sourceBody542_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_277

def sourceBody542_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_268 sourceBody542_278

def sourceBody542_280 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody542_281 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 20)

def sourceBody542_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_281 sourceBody542_274

def sourceBody542_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_282

def sourceBody542_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_280 sourceBody542_283

def sourceBody542_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_284

def sourceBody542_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_279 sourceBody542_285

def sourceBody542_287 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 256#64]))

def sourceBody542_288 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 18)

def sourceBody542_289 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody542_0, 542, 40)) (some 541) ([52, 8]) (some (52, sourceBody542_140, 542, 41))

def sourceBody542_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_289 sourceBody542_3

def sourceBody542_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_290 sourceBody542_0

def sourceBody542_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_288 sourceBody542_291

def sourceBody542_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_287 sourceBody542_292

def sourceBody542_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_293

def sourceBody542_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_294

def sourceBody542_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_286 sourceBody542_295

def sourceBody542_297 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody542_298 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody542_0, 542, 42)) (some 486) ([52]) (some (52, sourceBody542_140, 542, 43))

def sourceBody542_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_298 sourceBody542_3

def sourceBody542_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_299 sourceBody542_0

def sourceBody542_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_297 sourceBody542_300

def sourceBody542_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_301

def sourceBody542_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_302

def sourceBody542_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_296 sourceBody542_303

def sourceBody542_305 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody542_306 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody542_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_306 sourceBody542_0

def sourceBody542_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_305 sourceBody542_307

def sourceBody542_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_304 sourceBody542_308

def sourceBody542_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_257 sourceBody542_309

def sourceBody542_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_310

def sourceBody542_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_311

def sourceBody542_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_246 sourceBody542_312

def sourceBody542_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_313

def sourceBody542_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_314

def sourceBody542_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_241 sourceBody542_315

def sourceBody542_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_205 sourceBody542_316

def sourceBody542_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_317

def sourceBody542_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_318

def sourceBody542_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_199 sourceBody542_319

def sourceBody542_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_320

def sourceBody542_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_321

def sourceBody542_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_194 sourceBody542_322

def sourceBody542_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_90 sourceBody542_323

def sourceBody542_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_324

def sourceBody542_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_124 sourceBody542_325

def sourceBody542_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_326

def sourceBody542_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_327

def sourceBody542_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_119 sourceBody542_328

def sourceBody542_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_86 sourceBody542_329

def sourceBody542_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_330

def sourceBody542_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_331

def sourceBody542_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_72 sourceBody542_332

def sourceBody542_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_333

def sourceBody542_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_334

def sourceBody542_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_335

def sourceBody542_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_336

def sourceBody542_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_64 sourceBody542_337

def sourceBody542_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_338

def sourceBody542_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_339

def sourceBody542_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_340

def sourceBody542_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_341

def sourceBody542_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_44 sourceBody542_342

def sourceBody542_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_343

def sourceBody542_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_344

def sourceBody542_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_32 sourceBody542_345

def sourceBody542_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_9 sourceBody542_346

def sourceBody542_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_347

def sourceBody542_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_348

def sourceBody542_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_349

def sourceBody542_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_350

def sourceBody542_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_351

def sourceBody542_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_352

def sourceBody542_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_353

def sourceBody542_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_354

def sourceBody542_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_5 sourceBody542_355

def sourceBody542_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_356

def sourceBody542_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_357

def sourceBody542_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_358

def sourceBody542_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_359

def sourceBody542_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_360

def sourceBody542_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_361

def sourceBody542_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_362

def sourceBody542_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody542_0 sourceBody542_363

def source542 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (542, 2, sourceBody542_364)
end InitECandidate.Proofs.WordStages
