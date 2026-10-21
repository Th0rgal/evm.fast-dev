import InitECandidate.Proofs.WordStages.Source530
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody546_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody546_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 74

def sourceBody546_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody546_0, 546, 2)) (some 488) ([]) (some (74, sourceBody546_1, 546, 3))

def sourceBody546_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody546_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_2 sourceBody546_3

def sourceBody546_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_4 sourceBody546_0

def sourceBody546_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_5

def sourceBody546_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_6

def sourceBody546_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody546_9 : WordLangProgHOL (BitVec 64) :=
.call (some (([26, 74, 14, 62]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody546_0, 546, 4)) (some 471) ([]) (some (38, sourceBody546_8, 546, 5))

def sourceBody546_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_9 sourceBody546_3

def sourceBody546_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_10 sourceBody546_0

def sourceBody546_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody546_13 : WordLangProgHOL (BitVec 64) :=
.call (some (([38, 86, 8, 56]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 6)) (some 471) ([]) (some (32, sourceBody546_12, 546, 7))

def sourceBody546_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_13 sourceBody546_3

def sourceBody546_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_14 sourceBody546_0

def sourceBody546_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 280#64]))

def sourceBody546_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 26)

def sourceBody546_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 74)

def sourceBody546_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 14)

def sourceBody546_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 92 (Flapjack.WordLangExpHOL.var 62)

def sourceBody546_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 32)

def sourceBody546_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody546_23 : WordLangProgHOL (BitVec 64) :=
.call (some (([80]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 8)) (some 147) ([20, 68, 44, 92, 4]) (some (20, sourceBody546_22, 546, 9))

def sourceBody546_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_23 sourceBody546_3

def sourceBody546_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_24 sourceBody546_0

def sourceBody546_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_21 sourceBody546_25

def sourceBody546_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_20 sourceBody546_26

def sourceBody546_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_19 sourceBody546_27

def sourceBody546_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_18 sourceBody546_28

def sourceBody546_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_17 sourceBody546_29

def sourceBody546_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_30

def sourceBody546_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_31

def sourceBody546_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80
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

def sourceBody546_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 80)

def sourceBody546_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 32)

def sourceBody546_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 68

def sourceBody546_37 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 10)) (some 543) ([68, 44]) (some (68, sourceBody546_36, 546, 11))

def sourceBody546_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_37 sourceBody546_3

def sourceBody546_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_38 sourceBody546_0

def sourceBody546_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_35 sourceBody546_39

def sourceBody546_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_34 sourceBody546_40

def sourceBody546_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.const 100#64)

def sourceBody546_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 92 (Flapjack.WordLangExpHOL.var 20)

def sourceBody546_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 92 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody546_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 92 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_47 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 92 (Flapjack.WordRegImm.reg 4) sourceBody546_45 sourceBody546_46

def sourceBody546_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_47 sourceBody546_3

def sourceBody546_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 92)

def sourceBody546_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.const 2100#64)

def sourceBody546_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_50 sourceBody546_0

def sourceBody546_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_51 sourceBody546_0

def sourceBody546_53 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 52 (Flapjack.WordRegImm.imm 0#64) sourceBody546_52 sourceBody546_0

def sourceBody546_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_53 sourceBody546_3

def sourceBody546_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_54 sourceBody546_0

def sourceBody546_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_49 sourceBody546_55

def sourceBody546_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_48 sourceBody546_56

def sourceBody546_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_44 sourceBody546_57

def sourceBody546_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_43 sourceBody546_58

def sourceBody546_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 92 (Flapjack.WordLangExpHOL.var 68)

def sourceBody546_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.const 2300#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody546_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 92

def sourceBody546_63 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 12)) (some 93) ([92, 4]) (some (92, sourceBody546_62, 546, 13))

def sourceBody546_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_63 sourceBody546_3

def sourceBody546_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_64 sourceBody546_0

def sourceBody546_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_61 sourceBody546_65

def sourceBody546_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_60 sourceBody546_66

def sourceBody546_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 44)

def sourceBody546_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody546_70 : WordLangProgHOL (BitVec 64) :=
.call (some (([92]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 14)) (some 465) ([4]) (some (4, sourceBody546_69, 546, 15))

def sourceBody546_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_70 sourceBody546_3

def sourceBody546_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_71 sourceBody546_0

def sourceBody546_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_68 sourceBody546_72

def sourceBody546_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_73

def sourceBody546_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_74

def sourceBody546_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 68)

def sourceBody546_77 : WordLangProgHOL (BitVec 64) :=
.call (some (([92]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 16)) (some 466) ([4]) (some (4, sourceBody546_69, 546, 17))

def sourceBody546_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_77 sourceBody546_3

def sourceBody546_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_78 sourceBody546_0

def sourceBody546_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_76 sourceBody546_79

def sourceBody546_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_80

def sourceBody546_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_81

def sourceBody546_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_75 sourceBody546_82

def sourceBody546_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 20)

def sourceBody546_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody546_87 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.WordRegImm.reg 52) sourceBody546_86 sourceBody546_44

def sourceBody546_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_87 sourceBody546_3

def sourceBody546_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 4)

def sourceBody546_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 80)

def sourceBody546_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 32)

def sourceBody546_92 : WordLangProgHOL (BitVec 64) :=
.call (some (([92]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 18)) (some 544) ([4, 52]) (some (4, sourceBody546_69, 546, 19))

def sourceBody546_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_92 sourceBody546_3

def sourceBody546_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_93 sourceBody546_0

def sourceBody546_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_91 sourceBody546_94

def sourceBody546_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_90 sourceBody546_95

def sourceBody546_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_96

def sourceBody546_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_97

def sourceBody546_99 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody546_98 sourceBody546_0

def sourceBody546_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_99 sourceBody546_3

def sourceBody546_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_100 sourceBody546_0

def sourceBody546_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_89 sourceBody546_101

def sourceBody546_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_88 sourceBody546_102

def sourceBody546_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_85 sourceBody546_103

def sourceBody546_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_84 sourceBody546_104

def sourceBody546_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_83 sourceBody546_105

def sourceBody546_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 80)

def sourceBody546_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 32)

def sourceBody546_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 78

def sourceBody546_110 : WordLangProgHOL (BitVec 64) :=
.call (some (([92, 4, 52, 30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 20)) (some 407) ([78, 18]) (some (78, sourceBody546_109, 546, 21))

def sourceBody546_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_110 sourceBody546_3

def sourceBody546_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_111 sourceBody546_0

def sourceBody546_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_108 sourceBody546_112

def sourceBody546_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_107 sourceBody546_113

def sourceBody546_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 90 (Flapjack.WordLangExpHOL.var 80)

def sourceBody546_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 32)

def sourceBody546_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 90

def sourceBody546_118 : WordLangProgHOL (BitVec 64) :=
.call (some (([78, 18, 66, 42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 22)) (some 406) ([90, 12]) (some (90, sourceBody546_117, 546, 23))

def sourceBody546_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_118 sourceBody546_3

def sourceBody546_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_119 sourceBody546_0

def sourceBody546_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_116 sourceBody546_120

def sourceBody546_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_115 sourceBody546_121

def sourceBody546_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 92)

def sourceBody546_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 4)

def sourceBody546_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 52)

def sourceBody546_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 84 (Flapjack.WordLangExpHOL.var 30)

def sourceBody546_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 78)

def sourceBody546_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 18)

def sourceBody546_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 66)

def sourceBody546_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.var 42)

def sourceBody546_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody546_132 : WordLangProgHOL (BitVec 64) :=
.call (some (([90]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 24)) (some 105) ([12, 60, 36, 84, 24, 72, 48, 96]) (some (12, sourceBody546_131, 546, 25))

def sourceBody546_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_132 sourceBody546_3

def sourceBody546_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_133 sourceBody546_0

def sourceBody546_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_130 sourceBody546_134

def sourceBody546_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_129 sourceBody546_135

def sourceBody546_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_128 sourceBody546_136

def sourceBody546_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_127 sourceBody546_137

def sourceBody546_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_126 sourceBody546_138

def sourceBody546_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_125 sourceBody546_139

def sourceBody546_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_124 sourceBody546_140

def sourceBody546_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_123 sourceBody546_141

def sourceBody546_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 78)

def sourceBody546_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 18)

def sourceBody546_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 84 (Flapjack.WordLangExpHOL.var 66)

def sourceBody546_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 42)

def sourceBody546_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 38)

def sourceBody546_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 86)

def sourceBody546_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.var 8)

def sourceBody546_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 56)

def sourceBody546_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 60

def sourceBody546_152 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 26)) (some 105) ([60, 36, 84, 24, 72, 48, 96, 2]) (some (60, sourceBody546_151, 546, 27))

def sourceBody546_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_152 sourceBody546_3

def sourceBody546_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_153 sourceBody546_0

def sourceBody546_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_150 sourceBody546_154

def sourceBody546_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_149 sourceBody546_155

def sourceBody546_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_148 sourceBody546_156

def sourceBody546_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_147 sourceBody546_157

def sourceBody546_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_146 sourceBody546_158

def sourceBody546_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_145 sourceBody546_159

def sourceBody546_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_144 sourceBody546_160

def sourceBody546_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_143 sourceBody546_161

def sourceBody546_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 92)

def sourceBody546_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 84 (Flapjack.WordLangExpHOL.var 4)

def sourceBody546_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 52)

def sourceBody546_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 30)

def sourceBody546_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 38)

def sourceBody546_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.var 86)

def sourceBody546_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 8)

def sourceBody546_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 56)

def sourceBody546_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody546_172 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 28)) (some 105) ([36, 84, 24, 72, 48, 96, 2, 50]) (some (36, sourceBody546_171, 546, 29))

def sourceBody546_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_172 sourceBody546_3

def sourceBody546_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_173 sourceBody546_0

def sourceBody546_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_170 sourceBody546_174

def sourceBody546_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_169 sourceBody546_175

def sourceBody546_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_168 sourceBody546_176

def sourceBody546_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_167 sourceBody546_177

def sourceBody546_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_166 sourceBody546_178

def sourceBody546_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_165 sourceBody546_179

def sourceBody546_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_164 sourceBody546_180

def sourceBody546_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_163 sourceBody546_181

def sourceBody546_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 84 (Flapjack.WordLangExpHOL.var 92)

def sourceBody546_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody546_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 52)

def sourceBody546_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 30)

def sourceBody546_187 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 84

def sourceBody546_188 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 30)) (some 102) ([84, 24, 72, 48]) (some (84, sourceBody546_187, 546, 31))

def sourceBody546_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_188 sourceBody546_3

def sourceBody546_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_189 sourceBody546_0

def sourceBody546_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_186 sourceBody546_190

def sourceBody546_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_185 sourceBody546_191

def sourceBody546_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_184 sourceBody546_192

def sourceBody546_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_183 sourceBody546_193

def sourceBody546_195 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody546_196 : WordLangProgHOL (BitVec 64) :=
.call (some (([84]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 32)) (some 102) ([24, 72, 48, 96]) (some (24, sourceBody546_195, 546, 33))

def sourceBody546_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_196 sourceBody546_3

def sourceBody546_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_197 sourceBody546_0

def sourceBody546_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_130 sourceBody546_198

def sourceBody546_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_129 sourceBody546_199

def sourceBody546_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_128 sourceBody546_200

def sourceBody546_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_127 sourceBody546_201

def sourceBody546_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 72

def sourceBody546_204 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 34)) (some 102) ([72, 48, 96, 2]) (some (72, sourceBody546_203, 546, 35))

def sourceBody546_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_204 sourceBody546_3

def sourceBody546_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_205 sourceBody546_0

def sourceBody546_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_150 sourceBody546_206

def sourceBody546_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_149 sourceBody546_207

def sourceBody546_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_148 sourceBody546_208

def sourceBody546_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_147 sourceBody546_209

def sourceBody546_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 68)

def sourceBody546_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.var 90)

def sourceBody546_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_214 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody546_215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_216 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 96 (Flapjack.WordRegImm.reg 2) sourceBody546_214 sourceBody546_215

def sourceBody546_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_216 sourceBody546_3

def sourceBody546_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_219 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 96)

def sourceBody546_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody546_221 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.reg 76) sourceBody546_220 sourceBody546_218

def sourceBody546_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_221 sourceBody546_3

def sourceBody546_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 12)

def sourceBody546_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_225 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody546_226 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_227 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 64 (Flapjack.WordRegImm.reg 40) sourceBody546_225 sourceBody546_226

def sourceBody546_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_227 sourceBody546_3

def sourceBody546_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_230 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 64)

def sourceBody546_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody546_232 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 58) sourceBody546_231 sourceBody546_229

def sourceBody546_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_232 sourceBody546_3

def sourceBody546_234 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.var 10])

def sourceBody546_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 72, Flapjack.WordLangExpHOL.const 10000#64])

def sourceBody546_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 48)

def sourceBody546_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_236 sourceBody546_0

def sourceBody546_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_237 sourceBody546_0

def sourceBody546_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_235 sourceBody546_238

def sourceBody546_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_239

def sourceBody546_241 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.imm 0#64) sourceBody546_240 sourceBody546_0

def sourceBody546_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_241 sourceBody546_3

def sourceBody546_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_242 sourceBody546_0

def sourceBody546_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_234 sourceBody546_243

def sourceBody546_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_233 sourceBody546_244

def sourceBody546_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_230 sourceBody546_245

def sourceBody546_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_229 sourceBody546_246

def sourceBody546_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_228 sourceBody546_247

def sourceBody546_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_224 sourceBody546_248

def sourceBody546_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_223 sourceBody546_249

def sourceBody546_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_222 sourceBody546_250

def sourceBody546_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_219 sourceBody546_251

def sourceBody546_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_218 sourceBody546_252

def sourceBody546_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_217 sourceBody546_253

def sourceBody546_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_213 sourceBody546_254

def sourceBody546_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_212 sourceBody546_255

def sourceBody546_257 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.var 12)

def sourceBody546_258 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 96 (Flapjack.WordRegImm.reg 2) sourceBody546_214 sourceBody546_215

def sourceBody546_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_258 sourceBody546_3

def sourceBody546_260 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 96)

def sourceBody546_261 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.var 36)

def sourceBody546_262 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 84)

def sourceBody546_263 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.var 24)

def sourceBody546_264 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_265 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody546_266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_267 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 82 (Flapjack.WordRegImm.reg 22) sourceBody546_265 sourceBody546_266

def sourceBody546_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_267 sourceBody546_3

def sourceBody546_269 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_270 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 94 (Flapjack.WordLangExpHOL.var 82)

def sourceBody546_271 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody546_272 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 46 (Flapjack.WordRegImm.reg 94) sourceBody546_271 sourceBody546_269

def sourceBody546_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_272 sourceBody546_3

def sourceBody546_274 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 46])

def sourceBody546_275 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 96#64])

def sourceBody546_276 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96
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
            Flapjack.WordLangExpHOL.const 96#64]),
      Flapjack.WordLangExpHOL.const 11616#64])

def sourceBody546_277 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 96)

def sourceBody546_278 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 48) 2

def sourceBody546_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_278 sourceBody546_0

def sourceBody546_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_277 sourceBody546_279

def sourceBody546_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_280 sourceBody546_0

def sourceBody546_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_276 sourceBody546_281

def sourceBody546_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_282

def sourceBody546_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_275 sourceBody546_283

def sourceBody546_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_284

def sourceBody546_286 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody546_285 sourceBody546_0

def sourceBody546_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_286 sourceBody546_3

def sourceBody546_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_287 sourceBody546_0

def sourceBody546_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_274 sourceBody546_288

def sourceBody546_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_273 sourceBody546_289

def sourceBody546_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_270 sourceBody546_290

def sourceBody546_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_269 sourceBody546_291

def sourceBody546_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_268 sourceBody546_292

def sourceBody546_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_264 sourceBody546_293

def sourceBody546_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_263 sourceBody546_294

def sourceBody546_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_233 sourceBody546_295

def sourceBody546_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_230 sourceBody546_296

def sourceBody546_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_229 sourceBody546_297

def sourceBody546_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_228 sourceBody546_298

def sourceBody546_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_224 sourceBody546_299

def sourceBody546_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_262 sourceBody546_300

def sourceBody546_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_222 sourceBody546_301

def sourceBody546_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_219 sourceBody546_302

def sourceBody546_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_218 sourceBody546_303

def sourceBody546_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_259 sourceBody546_304

def sourceBody546_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_213 sourceBody546_305

def sourceBody546_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_261 sourceBody546_306

def sourceBody546_308 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 64 (Flapjack.WordRegImm.reg 40) sourceBody546_225 sourceBody546_226

def sourceBody546_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_308 sourceBody546_3

def sourceBody546_310 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
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
            Flapjack.WordLangExpHOL.const 96#64]),
      Flapjack.WordLangExpHOL.const 11616#64])

def sourceBody546_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_310 sourceBody546_281

def sourceBody546_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_311

def sourceBody546_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_275 sourceBody546_312

def sourceBody546_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_313

def sourceBody546_315 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.imm 0#64) sourceBody546_314 sourceBody546_0

def sourceBody546_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_315 sourceBody546_3

def sourceBody546_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_316 sourceBody546_0

def sourceBody546_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_234 sourceBody546_317

def sourceBody546_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_233 sourceBody546_318

def sourceBody546_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_230 sourceBody546_319

def sourceBody546_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_229 sourceBody546_320

def sourceBody546_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_309 sourceBody546_321

def sourceBody546_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_224 sourceBody546_322

def sourceBody546_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_262 sourceBody546_323

def sourceBody546_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_222 sourceBody546_324

def sourceBody546_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_219 sourceBody546_325

def sourceBody546_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_218 sourceBody546_326

def sourceBody546_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_259 sourceBody546_327

def sourceBody546_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_213 sourceBody546_328

def sourceBody546_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_261 sourceBody546_329

def sourceBody546_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_307 sourceBody546_330

def sourceBody546_332 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.var 60)

def sourceBody546_333 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96
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
            Flapjack.WordLangExpHOL.const 96#64]),
      Flapjack.WordLangExpHOL.const 10000#64])

def sourceBody546_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_333 sourceBody546_281

def sourceBody546_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_334

def sourceBody546_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_275 sourceBody546_335

def sourceBody546_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_336

def sourceBody546_338 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 50 (Flapjack.WordRegImm.imm 0#64) sourceBody546_337 sourceBody546_0

def sourceBody546_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_338 sourceBody546_3

def sourceBody546_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_339 sourceBody546_0

def sourceBody546_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_260 sourceBody546_340

def sourceBody546_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_217 sourceBody546_341

def sourceBody546_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_213 sourceBody546_342

def sourceBody546_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_332 sourceBody546_343

def sourceBody546_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_331 sourceBody546_344

def sourceBody546_346 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 50 (Flapjack.WordRegImm.imm 0#64) sourceBody546_345 sourceBody546_0

def sourceBody546_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_346 sourceBody546_3

def sourceBody546_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_347 sourceBody546_0

def sourceBody546_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_260 sourceBody546_348

def sourceBody546_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_259 sourceBody546_349

def sourceBody546_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_213 sourceBody546_350

def sourceBody546_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_257 sourceBody546_351

def sourceBody546_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_256 sourceBody546_352

def sourceBody546_354 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_355 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 90)

def sourceBody546_356 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_357 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody546_358 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.WordRegImm.reg 50) sourceBody546_357 sourceBody546_213

def sourceBody546_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_358 sourceBody546_3

def sourceBody546_360 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_361 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody546_362 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody546_363 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 76 (Flapjack.WordRegImm.reg 16) sourceBody546_362 sourceBody546_360

def sourceBody546_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_363 sourceBody546_3

def sourceBody546_365 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 12)

def sourceBody546_366 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 88 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_367 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody546_368 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 40 (Flapjack.WordRegImm.reg 88) sourceBody546_367 sourceBody546_224

def sourceBody546_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_368 sourceBody546_3

def sourceBody546_370 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_371 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 40)

def sourceBody546_372 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody546_373 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 58 (Flapjack.WordRegImm.reg 34) sourceBody546_372 sourceBody546_370

def sourceBody546_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_373 sourceBody546_3

def sourceBody546_375 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 36)

def sourceBody546_376 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_377 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody546_378 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.reg 70) sourceBody546_377 sourceBody546_264

def sourceBody546_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_378 sourceBody546_3

def sourceBody546_380 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 94 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody546_381 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 22)

def sourceBody546_382 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 94 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody546_383 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 94 (Flapjack.WordRegImm.reg 6) sourceBody546_382 sourceBody546_380

def sourceBody546_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_383 sourceBody546_3

def sourceBody546_385 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.var 76, Flapjack.WordLangExpHOL.var 58, Flapjack.WordLangExpHOL.var 94])

def sourceBody546_386 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 97920#64)

def sourceBody546_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_386 sourceBody546_0

def sourceBody546_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_387 sourceBody546_0

def sourceBody546_389 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 54 (Flapjack.WordRegImm.imm 0#64) sourceBody546_388 sourceBody546_0

def sourceBody546_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_389 sourceBody546_3

def sourceBody546_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_390 sourceBody546_0

def sourceBody546_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_385 sourceBody546_391

def sourceBody546_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_384 sourceBody546_392

def sourceBody546_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_381 sourceBody546_393

def sourceBody546_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_380 sourceBody546_394

def sourceBody546_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_379 sourceBody546_395

def sourceBody546_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_376 sourceBody546_396

def sourceBody546_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_375 sourceBody546_397

def sourceBody546_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_374 sourceBody546_398

def sourceBody546_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_371 sourceBody546_399

def sourceBody546_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_370 sourceBody546_400

def sourceBody546_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_369 sourceBody546_401

def sourceBody546_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_366 sourceBody546_402

def sourceBody546_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_365 sourceBody546_403

def sourceBody546_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_364 sourceBody546_404

def sourceBody546_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_361 sourceBody546_405

def sourceBody546_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_360 sourceBody546_406

def sourceBody546_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_359 sourceBody546_407

def sourceBody546_409 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_356 sourceBody546_408

def sourceBody546_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_355 sourceBody546_409

def sourceBody546_411 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 12)

def sourceBody546_412 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 2 (Flapjack.WordRegImm.reg 50) sourceBody546_357 sourceBody546_213

def sourceBody546_413 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_412 sourceBody546_3

def sourceBody546_414 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 60)

def sourceBody546_415 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.reg 88) sourceBody546_367 sourceBody546_224

def sourceBody546_416 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_415 sourceBody546_3

def sourceBody546_417 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 97920#64)

def sourceBody546_418 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody546_419 : WordLangProgHOL (BitVec 64) :=
.call (some (([96]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 36)) (some 468) ([2]) (some (2, sourceBody546_418, 546, 37))

def sourceBody546_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_419 sourceBody546_3

def sourceBody546_421 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_420 sourceBody546_0

def sourceBody546_422 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_417 sourceBody546_421

def sourceBody546_423 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_422

def sourceBody546_424 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_423

def sourceBody546_425 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 54 (Flapjack.WordRegImm.imm 0#64) sourceBody546_424 sourceBody546_0

def sourceBody546_426 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_425 sourceBody546_3

def sourceBody546_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_426 sourceBody546_0

def sourceBody546_428 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_385 sourceBody546_427

def sourceBody546_429 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_384 sourceBody546_428

def sourceBody546_430 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_381 sourceBody546_429

def sourceBody546_431 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_380 sourceBody546_430

def sourceBody546_432 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_379 sourceBody546_431

def sourceBody546_433 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_376 sourceBody546_432

def sourceBody546_434 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_375 sourceBody546_433

def sourceBody546_435 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_374 sourceBody546_434

def sourceBody546_436 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_371 sourceBody546_435

def sourceBody546_437 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_370 sourceBody546_436

def sourceBody546_438 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_416 sourceBody546_437

def sourceBody546_439 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_366 sourceBody546_438

def sourceBody546_440 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_414 sourceBody546_439

def sourceBody546_441 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_364 sourceBody546_440

def sourceBody546_442 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_361 sourceBody546_441

def sourceBody546_443 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_360 sourceBody546_442

def sourceBody546_444 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_413 sourceBody546_443

def sourceBody546_445 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_356 sourceBody546_444

def sourceBody546_446 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_411 sourceBody546_445

def sourceBody546_447 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_410 sourceBody546_446

def sourceBody546_448 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 72, Flapjack.WordLangExpHOL.var 68])

def sourceBody546_449 : WordLangProgHOL (BitVec 64) :=
.call (some (([96]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 38)) (some 466) ([2]) (some (2, sourceBody546_418, 546, 39))

def sourceBody546_450 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_449 sourceBody546_3

def sourceBody546_451 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_450 sourceBody546_0

def sourceBody546_452 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_448 sourceBody546_451

def sourceBody546_453 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_452

def sourceBody546_454 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_453

def sourceBody546_455 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_447 sourceBody546_454

def sourceBody546_456 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 48)

def sourceBody546_457 : WordLangProgHOL (BitVec 64) :=
.call (some (([96]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody546_0, 546, 40)) (some 467) ([2]) (some (2, sourceBody546_418, 546, 41))

def sourceBody546_458 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_457 sourceBody546_3

def sourceBody546_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_458 sourceBody546_0

def sourceBody546_460 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_456 sourceBody546_459

def sourceBody546_461 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_460

def sourceBody546_462 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_461

def sourceBody546_463 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_455 sourceBody546_462

def sourceBody546_464 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 80)

def sourceBody546_465 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 32)

def sourceBody546_466 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 38)

def sourceBody546_467 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 86)

def sourceBody546_468 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody546_469 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 56)

def sourceBody546_470 : WordLangProgHOL (BitVec 64) :=
.call (some (([96]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody546_0, 546, 42)) (some 416) ([2, 50, 28, 76, 16, 64]) (some (2, sourceBody546_418, 546, 43))

def sourceBody546_471 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_470 sourceBody546_3

def sourceBody546_472 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_471 sourceBody546_0

def sourceBody546_473 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_469 sourceBody546_472

def sourceBody546_474 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_468 sourceBody546_473

def sourceBody546_475 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_467 sourceBody546_474

def sourceBody546_476 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_466 sourceBody546_475

def sourceBody546_477 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_465 sourceBody546_476

def sourceBody546_478 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_464 sourceBody546_477

def sourceBody546_479 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_478

def sourceBody546_480 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_479

def sourceBody546_481 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_463 sourceBody546_480

def sourceBody546_482 : WordLangProgHOL (BitVec 64) :=
.call (some (([96]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody546_0, 546, 44)) (some 486) ([2]) (some (2, sourceBody546_418, 546, 45))

def sourceBody546_483 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_482 sourceBody546_3

def sourceBody546_484 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_483 sourceBody546_0

def sourceBody546_485 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_357 sourceBody546_484

def sourceBody546_486 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_485

def sourceBody546_487 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_486

def sourceBody546_488 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_481 sourceBody546_487

def sourceBody546_489 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [96]

def sourceBody546_490 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_489 sourceBody546_0

def sourceBody546_491 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_215 sourceBody546_490

def sourceBody546_492 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_488 sourceBody546_491

def sourceBody546_493 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_354 sourceBody546_492

def sourceBody546_494 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_493

def sourceBody546_495 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_353 sourceBody546_494

def sourceBody546_496 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_211 sourceBody546_495

def sourceBody546_497 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_496

def sourceBody546_498 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_210 sourceBody546_497

def sourceBody546_499 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_498

def sourceBody546_500 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_499

def sourceBody546_501 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_202 sourceBody546_500

def sourceBody546_502 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_501

def sourceBody546_503 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_502

def sourceBody546_504 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_194 sourceBody546_503

def sourceBody546_505 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_504

def sourceBody546_506 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_505

def sourceBody546_507 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_182 sourceBody546_506

def sourceBody546_508 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_507

def sourceBody546_509 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_508

def sourceBody546_510 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_162 sourceBody546_509

def sourceBody546_511 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_510

def sourceBody546_512 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_511

def sourceBody546_513 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_142 sourceBody546_512

def sourceBody546_514 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_513

def sourceBody546_515 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_514

def sourceBody546_516 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_122 sourceBody546_515

def sourceBody546_517 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_516

def sourceBody546_518 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_517

def sourceBody546_519 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_518

def sourceBody546_520 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_519

def sourceBody546_521 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_520

def sourceBody546_522 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_521

def sourceBody546_523 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_522

def sourceBody546_524 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_523

def sourceBody546_525 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_114 sourceBody546_524

def sourceBody546_526 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_525

def sourceBody546_527 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_526

def sourceBody546_528 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_527

def sourceBody546_529 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_528

def sourceBody546_530 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_529

def sourceBody546_531 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_530

def sourceBody546_532 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_531

def sourceBody546_533 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_532

def sourceBody546_534 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_106 sourceBody546_533

def sourceBody546_535 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_67 sourceBody546_534

def sourceBody546_536 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_535

def sourceBody546_537 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_536

def sourceBody546_538 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_59 sourceBody546_537

def sourceBody546_539 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_42 sourceBody546_538

def sourceBody546_540 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_539

def sourceBody546_541 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_41 sourceBody546_540

def sourceBody546_542 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_541

def sourceBody546_543 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_542

def sourceBody546_544 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_33 sourceBody546_543

def sourceBody546_545 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_544

def sourceBody546_546 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_32 sourceBody546_545

def sourceBody546_547 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_16 sourceBody546_546

def sourceBody546_548 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_547

def sourceBody546_549 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_15 sourceBody546_548

def sourceBody546_550 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_549

def sourceBody546_551 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_550

def sourceBody546_552 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_551

def sourceBody546_553 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_552

def sourceBody546_554 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_553

def sourceBody546_555 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_554

def sourceBody546_556 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_555

def sourceBody546_557 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_556

def sourceBody546_558 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_11 sourceBody546_557

def sourceBody546_559 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_558

def sourceBody546_560 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_559

def sourceBody546_561 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_560

def sourceBody546_562 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_561

def sourceBody546_563 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_562

def sourceBody546_564 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_563

def sourceBody546_565 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_564

def sourceBody546_566 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_0 sourceBody546_565

def sourceBody546_567 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody546_7 sourceBody546_566

def source546 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (546, 1, sourceBody546_567)
end InitECandidate.Proofs.WordStages
