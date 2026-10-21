import InitECandidate.Proofs.WordStages.Source830
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody846_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody846_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 176#64]),
        Flapjack.WordLangExpHOL.const 72#64]))

def sourceBody846_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 62

def sourceBody846_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody846_0, 846, 2)) (some 199) ([62]) (some (62, sourceBody846_2, 846, 3))

def sourceBody846_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody846_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_3 sourceBody846_4

def sourceBody846_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_5 sourceBody846_0

def sourceBody846_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_1 sourceBody846_6

def sourceBody846_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody846_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody846_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody846_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([62]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 4)) (some 182) ([14, 52]) (some (14, sourceBody846_10, 846, 5))

def sourceBody846_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_11 sourceBody846_4

def sourceBody846_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_12 sourceBody846_0

def sourceBody846_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_9 sourceBody846_13

def sourceBody846_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_8 sourceBody846_14

def sourceBody846_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 176#64]),
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody846_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 176#64]),
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody846_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 168#64]),
        Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody846_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody846_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 8)

def sourceBody846_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 72)

def sourceBody846_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 30 (Flapjack.WordRegImm.reg 68) sourceBody846_23 sourceBody846_24

def sourceBody846_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_25 sourceBody846_4

def sourceBody846_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 30)

def sourceBody846_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody846_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 8)

def sourceBody846_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody846_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([46, 30, 68]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 6)) (some 197) ([20, 58]) (some (20, sourceBody846_30, 846, 7))

def sourceBody846_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_31 sourceBody846_4

def sourceBody846_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_32 sourceBody846_0

def sourceBody846_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_29 sourceBody846_33

def sourceBody846_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_28 sourceBody846_34

def sourceBody846_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 46)

def sourceBody846_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 58 (Flapjack.WordRegImm.reg 38) sourceBody846_38 sourceBody846_39

def sourceBody846_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_40 sourceBody846_4

def sourceBody846_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 58)

def sourceBody846_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 68)

def sourceBody846_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 24)

def sourceBody846_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 20)

def sourceBody846_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 78

def sourceBody846_47 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 8)) (some 187) ([78, 6]) (some (78, sourceBody846_46, 846, 9))

def sourceBody846_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_47 sourceBody846_4

def sourceBody846_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_48 sourceBody846_0

def sourceBody846_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_45 sourceBody846_49

def sourceBody846_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_44 sourceBody846_50

def sourceBody846_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 38)

def sourceBody846_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_56 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.WordRegImm.reg 44) sourceBody846_54 sourceBody846_55

def sourceBody846_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_56 sourceBody846_4

def sourceBody846_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 6)

def sourceBody846_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 24)

def sourceBody846_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 20)

def sourceBody846_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody846_63 : WordLangProgHOL (BitVec 64) :=
.call (some (([78]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 10)) (some 192) ([6, 44, 28]) (some (6, sourceBody846_62, 846, 11))

def sourceBody846_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_63 sourceBody846_4

def sourceBody846_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_64 sourceBody846_0

def sourceBody846_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_61 sourceBody846_65

def sourceBody846_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_60 sourceBody846_66

def sourceBody846_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_59 sourceBody846_67

def sourceBody846_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_68

def sourceBody846_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_69

def sourceBody846_71 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody846_70 sourceBody846_0

def sourceBody846_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_71 sourceBody846_4

def sourceBody846_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_72 sourceBody846_0

def sourceBody846_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_58 sourceBody846_73

def sourceBody846_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_57 sourceBody846_74

def sourceBody846_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_53 sourceBody846_75

def sourceBody846_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_52 sourceBody846_76

def sourceBody846_78 : WordLangProgHOL (BitVec 64) :=
.call (some (([78]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 12)) (some 395) ([6]) (some (6, sourceBody846_62, 846, 13))

def sourceBody846_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_78 sourceBody846_4

def sourceBody846_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_79 sourceBody846_0

def sourceBody846_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_45 sourceBody846_80

def sourceBody846_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 34)

def sourceBody846_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 78)

def sourceBody846_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody846_86 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 14)) (some 305) ([44, 28, 66]) (some (44, sourceBody846_85, 846, 15))

def sourceBody846_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_86 sourceBody846_4

def sourceBody846_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_87 sourceBody846_0

def sourceBody846_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_84 sourceBody846_88

def sourceBody846_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_83 sourceBody846_89

def sourceBody846_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_82 sourceBody846_90

def sourceBody846_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody846_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody846_94 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 16)) (some 68) ([28]) (some (28, sourceBody846_93, 846, 17))

def sourceBody846_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_94 sourceBody846_4

def sourceBody846_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_95 sourceBody846_0

def sourceBody846_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_92 sourceBody846_96

def sourceBody846_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody846_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody846_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_103 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 18 (Flapjack.WordRegImm.reg 56) sourceBody846_101 sourceBody846_102

def sourceBody846_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_103 sourceBody846_4

def sourceBody846_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 18)

def sourceBody846_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 58, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody846_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 66)

def sourceBody846_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 18)

def sourceBody846_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_112 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 36 (Flapjack.WordRegImm.reg 76) sourceBody846_110 sourceBody846_111

def sourceBody846_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_112 sourceBody846_4

def sourceBody846_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 36)

def sourceBody846_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 58)

def sourceBody846_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 66)

def sourceBody846_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody846_118 : WordLangProgHOL (BitVec 64) :=
.call (some (([56, 36, 76]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 18)) (some 197) ([12, 50]) (some (12, sourceBody846_117, 846, 19))

def sourceBody846_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_118 sourceBody846_4

def sourceBody846_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_119 sourceBody846_0

def sourceBody846_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_116 sourceBody846_120

def sourceBody846_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_115 sourceBody846_121

def sourceBody846_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 56)

def sourceBody846_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_127 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 50 (Flapjack.WordRegImm.reg 32) sourceBody846_125 sourceBody846_126

def sourceBody846_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_127 sourceBody846_4

def sourceBody846_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 50)

def sourceBody846_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 76))

def sourceBody846_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 76, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody846_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 76, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody846_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 76, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody846_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 12)

def sourceBody846_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 50)

def sourceBody846_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 32)

def sourceBody846_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 70)

def sourceBody846_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 60

def sourceBody846_139 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 20)) (some 102) ([60, 40, 80, 4]) (some (60, sourceBody846_138, 846, 21))

def sourceBody846_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_139 sourceBody846_4

def sourceBody846_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_140 sourceBody846_0

def sourceBody846_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_137 sourceBody846_141

def sourceBody846_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_136 sourceBody846_142

def sourceBody846_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_135 sourceBody846_143

def sourceBody846_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_134 sourceBody846_144

def sourceBody846_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 28)

def sourceBody846_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_150 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 40 (Flapjack.WordRegImm.reg 80) sourceBody846_148 sourceBody846_149

def sourceBody846_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_150 sourceBody846_4

def sourceBody846_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 40)

def sourceBody846_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_155 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.reg 26) sourceBody846_154 sourceBody846_152

def sourceBody846_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_155 sourceBody846_4

def sourceBody846_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody846_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_161 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 54) sourceBody846_159 sourceBody846_160

def sourceBody846_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_161 sourceBody846_4

def sourceBody846_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody846_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_166 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 74 (Flapjack.WordRegImm.reg 10) sourceBody846_165 sourceBody846_163

def sourceBody846_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_166 sourceBody846_4

def sourceBody846_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.var 74])

def sourceBody846_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 12)

def sourceBody846_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 50)

def sourceBody846_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 32)

def sourceBody846_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 70)

def sourceBody846_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 44, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody846_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody846_175 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 22)) (some 148) ([40, 80, 4, 42, 26]) (some (40, sourceBody846_174, 846, 23))

def sourceBody846_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_175 sourceBody846_4

def sourceBody846_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_176 sourceBody846_0

def sourceBody846_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_173 sourceBody846_177

def sourceBody846_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_172 sourceBody846_178

def sourceBody846_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_171 sourceBody846_179

def sourceBody846_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_170 sourceBody846_180

def sourceBody846_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_169 sourceBody846_181

def sourceBody846_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 44, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody846_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 44, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody846_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 60)

def sourceBody846_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 80

def sourceBody846_187 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 24)) (some 176) ([80, 4, 42]) (some (80, sourceBody846_186, 846, 25))

def sourceBody846_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_187 sourceBody846_4

def sourceBody846_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_188 sourceBody846_0

def sourceBody846_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_185 sourceBody846_189

def sourceBody846_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_184 sourceBody846_190

def sourceBody846_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_183 sourceBody846_191

def sourceBody846_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 40#64)

def sourceBody846_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody846_195 : WordLangProgHOL (BitVec 64) :=
.call (some (([80]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 26)) (some 68) ([4]) (some (4, sourceBody846_194, 846, 27))

def sourceBody846_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_195 sourceBody846_4

def sourceBody846_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_196 sourceBody846_0

def sourceBody846_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_193 sourceBody846_197

def sourceBody846_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 80)

def sourceBody846_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 44, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody846_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 40)

def sourceBody846_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody846_203 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 28)) (some 77) ([42, 26, 64]) (some (42, sourceBody846_202, 846, 29))

def sourceBody846_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_203 sourceBody846_4

def sourceBody846_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_204 sourceBody846_0

def sourceBody846_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_201 sourceBody846_205

def sourceBody846_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_200 sourceBody846_206

def sourceBody846_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_199 sourceBody846_207

def sourceBody846_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_208

def sourceBody846_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_209

def sourceBody846_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 6)

def sourceBody846_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 36)

def sourceBody846_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody846_214 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 80)

def sourceBody846_215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 40)

def sourceBody846_216 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 30)) (some 316) ([42, 26, 64, 16, 54]) (some (42, sourceBody846_202, 846, 31))

def sourceBody846_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_216 sourceBody846_4

def sourceBody846_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_217 sourceBody846_0

def sourceBody846_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_215 sourceBody846_218

def sourceBody846_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_214 sourceBody846_219

def sourceBody846_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_213 sourceBody846_220

def sourceBody846_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_212 sourceBody846_221

def sourceBody846_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_211 sourceBody846_222

def sourceBody846_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_223

def sourceBody846_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_224

def sourceBody846_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_210 sourceBody846_225

def sourceBody846_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_198 sourceBody846_226

def sourceBody846_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_227

def sourceBody846_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_228

def sourceBody846_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_192 sourceBody846_229

def sourceBody846_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_230

def sourceBody846_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_231

def sourceBody846_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_182 sourceBody846_232

def sourceBody846_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_233

def sourceBody846_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_234

def sourceBody846_236 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.imm 0#64) sourceBody846_235 sourceBody846_0

def sourceBody846_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_236 sourceBody846_4

def sourceBody846_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_237 sourceBody846_0

def sourceBody846_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_168 sourceBody846_238

def sourceBody846_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_167 sourceBody846_239

def sourceBody846_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_164 sourceBody846_240

def sourceBody846_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_163 sourceBody846_241

def sourceBody846_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_162 sourceBody846_242

def sourceBody846_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_158 sourceBody846_243

def sourceBody846_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_157 sourceBody846_244

def sourceBody846_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_156 sourceBody846_245

def sourceBody846_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_153 sourceBody846_246

def sourceBody846_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_152 sourceBody846_247

def sourceBody846_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_151 sourceBody846_248

def sourceBody846_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_147 sourceBody846_249

def sourceBody846_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_146 sourceBody846_250

def sourceBody846_252 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_253 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 54) sourceBody846_159 sourceBody846_160

def sourceBody846_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_253 sourceBody846_4

def sourceBody846_255 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 6)

def sourceBody846_256 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 36)

def sourceBody846_257 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody846_258 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_259 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 32)) (some 316) ([40, 80, 4, 42, 26]) (some (40, sourceBody846_174, 846, 33))

def sourceBody846_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_259 sourceBody846_4

def sourceBody846_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_260 sourceBody846_0

def sourceBody846_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_258 sourceBody846_261

def sourceBody846_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_152 sourceBody846_262

def sourceBody846_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_257 sourceBody846_263

def sourceBody846_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_256 sourceBody846_264

def sourceBody846_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_255 sourceBody846_265

def sourceBody846_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_266

def sourceBody846_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_267

def sourceBody846_269 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.imm 0#64) sourceBody846_268 sourceBody846_0

def sourceBody846_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_269 sourceBody846_4

def sourceBody846_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_270 sourceBody846_0

def sourceBody846_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_168 sourceBody846_271

def sourceBody846_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_167 sourceBody846_272

def sourceBody846_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_164 sourceBody846_273

def sourceBody846_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_163 sourceBody846_274

def sourceBody846_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_254 sourceBody846_275

def sourceBody846_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_158 sourceBody846_276

def sourceBody846_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_157 sourceBody846_277

def sourceBody846_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_156 sourceBody846_278

def sourceBody846_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_153 sourceBody846_279

def sourceBody846_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_152 sourceBody846_280

def sourceBody846_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_151 sourceBody846_281

def sourceBody846_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_252 sourceBody846_282

def sourceBody846_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_146 sourceBody846_283

def sourceBody846_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_251 sourceBody846_284

def sourceBody846_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_145 sourceBody846_285

def sourceBody846_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_286

def sourceBody846_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_287

def sourceBody846_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_133 sourceBody846_288

def sourceBody846_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_289

def sourceBody846_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_132 sourceBody846_290

def sourceBody846_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_291

def sourceBody846_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_131 sourceBody846_292

def sourceBody846_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_293

def sourceBody846_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_130 sourceBody846_294

def sourceBody846_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_295

def sourceBody846_297 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 70 (Flapjack.WordRegImm.imm 0#64) sourceBody846_296 sourceBody846_0

def sourceBody846_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_297 sourceBody846_4

def sourceBody846_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_298 sourceBody846_0

def sourceBody846_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_129 sourceBody846_299

def sourceBody846_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_128 sourceBody846_300

def sourceBody846_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_124 sourceBody846_301

def sourceBody846_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_123 sourceBody846_302

def sourceBody846_304 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 66, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody846_305 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 12)

def sourceBody846_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_305 sourceBody846_0

def sourceBody846_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_306 sourceBody846_0

def sourceBody846_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_304 sourceBody846_307

def sourceBody846_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_308

def sourceBody846_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_303 sourceBody846_309

def sourceBody846_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_122 sourceBody846_310

def sourceBody846_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_311

def sourceBody846_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_312

def sourceBody846_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_313

def sourceBody846_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_314

def sourceBody846_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_315

def sourceBody846_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_316

def sourceBody846_318 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody846_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_317 sourceBody846_318

def sourceBody846_320 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody846_321 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody846_319 sourceBody846_320

def sourceBody846_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_321 sourceBody846_4

def sourceBody846_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_322 sourceBody846_0

def sourceBody846_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_114 sourceBody846_323

def sourceBody846_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_113 sourceBody846_324

def sourceBody846_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_109 sourceBody846_325

def sourceBody846_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_108 sourceBody846_326

def sourceBody846_328 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody846_327 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody846_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_328 sourceBody846_4

def sourceBody846_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_4 sourceBody846_329

def sourceBody846_331 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody846_332 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 56)

def sourceBody846_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_332 sourceBody846_0

def sourceBody846_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_333 sourceBody846_0

def sourceBody846_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_331 sourceBody846_334

def sourceBody846_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_335

def sourceBody846_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_330 sourceBody846_336

def sourceBody846_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_107 sourceBody846_337

def sourceBody846_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_338

def sourceBody846_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_106 sourceBody846_339

def sourceBody846_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_340

def sourceBody846_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_341 sourceBody846_318

def sourceBody846_343 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody846_342 sourceBody846_320

def sourceBody846_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_343 sourceBody846_4

def sourceBody846_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_344 sourceBody846_0

def sourceBody846_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_105 sourceBody846_345

def sourceBody846_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_104 sourceBody846_346

def sourceBody846_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_100 sourceBody846_347

def sourceBody846_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_99 sourceBody846_348

def sourceBody846_350 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody846_349 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody846_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_350 sourceBody846_4

def sourceBody846_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_4 sourceBody846_351

def sourceBody846_353 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody846_354 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody846_355 : WordLangProgHOL (BitVec 64) :=
.call (some (([66]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 34)) (some 68) ([18]) (some (18, sourceBody846_354, 846, 35))

def sourceBody846_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_355 sourceBody846_4

def sourceBody846_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_356 sourceBody846_0

def sourceBody846_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_353 sourceBody846_357

def sourceBody846_359 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 6)

def sourceBody846_360 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 56

def sourceBody846_361 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 36)) (some 327) ([56, 36]) (some (56, sourceBody846_360, 846, 37))

def sourceBody846_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_361 sourceBody846_4

def sourceBody846_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_362 sourceBody846_0

def sourceBody846_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_108 sourceBody846_363

def sourceBody846_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_359 sourceBody846_364

def sourceBody846_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_365

def sourceBody846_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_366

def sourceBody846_368 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 62)

def sourceBody846_369 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 20)

def sourceBody846_370 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 66)

def sourceBody846_371 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 38)) (some 192) ([56, 36, 76]) (some (56, sourceBody846_360, 846, 39))

def sourceBody846_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_371 sourceBody846_4

def sourceBody846_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_372 sourceBody846_0

def sourceBody846_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_370 sourceBody846_373

def sourceBody846_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_369 sourceBody846_374

def sourceBody846_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_368 sourceBody846_375

def sourceBody846_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_376

def sourceBody846_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_377

def sourceBody846_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_367 sourceBody846_378

def sourceBody846_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_358 sourceBody846_379

def sourceBody846_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_380

def sourceBody846_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_381

def sourceBody846_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_352 sourceBody846_382

def sourceBody846_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_98 sourceBody846_383

def sourceBody846_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_384

def sourceBody846_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_97 sourceBody846_385

def sourceBody846_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_386

def sourceBody846_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_387

def sourceBody846_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_91 sourceBody846_388

def sourceBody846_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_389

def sourceBody846_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_390

def sourceBody846_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_81 sourceBody846_391

def sourceBody846_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_392

def sourceBody846_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_393

def sourceBody846_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_77 sourceBody846_394

def sourceBody846_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_51 sourceBody846_395

def sourceBody846_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_396

def sourceBody846_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_397

def sourceBody846_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_43 sourceBody846_398

def sourceBody846_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_399

def sourceBody846_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_27 sourceBody846_400

def sourceBody846_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_401

def sourceBody846_403 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 78 (Flapjack.WordRegImm.imm 0#64) sourceBody846_402 sourceBody846_0

def sourceBody846_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_403 sourceBody846_4

def sourceBody846_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_404 sourceBody846_0

def sourceBody846_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_42 sourceBody846_405

def sourceBody846_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_41 sourceBody846_406

def sourceBody846_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_37 sourceBody846_407

def sourceBody846_409 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_36 sourceBody846_408

def sourceBody846_410 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody846_411 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 20)

def sourceBody846_412 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_411 sourceBody846_0

def sourceBody846_413 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_412 sourceBody846_0

def sourceBody846_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_410 sourceBody846_413

def sourceBody846_415 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_414

def sourceBody846_416 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_409 sourceBody846_415

def sourceBody846_417 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_35 sourceBody846_416

def sourceBody846_418 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_417

def sourceBody846_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_418

def sourceBody846_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_419

def sourceBody846_421 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_420

def sourceBody846_422 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_421

def sourceBody846_423 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_422

def sourceBody846_424 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_423 sourceBody846_318

def sourceBody846_425 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody846_424 sourceBody846_320

def sourceBody846_426 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_425 sourceBody846_4

def sourceBody846_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_426 sourceBody846_0

def sourceBody846_428 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_27 sourceBody846_427

def sourceBody846_429 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_26 sourceBody846_428

def sourceBody846_430 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_22 sourceBody846_429

def sourceBody846_431 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_21 sourceBody846_430

def sourceBody846_432 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody846_431 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody846_433 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_432 sourceBody846_4

def sourceBody846_434 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_4 sourceBody846_433

def sourceBody846_435 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 34)

def sourceBody846_436 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 168#64]),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody846_437 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_438 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody846_439 : WordLangProgHOL (BitVec 64) :=
.call (some (([46]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 40)) (some 305) ([30, 68, 20]) (some (30, sourceBody846_438, 846, 41))

def sourceBody846_440 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_439 sourceBody846_4

def sourceBody846_441 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_440 sourceBody846_0

def sourceBody846_442 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_437 sourceBody846_441

def sourceBody846_443 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_436 sourceBody846_442

def sourceBody846_444 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_435 sourceBody846_443

def sourceBody846_445 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_20 sourceBody846_0

def sourceBody846_446 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_445 sourceBody846_0

def sourceBody846_447 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 8)

def sourceBody846_448 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 72)

def sourceBody846_449 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_450 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_451 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 68 (Flapjack.WordRegImm.reg 20) sourceBody846_449 sourceBody846_450

def sourceBody846_452 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_451 sourceBody846_4

def sourceBody846_453 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 14)

def sourceBody846_454 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 8)

def sourceBody846_455 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 58

def sourceBody846_456 : WordLangProgHOL (BitVec 64) :=
.call (some (([30, 68, 20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 42)) (some 197) ([58, 38]) (some (58, sourceBody846_455, 846, 43))

def sourceBody846_457 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_456 sourceBody846_4

def sourceBody846_458 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_457 sourceBody846_0

def sourceBody846_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_454 sourceBody846_458

def sourceBody846_460 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_453 sourceBody846_459

def sourceBody846_461 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 30)

def sourceBody846_462 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_463 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_464 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.reg 78) sourceBody846_463 sourceBody846_37

def sourceBody846_465 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_464 sourceBody846_4

def sourceBody846_466 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 52)

def sourceBody846_467 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 68)

def sourceBody846_468 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody846_469 : WordLangProgHOL (BitVec 64) :=
.call (some (([58]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 44)) (some 187) ([38, 78]) (some (38, sourceBody846_468, 846, 45))

def sourceBody846_470 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_469 sourceBody846_4

def sourceBody846_471 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_470 sourceBody846_0

def sourceBody846_472 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_467 sourceBody846_471

def sourceBody846_473 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_466 sourceBody846_472

def sourceBody846_474 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_475 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 78 (Flapjack.WordRegImm.reg 6) sourceBody846_474 sourceBody846_462

def sourceBody846_476 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_475 sourceBody846_4

def sourceBody846_477 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 78)

def sourceBody846_478 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 46)) (some 394) ([78]) (some (78, sourceBody846_46, 846, 47))

def sourceBody846_479 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_478 sourceBody846_4

def sourceBody846_480 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_479 sourceBody846_0

def sourceBody846_481 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_467 sourceBody846_480

def sourceBody846_482 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 68)

def sourceBody846_483 : WordLangProgHOL (BitVec 64) :=
.call (some (([78]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 48)) (some 192) ([6, 44, 28]) (some (6, sourceBody846_62, 846, 49))

def sourceBody846_484 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_483 sourceBody846_4

def sourceBody846_485 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_484 sourceBody846_0

def sourceBody846_486 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_61 sourceBody846_485

def sourceBody846_487 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_482 sourceBody846_486

def sourceBody846_488 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_59 sourceBody846_487

def sourceBody846_489 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_488

def sourceBody846_490 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_489

def sourceBody846_491 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody846_492 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.reg 44) sourceBody846_54 sourceBody846_55

def sourceBody846_493 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_492 sourceBody846_4

def sourceBody846_494 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 62)

def sourceBody846_495 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 68)

def sourceBody846_496 : WordLangProgHOL (BitVec 64) :=
.call (some (([78, 6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 50)) (some 186) ([44, 28]) (some (44, sourceBody846_85, 846, 51))

def sourceBody846_497 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_496 sourceBody846_4

def sourceBody846_498 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_497 sourceBody846_0

def sourceBody846_499 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_495 sourceBody846_498

def sourceBody846_500 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_494 sourceBody846_499

def sourceBody846_501 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 128#64]))

def sourceBody846_502 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 78)

def sourceBody846_503 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 66 (Flapjack.WordRegImm.reg 18) sourceBody846_84 sourceBody846_106

def sourceBody846_504 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_503 sourceBody846_4

def sourceBody846_505 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 66)

def sourceBody846_506 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 6)

def sourceBody846_507 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_506 sourceBody846_0

def sourceBody846_508 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_507 sourceBody846_0

def sourceBody846_509 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 56 (Flapjack.WordRegImm.imm 0#64) sourceBody846_508 sourceBody846_0

def sourceBody846_510 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_509 sourceBody846_4

def sourceBody846_511 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_510 sourceBody846_0

def sourceBody846_512 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_505 sourceBody846_511

def sourceBody846_513 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_504 sourceBody846_512

def sourceBody846_514 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_102 sourceBody846_513

def sourceBody846_515 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_502 sourceBody846_514

def sourceBody846_516 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody846_517 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 66

def sourceBody846_518 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 52)) (some 68) ([66]) (some (66, sourceBody846_517, 846, 53))

def sourceBody846_519 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_518 sourceBody846_4

def sourceBody846_520 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_519 sourceBody846_0

def sourceBody846_521 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_516 sourceBody846_520

def sourceBody846_522 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody846_523 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody846_524 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody846_525 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody846_526 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody846_527 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 44)

def sourceBody846_528 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody846_529 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 28)

def sourceBody846_530 : WordLangProgHOL (BitVec 64) :=
.call (some (([66]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 54)) (some 330) ([18, 56, 36, 76, 12, 50, 32, 70]) (some (18, sourceBody846_354, 846, 55))

def sourceBody846_531 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_530 sourceBody846_4

def sourceBody846_532 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_531 sourceBody846_0

def sourceBody846_533 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_529 sourceBody846_532

def sourceBody846_534 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_528 sourceBody846_533

def sourceBody846_535 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_527 sourceBody846_534

def sourceBody846_536 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_526 sourceBody846_535

def sourceBody846_537 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_525 sourceBody846_536

def sourceBody846_538 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_524 sourceBody846_537

def sourceBody846_539 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_523 sourceBody846_538

def sourceBody846_540 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_522 sourceBody846_539

def sourceBody846_541 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 46)

def sourceBody846_542 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 68)

def sourceBody846_543 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody846_544 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 28)

def sourceBody846_545 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 56)) (some 316) ([56, 36, 76, 12, 50]) (some (56, sourceBody846_360, 846, 57))

def sourceBody846_546 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_545 sourceBody846_4

def sourceBody846_547 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_546 sourceBody846_0

def sourceBody846_548 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_116 sourceBody846_547

def sourceBody846_549 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_544 sourceBody846_548

def sourceBody846_550 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_543 sourceBody846_549

def sourceBody846_551 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_542 sourceBody846_550

def sourceBody846_552 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_541 sourceBody846_551

def sourceBody846_553 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_552

def sourceBody846_554 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_553

def sourceBody846_555 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_540 sourceBody846_554

def sourceBody846_556 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_555

def sourceBody846_557 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_556

def sourceBody846_558 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_521 sourceBody846_557

def sourceBody846_559 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_558

def sourceBody846_560 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_559

def sourceBody846_561 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_515 sourceBody846_560

def sourceBody846_562 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_501 sourceBody846_561

def sourceBody846_563 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_562

def sourceBody846_564 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_500 sourceBody846_563

def sourceBody846_565 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_564

def sourceBody846_566 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_565

def sourceBody846_567 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_566

def sourceBody846_568 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_567

def sourceBody846_569 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody846_568 sourceBody846_0

def sourceBody846_570 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_569 sourceBody846_4

def sourceBody846_571 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_570 sourceBody846_0

def sourceBody846_572 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_58 sourceBody846_571

def sourceBody846_573 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_493 sourceBody846_572

def sourceBody846_574 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_491 sourceBody846_573

def sourceBody846_575 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_52 sourceBody846_574

def sourceBody846_576 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_490 sourceBody846_575

def sourceBody846_577 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_481 sourceBody846_576

def sourceBody846_578 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_577

def sourceBody846_579 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_578

def sourceBody846_580 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 44 (Flapjack.WordRegImm.imm 0#64) sourceBody846_579 sourceBody846_0

def sourceBody846_581 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_580 sourceBody846_4

def sourceBody846_582 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_581 sourceBody846_0

def sourceBody846_583 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_477 sourceBody846_582

def sourceBody846_584 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_476 sourceBody846_583

def sourceBody846_585 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_55 sourceBody846_584

def sourceBody846_586 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_42 sourceBody846_585

def sourceBody846_587 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_473 sourceBody846_586

def sourceBody846_588 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_587

def sourceBody846_589 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_588

def sourceBody846_590 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody846_589 sourceBody846_0

def sourceBody846_591 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_590 sourceBody846_4

def sourceBody846_592 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_591 sourceBody846_0

def sourceBody846_593 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_52 sourceBody846_592

def sourceBody846_594 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_465 sourceBody846_593

def sourceBody846_595 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_462 sourceBody846_594

def sourceBody846_596 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_461 sourceBody846_595

def sourceBody846_597 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody846_598 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 58)

def sourceBody846_599 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_598 sourceBody846_0

def sourceBody846_600 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_599 sourceBody846_0

def sourceBody846_601 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_597 sourceBody846_600

def sourceBody846_602 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_601

def sourceBody846_603 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_596 sourceBody846_602

def sourceBody846_604 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_460 sourceBody846_603

def sourceBody846_605 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_604

def sourceBody846_606 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_605

def sourceBody846_607 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_606

def sourceBody846_608 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_607

def sourceBody846_609 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_608

def sourceBody846_610 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_609

def sourceBody846_611 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_610 sourceBody846_318

def sourceBody846_612 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 58 (Flapjack.WordRegImm.imm 0#64) sourceBody846_611 sourceBody846_320

def sourceBody846_613 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_612 sourceBody846_4

def sourceBody846_614 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_613 sourceBody846_0

def sourceBody846_615 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_43 sourceBody846_614

def sourceBody846_616 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_452 sourceBody846_615

def sourceBody846_617 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_448 sourceBody846_616

def sourceBody846_618 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_447 sourceBody846_617

def sourceBody846_619 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody846_618 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody846_620 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_619 sourceBody846_4

def sourceBody846_621 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_4 sourceBody846_620

def sourceBody846_622 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_446 sourceBody846_621

def sourceBody846_623 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 52, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody846_624 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody846_625 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 30)

def sourceBody846_626 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_627 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 20 (Flapjack.WordRegImm.reg 58) sourceBody846_437 sourceBody846_626

def sourceBody846_628 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_627 sourceBody846_4

def sourceBody846_629 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 20)

def sourceBody846_630 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 8)

def sourceBody846_631 : WordLangProgHOL (BitVec 64) :=
.call (some (([68, 20, 58]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 58)) (some 197) ([38, 78]) (some (38, sourceBody846_468, 846, 59))

def sourceBody846_632 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_631 sourceBody846_4

def sourceBody846_633 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_632 sourceBody846_0

def sourceBody846_634 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_630 sourceBody846_633

def sourceBody846_635 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_466 sourceBody846_634

def sourceBody846_636 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 78 (Flapjack.WordRegImm.reg 6) sourceBody846_474 sourceBody846_462

def sourceBody846_637 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_636 sourceBody846_4

def sourceBody846_638 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 44 (Flapjack.WordRegImm.reg 28) sourceBody846_491 sourceBody846_53

def sourceBody846_639 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_638 sourceBody846_4

def sourceBody846_640 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 44)

def sourceBody846_641 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 46)

def sourceBody846_642 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 38)

def sourceBody846_643 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody846_644 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody846_645 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 60)) (some 316) ([44, 28, 66, 18, 56]) (some (44, sourceBody846_85, 846, 61))

def sourceBody846_646 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_645 sourceBody846_4

def sourceBody846_647 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_646 sourceBody846_0

def sourceBody846_648 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_644 sourceBody846_647

def sourceBody846_649 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_102 sourceBody846_648

def sourceBody846_650 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_643 sourceBody846_649

def sourceBody846_651 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_642 sourceBody846_650

def sourceBody846_652 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_641 sourceBody846_651

def sourceBody846_653 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_652

def sourceBody846_654 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_653

def sourceBody846_655 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 62)

def sourceBody846_656 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 38)

def sourceBody846_657 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 62)) (some 186) ([28, 66]) (some (28, sourceBody846_93, 846, 63))

def sourceBody846_658 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_657 sourceBody846_4

def sourceBody846_659 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_658 sourceBody846_0

def sourceBody846_660 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_656 sourceBody846_659

def sourceBody846_661 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_655 sourceBody846_660

def sourceBody846_662 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody846_663 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.reg 56) sourceBody846_101 sourceBody846_102

def sourceBody846_664 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_663 sourceBody846_4

def sourceBody846_665 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 44)

def sourceBody846_666 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_665 sourceBody846_0

def sourceBody846_667 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_666 sourceBody846_0

def sourceBody846_668 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 24)

def sourceBody846_669 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 38)

def sourceBody846_670 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 64)) (some 845) ([66, 18]) (some (66, sourceBody846_517, 846, 65))

def sourceBody846_671 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_670 sourceBody846_4

def sourceBody846_672 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_671 sourceBody846_0

def sourceBody846_673 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_669 sourceBody846_672

def sourceBody846_674 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_668 sourceBody846_673

def sourceBody846_675 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody846_667 sourceBody846_674

def sourceBody846_676 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_675 sourceBody846_4

def sourceBody846_677 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_676 sourceBody846_0

def sourceBody846_678 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_105 sourceBody846_677

def sourceBody846_679 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_664 sourceBody846_678

def sourceBody846_680 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_644 sourceBody846_679

def sourceBody846_681 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_662 sourceBody846_680

def sourceBody846_682 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody846_683 : WordLangProgHOL (BitVec 64) :=
.call (some (([66]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 66)) (some 68) ([18]) (some (18, sourceBody846_354, 846, 67))

def sourceBody846_684 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_683 sourceBody846_4

def sourceBody846_685 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_684 sourceBody846_0

def sourceBody846_686 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_682 sourceBody846_685

def sourceBody846_687 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 78, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody846_688 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 78, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody846_689 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 78, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody846_690 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 78, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody846_691 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 78, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody846_692 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 28)

def sourceBody846_693 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 78, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody846_694 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 66)

def sourceBody846_695 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 68)) (some 330) ([56, 36, 76, 12, 50, 32, 70, 22]) (some (56, sourceBody846_360, 846, 69))

def sourceBody846_696 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_695 sourceBody846_4

def sourceBody846_697 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_696 sourceBody846_0

def sourceBody846_698 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_694 sourceBody846_697

def sourceBody846_699 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_693 sourceBody846_698

def sourceBody846_700 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_692 sourceBody846_699

def sourceBody846_701 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_691 sourceBody846_700

def sourceBody846_702 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_690 sourceBody846_701

def sourceBody846_703 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_689 sourceBody846_702

def sourceBody846_704 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_688 sourceBody846_703

def sourceBody846_705 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_687 sourceBody846_704

def sourceBody846_706 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 46)

def sourceBody846_707 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 38)

def sourceBody846_708 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody846_709 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 18)

def sourceBody846_710 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody846_711 : WordLangProgHOL (BitVec 64) :=
.call (some (([56]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody846_0, 846, 70)) (some 316) ([36, 76, 12, 50, 32]) (some (36, sourceBody846_710, 846, 71))

def sourceBody846_712 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_711 sourceBody846_4

def sourceBody846_713 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_712 sourceBody846_0

def sourceBody846_714 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_709 sourceBody846_713

def sourceBody846_715 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_116 sourceBody846_714

def sourceBody846_716 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_708 sourceBody846_715

def sourceBody846_717 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_707 sourceBody846_716

def sourceBody846_718 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_706 sourceBody846_717

def sourceBody846_719 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_718

def sourceBody846_720 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_719

def sourceBody846_721 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_705 sourceBody846_720

def sourceBody846_722 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_721

def sourceBody846_723 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_722

def sourceBody846_724 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_686 sourceBody846_723

def sourceBody846_725 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_724

def sourceBody846_726 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_725

def sourceBody846_727 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_681 sourceBody846_726

def sourceBody846_728 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_727

def sourceBody846_729 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_728

def sourceBody846_730 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_661 sourceBody846_729

def sourceBody846_731 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_730

def sourceBody846_732 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_731

def sourceBody846_733 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_732

def sourceBody846_734 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_733

def sourceBody846_735 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 66 (Flapjack.WordRegImm.imm 0#64) sourceBody846_654 sourceBody846_734

def sourceBody846_736 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_735 sourceBody846_4

def sourceBody846_737 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_736 sourceBody846_0

def sourceBody846_738 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_640 sourceBody846_737

def sourceBody846_739 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_639 sourceBody846_738

def sourceBody846_740 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_61 sourceBody846_739

def sourceBody846_741 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_477 sourceBody846_740

def sourceBody846_742 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_42 sourceBody846_741

def sourceBody846_743 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_742

def sourceBody846_744 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_629 sourceBody846_743

def sourceBody846_745 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_744

def sourceBody846_746 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 44 (Flapjack.WordRegImm.imm 0#64) sourceBody846_745 sourceBody846_0

def sourceBody846_747 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_746 sourceBody846_4

def sourceBody846_748 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_747 sourceBody846_0

def sourceBody846_749 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_477 sourceBody846_748

def sourceBody846_750 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_637 sourceBody846_749

def sourceBody846_751 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_55 sourceBody846_750

def sourceBody846_752 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_467 sourceBody846_751

def sourceBody846_753 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody846_754 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 38)

def sourceBody846_755 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_754 sourceBody846_0

def sourceBody846_756 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_755 sourceBody846_0

def sourceBody846_757 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_753 sourceBody846_756

def sourceBody846_758 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_757

def sourceBody846_759 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_752 sourceBody846_758

def sourceBody846_760 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_635 sourceBody846_759

def sourceBody846_761 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_760

def sourceBody846_762 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_761

def sourceBody846_763 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_762

def sourceBody846_764 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_763

def sourceBody846_765 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_764

def sourceBody846_766 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_765

def sourceBody846_767 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_766 sourceBody846_318

def sourceBody846_768 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.imm 0#64) sourceBody846_767 sourceBody846_320

def sourceBody846_769 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_768 sourceBody846_4

def sourceBody846_770 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_769 sourceBody846_0

def sourceBody846_771 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_629 sourceBody846_770

def sourceBody846_772 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_628 sourceBody846_771

def sourceBody846_773 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_625 sourceBody846_772

def sourceBody846_774 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_624 sourceBody846_773

def sourceBody846_775 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody846_774 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln)
  PUnit.unit Flapjack.Spt.ln)

def sourceBody846_776 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_775 sourceBody846_4

def sourceBody846_777 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_4 sourceBody846_776

def sourceBody846_778 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_446 sourceBody846_777

def sourceBody846_779 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 46)

def sourceBody846_780 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 2)

def sourceBody846_781 : WordLangProgHOL (BitVec 64) :=
.call (some (([68]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody846_0, 846, 72)) (some 327) ([20, 58]) (some (20, sourceBody846_30, 846, 73))

def sourceBody846_782 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_781 sourceBody846_4

def sourceBody846_783 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_782 sourceBody846_0

def sourceBody846_784 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_780 sourceBody846_783

def sourceBody846_785 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_779 sourceBody846_784

def sourceBody846_786 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_785

def sourceBody846_787 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_786

def sourceBody846_788 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_778 sourceBody846_787

def sourceBody846_789 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [68]

def sourceBody846_790 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_789 sourceBody846_0

def sourceBody846_791 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_450 sourceBody846_790

def sourceBody846_792 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_788 sourceBody846_791

def sourceBody846_793 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_623 sourceBody846_792

def sourceBody846_794 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_793

def sourceBody846_795 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_622 sourceBody846_794

def sourceBody846_796 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_444 sourceBody846_795

def sourceBody846_797 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_796

def sourceBody846_798 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_797

def sourceBody846_799 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_434 sourceBody846_798

def sourceBody846_800 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_20 sourceBody846_799

def sourceBody846_801 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_800

def sourceBody846_802 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_19 sourceBody846_801

def sourceBody846_803 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_802

def sourceBody846_804 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_18 sourceBody846_803

def sourceBody846_805 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_804

def sourceBody846_806 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_17 sourceBody846_805

def sourceBody846_807 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_806

def sourceBody846_808 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_16 sourceBody846_807

def sourceBody846_809 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_808

def sourceBody846_810 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_15 sourceBody846_809

def sourceBody846_811 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_810

def sourceBody846_812 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_811

def sourceBody846_813 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_7 sourceBody846_812

def sourceBody846_814 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_813

def sourceBody846_815 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody846_0 sourceBody846_814

def source846 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (846, 2, sourceBody846_815)
end InitECandidate.Proofs.WordStages
