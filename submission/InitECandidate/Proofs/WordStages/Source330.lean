import InitECandidate.Proofs.WordStages.Source314
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody330_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody330_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody330_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.var 28])

def sourceBody330_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody330_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody330_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody330_0, 330, 2)) (some 177) ([32, 20]) (some (32, sourceBody330_4, 330, 3))

def sourceBody330_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody330_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_5 sourceBody330_6

def sourceBody330_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_7 sourceBody330_0

def sourceBody330_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_3 sourceBody330_8

def sourceBody330_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_2 sourceBody330_9

def sourceBody330_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.var 22])

def sourceBody330_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 32)

def sourceBody330_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_12 sourceBody330_0

def sourceBody330_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_13 sourceBody330_0

def sourceBody330_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_11 sourceBody330_14

def sourceBody330_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_15

def sourceBody330_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 152#64]))

def sourceBody330_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 10)

def sourceBody330_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody330_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody330_0, 330, 4)) (some 89) ([20, 30]) (some (20, sourceBody330_19, 330, 5))

def sourceBody330_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_20 sourceBody330_6

def sourceBody330_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_21 sourceBody330_0

def sourceBody330_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_18 sourceBody330_22

def sourceBody330_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_17 sourceBody330_23

def sourceBody330_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_24

def sourceBody330_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_25

def sourceBody330_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_16 sourceBody330_26

def sourceBody330_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 152#64]),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody330_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 8)

def sourceBody330_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody330_0, 330, 6)) (some 89) ([20, 30]) (some (20, sourceBody330_19, 330, 7))

def sourceBody330_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_30 sourceBody330_6

def sourceBody330_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_31 sourceBody330_0

def sourceBody330_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_29 sourceBody330_32

def sourceBody330_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_28 sourceBody330_33

def sourceBody330_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_34

def sourceBody330_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_35

def sourceBody330_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_27 sourceBody330_36

def sourceBody330_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 152#64]),
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody330_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 6)

def sourceBody330_40 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody330_0, 330, 8)) (some 89) ([20, 30]) (some (20, sourceBody330_19, 330, 9))

def sourceBody330_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_40 sourceBody330_6

def sourceBody330_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_41 sourceBody330_0

def sourceBody330_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_39 sourceBody330_42

def sourceBody330_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_38 sourceBody330_43

def sourceBody330_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_44

def sourceBody330_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_45

def sourceBody330_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_37 sourceBody330_46

def sourceBody330_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 152#64]),
      Flapjack.WordLangExpHOL.const 24#64])

def sourceBody330_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 4)

def sourceBody330_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody330_0, 330, 10)) (some 89) ([20, 30]) (some (20, sourceBody330_19, 330, 11))

def sourceBody330_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_50 sourceBody330_6

def sourceBody330_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_51 sourceBody330_0

def sourceBody330_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_49 sourceBody330_52

def sourceBody330_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_48 sourceBody330_53

def sourceBody330_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_54

def sourceBody330_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_55

def sourceBody330_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_47 sourceBody330_56

def sourceBody330_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody330_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 32)

def sourceBody330_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody330_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody330_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody330_63 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 30 (Flapjack.WordRegImm.reg 24) sourceBody330_61 sourceBody330_62

def sourceBody330_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_63 sourceBody330_6

def sourceBody330_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 30)

def sourceBody330_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 152#64]),
      Flapjack.WordLangExpHOL.var 32])

def sourceBody330_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 20 (Flapjack.WordLangAddr.addr 20 0#64))

def sourceBody330_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 20)

def sourceBody330_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody330_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody330_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody330_72 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.reg 34) sourceBody330_70 sourceBody330_71

def sourceBody330_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_72 sourceBody330_6

def sourceBody330_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody330_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody330_76 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody330_75 sourceBody330_0

def sourceBody330_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_76 sourceBody330_6

def sourceBody330_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_77 sourceBody330_0

def sourceBody330_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_74 sourceBody330_78

def sourceBody330_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_73 sourceBody330_79

def sourceBody330_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_69 sourceBody330_80

def sourceBody330_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_68 sourceBody330_81

def sourceBody330_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_67 sourceBody330_82

def sourceBody330_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_66 sourceBody330_83

def sourceBody330_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody330_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 20)

def sourceBody330_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_86 sourceBody330_0

def sourceBody330_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_87 sourceBody330_0

def sourceBody330_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_85 sourceBody330_88

def sourceBody330_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_89

def sourceBody330_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_84 sourceBody330_90

def sourceBody330_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody330_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_91 sourceBody330_92

def sourceBody330_94 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.imm 0#64) sourceBody330_93 sourceBody330_75

def sourceBody330_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_94 sourceBody330_6

def sourceBody330_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_95 sourceBody330_0

def sourceBody330_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_65 sourceBody330_96

def sourceBody330_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_64 sourceBody330_97

def sourceBody330_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_60 sourceBody330_98

def sourceBody330_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_59 sourceBody330_99

def sourceBody330_101 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody330_100 (Flapjack.Spt.bs
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody330_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_101 sourceBody330_6

def sourceBody330_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_6 sourceBody330_102

def sourceBody330_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.var 28])

def sourceBody330_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 152#64]),
      Flapjack.WordLangExpHOL.var 32])

def sourceBody330_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.const 32#64, Flapjack.WordLangExpHOL.var 32])

def sourceBody330_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody330_108 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody330_0, 330, 12)) (some 176) ([30, 24, 34]) (some (30, sourceBody330_107, 330, 13))

def sourceBody330_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_108 sourceBody330_6

def sourceBody330_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_109 sourceBody330_0

def sourceBody330_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_106 sourceBody330_110

def sourceBody330_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_105 sourceBody330_111

def sourceBody330_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_104 sourceBody330_112

def sourceBody330_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.var 20])

def sourceBody330_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 30)

def sourceBody330_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_115 sourceBody330_0

def sourceBody330_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_116 sourceBody330_0

def sourceBody330_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_114 sourceBody330_117

def sourceBody330_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_118

def sourceBody330_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.var 28])

def sourceBody330_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 12)

def sourceBody330_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody330_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody330_124 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody330_0, 330, 14)) (some 176) ([24, 34, 18]) (some (24, sourceBody330_123, 330, 15))

def sourceBody330_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_124 sourceBody330_6

def sourceBody330_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_125 sourceBody330_0

def sourceBody330_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_122 sourceBody330_126

def sourceBody330_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_121 sourceBody330_127

def sourceBody330_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_120 sourceBody330_128

def sourceBody330_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.var 30])

def sourceBody330_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 24)

def sourceBody330_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_131 sourceBody330_0

def sourceBody330_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_132 sourceBody330_0

def sourceBody330_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_130 sourceBody330_133

def sourceBody330_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_134

def sourceBody330_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.var 28])

def sourceBody330_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody330_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody330_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody330_140 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody330_0, 330, 16)) (some 176) ([34, 18, 26]) (some (34, sourceBody330_139, 330, 17))

def sourceBody330_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_140 sourceBody330_6

def sourceBody330_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_141 sourceBody330_0

def sourceBody330_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_138 sourceBody330_142

def sourceBody330_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_137 sourceBody330_143

def sourceBody330_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_136 sourceBody330_144

def sourceBody330_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.var 24])

def sourceBody330_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 34)

def sourceBody330_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_147 sourceBody330_0

def sourceBody330_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_148 sourceBody330_0

def sourceBody330_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_146 sourceBody330_149

def sourceBody330_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_150

def sourceBody330_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody330_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 248#64)

def sourceBody330_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 18 (Flapjack.WordLangAddr.addr 34 0#64))

def sourceBody330_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_154 sourceBody330_0

def sourceBody330_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_153 sourceBody330_155

def sourceBody330_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_152 sourceBody330_156

def sourceBody330_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_151 sourceBody330_157

def sourceBody330_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody330_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody330_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_160 sourceBody330_155

def sourceBody330_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_159 sourceBody330_161

def sourceBody330_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_158 sourceBody330_162

def sourceBody330_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 28)

def sourceBody330_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [34]

def sourceBody330_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_165 sourceBody330_0

def sourceBody330_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_164 sourceBody330_166

def sourceBody330_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_163 sourceBody330_167

def sourceBody330_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_145 sourceBody330_168

def sourceBody330_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_169

def sourceBody330_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_170

def sourceBody330_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_135 sourceBody330_171

def sourceBody330_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_129 sourceBody330_172

def sourceBody330_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_173

def sourceBody330_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_174

def sourceBody330_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_119 sourceBody330_175

def sourceBody330_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_113 sourceBody330_176

def sourceBody330_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_177

def sourceBody330_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_178

def sourceBody330_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_103 sourceBody330_179

def sourceBody330_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_58 sourceBody330_180

def sourceBody330_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_181

def sourceBody330_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_57 sourceBody330_182

def sourceBody330_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_10 sourceBody330_183

def sourceBody330_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_184

def sourceBody330_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_185

def sourceBody330_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_1 sourceBody330_186

def sourceBody330_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody330_0 sourceBody330_187

def source330 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (330, 9, sourceBody330_188)
end InitECandidate.Proofs.WordStages
