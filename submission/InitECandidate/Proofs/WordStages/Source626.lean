import InitECandidate.Proofs.WordStages.Source610
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody626_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody626_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody626_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody626_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 36)

def sourceBody626_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody626_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody626_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody626_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 30 (Flapjack.WordRegImm.reg 20) sourceBody626_5 sourceBody626_6

def sourceBody626_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_7 sourceBody626_2

def sourceBody626_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 30)

def sourceBody626_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 328#64]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody626_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 4,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
        (Flapjack.WordLangExpHOL.const 2#64)])

def sourceBody626_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 30 (Flapjack.WordLangAddr.addr 30 0#64))

def sourceBody626_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 4,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
        (Flapjack.WordLangExpHOL.const 2#64),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody626_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 20 (Flapjack.WordLangAddr.addr 20 0#64))

def sourceBody626_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 4,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
        (Flapjack.WordLangExpHOL.const 2#64),
      Flapjack.WordLangExpHOL.const 2#64])

def sourceBody626_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 42 (Flapjack.WordLangAddr.addr 42 0#64))

def sourceBody626_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 4,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
        (Flapjack.WordLangExpHOL.const 2#64),
      Flapjack.WordLangExpHOL.const 3#64])

def sourceBody626_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 8 (Flapjack.WordLangAddr.addr 8 0#64))

def sourceBody626_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_18 sourceBody626_0

def sourceBody626_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_17 sourceBody626_19

def sourceBody626_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_16 sourceBody626_20

def sourceBody626_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_15 sourceBody626_21

def sourceBody626_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_14 sourceBody626_22

def sourceBody626_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_13 sourceBody626_23

def sourceBody626_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_12 sourceBody626_24

def sourceBody626_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_11 sourceBody626_25

def sourceBody626_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 30,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 20)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 42)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
        (Flapjack.WordLangExpHOL.const 24#64)])

def sourceBody626_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody626_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 18

def sourceBody626_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_29 sourceBody626_0

def sourceBody626_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_28 sourceBody626_30

def sourceBody626_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_31 sourceBody626_0

def sourceBody626_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_27 sourceBody626_32

def sourceBody626_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_26 sourceBody626_33

def sourceBody626_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_10 sourceBody626_34

def sourceBody626_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_35

def sourceBody626_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody626_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 10)

def sourceBody626_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_38 sourceBody626_0

def sourceBody626_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_39 sourceBody626_0

def sourceBody626_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_37 sourceBody626_40

def sourceBody626_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_41

def sourceBody626_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_36 sourceBody626_42

def sourceBody626_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody626_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_43 sourceBody626_44

def sourceBody626_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody626_47 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.imm 0#64) sourceBody626_45 sourceBody626_46

def sourceBody626_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_47 sourceBody626_2

def sourceBody626_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_48 sourceBody626_0

def sourceBody626_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_9 sourceBody626_49

def sourceBody626_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_8 sourceBody626_50

def sourceBody626_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_4 sourceBody626_51

def sourceBody626_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_3 sourceBody626_52

def sourceBody626_54 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln) sourceBody626_53 (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody626_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_54 sourceBody626_2

def sourceBody626_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_2 sourceBody626_55

def sourceBody626_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 2))

def sourceBody626_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody626_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody626_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody626_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody626_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 10)

def sourceBody626_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 30)

def sourceBody626_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 20)

def sourceBody626_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 42)

def sourceBody626_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 8)

def sourceBody626_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody626_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 24)

def sourceBody626_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 80#64)

def sourceBody626_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody626_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody626_72 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 6 (Flapjack.WordRegImm.reg 26) sourceBody626_70 sourceBody626_71

def sourceBody626_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_72 sourceBody626_2

def sourceBody626_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody626_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody626_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody626_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 42)

def sourceBody626_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody626_79 : WordLangProgHOL (BitVec 64) :=
.call (some (([46]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody626_0, 626, 2)) (some 623) ([6, 26, 16, 38]) (some (6, sourceBody626_78, 626, 3))

def sourceBody626_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_79 sourceBody626_2

def sourceBody626_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_80 sourceBody626_0

def sourceBody626_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_77 sourceBody626_81

def sourceBody626_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_76 sourceBody626_82

def sourceBody626_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_75 sourceBody626_83

def sourceBody626_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_68 sourceBody626_84

def sourceBody626_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 24)

def sourceBody626_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody626_88 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody626_0, 626, 4)) (some 624) ([26]) (some (26, sourceBody626_87, 626, 5))

def sourceBody626_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_88 sourceBody626_2

def sourceBody626_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_89 sourceBody626_0

def sourceBody626_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_86 sourceBody626_90

def sourceBody626_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 46,
          Flapjack.WordLangExpHOL.load
            (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.load
                  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                            (Flapjack.WordLangExpHOL.const 1#64)],
                      Flapjack.WordLangExpHOL.const 328#64]),
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
                    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
                        (Flapjack.WordLangExpHOL.load
                          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                            [Flapjack.WordLangExpHOL.load
                                (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                                  [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                                      [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                                        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                                          (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                                          (Flapjack.WordLangExpHOL.const 1#64)],
                                    Flapjack.WordLangExpHOL.const 320#64]),
                              Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                                (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                                  [Flapjack.WordLangExpHOL.const 0#64,
                                    Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 24)
                                      (Flapjack.WordLangExpHOL.const 4#64)])
                                (Flapjack.WordLangExpHOL.const 3#64)]))
                        (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
                            [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 15#64])
                          (Flapjack.WordLangExpHOL.const 2#64)),
                      Flapjack.WordLangExpHOL.const 15#64])
                  (Flapjack.WordLangExpHOL.const 3#64)]),
          Flapjack.WordLangExpHOL.var 6],
      Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody626_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
        (Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.load
                (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                  [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                      [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                          (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                          (Flapjack.WordLangExpHOL.const 1#64)],
                    Flapjack.WordLangExpHOL.const 320#64]),
              Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                  [Flapjack.WordLangExpHOL.const 10#64,
                    Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 24)
                      (Flapjack.WordLangExpHOL.const 4#64)])
                (Flapjack.WordLangExpHOL.const 3#64)]))
        (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
            [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 15#64])
          (Flapjack.WordLangExpHOL.const 2#64)),
      Flapjack.WordLangExpHOL.const 15#64])

def sourceBody626_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
                [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 26)
                    (Flapjack.WordLangExpHOL.var 16),
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 26)
                    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                      [Flapjack.WordLangExpHOL.const 32#64, Flapjack.WordLangExpHOL.var 16])],
              Flapjack.WordLangExpHOL.const 4294967295#64],
          Flapjack.WordLangExpHOL.var 8],
      Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody626_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 38)

def sourceBody626_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_95 sourceBody626_0

def sourceBody626_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_96 sourceBody626_0

def sourceBody626_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_94 sourceBody626_97

def sourceBody626_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_98

def sourceBody626_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody626_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_100 sourceBody626_0

def sourceBody626_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_101 sourceBody626_0

def sourceBody626_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_99 sourceBody626_102

def sourceBody626_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 42)

def sourceBody626_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_104 sourceBody626_0

def sourceBody626_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_105 sourceBody626_0

def sourceBody626_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_103 sourceBody626_106

def sourceBody626_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
        [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 20)
            (Flapjack.WordLangExpHOL.const 10#64),
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 20)
            (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
              [Flapjack.WordLangExpHOL.const 32#64, Flapjack.WordLangExpHOL.const 10#64])],
      Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody626_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_108 sourceBody626_0

def sourceBody626_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_109 sourceBody626_0

def sourceBody626_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_107 sourceBody626_110

def sourceBody626_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 30)

def sourceBody626_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_112 sourceBody626_0

def sourceBody626_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_113 sourceBody626_0

def sourceBody626_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_111 sourceBody626_114

def sourceBody626_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 26)

def sourceBody626_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_116 sourceBody626_0

def sourceBody626_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_117 sourceBody626_0

def sourceBody626_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_115 sourceBody626_118

def sourceBody626_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.const 79#64, Flapjack.WordLangExpHOL.var 24])

def sourceBody626_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 18)

def sourceBody626_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 40)

def sourceBody626_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 14)

def sourceBody626_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody626_125 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody626_0, 626, 6)) (some 623) ([12, 32, 22, 44]) (some (12, sourceBody626_124, 626, 7))

def sourceBody626_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_125 sourceBody626_2

def sourceBody626_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_126 sourceBody626_0

def sourceBody626_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_123 sourceBody626_127

def sourceBody626_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_122 sourceBody626_128

def sourceBody626_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_121 sourceBody626_129

def sourceBody626_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_120 sourceBody626_130

def sourceBody626_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 24)

def sourceBody626_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody626_134 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody626_0, 626, 8)) (some 625) ([32]) (some (32, sourceBody626_133, 626, 9))

def sourceBody626_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_134 sourceBody626_2

def sourceBody626_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_135 sourceBody626_0

def sourceBody626_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_132 sourceBody626_136

def sourceBody626_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.var 38,
          Flapjack.WordLangExpHOL.load
            (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.load
                  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                            (Flapjack.WordLangExpHOL.const 1#64)],
                      Flapjack.WordLangExpHOL.const 328#64]),
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
                    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
                        (Flapjack.WordLangExpHOL.load
                          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                            [Flapjack.WordLangExpHOL.load
                                (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                                  [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                                      [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                                        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                                          (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                                          (Flapjack.WordLangExpHOL.const 1#64)],
                                    Flapjack.WordLangExpHOL.const 320#64]),
                              Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                                (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                                  [Flapjack.WordLangExpHOL.const 5#64,
                                    Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 24)
                                      (Flapjack.WordLangExpHOL.const 4#64)])
                                (Flapjack.WordLangExpHOL.const 3#64)]))
                        (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
                            [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 15#64])
                          (Flapjack.WordLangExpHOL.const 2#64)),
                      Flapjack.WordLangExpHOL.const 15#64])
                  (Flapjack.WordLangExpHOL.const 3#64)]),
          Flapjack.WordLangExpHOL.var 12],
      Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody626_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
        (Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.load
                (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                  [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                      [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                          (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                          (Flapjack.WordLangExpHOL.const 1#64)],
                    Flapjack.WordLangExpHOL.const 320#64]),
              Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                  [Flapjack.WordLangExpHOL.const 15#64,
                    Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 24)
                      (Flapjack.WordLangExpHOL.const 4#64)])
                (Flapjack.WordLangExpHOL.const 3#64)]))
        (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
            [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 15#64])
          (Flapjack.WordLangExpHOL.const 2#64)),
      Flapjack.WordLangExpHOL.const 15#64])

def sourceBody626_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
                [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 32)
                    (Flapjack.WordLangExpHOL.var 22),
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 32)
                    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                      [Flapjack.WordLangExpHOL.const 32#64, Flapjack.WordLangExpHOL.var 22])],
              Flapjack.WordLangExpHOL.const 4294967295#64],
          Flapjack.WordLangExpHOL.var 34],
      Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody626_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 44)

def sourceBody626_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_141 sourceBody626_0

def sourceBody626_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_142 sourceBody626_0

def sourceBody626_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_140 sourceBody626_143

def sourceBody626_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_144

def sourceBody626_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 34)

def sourceBody626_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_146 sourceBody626_0

def sourceBody626_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_147 sourceBody626_0

def sourceBody626_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_145 sourceBody626_148

def sourceBody626_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 14)

def sourceBody626_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_150 sourceBody626_0

def sourceBody626_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_151 sourceBody626_0

def sourceBody626_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_149 sourceBody626_152

def sourceBody626_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
        [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
            (Flapjack.WordLangExpHOL.const 10#64),
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 40)
            (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
              [Flapjack.WordLangExpHOL.const 32#64, Flapjack.WordLangExpHOL.const 10#64])],
      Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody626_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_154 sourceBody626_0

def sourceBody626_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_155 sourceBody626_0

def sourceBody626_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_153 sourceBody626_156

def sourceBody626_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 18)

def sourceBody626_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_158 sourceBody626_0

def sourceBody626_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_159 sourceBody626_0

def sourceBody626_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_157 sourceBody626_160

def sourceBody626_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 32)

def sourceBody626_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_162 sourceBody626_0

def sourceBody626_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_163 sourceBody626_0

def sourceBody626_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_161 sourceBody626_164

def sourceBody626_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody626_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 44)

def sourceBody626_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_167 sourceBody626_0

def sourceBody626_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_168 sourceBody626_0

def sourceBody626_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_166 sourceBody626_169

def sourceBody626_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_170

def sourceBody626_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_165 sourceBody626_171

def sourceBody626_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_139 sourceBody626_172

def sourceBody626_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_173

def sourceBody626_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_138 sourceBody626_174

def sourceBody626_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_175

def sourceBody626_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_137 sourceBody626_176

def sourceBody626_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_177

def sourceBody626_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_178

def sourceBody626_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_131 sourceBody626_179

def sourceBody626_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_180

def sourceBody626_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_181

def sourceBody626_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_119 sourceBody626_182

def sourceBody626_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_93 sourceBody626_183

def sourceBody626_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_184

def sourceBody626_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_92 sourceBody626_185

def sourceBody626_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_186

def sourceBody626_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_91 sourceBody626_187

def sourceBody626_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_188

def sourceBody626_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_189

def sourceBody626_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_85 sourceBody626_190

def sourceBody626_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_191

def sourceBody626_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_192

def sourceBody626_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_193 sourceBody626_44

def sourceBody626_195 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody626_194 sourceBody626_46

def sourceBody626_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_195 sourceBody626_2

def sourceBody626_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_196 sourceBody626_0

def sourceBody626_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_74 sourceBody626_197

def sourceBody626_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_73 sourceBody626_198

def sourceBody626_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_69 sourceBody626_199

def sourceBody626_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_68 sourceBody626_200

def sourceBody626_202 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody626_201 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody626_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_202 sourceBody626_2

def sourceBody626_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_2 sourceBody626_203

def sourceBody626_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 2))

def sourceBody626_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody626_207 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody626_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody626_209 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody626_210 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody626_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.var 14],
      Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody626_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 32)

def sourceBody626_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 12) 22

def sourceBody626_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_213 sourceBody626_0

def sourceBody626_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_212 sourceBody626_214

def sourceBody626_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_215 sourceBody626_0

def sourceBody626_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_211 sourceBody626_216

def sourceBody626_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_217

def sourceBody626_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_210 sourceBody626_218

def sourceBody626_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_219

def sourceBody626_221 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody626_222 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.var 34],
      Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody626_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_222 sourceBody626_216

def sourceBody626_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_223

def sourceBody626_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_221 sourceBody626_224

def sourceBody626_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_225

def sourceBody626_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_220 sourceBody626_226

def sourceBody626_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody626_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 28],
      Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody626_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_229 sourceBody626_216

def sourceBody626_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_230

def sourceBody626_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_228 sourceBody626_231

def sourceBody626_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_232

def sourceBody626_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_227 sourceBody626_233

def sourceBody626_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody626_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 18],
      Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody626_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_236 sourceBody626_216

def sourceBody626_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_237

def sourceBody626_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_235 sourceBody626_238

def sourceBody626_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_239

def sourceBody626_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_234 sourceBody626_240

def sourceBody626_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody626_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.var 46, Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.var 40],
      Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody626_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_243 sourceBody626_216

def sourceBody626_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_244

def sourceBody626_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_242 sourceBody626_245

def sourceBody626_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_246

def sourceBody626_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_241 sourceBody626_247

def sourceBody626_249 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody626_250 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody626_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_250 sourceBody626_0

def sourceBody626_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_249 sourceBody626_251

def sourceBody626_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_248 sourceBody626_252

def sourceBody626_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_209 sourceBody626_253

def sourceBody626_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_254

def sourceBody626_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_208 sourceBody626_255

def sourceBody626_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_256

def sourceBody626_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_207 sourceBody626_257

def sourceBody626_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_258

def sourceBody626_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_206 sourceBody626_259

def sourceBody626_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_260

def sourceBody626_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_205 sourceBody626_261

def sourceBody626_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_262

def sourceBody626_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_204 sourceBody626_263

def sourceBody626_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_67 sourceBody626_264

def sourceBody626_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_265

def sourceBody626_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_66 sourceBody626_266

def sourceBody626_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_267

def sourceBody626_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_65 sourceBody626_268

def sourceBody626_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_269

def sourceBody626_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_64 sourceBody626_270

def sourceBody626_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_271

def sourceBody626_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_63 sourceBody626_272

def sourceBody626_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_273

def sourceBody626_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_62 sourceBody626_274

def sourceBody626_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_275

def sourceBody626_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_61 sourceBody626_276

def sourceBody626_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_277

def sourceBody626_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_60 sourceBody626_278

def sourceBody626_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_279

def sourceBody626_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_59 sourceBody626_280

def sourceBody626_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_281

def sourceBody626_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_58 sourceBody626_282

def sourceBody626_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_283

def sourceBody626_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_57 sourceBody626_284

def sourceBody626_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_285

def sourceBody626_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_56 sourceBody626_286

def sourceBody626_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_1 sourceBody626_287

def sourceBody626_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody626_0 sourceBody626_288

def source626 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (626, 3, sourceBody626_289)
end InitECandidate.Proofs.WordStages
