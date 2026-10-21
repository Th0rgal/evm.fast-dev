import InitECandidate.Proofs.WordStages.Source846
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody862_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody862_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody862_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody862_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody862_0, 862, 2)) (some 68) ([14]) (some (14, sourceBody862_2, 862, 3))

def sourceBody862_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody862_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_3 sourceBody862_4

def sourceBody862_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_5 sourceBody862_0

def sourceBody862_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_1 sourceBody862_6

def sourceBody862_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody862_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody862_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 12 (Flapjack.WordLangAddr.addr 14 0#64))

def sourceBody862_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_10 sourceBody862_0

def sourceBody862_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_9 sourceBody862_11

def sourceBody862_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_8 sourceBody862_12

def sourceBody862_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody862_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody862_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody862_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody862_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody862_0, 862, 4)) (some 77) ([12, 16, 8]) (some (12, sourceBody862_17, 862, 5))

def sourceBody862_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_18 sourceBody862_4

def sourceBody862_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_19 sourceBody862_0

def sourceBody862_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_16 sourceBody862_20

def sourceBody862_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_15 sourceBody862_21

def sourceBody862_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_14 sourceBody862_22

def sourceBody862_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_0 sourceBody862_23

def sourceBody862_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_0 sourceBody862_24

def sourceBody862_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_13 sourceBody862_25

def sourceBody862_27 : WordLangProgHOL (BitVec 64) :=
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
              Flapjack.WordLangExpHOL.const 416#64]),
        Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody862_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
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
                  Flapjack.WordLangExpHOL.const 416#64]),
            Flapjack.WordLangExpHOL.const 56#64]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
        (Flapjack.WordLangExpHOL.const 4#64)])

def sourceBody862_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody862_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 16)

def sourceBody862_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 12) 8

def sourceBody862_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_31 sourceBody862_0

def sourceBody862_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_30 sourceBody862_32

def sourceBody862_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_33 sourceBody862_0

def sourceBody862_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_29 sourceBody862_34

def sourceBody862_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_0 sourceBody862_35

def sourceBody862_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_28 sourceBody862_36

def sourceBody862_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_0 sourceBody862_37

def sourceBody862_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
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
                  Flapjack.WordLangExpHOL.const 416#64]),
            Flapjack.WordLangExpHOL.const 56#64]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
        (Flapjack.WordLangExpHOL.const 4#64),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody862_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody862_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_40 sourceBody862_34

def sourceBody862_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_0 sourceBody862_41

def sourceBody862_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_39 sourceBody862_42

def sourceBody862_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_0 sourceBody862_43

def sourceBody862_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_38 sourceBody862_44

def sourceBody862_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 416#64]),
      Flapjack.WordLangExpHOL.const 64#64])

def sourceBody862_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody862_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_47 sourceBody862_34

def sourceBody862_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_0 sourceBody862_48

def sourceBody862_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_46 sourceBody862_49

def sourceBody862_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_0 sourceBody862_50

def sourceBody862_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_45 sourceBody862_51

def sourceBody862_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody862_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody862_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_54 sourceBody862_0

def sourceBody862_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_53 sourceBody862_55

def sourceBody862_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_52 sourceBody862_56

def sourceBody862_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_27 sourceBody862_57

def sourceBody862_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_0 sourceBody862_58

def sourceBody862_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_26 sourceBody862_59

def sourceBody862_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_7 sourceBody862_60

def sourceBody862_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_0 sourceBody862_61

def sourceBody862_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody862_0 sourceBody862_62

def source862 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (862, 4, sourceBody862_63)
end InitECandidate.Proofs.WordStages
