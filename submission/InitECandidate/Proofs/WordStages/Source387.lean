import InitECandidate.Proofs.WordStages.Source371
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody387_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody387_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody387_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody387_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody387_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody387_5 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 14 (Flapjack.WordRegImm.reg 6) sourceBody387_3 sourceBody387_4

def sourceBody387_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_5 sourceBody387_0

def sourceBody387_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody387_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody387_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody387_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 16#64]),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody387_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 14)

def sourceBody387_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 6

def sourceBody387_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_12 sourceBody387_8

def sourceBody387_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_11 sourceBody387_13

def sourceBody387_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_14 sourceBody387_8

def sourceBody387_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_10 sourceBody387_15

def sourceBody387_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_8 sourceBody387_16

def sourceBody387_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_9 sourceBody387_17

def sourceBody387_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_8 sourceBody387_18

def sourceBody387_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 200#64]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 16#64]))
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody387_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 8))

def sourceBody387_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody387_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody387_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody387_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody387_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody387_27 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 16) sourceBody387_25 sourceBody387_26

def sourceBody387_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_27 sourceBody387_0

def sourceBody387_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody387_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody387_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody387_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody387_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody387_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody387_8, 387, 2)) (some 192) ([10, 16, 4]) (some (10, sourceBody387_33, 387, 3))

def sourceBody387_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_34 sourceBody387_0

def sourceBody387_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_35 sourceBody387_8

def sourceBody387_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_32 sourceBody387_36

def sourceBody387_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_31 sourceBody387_37

def sourceBody387_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_30 sourceBody387_38

def sourceBody387_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_8 sourceBody387_39

def sourceBody387_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_8 sourceBody387_40

def sourceBody387_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody387_8, 387, 4)) (some 193) ([10, 16]) (some (10, sourceBody387_33, 387, 5))

def sourceBody387_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_42 sourceBody387_0

def sourceBody387_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_43 sourceBody387_8

def sourceBody387_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_31 sourceBody387_44

def sourceBody387_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_30 sourceBody387_45

def sourceBody387_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_8 sourceBody387_46

def sourceBody387_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_8 sourceBody387_47

def sourceBody387_49 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody387_41 sourceBody387_48

def sourceBody387_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_49 sourceBody387_0

def sourceBody387_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_50 sourceBody387_8

def sourceBody387_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_29 sourceBody387_51

def sourceBody387_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_28 sourceBody387_52

def sourceBody387_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_24 sourceBody387_53

def sourceBody387_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_23 sourceBody387_54

def sourceBody387_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_22 sourceBody387_55

def sourceBody387_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_8 sourceBody387_56

def sourceBody387_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_21 sourceBody387_57

def sourceBody387_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_8 sourceBody387_58

def sourceBody387_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_20 sourceBody387_59

def sourceBody387_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_8 sourceBody387_60

def sourceBody387_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_19 sourceBody387_61

def sourceBody387_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody387_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_62 sourceBody387_63

def sourceBody387_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody387_66 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody387_64 sourceBody387_65

def sourceBody387_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_66 sourceBody387_0

def sourceBody387_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_67 sourceBody387_8

def sourceBody387_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_7 sourceBody387_68

def sourceBody387_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_6 sourceBody387_69

def sourceBody387_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_2 sourceBody387_70

def sourceBody387_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_1 sourceBody387_71

def sourceBody387_73 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) sourceBody387_72 (Flapjack.Spt.ls PUnit.unit)

def sourceBody387_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_73 sourceBody387_0

def sourceBody387_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_0 sourceBody387_74

def sourceBody387_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody387_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody387_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_77 sourceBody387_8

def sourceBody387_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_76 sourceBody387_78

def sourceBody387_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody387_75 sourceBody387_79

def source387 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (387, 2, sourceBody387_80)
end InitECandidate.Proofs.WordStages
