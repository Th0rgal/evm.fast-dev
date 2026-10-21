import InitECandidate.Proofs.WordStages.Source418
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody434_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody434_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody434_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody434_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody434_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody434_0, 434, 2)) (some 182) ([8, 2]) (some (8, sourceBody434_3, 434, 3))

def sourceBody434_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody434_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_4 sourceBody434_5

def sourceBody434_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_6 sourceBody434_0

def sourceBody434_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_2 sourceBody434_7

def sourceBody434_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_1 sourceBody434_8

def sourceBody434_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 216#64])

def sourceBody434_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody434_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody434_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 6

def sourceBody434_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_13 sourceBody434_0

def sourceBody434_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_12 sourceBody434_14

def sourceBody434_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_15 sourceBody434_0

def sourceBody434_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_11 sourceBody434_16

def sourceBody434_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_0 sourceBody434_17

def sourceBody434_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_10 sourceBody434_18

def sourceBody434_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_0 sourceBody434_19

def sourceBody434_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_9 sourceBody434_20

def sourceBody434_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_0 sourceBody434_21

def sourceBody434_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_0 sourceBody434_22

def sourceBody434_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 28#64)

def sourceBody434_25 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody434_0, 434, 4)) (some 182) ([8, 2]) (some (8, sourceBody434_3, 434, 5))

def sourceBody434_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_25 sourceBody434_5

def sourceBody434_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_26 sourceBody434_0

def sourceBody434_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_2 sourceBody434_27

def sourceBody434_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_24 sourceBody434_28

def sourceBody434_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 232#64])

def sourceBody434_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_30 sourceBody434_18

def sourceBody434_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_0 sourceBody434_31

def sourceBody434_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_29 sourceBody434_32

def sourceBody434_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_0 sourceBody434_33

def sourceBody434_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_0 sourceBody434_34

def sourceBody434_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_23 sourceBody434_35

def sourceBody434_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 60#64)

def sourceBody434_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody434_0, 434, 6)) (some 182) ([8, 2]) (some (8, sourceBody434_3, 434, 7))

def sourceBody434_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_38 sourceBody434_5

def sourceBody434_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_39 sourceBody434_0

def sourceBody434_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_2 sourceBody434_40

def sourceBody434_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_37 sourceBody434_41

def sourceBody434_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 240#64])

def sourceBody434_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_43 sourceBody434_18

def sourceBody434_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_0 sourceBody434_44

def sourceBody434_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_42 sourceBody434_45

def sourceBody434_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_0 sourceBody434_46

def sourceBody434_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_0 sourceBody434_47

def sourceBody434_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_36 sourceBody434_48

def sourceBody434_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody434_51 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody434_0, 434, 8)) (some 68) ([8]) (some (8, sourceBody434_3, 434, 9))

def sourceBody434_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_51 sourceBody434_5

def sourceBody434_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_52 sourceBody434_0

def sourceBody434_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_50 sourceBody434_53

def sourceBody434_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 248#64])

def sourceBody434_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_55 sourceBody434_18

def sourceBody434_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_0 sourceBody434_56

def sourceBody434_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_54 sourceBody434_57

def sourceBody434_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_0 sourceBody434_58

def sourceBody434_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_0 sourceBody434_59

def sourceBody434_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_49 sourceBody434_60

def sourceBody434_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 224#64])

def sourceBody434_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody434_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 8)

def sourceBody434_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 4) 2

def sourceBody434_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_65 sourceBody434_0

def sourceBody434_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_64 sourceBody434_66

def sourceBody434_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_67 sourceBody434_0

def sourceBody434_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_63 sourceBody434_68

def sourceBody434_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_0 sourceBody434_69

def sourceBody434_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_62 sourceBody434_70

def sourceBody434_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_0 sourceBody434_71

def sourceBody434_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_61 sourceBody434_72

def sourceBody434_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody434_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody434_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_75 sourceBody434_0

def sourceBody434_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_74 sourceBody434_76

def sourceBody434_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody434_73 sourceBody434_77

def source434 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (434, 1, sourceBody434_78)
end InitECandidate.Proofs.WordStages
