import InitECandidate.Proofs.WordStages.Source518
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody534_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody534_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
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

def sourceBody534_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
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
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody534_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
              [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 1#64],
            Flapjack.WordLangExpHOL.var 2])
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody534_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
              [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 1#64],
            Flapjack.WordLangExpHOL.var 4])
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody534_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 28))

def sourceBody534_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody534_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody534_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody534_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 20))

def sourceBody534_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody534_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody534_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody534_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 28)

def sourceBody534_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 36)

def sourceBody534_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody534_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 30)

def sourceBody534_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 22)

def sourceBody534_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody534_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 40) 12

def sourceBody534_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_19 sourceBody534_0

def sourceBody534_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_18 sourceBody534_20

def sourceBody534_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 24)

def sourceBody534_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 8#64])
  12

def sourceBody534_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_23 sourceBody534_0

def sourceBody534_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_22 sourceBody534_24

def sourceBody534_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody534_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 16#64])
  12

def sourceBody534_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_27 sourceBody534_0

def sourceBody534_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_26 sourceBody534_28

def sourceBody534_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 34)

def sourceBody534_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 24#64])
  12

def sourceBody534_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_31 sourceBody534_0

def sourceBody534_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_30 sourceBody534_32

def sourceBody534_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_33 sourceBody534_0

def sourceBody534_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_29 sourceBody534_34

def sourceBody534_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_25 sourceBody534_35

def sourceBody534_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_21 sourceBody534_36

def sourceBody534_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_17 sourceBody534_37

def sourceBody534_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_38

def sourceBody534_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_16 sourceBody534_39

def sourceBody534_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_40

def sourceBody534_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_15 sourceBody534_41

def sourceBody534_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_42

def sourceBody534_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_14 sourceBody534_43

def sourceBody534_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_44

def sourceBody534_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_13 sourceBody534_45

def sourceBody534_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_46

def sourceBody534_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 20)

def sourceBody534_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 38)

def sourceBody534_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody534_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 26)

def sourceBody534_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 18)

def sourceBody534_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_52 sourceBody534_37

def sourceBody534_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_53

def sourceBody534_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_51 sourceBody534_54

def sourceBody534_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_55

def sourceBody534_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_50 sourceBody534_56

def sourceBody534_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_57

def sourceBody534_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_49 sourceBody534_58

def sourceBody534_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_59

def sourceBody534_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_48 sourceBody534_60

def sourceBody534_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_61

def sourceBody534_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_47 sourceBody534_62

def sourceBody534_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody534_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [40]

def sourceBody534_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_65 sourceBody534_0

def sourceBody534_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_64 sourceBody534_66

def sourceBody534_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_63 sourceBody534_67

def sourceBody534_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_12 sourceBody534_68

def sourceBody534_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_69

def sourceBody534_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_11 sourceBody534_70

def sourceBody534_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_71

def sourceBody534_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_10 sourceBody534_72

def sourceBody534_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_73

def sourceBody534_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_9 sourceBody534_74

def sourceBody534_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_75

def sourceBody534_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_8 sourceBody534_76

def sourceBody534_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_77

def sourceBody534_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_7 sourceBody534_78

def sourceBody534_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_79

def sourceBody534_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_6 sourceBody534_80

def sourceBody534_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_81

def sourceBody534_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_5 sourceBody534_82

def sourceBody534_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_83

def sourceBody534_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_4 sourceBody534_84

def sourceBody534_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_85

def sourceBody534_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_3 sourceBody534_86

def sourceBody534_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_87

def sourceBody534_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_2 sourceBody534_88

def sourceBody534_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_89

def sourceBody534_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_1 sourceBody534_90

def sourceBody534_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody534_0 sourceBody534_91

def source534 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (534, 3, sourceBody534_92)
end InitECandidate.Proofs.WordStages
