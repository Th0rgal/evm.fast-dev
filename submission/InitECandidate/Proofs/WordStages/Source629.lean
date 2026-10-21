import InitECandidate.Proofs.WordStages.Source613
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody629_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody629_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 368#64]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 2)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody629_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 368#64]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody629_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 368#64]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 6)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody629_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 368#64]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody629_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 32))

def sourceBody629_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 16))

def sourceBody629_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 26))

def sourceBody629_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 20))

def sourceBody629_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 10])

def sourceBody629_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 34)

def sourceBody629_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_10 sourceBody629_0

def sourceBody629_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_11 sourceBody629_0

def sourceBody629_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_9 sourceBody629_12

def sourceBody629_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_13

def sourceBody629_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.ror
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.var 30])
    (Flapjack.WordLangExpHOL.const 32#64))

def sourceBody629_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 34)

def sourceBody629_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_16 sourceBody629_0

def sourceBody629_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_17 sourceBody629_0

def sourceBody629_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_15 sourceBody629_18

def sourceBody629_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_19

def sourceBody629_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_14 sourceBody629_20

def sourceBody629_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.var 22])

def sourceBody629_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 34)

def sourceBody629_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_23 sourceBody629_0

def sourceBody629_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_24 sourceBody629_0

def sourceBody629_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_22 sourceBody629_25

def sourceBody629_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_26

def sourceBody629_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_21 sourceBody629_27

def sourceBody629_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.ror
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 28])
    (Flapjack.WordLangExpHOL.const 24#64))

def sourceBody629_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 34)

def sourceBody629_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_30 sourceBody629_0

def sourceBody629_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_31 sourceBody629_0

def sourceBody629_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_29 sourceBody629_32

def sourceBody629_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_33

def sourceBody629_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_28 sourceBody629_34

def sourceBody629_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 12])

def sourceBody629_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_36 sourceBody629_12

def sourceBody629_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_37

def sourceBody629_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_35 sourceBody629_38

def sourceBody629_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.ror
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.var 30])
    (Flapjack.WordLangExpHOL.const 16#64))

def sourceBody629_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_40 sourceBody629_18

def sourceBody629_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_41

def sourceBody629_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_39 sourceBody629_42

def sourceBody629_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_43 sourceBody629_27

def sourceBody629_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.ror
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 28])
    (Flapjack.WordLangExpHOL.const 63#64))

def sourceBody629_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_45 sourceBody629_32

def sourceBody629_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_46

def sourceBody629_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_44 sourceBody629_47

def sourceBody629_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 32)

def sourceBody629_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 30)

def sourceBody629_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody629_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 34) 24

def sourceBody629_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_52 sourceBody629_0

def sourceBody629_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_51 sourceBody629_53

def sourceBody629_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_54 sourceBody629_0

def sourceBody629_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_50 sourceBody629_55

def sourceBody629_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_56

def sourceBody629_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_49 sourceBody629_57

def sourceBody629_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_58

def sourceBody629_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_48 sourceBody629_59

def sourceBody629_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody629_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody629_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_62 sourceBody629_55

def sourceBody629_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_63

def sourceBody629_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_61 sourceBody629_64

def sourceBody629_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_65

def sourceBody629_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_60 sourceBody629_66

def sourceBody629_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 26)

def sourceBody629_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 28)

def sourceBody629_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_69 sourceBody629_55

def sourceBody629_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_70

def sourceBody629_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_68 sourceBody629_71

def sourceBody629_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_72

def sourceBody629_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_67 sourceBody629_73

def sourceBody629_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 20)

def sourceBody629_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 22)

def sourceBody629_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_76 sourceBody629_55

def sourceBody629_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_77

def sourceBody629_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_75 sourceBody629_78

def sourceBody629_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_79

def sourceBody629_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_74 sourceBody629_80

def sourceBody629_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody629_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [34]

def sourceBody629_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_83 sourceBody629_0

def sourceBody629_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_82 sourceBody629_84

def sourceBody629_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_81 sourceBody629_85

def sourceBody629_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_8 sourceBody629_86

def sourceBody629_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_87

def sourceBody629_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_7 sourceBody629_88

def sourceBody629_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_89

def sourceBody629_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_6 sourceBody629_90

def sourceBody629_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_91

def sourceBody629_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_5 sourceBody629_92

def sourceBody629_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_93

def sourceBody629_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_4 sourceBody629_94

def sourceBody629_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_95

def sourceBody629_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_3 sourceBody629_96

def sourceBody629_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_97

def sourceBody629_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_2 sourceBody629_98

def sourceBody629_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_99

def sourceBody629_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_1 sourceBody629_100

def sourceBody629_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody629_0 sourceBody629_101

def source629 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (629, 7, sourceBody629_102)
end InitECandidate.Proofs.WordStages
