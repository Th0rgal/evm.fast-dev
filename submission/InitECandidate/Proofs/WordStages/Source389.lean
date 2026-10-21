import InitECandidate.Proofs.WordStages.Source373
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody389_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody389_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 56#64)

def sourceBody389_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody389_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody389_0, 389, 2)) (some 68) ([14]) (some (14, sourceBody389_2, 389, 3))

def sourceBody389_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody389_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_3 sourceBody389_4

def sourceBody389_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_5 sourceBody389_0

def sourceBody389_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_1 sourceBody389_6

def sourceBody389_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody389_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody389_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody389_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 14) 18

def sourceBody389_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_11 sourceBody389_0

def sourceBody389_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_10 sourceBody389_12

def sourceBody389_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_13 sourceBody389_0

def sourceBody389_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_9 sourceBody389_14

def sourceBody389_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_0 sourceBody389_15

def sourceBody389_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_8 sourceBody389_16

def sourceBody389_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_0 sourceBody389_17

def sourceBody389_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody389_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody389_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody389_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody389_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody389_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 20)

def sourceBody389_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 14) 22

def sourceBody389_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_25 sourceBody389_0

def sourceBody389_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_24 sourceBody389_26

def sourceBody389_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody389_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 8#64])
  22

def sourceBody389_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_29 sourceBody389_0

def sourceBody389_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_28 sourceBody389_30

def sourceBody389_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 24)

def sourceBody389_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 16#64])
  22

def sourceBody389_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_33 sourceBody389_0

def sourceBody389_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_32 sourceBody389_34

def sourceBody389_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 16)

def sourceBody389_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 24#64])
  22

def sourceBody389_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_37 sourceBody389_0

def sourceBody389_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_36 sourceBody389_38

def sourceBody389_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_39 sourceBody389_0

def sourceBody389_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_35 sourceBody389_40

def sourceBody389_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_31 sourceBody389_41

def sourceBody389_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_27 sourceBody389_42

def sourceBody389_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_23 sourceBody389_43

def sourceBody389_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_0 sourceBody389_44

def sourceBody389_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_22 sourceBody389_45

def sourceBody389_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_0 sourceBody389_46

def sourceBody389_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_21 sourceBody389_47

def sourceBody389_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_0 sourceBody389_48

def sourceBody389_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_20 sourceBody389_49

def sourceBody389_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_0 sourceBody389_50

def sourceBody389_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_19 sourceBody389_51

def sourceBody389_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_0 sourceBody389_52

def sourceBody389_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_18 sourceBody389_53

def sourceBody389_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody389_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 128#64]))

def sourceBody389_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_56 sourceBody389_14

def sourceBody389_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_0 sourceBody389_57

def sourceBody389_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_55 sourceBody389_58

def sourceBody389_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_0 sourceBody389_59

def sourceBody389_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_54 sourceBody389_60

def sourceBody389_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody389_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody389_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_63 sourceBody389_14

def sourceBody389_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_0 sourceBody389_64

def sourceBody389_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_62 sourceBody389_65

def sourceBody389_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_0 sourceBody389_66

def sourceBody389_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_61 sourceBody389_67

def sourceBody389_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 26)

def sourceBody389_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody389_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_70 sourceBody389_0

def sourceBody389_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_69 sourceBody389_71

def sourceBody389_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_68 sourceBody389_72

def sourceBody389_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_7 sourceBody389_73

def sourceBody389_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_0 sourceBody389_74

def sourceBody389_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody389_0 sourceBody389_75

def source389 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (389, 7, sourceBody389_76)
end InitECandidate.Proofs.WordStages
