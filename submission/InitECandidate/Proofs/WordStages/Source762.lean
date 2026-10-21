import InitECandidate.Proofs.WordStages.Source746
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody762_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody762_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody762_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 8505329371266088957#64)

def sourceBody762_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 17002214543764226050#64)

def sourceBody762_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 6865905132761471162#64)

def sourceBody762_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 8632934651105793861#64)

def sourceBody762_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 6631298214892334189#64)

def sourceBody762_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1582556514881692819#64)

def sourceBody762_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody762_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 12

def sourceBody762_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_9 sourceBody762_0

def sourceBody762_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_8 sourceBody762_10

def sourceBody762_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody762_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 8#64]) 12

def sourceBody762_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_13 sourceBody762_0

def sourceBody762_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_12 sourceBody762_14

def sourceBody762_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody762_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 16#64])
  12

def sourceBody762_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_17 sourceBody762_0

def sourceBody762_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_16 sourceBody762_18

def sourceBody762_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody762_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 24#64])
  12

def sourceBody762_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_21 sourceBody762_0

def sourceBody762_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_20 sourceBody762_22

def sourceBody762_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody762_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 32#64])
  12

def sourceBody762_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_25 sourceBody762_0

def sourceBody762_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_24 sourceBody762_26

def sourceBody762_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody762_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 40#64])
  12

def sourceBody762_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_29 sourceBody762_0

def sourceBody762_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_28 sourceBody762_30

def sourceBody762_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_31 sourceBody762_0

def sourceBody762_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_27 sourceBody762_32

def sourceBody762_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_23 sourceBody762_33

def sourceBody762_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_19 sourceBody762_34

def sourceBody762_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_15 sourceBody762_35

def sourceBody762_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_11 sourceBody762_36

def sourceBody762_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_7 sourceBody762_37

def sourceBody762_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_0 sourceBody762_38

def sourceBody762_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_6 sourceBody762_39

def sourceBody762_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_0 sourceBody762_40

def sourceBody762_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_5 sourceBody762_41

def sourceBody762_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_0 sourceBody762_42

def sourceBody762_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_4 sourceBody762_43

def sourceBody762_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_0 sourceBody762_44

def sourceBody762_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_3 sourceBody762_45

def sourceBody762_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_0 sourceBody762_46

def sourceBody762_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_2 sourceBody762_47

def sourceBody762_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_0 sourceBody762_48

def sourceBody762_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_1 sourceBody762_49

def sourceBody762_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_0 sourceBody762_50

def sourceBody762_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody762_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_52 sourceBody762_49

def sourceBody762_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_0 sourceBody762_53

def sourceBody762_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_51 sourceBody762_54

def sourceBody762_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody762_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody762_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody762_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody762_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody762_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody762_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody762_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_62 sourceBody762_37

def sourceBody762_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_0 sourceBody762_63

def sourceBody762_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_61 sourceBody762_64

def sourceBody762_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_0 sourceBody762_65

def sourceBody762_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_60 sourceBody762_66

def sourceBody762_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_0 sourceBody762_67

def sourceBody762_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_59 sourceBody762_68

def sourceBody762_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_0 sourceBody762_69

def sourceBody762_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_58 sourceBody762_70

def sourceBody762_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_0 sourceBody762_71

def sourceBody762_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_57 sourceBody762_72

def sourceBody762_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_0 sourceBody762_73

def sourceBody762_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_56 sourceBody762_74

def sourceBody762_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_0 sourceBody762_75

def sourceBody762_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_55 sourceBody762_76

def sourceBody762_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody762_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody762_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_79 sourceBody762_0

def sourceBody762_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_78 sourceBody762_80

def sourceBody762_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody762_77 sourceBody762_81

def source762 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (762, 2, sourceBody762_82)
end InitECandidate.Proofs.WordStages
