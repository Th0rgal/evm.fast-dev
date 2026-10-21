import InitECandidate.Proofs.WordStages.Source711
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody727_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody727_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody727_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 8505329371266088957#64)

def sourceBody727_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 17002214543764226050#64)

def sourceBody727_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 6865905132761471162#64)

def sourceBody727_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 8632934651105793861#64)

def sourceBody727_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 6631298214892334189#64)

def sourceBody727_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1582556514881692819#64)

def sourceBody727_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody727_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 12

def sourceBody727_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_9 sourceBody727_0

def sourceBody727_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_8 sourceBody727_10

def sourceBody727_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody727_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 8#64]) 12

def sourceBody727_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_13 sourceBody727_0

def sourceBody727_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_12 sourceBody727_14

def sourceBody727_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody727_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 16#64])
  12

def sourceBody727_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_17 sourceBody727_0

def sourceBody727_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_16 sourceBody727_18

def sourceBody727_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody727_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 24#64])
  12

def sourceBody727_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_21 sourceBody727_0

def sourceBody727_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_20 sourceBody727_22

def sourceBody727_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody727_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 32#64])
  12

def sourceBody727_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_25 sourceBody727_0

def sourceBody727_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_24 sourceBody727_26

def sourceBody727_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody727_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 40#64])
  12

def sourceBody727_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_29 sourceBody727_0

def sourceBody727_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_28 sourceBody727_30

def sourceBody727_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_31 sourceBody727_0

def sourceBody727_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_27 sourceBody727_32

def sourceBody727_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_23 sourceBody727_33

def sourceBody727_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_19 sourceBody727_34

def sourceBody727_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_15 sourceBody727_35

def sourceBody727_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_11 sourceBody727_36

def sourceBody727_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_7 sourceBody727_37

def sourceBody727_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_0 sourceBody727_38

def sourceBody727_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_6 sourceBody727_39

def sourceBody727_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_0 sourceBody727_40

def sourceBody727_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_5 sourceBody727_41

def sourceBody727_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_0 sourceBody727_42

def sourceBody727_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_4 sourceBody727_43

def sourceBody727_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_0 sourceBody727_44

def sourceBody727_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_3 sourceBody727_45

def sourceBody727_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_0 sourceBody727_46

def sourceBody727_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_2 sourceBody727_47

def sourceBody727_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_0 sourceBody727_48

def sourceBody727_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_1 sourceBody727_49

def sourceBody727_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_0 sourceBody727_50

def sourceBody727_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody727_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody727_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody727_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody727_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody727_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody727_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody727_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_58 sourceBody727_37

def sourceBody727_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_0 sourceBody727_59

def sourceBody727_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_57 sourceBody727_60

def sourceBody727_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_0 sourceBody727_61

def sourceBody727_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_56 sourceBody727_62

def sourceBody727_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_0 sourceBody727_63

def sourceBody727_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_55 sourceBody727_64

def sourceBody727_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_0 sourceBody727_65

def sourceBody727_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_54 sourceBody727_66

def sourceBody727_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_0 sourceBody727_67

def sourceBody727_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_53 sourceBody727_68

def sourceBody727_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_0 sourceBody727_69

def sourceBody727_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_52 sourceBody727_70

def sourceBody727_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_0 sourceBody727_71

def sourceBody727_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_51 sourceBody727_72

def sourceBody727_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody727_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody727_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_75 sourceBody727_0

def sourceBody727_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_74 sourceBody727_76

def sourceBody727_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody727_73 sourceBody727_77

def source727 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (727, 2, sourceBody727_78)
end InitECandidate.Proofs.WordStages
