import InitECandidate.Proofs.WordStages.Source629
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody645_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody645_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 2)

def sourceBody645_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody645_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 6)

def sourceBody645_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 8)

def sourceBody645_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody645_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 28)

def sourceBody645_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 22) 30

def sourceBody645_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_7 sourceBody645_0

def sourceBody645_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_6 sourceBody645_8

def sourceBody645_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 20)

def sourceBody645_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 8#64])
  30

def sourceBody645_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_11 sourceBody645_0

def sourceBody645_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_10 sourceBody645_12

def sourceBody645_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 26)

def sourceBody645_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 16#64])
  30

def sourceBody645_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_15 sourceBody645_0

def sourceBody645_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_14 sourceBody645_16

def sourceBody645_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 24)

def sourceBody645_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 24#64])
  30

def sourceBody645_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_19 sourceBody645_0

def sourceBody645_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_18 sourceBody645_20

def sourceBody645_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_21 sourceBody645_0

def sourceBody645_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_17 sourceBody645_22

def sourceBody645_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_13 sourceBody645_23

def sourceBody645_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_9 sourceBody645_24

def sourceBody645_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_5 sourceBody645_25

def sourceBody645_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_0 sourceBody645_26

def sourceBody645_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_4 sourceBody645_27

def sourceBody645_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_0 sourceBody645_28

def sourceBody645_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_3 sourceBody645_29

def sourceBody645_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_0 sourceBody645_30

def sourceBody645_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_2 sourceBody645_31

def sourceBody645_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_0 sourceBody645_32

def sourceBody645_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_1 sourceBody645_33

def sourceBody645_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_0 sourceBody645_34

def sourceBody645_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody645_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 12)

def sourceBody645_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody645_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 16)

def sourceBody645_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody645_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_40 sourceBody645_25

def sourceBody645_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_0 sourceBody645_41

def sourceBody645_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_39 sourceBody645_42

def sourceBody645_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_0 sourceBody645_43

def sourceBody645_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_38 sourceBody645_44

def sourceBody645_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_0 sourceBody645_45

def sourceBody645_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_37 sourceBody645_46

def sourceBody645_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_0 sourceBody645_47

def sourceBody645_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_36 sourceBody645_48

def sourceBody645_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_0 sourceBody645_49

def sourceBody645_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_35 sourceBody645_50

def sourceBody645_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody645_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody645_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody645_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody645_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody645_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_56 sourceBody645_25

def sourceBody645_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_0 sourceBody645_57

def sourceBody645_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_55 sourceBody645_58

def sourceBody645_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_0 sourceBody645_59

def sourceBody645_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_54 sourceBody645_60

def sourceBody645_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_0 sourceBody645_61

def sourceBody645_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_53 sourceBody645_62

def sourceBody645_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_0 sourceBody645_63

def sourceBody645_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_52 sourceBody645_64

def sourceBody645_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_0 sourceBody645_65

def sourceBody645_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_51 sourceBody645_66

def sourceBody645_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody645_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [22]

def sourceBody645_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_69 sourceBody645_0

def sourceBody645_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_68 sourceBody645_70

def sourceBody645_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody645_67 sourceBody645_71

def source645 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (645, 10, sourceBody645_72)
end InitECandidate.Proofs.WordStages
