import InitECandidate.Proofs.WordStages.Source276
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody292_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody292_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody292_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody292_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody292_0, 292, 2)) (some 68) ([12]) (some (12, sourceBody292_2, 292, 3))

def sourceBody292_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody292_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_3 sourceBody292_4

def sourceBody292_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_5 sourceBody292_0

def sourceBody292_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_1 sourceBody292_6

def sourceBody292_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody292_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody292_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody292_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 12) 10

def sourceBody292_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_11 sourceBody292_0

def sourceBody292_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_10 sourceBody292_12

def sourceBody292_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_13 sourceBody292_0

def sourceBody292_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_9 sourceBody292_14

def sourceBody292_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_0 sourceBody292_15

def sourceBody292_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_8 sourceBody292_16

def sourceBody292_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_0 sourceBody292_17

def sourceBody292_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody292_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody292_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_20 sourceBody292_14

def sourceBody292_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_0 sourceBody292_21

def sourceBody292_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_19 sourceBody292_22

def sourceBody292_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_0 sourceBody292_23

def sourceBody292_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_18 sourceBody292_24

def sourceBody292_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody292_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_26 sourceBody292_22

def sourceBody292_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_0 sourceBody292_27

def sourceBody292_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_25 sourceBody292_28

def sourceBody292_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody292_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_30 sourceBody292_22

def sourceBody292_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_0 sourceBody292_31

def sourceBody292_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_29 sourceBody292_32

def sourceBody292_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody292_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody292_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_35 sourceBody292_14

def sourceBody292_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_0 sourceBody292_36

def sourceBody292_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_34 sourceBody292_37

def sourceBody292_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_0 sourceBody292_38

def sourceBody292_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_33 sourceBody292_39

def sourceBody292_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody292_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody292_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_42 sourceBody292_14

def sourceBody292_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_0 sourceBody292_43

def sourceBody292_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_41 sourceBody292_44

def sourceBody292_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_0 sourceBody292_45

def sourceBody292_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_40 sourceBody292_46

def sourceBody292_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody292_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody292_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_49 sourceBody292_14

def sourceBody292_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_0 sourceBody292_50

def sourceBody292_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_48 sourceBody292_51

def sourceBody292_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_0 sourceBody292_52

def sourceBody292_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_47 sourceBody292_53

def sourceBody292_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 56#64])

def sourceBody292_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody292_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_56 sourceBody292_14

def sourceBody292_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_0 sourceBody292_57

def sourceBody292_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_55 sourceBody292_58

def sourceBody292_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_0 sourceBody292_59

def sourceBody292_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_54 sourceBody292_60

def sourceBody292_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody292_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody292_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_63 sourceBody292_0

def sourceBody292_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_62 sourceBody292_64

def sourceBody292_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_61 sourceBody292_65

def sourceBody292_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_7 sourceBody292_66

def sourceBody292_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_0 sourceBody292_67

def sourceBody292_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody292_0 sourceBody292_68

def source292 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (292, 5, sourceBody292_69)
end InitECandidate.Proofs.WordStages
