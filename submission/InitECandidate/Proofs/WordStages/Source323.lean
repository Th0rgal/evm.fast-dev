import InitECandidate.Proofs.WordStages.Source307
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody323_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody323_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody323_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody323_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody323_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.WordRegImm.reg 4) sourceBody323_2 sourceBody323_3

def sourceBody323_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody323_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_4 sourceBody323_5

def sourceBody323_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody323_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody323_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody323_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody323_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_9 sourceBody323_10

def sourceBody323_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_8 sourceBody323_11

def sourceBody323_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody323_12 sourceBody323_10

def sourceBody323_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_13 sourceBody323_5

def sourceBody323_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_14 sourceBody323_10

def sourceBody323_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_7 sourceBody323_15

def sourceBody323_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_6 sourceBody323_16

def sourceBody323_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_1 sourceBody323_17

def sourceBody323_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_0 sourceBody323_18

def sourceBody323_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody323_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 33#64)

def sourceBody323_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_21 sourceBody323_11

def sourceBody323_23 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody323_22 sourceBody323_10

def sourceBody323_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_23 sourceBody323_5

def sourceBody323_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_24 sourceBody323_10

def sourceBody323_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_7 sourceBody323_25

def sourceBody323_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_6 sourceBody323_26

def sourceBody323_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_1 sourceBody323_27

def sourceBody323_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_20 sourceBody323_28

def sourceBody323_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_19 sourceBody323_29

def sourceBody323_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody323_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 13#64)

def sourceBody323_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody323_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody323_10, 323, 2)) (some 282) ([12]) (some (12, sourceBody323_33, 323, 3))

def sourceBody323_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_34 sourceBody323_5

def sourceBody323_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_35 sourceBody323_10

def sourceBody323_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_32 sourceBody323_36

def sourceBody323_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_10 sourceBody323_37

def sourceBody323_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_10 sourceBody323_38

def sourceBody323_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody323_39 sourceBody323_10

def sourceBody323_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_40 sourceBody323_5

def sourceBody323_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_41 sourceBody323_10

def sourceBody323_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_7 sourceBody323_42

def sourceBody323_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_6 sourceBody323_43

def sourceBody323_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_1 sourceBody323_44

def sourceBody323_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_31 sourceBody323_45

def sourceBody323_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_30 sourceBody323_46

def sourceBody323_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody323_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody323_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody323_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody323_52 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 4 (Flapjack.WordRegImm.reg 10) sourceBody323_51 sourceBody323_1

def sourceBody323_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_52 sourceBody323_5

def sourceBody323_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody323_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody323_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody323_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_56 sourceBody323_10

def sourceBody323_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_55 sourceBody323_57

def sourceBody323_59 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody323_58 sourceBody323_10

def sourceBody323_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_59 sourceBody323_5

def sourceBody323_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_60 sourceBody323_10

def sourceBody323_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_54 sourceBody323_61

def sourceBody323_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_53 sourceBody323_62

def sourceBody323_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_50 sourceBody323_63

def sourceBody323_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_49 sourceBody323_64

def sourceBody323_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 33#64)

def sourceBody323_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_66 sourceBody323_57

def sourceBody323_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_65 sourceBody323_67

def sourceBody323_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_48 sourceBody323_68

def sourceBody323_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_10 sourceBody323_69

def sourceBody323_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody323_47 sourceBody323_70

def source323 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (323, 2, sourceBody323_71)
end InitECandidate.Proofs.WordStages
