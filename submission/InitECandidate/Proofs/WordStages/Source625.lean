import InitECandidate.Proofs.WordStages.Source609
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody625_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody625_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody625_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody625_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody625_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 4) sourceBody625_2 sourceBody625_3

def sourceBody625_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody625_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_4 sourceBody625_5

def sourceBody625_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody625_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1352829926#64)

def sourceBody625_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody625_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody625_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_9 sourceBody625_10

def sourceBody625_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_8 sourceBody625_11

def sourceBody625_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody625_12 sourceBody625_10

def sourceBody625_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_13 sourceBody625_5

def sourceBody625_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_14 sourceBody625_10

def sourceBody625_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_7 sourceBody625_15

def sourceBody625_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_6 sourceBody625_16

def sourceBody625_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_1 sourceBody625_17

def sourceBody625_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_0 sourceBody625_18

def sourceBody625_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody625_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1548603684#64)

def sourceBody625_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_21 sourceBody625_11

def sourceBody625_23 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody625_22 sourceBody625_10

def sourceBody625_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_23 sourceBody625_5

def sourceBody625_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_24 sourceBody625_10

def sourceBody625_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_7 sourceBody625_25

def sourceBody625_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_6 sourceBody625_26

def sourceBody625_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_20 sourceBody625_27

def sourceBody625_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_0 sourceBody625_28

def sourceBody625_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_19 sourceBody625_29

def sourceBody625_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 48#64)

def sourceBody625_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1836072691#64)

def sourceBody625_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_32 sourceBody625_11

def sourceBody625_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody625_33 sourceBody625_10

def sourceBody625_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_34 sourceBody625_5

def sourceBody625_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_35 sourceBody625_10

def sourceBody625_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_7 sourceBody625_36

def sourceBody625_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_6 sourceBody625_37

def sourceBody625_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_31 sourceBody625_38

def sourceBody625_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_0 sourceBody625_39

def sourceBody625_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_30 sourceBody625_40

def sourceBody625_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody625_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 2053994217#64)

def sourceBody625_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_43 sourceBody625_11

def sourceBody625_45 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody625_44 sourceBody625_10

def sourceBody625_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_45 sourceBody625_5

def sourceBody625_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_46 sourceBody625_10

def sourceBody625_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_7 sourceBody625_47

def sourceBody625_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_6 sourceBody625_48

def sourceBody625_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_42 sourceBody625_49

def sourceBody625_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_0 sourceBody625_50

def sourceBody625_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_41 sourceBody625_51

def sourceBody625_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody625_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_53 sourceBody625_11

def sourceBody625_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody625_52 sourceBody625_54

def source625 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (625, 2, sourceBody625_55)
end InitECandidate.Proofs.WordStages
