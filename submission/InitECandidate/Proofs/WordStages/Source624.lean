import InitECandidate.Proofs.WordStages.Source608
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody624_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody624_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody624_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody624_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody624_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 4) sourceBody624_2 sourceBody624_3

def sourceBody624_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody624_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_4 sourceBody624_5

def sourceBody624_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody624_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody624_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody624_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody624_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_9 sourceBody624_10

def sourceBody624_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_8 sourceBody624_11

def sourceBody624_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody624_12 sourceBody624_10

def sourceBody624_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_13 sourceBody624_5

def sourceBody624_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_14 sourceBody624_10

def sourceBody624_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_7 sourceBody624_15

def sourceBody624_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_6 sourceBody624_16

def sourceBody624_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_1 sourceBody624_17

def sourceBody624_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_0 sourceBody624_18

def sourceBody624_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody624_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1518500249#64)

def sourceBody624_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_21 sourceBody624_11

def sourceBody624_23 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody624_22 sourceBody624_10

def sourceBody624_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_23 sourceBody624_5

def sourceBody624_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_24 sourceBody624_10

def sourceBody624_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_7 sourceBody624_25

def sourceBody624_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_6 sourceBody624_26

def sourceBody624_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_20 sourceBody624_27

def sourceBody624_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_0 sourceBody624_28

def sourceBody624_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_19 sourceBody624_29

def sourceBody624_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 48#64)

def sourceBody624_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1859775393#64)

def sourceBody624_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_32 sourceBody624_11

def sourceBody624_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody624_33 sourceBody624_10

def sourceBody624_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_34 sourceBody624_5

def sourceBody624_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_35 sourceBody624_10

def sourceBody624_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_7 sourceBody624_36

def sourceBody624_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_6 sourceBody624_37

def sourceBody624_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_31 sourceBody624_38

def sourceBody624_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_0 sourceBody624_39

def sourceBody624_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_30 sourceBody624_40

def sourceBody624_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody624_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 2400959708#64)

def sourceBody624_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_43 sourceBody624_11

def sourceBody624_45 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody624_44 sourceBody624_10

def sourceBody624_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_45 sourceBody624_5

def sourceBody624_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_46 sourceBody624_10

def sourceBody624_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_7 sourceBody624_47

def sourceBody624_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_6 sourceBody624_48

def sourceBody624_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_42 sourceBody624_49

def sourceBody624_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_0 sourceBody624_50

def sourceBody624_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_41 sourceBody624_51

def sourceBody624_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 2840853838#64)

def sourceBody624_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_53 sourceBody624_11

def sourceBody624_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody624_52 sourceBody624_54

def source624 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (624, 2, sourceBody624_55)
end InitECandidate.Proofs.WordStages
