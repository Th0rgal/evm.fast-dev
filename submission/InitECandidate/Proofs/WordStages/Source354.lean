import InitECandidate.Proofs.WordStages.Source338
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody354_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody354_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody354_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody354_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody354_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody354_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody354_6 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody354_0, 354, 2)) (some 139) ([12, 18, 10, 14]) (some (12, sourceBody354_5, 354, 3))

def sourceBody354_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody354_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_6 sourceBody354_7

def sourceBody354_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_8 sourceBody354_0

def sourceBody354_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_4 sourceBody354_9

def sourceBody354_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_3 sourceBody354_10

def sourceBody354_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_2 sourceBody354_11

def sourceBody354_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_1 sourceBody354_12

def sourceBody354_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody354_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody354_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody354_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody354_18 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 18 (Flapjack.WordRegImm.reg 10) sourceBody354_16 sourceBody354_17

def sourceBody354_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_18 sourceBody354_7

def sourceBody354_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody354_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody354_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody354_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_22 sourceBody354_0

def sourceBody354_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_21 sourceBody354_23

def sourceBody354_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody354_24 sourceBody354_0

def sourceBody354_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_25 sourceBody354_7

def sourceBody354_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_26 sourceBody354_0

def sourceBody354_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_20 sourceBody354_27

def sourceBody354_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_19 sourceBody354_28

def sourceBody354_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_15 sourceBody354_29

def sourceBody354_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_14 sourceBody354_30

def sourceBody354_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody354_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody354_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody354_35 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 18 (Flapjack.WordRegImm.reg 10) sourceBody354_16 sourceBody354_17

def sourceBody354_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_35 sourceBody354_7

def sourceBody354_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_36 sourceBody354_28

def sourceBody354_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_34 sourceBody354_37

def sourceBody354_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_33 sourceBody354_38

def sourceBody354_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody354_39 sourceBody354_0

def sourceBody354_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_40 sourceBody354_7

def sourceBody354_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_41 sourceBody354_0

def sourceBody354_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_20 sourceBody354_42

def sourceBody354_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_19 sourceBody354_43

def sourceBody354_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_32 sourceBody354_44

def sourceBody354_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_14 sourceBody354_45

def sourceBody354_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_31 sourceBody354_46

def sourceBody354_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.const 1#64, Flapjack.WordLangExpHOL.var 16])

def sourceBody354_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_48 sourceBody354_23

def sourceBody354_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_47 sourceBody354_49

def sourceBody354_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_13 sourceBody354_50

def sourceBody354_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_0 sourceBody354_51

def sourceBody354_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody354_0 sourceBody354_52

def source354 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (354, 5, sourceBody354_53)
end InitECandidate.Proofs.WordStages
