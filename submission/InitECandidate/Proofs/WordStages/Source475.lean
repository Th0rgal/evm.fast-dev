import InitECandidate.Proofs.WordStages.Source459
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody475_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody475_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody475_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody475_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody475_0, 475, 2)) (some 461) ([18]) (some (18, sourceBody475_2, 475, 3))

def sourceBody475_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody475_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_3 sourceBody475_4

def sourceBody475_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_5 sourceBody475_0

def sourceBody475_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_1 sourceBody475_6

def sourceBody475_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody475_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody475_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody475_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 6]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody475_0, 475, 4)) (some 119) ([16, 12]) (some (16, sourceBody475_10, 475, 5))

def sourceBody475_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_11 sourceBody475_4

def sourceBody475_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_12 sourceBody475_0

def sourceBody475_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_9 sourceBody475_13

def sourceBody475_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_8 sourceBody475_14

def sourceBody475_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody475_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody475_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody475_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody475_20 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 20) sourceBody475_18 sourceBody475_19

def sourceBody475_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_20 sourceBody475_4

def sourceBody475_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 12)

def sourceBody475_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 18446744073709551615#64)

def sourceBody475_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody475_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_24 sourceBody475_0

def sourceBody475_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_23 sourceBody475_25

def sourceBody475_27 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody475_26 sourceBody475_0

def sourceBody475_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_27 sourceBody475_4

def sourceBody475_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_28 sourceBody475_0

def sourceBody475_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_22 sourceBody475_29

def sourceBody475_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_21 sourceBody475_30

def sourceBody475_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_17 sourceBody475_31

def sourceBody475_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_16 sourceBody475_32

def sourceBody475_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody475_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 4 4 12 20))

def sourceBody475_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody475_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 18)
    (Flapjack.WordLangExpHOL.const 9#64))

def sourceBody475_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody475_39 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody475_0, 475, 6)) (some 459) ([14, 10]) (some (12, sourceBody475_38, 475, 7))

def sourceBody475_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_39 sourceBody475_4

def sourceBody475_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_40 sourceBody475_0

def sourceBody475_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_37 sourceBody475_41

def sourceBody475_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_36 sourceBody475_42

def sourceBody475_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_35 sourceBody475_43

def sourceBody475_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_34 sourceBody475_44

def sourceBody475_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_9 sourceBody475_45

def sourceBody475_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody475_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody475_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_48 sourceBody475_0

def sourceBody475_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_47 sourceBody475_49

def sourceBody475_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_46 sourceBody475_50

def sourceBody475_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_0 sourceBody475_51

def sourceBody475_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_0 sourceBody475_52

def sourceBody475_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_33 sourceBody475_53

def sourceBody475_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_15 sourceBody475_54

def sourceBody475_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_0 sourceBody475_55

def sourceBody475_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_0 sourceBody475_56

def sourceBody475_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_0 sourceBody475_57

def sourceBody475_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_0 sourceBody475_58

def sourceBody475_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_7 sourceBody475_59

def sourceBody475_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_0 sourceBody475_60

def sourceBody475_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody475_0 sourceBody475_61

def source475 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (475, 2, sourceBody475_62)
end InitECandidate.Proofs.WordStages
