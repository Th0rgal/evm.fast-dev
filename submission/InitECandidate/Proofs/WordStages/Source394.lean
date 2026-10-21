import InitECandidate.Proofs.WordStages.Source378
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody394_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody394_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody394_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody394_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 16, 6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody394_0, 394, 2)) (some 393) ([14]) (some (14, sourceBody394_2, 394, 3))

def sourceBody394_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody394_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_3 sourceBody394_4

def sourceBody394_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_5 sourceBody394_0

def sourceBody394_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_1 sourceBody394_6

def sourceBody394_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody394_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody394_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody394_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody394_12 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 18) sourceBody394_10 sourceBody394_11

def sourceBody394_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_12 sourceBody394_4

def sourceBody394_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody394_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody394_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody394_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_16 sourceBody394_0

def sourceBody394_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_15 sourceBody394_17

def sourceBody394_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody394_18 sourceBody394_0

def sourceBody394_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_19 sourceBody394_4

def sourceBody394_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_20 sourceBody394_0

def sourceBody394_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_14 sourceBody394_21

def sourceBody394_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_13 sourceBody394_22

def sourceBody394_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_9 sourceBody394_23

def sourceBody394_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_8 sourceBody394_24

def sourceBody394_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 56#64)

def sourceBody394_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody394_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody394_0, 394, 4)) (some 68) ([10]) (some (10, sourceBody394_27, 394, 5))

def sourceBody394_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_28 sourceBody394_4

def sourceBody394_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_29 sourceBody394_0

def sourceBody394_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_26 sourceBody394_30

def sourceBody394_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody394_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody394_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody394_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody394_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody394_0, 394, 6)) (some 329) ([18, 4, 12]) (some (18, sourceBody394_35, 394, 7))

def sourceBody394_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_36 sourceBody394_4

def sourceBody394_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_37 sourceBody394_0

def sourceBody394_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_34 sourceBody394_38

def sourceBody394_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_33 sourceBody394_39

def sourceBody394_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_32 sourceBody394_40

def sourceBody394_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_0 sourceBody394_41

def sourceBody394_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_0 sourceBody394_42

def sourceBody394_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody394_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody394_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_45 sourceBody394_0

def sourceBody394_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_44 sourceBody394_46

def sourceBody394_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_43 sourceBody394_47

def sourceBody394_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_31 sourceBody394_48

def sourceBody394_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_0 sourceBody394_49

def sourceBody394_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_0 sourceBody394_50

def sourceBody394_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_25 sourceBody394_51

def sourceBody394_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_7 sourceBody394_52

def sourceBody394_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_0 sourceBody394_53

def sourceBody394_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_0 sourceBody394_54

def sourceBody394_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_0 sourceBody394_55

def sourceBody394_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_0 sourceBody394_56

def sourceBody394_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_0 sourceBody394_57

def sourceBody394_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody394_0 sourceBody394_58

def source394 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (394, 2, sourceBody394_59)
end InitECandidate.Proofs.WordStages
