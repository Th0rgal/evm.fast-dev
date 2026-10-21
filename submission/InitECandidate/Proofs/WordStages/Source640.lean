import InitECandidate.Proofs.WordStages.Source624
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody640_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody640_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody640_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 4)

def sourceBody640_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody640_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody640_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 18446744073709551615#64)

def sourceBody640_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 4294967295#64)

def sourceBody640_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody640_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 18446744069414584321#64)

def sourceBody640_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody640_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody640_0, 640, 2)) (some 106) ([16, 26, 10, 18, 14, 24, 12, 22]) (some (16, sourceBody640_9, 640, 3))

def sourceBody640_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody640_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_10 sourceBody640_11

def sourceBody640_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_12 sourceBody640_0

def sourceBody640_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_8 sourceBody640_13

def sourceBody640_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_7 sourceBody640_14

def sourceBody640_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_6 sourceBody640_15

def sourceBody640_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_5 sourceBody640_16

def sourceBody640_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_4 sourceBody640_17

def sourceBody640_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_3 sourceBody640_18

def sourceBody640_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_2 sourceBody640_19

def sourceBody640_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_1 sourceBody640_20

def sourceBody640_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 20)

def sourceBody640_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody640_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody640_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody640_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 26 (Flapjack.WordRegImm.reg 10) sourceBody640_24 sourceBody640_25

def sourceBody640_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_26 sourceBody640_11

def sourceBody640_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 26)

def sourceBody640_29 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 117) ([0, 16, 26, 10, 18, 14, 24, 12, 22]) (none)

def sourceBody640_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_29 sourceBody640_0

def sourceBody640_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_8 sourceBody640_30

def sourceBody640_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_7 sourceBody640_31

def sourceBody640_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_6 sourceBody640_32

def sourceBody640_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_5 sourceBody640_33

def sourceBody640_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_4 sourceBody640_34

def sourceBody640_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_3 sourceBody640_35

def sourceBody640_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_2 sourceBody640_36

def sourceBody640_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_1 sourceBody640_37

def sourceBody640_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody640_38 sourceBody640_0

def sourceBody640_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_39 sourceBody640_11

def sourceBody640_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_40 sourceBody640_0

def sourceBody640_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_28 sourceBody640_41

def sourceBody640_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_27 sourceBody640_42

def sourceBody640_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_23 sourceBody640_43

def sourceBody640_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_22 sourceBody640_44

def sourceBody640_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16, 26, 10, 18]

def sourceBody640_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_46 sourceBody640_0

def sourceBody640_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_4 sourceBody640_47

def sourceBody640_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_3 sourceBody640_48

def sourceBody640_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_2 sourceBody640_49

def sourceBody640_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_1 sourceBody640_50

def sourceBody640_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_45 sourceBody640_51

def sourceBody640_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_21 sourceBody640_52

def sourceBody640_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_0 sourceBody640_53

def sourceBody640_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody640_0 sourceBody640_54

def source640 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (640, 5, sourceBody640_55)
end InitECandidate.Proofs.WordStages
