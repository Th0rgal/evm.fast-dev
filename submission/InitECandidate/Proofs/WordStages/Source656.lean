import InitECandidate.Proofs.WordStages.Source640
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody656_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody656_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody656_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 4)

def sourceBody656_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody656_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody656_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody656_6 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody656_0, 656, 2)) (some 102) ([16, 26, 10, 18]) (some (16, sourceBody656_5, 656, 3))

def sourceBody656_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody656_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_6 sourceBody656_7

def sourceBody656_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_8 sourceBody656_0

def sourceBody656_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_4 sourceBody656_9

def sourceBody656_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_3 sourceBody656_10

def sourceBody656_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_2 sourceBody656_11

def sourceBody656_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_1 sourceBody656_12

def sourceBody656_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 20)

def sourceBody656_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody656_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody656_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody656_18 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 26 (Flapjack.WordRegImm.reg 10) sourceBody656_16 sourceBody656_17

def sourceBody656_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_18 sourceBody656_7

def sourceBody656_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 26)

def sourceBody656_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody656_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody656_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody656_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16, 26, 10, 18]

def sourceBody656_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_24 sourceBody656_0

def sourceBody656_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_23 sourceBody656_25

def sourceBody656_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_22 sourceBody656_26

def sourceBody656_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_17 sourceBody656_27

def sourceBody656_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_21 sourceBody656_28

def sourceBody656_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody656_29 sourceBody656_0

def sourceBody656_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_30 sourceBody656_7

def sourceBody656_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_31 sourceBody656_0

def sourceBody656_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_20 sourceBody656_32

def sourceBody656_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_19 sourceBody656_33

def sourceBody656_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_15 sourceBody656_34

def sourceBody656_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_14 sourceBody656_35

def sourceBody656_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 4332616871279656263#64)

def sourceBody656_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 10917124144477883021#64)

def sourceBody656_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 13281191951274694749#64)

def sourceBody656_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 3486998266802970665#64)

def sourceBody656_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody656_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody656_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody656_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 8)

def sourceBody656_45 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 117) ([0, 16, 26, 10, 18, 14, 24, 12, 22]) (none)

def sourceBody656_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_45 sourceBody656_0

def sourceBody656_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_44 sourceBody656_46

def sourceBody656_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_43 sourceBody656_47

def sourceBody656_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_42 sourceBody656_48

def sourceBody656_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_41 sourceBody656_49

def sourceBody656_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_40 sourceBody656_50

def sourceBody656_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_39 sourceBody656_51

def sourceBody656_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_38 sourceBody656_52

def sourceBody656_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_37 sourceBody656_53

def sourceBody656_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_36 sourceBody656_54

def sourceBody656_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_13 sourceBody656_55

def sourceBody656_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_0 sourceBody656_56

def sourceBody656_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody656_0 sourceBody656_57

def source656 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (656, 5, sourceBody656_58)
end InitECandidate.Proofs.WordStages
