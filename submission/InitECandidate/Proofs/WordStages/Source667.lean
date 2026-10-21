import InitECandidate.Proofs.WordStages.Source651
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody667_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody667_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody667_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody667_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody667_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 12) sourceBody667_2 sourceBody667_3

def sourceBody667_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody667_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_4 sourceBody667_5

def sourceBody667_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody667_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody667_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody667_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody667_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody667_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody667_8, 667, 2)) (some 665) ([14, 12]) (some (14, sourceBody667_11, 667, 3))

def sourceBody667_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_12 sourceBody667_5

def sourceBody667_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_13 sourceBody667_8

def sourceBody667_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_10 sourceBody667_14

def sourceBody667_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_9 sourceBody667_15

def sourceBody667_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_8 sourceBody667_16

def sourceBody667_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_8 sourceBody667_17

def sourceBody667_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody667_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody667_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_20 sourceBody667_8

def sourceBody667_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_19 sourceBody667_21

def sourceBody667_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_18 sourceBody667_22

def sourceBody667_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody667_23 sourceBody667_8

def sourceBody667_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_24 sourceBody667_5

def sourceBody667_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_25 sourceBody667_8

def sourceBody667_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_7 sourceBody667_26

def sourceBody667_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_6 sourceBody667_27

def sourceBody667_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_1 sourceBody667_28

def sourceBody667_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_0 sourceBody667_29

def sourceBody667_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody667_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody667_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody667_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody667_8, 667, 4)) (some 666) ([14, 12, 16, 8]) (some (14, sourceBody667_11, 667, 5))

def sourceBody667_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_34 sourceBody667_5

def sourceBody667_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_35 sourceBody667_8

def sourceBody667_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_33 sourceBody667_36

def sourceBody667_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_32 sourceBody667_37

def sourceBody667_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_31 sourceBody667_38

def sourceBody667_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_0 sourceBody667_39

def sourceBody667_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_8 sourceBody667_40

def sourceBody667_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_8 sourceBody667_41

def sourceBody667_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_30 sourceBody667_42

def sourceBody667_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody667_43 sourceBody667_22

def source667 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (667, 4, sourceBody667_44)
end InitECandidate.Proofs.WordStages
