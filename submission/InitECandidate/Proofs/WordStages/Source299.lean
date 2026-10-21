import InitECandidate.Proofs.WordStages.Source283
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody299_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody299_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody299_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody299_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody299_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody299_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody299_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.lookup (Flapjack.WordStore.temp 0#5))

def sourceBody299_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_6 sourceBody299_0

def sourceBody299_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_7 sourceBody299_0

def sourceBody299_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody299_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody299_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody299_0, 299, 3)) (some 76) ([10]) (some (10, sourceBody299_10, 299, 4))

def sourceBody299_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_11 sourceBody299_5

def sourceBody299_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_12 sourceBody299_0

def sourceBody299_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_9 sourceBody299_13

def sourceBody299_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_0 sourceBody299_14

def sourceBody299_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_0 sourceBody299_15

def sourceBody299_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody299_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 18)

def sourceBody299_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_18 sourceBody299_0

def sourceBody299_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_19 sourceBody299_0

def sourceBody299_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_17 sourceBody299_20

def sourceBody299_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_0 sourceBody299_21

def sourceBody299_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody299_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_23 sourceBody299_4

def sourceBody299_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_22 sourceBody299_24

def sourceBody299_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_16 sourceBody299_25

def sourceBody299_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_8 sourceBody299_26

def sourceBody299_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_5 sourceBody299_27

def sourceBody299_29 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 5#64) sourceBody299_4 sourceBody299_28

def sourceBody299_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_29 sourceBody299_5

def sourceBody299_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody299_0, 299, 2)) (some 298) ([18, 10, 14]) (some (18, sourceBody299_30, 299, 5))

def sourceBody299_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_31 sourceBody299_5

def sourceBody299_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_32 sourceBody299_0

def sourceBody299_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_3 sourceBody299_33

def sourceBody299_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_2 sourceBody299_34

def sourceBody299_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_1 sourceBody299_35

def sourceBody299_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody299_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody299_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_38 sourceBody299_0

def sourceBody299_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_37 sourceBody299_39

def sourceBody299_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_36 sourceBody299_40

def sourceBody299_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_0 sourceBody299_41

def sourceBody299_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_0 sourceBody299_42

def sourceBody299_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_0 sourceBody299_43

def sourceBody299_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody299_0 sourceBody299_44

def source299 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (299, 5, sourceBody299_45)
end InitECandidate.Proofs.WordStages
