import InitECandidate.Proofs.WordStages.Source438
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody454_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody454_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody454_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody454_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 8]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody454_0, 454, 2)) (some 198) ([16]) (some (16, sourceBody454_2, 454, 3))

def sourceBody454_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody454_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_3 sourceBody454_4

def sourceBody454_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_5 sourceBody454_0

def sourceBody454_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_1 sourceBody454_6

def sourceBody454_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody454_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody454_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody454_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody454_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody454_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody454_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody454_0, 454, 4)) (some 453) ([12, 20, 6, 14, 10]) (some (12, sourceBody454_13, 454, 5))

def sourceBody454_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_14 sourceBody454_4

def sourceBody454_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_15 sourceBody454_0

def sourceBody454_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_12 sourceBody454_16

def sourceBody454_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_11 sourceBody454_17

def sourceBody454_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_10 sourceBody454_18

def sourceBody454_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_9 sourceBody454_19

def sourceBody454_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_8 sourceBody454_20

def sourceBody454_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_0 sourceBody454_21

def sourceBody454_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_0 sourceBody454_22

def sourceBody454_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody454_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody454_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16, 12]

def sourceBody454_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_26 sourceBody454_0

def sourceBody454_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_25 sourceBody454_27

def sourceBody454_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_24 sourceBody454_28

def sourceBody454_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_23 sourceBody454_29

def sourceBody454_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_7 sourceBody454_30

def sourceBody454_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_0 sourceBody454_31

def sourceBody454_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_0 sourceBody454_32

def sourceBody454_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_0 sourceBody454_33

def sourceBody454_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody454_0 sourceBody454_34

def source454 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (454, 3, sourceBody454_35)
end InitECandidate.Proofs.WordStages
