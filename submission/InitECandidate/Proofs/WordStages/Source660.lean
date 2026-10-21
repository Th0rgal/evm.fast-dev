import InitECandidate.Proofs.WordStages.Source644
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody660_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody660_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 2)

def sourceBody660_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody660_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 6)

def sourceBody660_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody660_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 4332616871279656263#64)

def sourceBody660_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 10917124144477883021#64)

def sourceBody660_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 13281191951274694749#64)

def sourceBody660_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 3486998266802970665#64)

def sourceBody660_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody660_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([24, 18, 30, 12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody660_0, 660, 2)) (some 210) ([22, 16, 28, 14, 26, 20, 32, 10]) (some (22, sourceBody660_9, 660, 3))

def sourceBody660_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody660_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_10 sourceBody660_11

def sourceBody660_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_12 sourceBody660_0

def sourceBody660_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_8 sourceBody660_13

def sourceBody660_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_7 sourceBody660_14

def sourceBody660_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_6 sourceBody660_15

def sourceBody660_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_5 sourceBody660_16

def sourceBody660_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_4 sourceBody660_17

def sourceBody660_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_3 sourceBody660_18

def sourceBody660_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_2 sourceBody660_19

def sourceBody660_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_1 sourceBody660_20

def sourceBody660_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 24)

def sourceBody660_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody660_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 30)

def sourceBody660_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody660_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 12812017116984455391#64)

def sourceBody660_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 7129779742913871286#64)

def sourceBody660_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 17257524443456604923#64)

def sourceBody660_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 2377177743836652868#64)

def sourceBody660_30 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 657) ([0, 22, 16, 28, 14, 26, 20, 32, 10]) (none)

def sourceBody660_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_30 sourceBody660_0

def sourceBody660_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_29 sourceBody660_31

def sourceBody660_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_28 sourceBody660_32

def sourceBody660_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_27 sourceBody660_33

def sourceBody660_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_26 sourceBody660_34

def sourceBody660_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_25 sourceBody660_35

def sourceBody660_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_24 sourceBody660_36

def sourceBody660_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_23 sourceBody660_37

def sourceBody660_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_22 sourceBody660_38

def sourceBody660_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_21 sourceBody660_39

def sourceBody660_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_0 sourceBody660_40

def sourceBody660_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_0 sourceBody660_41

def sourceBody660_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_0 sourceBody660_42

def sourceBody660_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_0 sourceBody660_43

def sourceBody660_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_0 sourceBody660_44

def sourceBody660_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_0 sourceBody660_45

def sourceBody660_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_0 sourceBody660_46

def sourceBody660_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody660_0 sourceBody660_47

def source660 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (660, 5, sourceBody660_48)
end InitECandidate.Proofs.WordStages
