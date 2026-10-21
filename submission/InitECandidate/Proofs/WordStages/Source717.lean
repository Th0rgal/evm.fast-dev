import InitECandidate.Proofs.WordStages.Source701
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody717_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody717_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 2)

def sourceBody717_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 4)

def sourceBody717_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 6)

def sourceBody717_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody717_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody717_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody717_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody717_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([44, 16, 34, 26, 42, 22]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody717_0, 717, 2)) (some 716) ([38, 30, 48, 14, 32, 24]) (some (38, sourceBody717_7, 717, 3))

def sourceBody717_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody717_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_8 sourceBody717_9

def sourceBody717_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_10 sourceBody717_0

def sourceBody717_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_6 sourceBody717_11

def sourceBody717_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_5 sourceBody717_12

def sourceBody717_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_4 sourceBody717_13

def sourceBody717_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_3 sourceBody717_14

def sourceBody717_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_2 sourceBody717_15

def sourceBody717_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_1 sourceBody717_16

def sourceBody717_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 44)

def sourceBody717_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 16)

def sourceBody717_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 34)

def sourceBody717_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 26)

def sourceBody717_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 42)

def sourceBody717_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 22)

def sourceBody717_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 17098105564519244256#64)

def sourceBody717_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 3557706395579559416#64)

def sourceBody717_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 11120290361046346205#64)

def sourceBody717_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 3801124253586036577#64)

def sourceBody717_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 2671430854784468776#64)

def sourceBody717_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 767358375875140941#64)

def sourceBody717_30 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 710) ([0, 38, 30, 48, 14, 32, 24, 40, 20, 36, 28, 46, 18]) (none)

def sourceBody717_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_30 sourceBody717_0

def sourceBody717_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_29 sourceBody717_31

def sourceBody717_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_28 sourceBody717_32

def sourceBody717_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_27 sourceBody717_33

def sourceBody717_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_26 sourceBody717_34

def sourceBody717_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_25 sourceBody717_35

def sourceBody717_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_24 sourceBody717_36

def sourceBody717_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_23 sourceBody717_37

def sourceBody717_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_22 sourceBody717_38

def sourceBody717_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_21 sourceBody717_39

def sourceBody717_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_20 sourceBody717_40

def sourceBody717_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_19 sourceBody717_41

def sourceBody717_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_18 sourceBody717_42

def sourceBody717_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_17 sourceBody717_43

def sourceBody717_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_0 sourceBody717_44

def sourceBody717_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_0 sourceBody717_45

def sourceBody717_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_0 sourceBody717_46

def sourceBody717_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_0 sourceBody717_47

def sourceBody717_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_0 sourceBody717_48

def sourceBody717_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_0 sourceBody717_49

def sourceBody717_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_0 sourceBody717_50

def sourceBody717_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_0 sourceBody717_51

def sourceBody717_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_0 sourceBody717_52

def sourceBody717_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_0 sourceBody717_53

def sourceBody717_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_0 sourceBody717_54

def sourceBody717_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody717_0 sourceBody717_55

def source717 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (717, 7, sourceBody717_56)
end InitECandidate.Proofs.WordStages
