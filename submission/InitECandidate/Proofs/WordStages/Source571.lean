import InitECandidate.Proofs.WordStages.Source555
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody571_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody571_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody571_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody571_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody571_0, 571, 2)) (some 466) ([16]) (some (16, sourceBody571_2, 571, 3))

def sourceBody571_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody571_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_3 sourceBody571_4

def sourceBody571_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_5 sourceBody571_0

def sourceBody571_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_1 sourceBody571_6

def sourceBody571_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_0 sourceBody571_7

def sourceBody571_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_0 sourceBody571_8

def sourceBody571_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody571_0, 571, 4)) (some 568) ([]) (some (16, sourceBody571_2, 571, 5))

def sourceBody571_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_10 sourceBody571_4

def sourceBody571_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_11 sourceBody571_0

def sourceBody571_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody571_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody571_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 4, 14, 10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody571_0, 571, 6)) (some 276) ([20]) (some (20, sourceBody571_14, 571, 7))

def sourceBody571_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_15 sourceBody571_4

def sourceBody571_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_16 sourceBody571_0

def sourceBody571_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_13 sourceBody571_17

def sourceBody571_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 16)

def sourceBody571_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody571_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody571_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody571_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody571_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody571_0, 571, 8)) (some 472) ([2, 12, 8, 18]) (some (2, sourceBody571_23, 571, 9))

def sourceBody571_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_24 sourceBody571_4

def sourceBody571_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_25 sourceBody571_0

def sourceBody571_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_22 sourceBody571_26

def sourceBody571_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_21 sourceBody571_27

def sourceBody571_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_20 sourceBody571_28

def sourceBody571_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_19 sourceBody571_29

def sourceBody571_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_0 sourceBody571_30

def sourceBody571_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_0 sourceBody571_31

def sourceBody571_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody571_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody571_0, 571, 10)) (some 486) ([2]) (some (2, sourceBody571_23, 571, 11))

def sourceBody571_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_34 sourceBody571_4

def sourceBody571_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_35 sourceBody571_0

def sourceBody571_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_33 sourceBody571_36

def sourceBody571_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_0 sourceBody571_37

def sourceBody571_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_0 sourceBody571_38

def sourceBody571_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_32 sourceBody571_39

def sourceBody571_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody571_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody571_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_42 sourceBody571_0

def sourceBody571_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_41 sourceBody571_43

def sourceBody571_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_40 sourceBody571_44

def sourceBody571_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_18 sourceBody571_45

def sourceBody571_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_0 sourceBody571_46

def sourceBody571_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_0 sourceBody571_47

def sourceBody571_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_0 sourceBody571_48

def sourceBody571_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_0 sourceBody571_49

def sourceBody571_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_0 sourceBody571_50

def sourceBody571_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_0 sourceBody571_51

def sourceBody571_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_0 sourceBody571_52

def sourceBody571_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_0 sourceBody571_53

def sourceBody571_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_12 sourceBody571_54

def sourceBody571_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_0 sourceBody571_55

def sourceBody571_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_0 sourceBody571_56

def sourceBody571_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody571_9 sourceBody571_57

def source571 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (571, 1, sourceBody571_58)
end InitECandidate.Proofs.WordStages
