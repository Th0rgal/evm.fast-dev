import InitECandidate.Proofs.WordStages.Source557
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody573_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody573_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody573_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody573_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody573_0, 573, 2)) (some 466) ([16]) (some (16, sourceBody573_2, 573, 3))

def sourceBody573_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody573_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_3 sourceBody573_4

def sourceBody573_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_5 sourceBody573_0

def sourceBody573_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_1 sourceBody573_6

def sourceBody573_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_0 sourceBody573_7

def sourceBody573_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_0 sourceBody573_8

def sourceBody573_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody573_0, 573, 4)) (some 568) ([]) (some (16, sourceBody573_2, 573, 5))

def sourceBody573_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_10 sourceBody573_4

def sourceBody573_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_11 sourceBody573_0

def sourceBody573_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody573_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody573_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 4, 14, 10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody573_0, 573, 6)) (some 463) ([20]) (some (20, sourceBody573_14, 573, 7))

def sourceBody573_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_15 sourceBody573_4

def sourceBody573_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_16 sourceBody573_0

def sourceBody573_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_13 sourceBody573_17

def sourceBody573_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 16)

def sourceBody573_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody573_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody573_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody573_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody573_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody573_0, 573, 8)) (some 472) ([2, 12, 8, 18]) (some (2, sourceBody573_23, 573, 9))

def sourceBody573_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_24 sourceBody573_4

def sourceBody573_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_25 sourceBody573_0

def sourceBody573_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_22 sourceBody573_26

def sourceBody573_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_21 sourceBody573_27

def sourceBody573_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_20 sourceBody573_28

def sourceBody573_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_19 sourceBody573_29

def sourceBody573_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_0 sourceBody573_30

def sourceBody573_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_0 sourceBody573_31

def sourceBody573_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody573_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody573_0, 573, 10)) (some 486) ([2]) (some (2, sourceBody573_23, 573, 11))

def sourceBody573_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_34 sourceBody573_4

def sourceBody573_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_35 sourceBody573_0

def sourceBody573_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_33 sourceBody573_36

def sourceBody573_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_0 sourceBody573_37

def sourceBody573_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_0 sourceBody573_38

def sourceBody573_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_32 sourceBody573_39

def sourceBody573_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody573_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody573_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_42 sourceBody573_0

def sourceBody573_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_41 sourceBody573_43

def sourceBody573_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_40 sourceBody573_44

def sourceBody573_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_18 sourceBody573_45

def sourceBody573_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_0 sourceBody573_46

def sourceBody573_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_0 sourceBody573_47

def sourceBody573_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_0 sourceBody573_48

def sourceBody573_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_0 sourceBody573_49

def sourceBody573_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_0 sourceBody573_50

def sourceBody573_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_0 sourceBody573_51

def sourceBody573_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_0 sourceBody573_52

def sourceBody573_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_0 sourceBody573_53

def sourceBody573_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_12 sourceBody573_54

def sourceBody573_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_0 sourceBody573_55

def sourceBody573_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_0 sourceBody573_56

def sourceBody573_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody573_9 sourceBody573_57

def source573 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (573, 1, sourceBody573_58)
end InitECandidate.Proofs.WordStages
