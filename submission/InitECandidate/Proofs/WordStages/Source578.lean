import InitECandidate.Proofs.WordStages.Source562
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody578_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody578_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody578_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody578_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody578_0, 578, 2)) (some 466) ([16]) (some (16, sourceBody578_2, 578, 3))

def sourceBody578_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody578_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_3 sourceBody578_4

def sourceBody578_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_5 sourceBody578_0

def sourceBody578_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_1 sourceBody578_6

def sourceBody578_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_0 sourceBody578_7

def sourceBody578_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_0 sourceBody578_8

def sourceBody578_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody578_0, 578, 4)) (some 568) ([]) (some (16, sourceBody578_2, 578, 5))

def sourceBody578_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_10 sourceBody578_4

def sourceBody578_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_11 sourceBody578_0

def sourceBody578_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody578_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody578_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody578_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 4, 14, 10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody578_0, 578, 6)) (some 146) ([20, 2]) (some (20, sourceBody578_15, 578, 7))

def sourceBody578_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_16 sourceBody578_4

def sourceBody578_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_17 sourceBody578_0

def sourceBody578_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_14 sourceBody578_18

def sourceBody578_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_13 sourceBody578_19

def sourceBody578_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 16)

def sourceBody578_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody578_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody578_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody578_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody578_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody578_0, 578, 8)) (some 472) ([2, 12, 8, 18]) (some (2, sourceBody578_25, 578, 9))

def sourceBody578_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_26 sourceBody578_4

def sourceBody578_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_27 sourceBody578_0

def sourceBody578_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_24 sourceBody578_28

def sourceBody578_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_23 sourceBody578_29

def sourceBody578_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_22 sourceBody578_30

def sourceBody578_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_21 sourceBody578_31

def sourceBody578_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_0 sourceBody578_32

def sourceBody578_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_0 sourceBody578_33

def sourceBody578_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody578_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody578_0, 578, 10)) (some 486) ([2]) (some (2, sourceBody578_25, 578, 11))

def sourceBody578_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_36 sourceBody578_4

def sourceBody578_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_37 sourceBody578_0

def sourceBody578_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_35 sourceBody578_38

def sourceBody578_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_0 sourceBody578_39

def sourceBody578_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_0 sourceBody578_40

def sourceBody578_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_34 sourceBody578_41

def sourceBody578_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody578_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody578_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_44 sourceBody578_0

def sourceBody578_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_43 sourceBody578_45

def sourceBody578_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_42 sourceBody578_46

def sourceBody578_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_20 sourceBody578_47

def sourceBody578_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_0 sourceBody578_48

def sourceBody578_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_0 sourceBody578_49

def sourceBody578_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_0 sourceBody578_50

def sourceBody578_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_0 sourceBody578_51

def sourceBody578_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_0 sourceBody578_52

def sourceBody578_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_0 sourceBody578_53

def sourceBody578_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_0 sourceBody578_54

def sourceBody578_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_0 sourceBody578_55

def sourceBody578_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_12 sourceBody578_56

def sourceBody578_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_0 sourceBody578_57

def sourceBody578_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_0 sourceBody578_58

def sourceBody578_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody578_9 sourceBody578_59

def source578 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (578, 1, sourceBody578_60)
end InitECandidate.Proofs.WordStages
