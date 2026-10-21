import InitECandidate.Proofs.WordStages.Source251
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody267_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody267_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody267_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 4)

def sourceBody267_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody267_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody267_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody267_0, 267, 2)) (some 265) ([16, 26, 8]) (some (16, sourceBody267_4, 267, 3))

def sourceBody267_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody267_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_5 sourceBody267_6

def sourceBody267_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_7 sourceBody267_0

def sourceBody267_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_3 sourceBody267_8

def sourceBody267_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_2 sourceBody267_9

def sourceBody267_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_1 sourceBody267_10

def sourceBody267_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody267_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 20)

def sourceBody267_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody267_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody267_16 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 26 (Flapjack.WordRegImm.reg 8) sourceBody267_14 sourceBody267_15

def sourceBody267_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_16 sourceBody267_6

def sourceBody267_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 26)

def sourceBody267_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody267_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 16)

def sourceBody267_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_20 sourceBody267_0

def sourceBody267_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_21 sourceBody267_0

def sourceBody267_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_19 sourceBody267_22

def sourceBody267_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_0 sourceBody267_23

def sourceBody267_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody267_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_25 sourceBody267_4

def sourceBody267_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_24 sourceBody267_26

def sourceBody267_28 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody267_27 sourceBody267_0

def sourceBody267_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_28 sourceBody267_6

def sourceBody267_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_29 sourceBody267_0

def sourceBody267_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_18 sourceBody267_30

def sourceBody267_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_17 sourceBody267_31

def sourceBody267_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_13 sourceBody267_32

def sourceBody267_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_12 sourceBody267_33

def sourceBody267_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody267_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 20)

def sourceBody267_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody267_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 26, 8, 18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody267_0, 267, 4)) (some 146) ([14, 24]) (some (14, sourceBody267_37, 267, 5))

def sourceBody267_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_38 sourceBody267_6

def sourceBody267_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_39 sourceBody267_0

def sourceBody267_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_36 sourceBody267_40

def sourceBody267_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_35 sourceBody267_41

def sourceBody267_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody267_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody267_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody267_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody267_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14, 24, 12, 22]

def sourceBody267_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_47 sourceBody267_0

def sourceBody267_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_46 sourceBody267_48

def sourceBody267_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_45 sourceBody267_49

def sourceBody267_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_44 sourceBody267_50

def sourceBody267_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_43 sourceBody267_51

def sourceBody267_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_42 sourceBody267_52

def sourceBody267_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_0 sourceBody267_53

def sourceBody267_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_0 sourceBody267_54

def sourceBody267_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_0 sourceBody267_55

def sourceBody267_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_0 sourceBody267_56

def sourceBody267_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_0 sourceBody267_57

def sourceBody267_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_0 sourceBody267_58

def sourceBody267_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_0 sourceBody267_59

def sourceBody267_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_0 sourceBody267_60

def sourceBody267_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_34 sourceBody267_61

def sourceBody267_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_11 sourceBody267_62

def sourceBody267_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_0 sourceBody267_63

def sourceBody267_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_0 sourceBody267_64

def sourceBody267_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_0 sourceBody267_65

def sourceBody267_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody267_0 sourceBody267_66

def source267 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (267, 4, sourceBody267_67)
end InitECandidate.Proofs.WordStages
