import InitECandidate.Proofs.WordStages.Source704
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody720_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody720_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 2)

def sourceBody720_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 4)

def sourceBody720_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 6)

def sourceBody720_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody720_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody720_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody720_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody720_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([46, 16, 34, 26, 44, 22]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody720_0, 720, 2)) (some 713) ([40, 30, 50, 14, 32, 24]) (some (40, sourceBody720_7, 720, 3))

def sourceBody720_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody720_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_8 sourceBody720_9

def sourceBody720_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_10 sourceBody720_0

def sourceBody720_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_6 sourceBody720_11

def sourceBody720_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_5 sourceBody720_12

def sourceBody720_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_4 sourceBody720_13

def sourceBody720_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_3 sourceBody720_14

def sourceBody720_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_2 sourceBody720_15

def sourceBody720_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_1 sourceBody720_16

def sourceBody720_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 15924587544893707605#64)

def sourceBody720_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 1105070755758604287#64)

def sourceBody720_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 12941209323636816658#64)

def sourceBody720_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 12843041017062132063#64)

def sourceBody720_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 2706051889235351147#64)

def sourceBody720_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 936899308823769933#64)

def sourceBody720_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 46)

def sourceBody720_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 16)

def sourceBody720_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 34)

def sourceBody720_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 26)

def sourceBody720_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 44)

def sourceBody720_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 22)

def sourceBody720_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody720_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody720_0, 720, 4)) (some 703) ([30, 50, 14, 32, 24, 42, 20, 38, 28, 48, 18, 36]) (some (30, sourceBody720_30, 720, 5))

def sourceBody720_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_31 sourceBody720_9

def sourceBody720_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_32 sourceBody720_0

def sourceBody720_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_29 sourceBody720_33

def sourceBody720_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_28 sourceBody720_34

def sourceBody720_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_27 sourceBody720_35

def sourceBody720_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_26 sourceBody720_36

def sourceBody720_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_25 sourceBody720_37

def sourceBody720_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_24 sourceBody720_38

def sourceBody720_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_23 sourceBody720_39

def sourceBody720_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_22 sourceBody720_40

def sourceBody720_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_21 sourceBody720_41

def sourceBody720_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_20 sourceBody720_42

def sourceBody720_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_19 sourceBody720_43

def sourceBody720_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_18 sourceBody720_44

def sourceBody720_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 40)

def sourceBody720_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30]

def sourceBody720_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_47 sourceBody720_0

def sourceBody720_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_46 sourceBody720_48

def sourceBody720_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_45 sourceBody720_49

def sourceBody720_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_0 sourceBody720_50

def sourceBody720_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_0 sourceBody720_51

def sourceBody720_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_17 sourceBody720_52

def sourceBody720_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_0 sourceBody720_53

def sourceBody720_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_0 sourceBody720_54

def sourceBody720_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_0 sourceBody720_55

def sourceBody720_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_0 sourceBody720_56

def sourceBody720_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_0 sourceBody720_57

def sourceBody720_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_0 sourceBody720_58

def sourceBody720_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_0 sourceBody720_59

def sourceBody720_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_0 sourceBody720_60

def sourceBody720_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_0 sourceBody720_61

def sourceBody720_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_0 sourceBody720_62

def sourceBody720_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_0 sourceBody720_63

def sourceBody720_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody720_0 sourceBody720_64

def source720 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (720, 7, sourceBody720_65)
end InitECandidate.Proofs.WordStages
