import InitECandidate.Proofs.WordStages.Source837
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody853_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody853_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 2)

def sourceBody853_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody853_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody853_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody853_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody853_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 6)

def sourceBody853_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody853_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody853_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody853_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([24, 40, 14, 30, 22, 38, 18, 34]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody853_0, 853, 2)) (some 121) ([26, 42, 12, 28, 20, 36, 16, 32]) (some (26, sourceBody853_9, 853, 3))

def sourceBody853_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody853_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_10 sourceBody853_11

def sourceBody853_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_12 sourceBody853_0

def sourceBody853_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_8 sourceBody853_13

def sourceBody853_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_7 sourceBody853_14

def sourceBody853_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_6 sourceBody853_15

def sourceBody853_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_5 sourceBody853_16

def sourceBody853_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_4 sourceBody853_17

def sourceBody853_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_3 sourceBody853_18

def sourceBody853_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_2 sourceBody853_19

def sourceBody853_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_1 sourceBody853_20

def sourceBody853_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody853_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.var 18,
      Flapjack.WordLangExpHOL.var 34])

def sourceBody853_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody853_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 28) sourceBody853_24 sourceBody853_3

def sourceBody853_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_25 sourceBody853_11

def sourceBody853_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody853_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody853_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_28 sourceBody853_0

def sourceBody853_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_29 sourceBody853_0

def sourceBody853_31 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody853_30 sourceBody853_0

def sourceBody853_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_31 sourceBody853_11

def sourceBody853_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_32 sourceBody853_0

def sourceBody853_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_27 sourceBody853_33

def sourceBody853_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_26 sourceBody853_34

def sourceBody853_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_4 sourceBody853_35

def sourceBody853_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_23 sourceBody853_36

def sourceBody853_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 26)

def sourceBody853_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 24)

def sourceBody853_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 40)

def sourceBody853_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody853_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 30)

def sourceBody853_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [42, 12, 28, 20, 36]

def sourceBody853_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_43 sourceBody853_0

def sourceBody853_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_42 sourceBody853_44

def sourceBody853_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_41 sourceBody853_45

def sourceBody853_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_40 sourceBody853_46

def sourceBody853_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_39 sourceBody853_47

def sourceBody853_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_38 sourceBody853_48

def sourceBody853_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_37 sourceBody853_49

def sourceBody853_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_22 sourceBody853_50

def sourceBody853_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_0 sourceBody853_51

def sourceBody853_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_21 sourceBody853_52

def sourceBody853_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_0 sourceBody853_53

def sourceBody853_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_0 sourceBody853_54

def sourceBody853_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_0 sourceBody853_55

def sourceBody853_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_0 sourceBody853_56

def sourceBody853_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_0 sourceBody853_57

def sourceBody853_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_0 sourceBody853_58

def sourceBody853_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_0 sourceBody853_59

def sourceBody853_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_0 sourceBody853_60

def sourceBody853_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_0 sourceBody853_61

def sourceBody853_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_0 sourceBody853_62

def sourceBody853_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_0 sourceBody853_63

def sourceBody853_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_0 sourceBody853_64

def sourceBody853_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_0 sourceBody853_65

def sourceBody853_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_0 sourceBody853_66

def sourceBody853_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_0 sourceBody853_67

def sourceBody853_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody853_0 sourceBody853_68

def source853 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (853, 6, sourceBody853_69)
end InitECandidate.Proofs.WordStages
