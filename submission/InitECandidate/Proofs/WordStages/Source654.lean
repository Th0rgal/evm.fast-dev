import InitECandidate.Proofs.WordStages.Source638
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody654_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody654_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 2)

def sourceBody654_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody654_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 6)

def sourceBody654_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody654_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 10)

def sourceBody654_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody654_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 14)

def sourceBody654_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody654_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody654_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([32, 26, 40, 22]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody654_0, 654, 2)) (some 116) ([36, 28, 42, 18, 30, 24, 38, 20]) (some (36, sourceBody654_9, 654, 3))

def sourceBody654_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody654_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_10 sourceBody654_11

def sourceBody654_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_12 sourceBody654_0

def sourceBody654_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_8 sourceBody654_13

def sourceBody654_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_7 sourceBody654_14

def sourceBody654_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_6 sourceBody654_15

def sourceBody654_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_5 sourceBody654_16

def sourceBody654_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_4 sourceBody654_17

def sourceBody654_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_3 sourceBody654_18

def sourceBody654_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_2 sourceBody654_19

def sourceBody654_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_1 sourceBody654_20

def sourceBody654_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 32)

def sourceBody654_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 26)

def sourceBody654_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 40)

def sourceBody654_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 22)

def sourceBody654_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 4332616871279656263#64)

def sourceBody654_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 10917124144477883021#64)

def sourceBody654_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 13281191951274694749#64)

def sourceBody654_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 3486998266802970665#64)

def sourceBody654_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody654_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody654_0, 654, 4)) (some 106) ([28, 42, 18, 30, 24, 38, 20, 34]) (some (28, sourceBody654_30, 654, 5))

def sourceBody654_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_31 sourceBody654_11

def sourceBody654_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_32 sourceBody654_0

def sourceBody654_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_29 sourceBody654_33

def sourceBody654_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_28 sourceBody654_34

def sourceBody654_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_27 sourceBody654_35

def sourceBody654_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_26 sourceBody654_36

def sourceBody654_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_25 sourceBody654_37

def sourceBody654_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_24 sourceBody654_38

def sourceBody654_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_23 sourceBody654_39

def sourceBody654_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_22 sourceBody654_40

def sourceBody654_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 36)

def sourceBody654_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody654_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody654_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody654_46 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 42 (Flapjack.WordRegImm.reg 18) sourceBody654_44 sourceBody654_45

def sourceBody654_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_46 sourceBody654_11

def sourceBody654_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 42)

def sourceBody654_49 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 117) ([0, 28, 42, 18, 30, 24, 38, 20, 34]) (none)

def sourceBody654_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_49 sourceBody654_0

def sourceBody654_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_29 sourceBody654_50

def sourceBody654_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_28 sourceBody654_51

def sourceBody654_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_27 sourceBody654_52

def sourceBody654_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_26 sourceBody654_53

def sourceBody654_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_25 sourceBody654_54

def sourceBody654_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_24 sourceBody654_55

def sourceBody654_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_23 sourceBody654_56

def sourceBody654_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_22 sourceBody654_57

def sourceBody654_59 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody654_58 sourceBody654_0

def sourceBody654_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_59 sourceBody654_11

def sourceBody654_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_60 sourceBody654_0

def sourceBody654_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_48 sourceBody654_61

def sourceBody654_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_47 sourceBody654_62

def sourceBody654_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_43 sourceBody654_63

def sourceBody654_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_42 sourceBody654_64

def sourceBody654_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [28, 42, 18, 30]

def sourceBody654_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_66 sourceBody654_0

def sourceBody654_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_25 sourceBody654_67

def sourceBody654_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_24 sourceBody654_68

def sourceBody654_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_23 sourceBody654_69

def sourceBody654_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_22 sourceBody654_70

def sourceBody654_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_65 sourceBody654_71

def sourceBody654_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_41 sourceBody654_72

def sourceBody654_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_0 sourceBody654_73

def sourceBody654_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_0 sourceBody654_74

def sourceBody654_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_21 sourceBody654_75

def sourceBody654_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_0 sourceBody654_76

def sourceBody654_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_0 sourceBody654_77

def sourceBody654_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_0 sourceBody654_78

def sourceBody654_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_0 sourceBody654_79

def sourceBody654_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_0 sourceBody654_80

def sourceBody654_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_0 sourceBody654_81

def sourceBody654_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_0 sourceBody654_82

def sourceBody654_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody654_0 sourceBody654_83

def source654 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (654, 9, sourceBody654_84)
end InitECandidate.Proofs.WordStages
