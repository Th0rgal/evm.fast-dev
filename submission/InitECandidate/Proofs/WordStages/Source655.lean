import InitECandidate.Proofs.WordStages.Source639
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody655_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody655_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 2)

def sourceBody655_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 4)

def sourceBody655_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 6)

def sourceBody655_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 8)

def sourceBody655_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 10)

def sourceBody655_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 12)

def sourceBody655_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody655_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 16)

def sourceBody655_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody655_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody655_0, 655, 2)) (some 106) ([26, 40, 22, 36, 28, 42, 18, 30]) (some (26, sourceBody655_9, 655, 3))

def sourceBody655_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody655_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_10 sourceBody655_11

def sourceBody655_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_12 sourceBody655_0

def sourceBody655_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_8 sourceBody655_13

def sourceBody655_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_7 sourceBody655_14

def sourceBody655_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_6 sourceBody655_15

def sourceBody655_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_5 sourceBody655_16

def sourceBody655_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_4 sourceBody655_17

def sourceBody655_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_3 sourceBody655_18

def sourceBody655_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_2 sourceBody655_19

def sourceBody655_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_1 sourceBody655_20

def sourceBody655_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 2)

def sourceBody655_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 4)

def sourceBody655_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody655_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 8)

def sourceBody655_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody655_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 12)

def sourceBody655_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody655_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody655_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody655_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([26, 40, 22, 36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody655_0, 655, 4)) (some 117) ([28, 42, 18, 30, 24, 38, 20, 34]) (some (28, sourceBody655_30, 655, 5))

def sourceBody655_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_31 sourceBody655_11

def sourceBody655_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_32 sourceBody655_0

def sourceBody655_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_29 sourceBody655_33

def sourceBody655_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_28 sourceBody655_34

def sourceBody655_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_27 sourceBody655_35

def sourceBody655_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_26 sourceBody655_36

def sourceBody655_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_25 sourceBody655_37

def sourceBody655_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_24 sourceBody655_38

def sourceBody655_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_23 sourceBody655_39

def sourceBody655_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_22 sourceBody655_40

def sourceBody655_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 32)

def sourceBody655_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody655_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody655_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody655_46 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 42 (Flapjack.WordRegImm.reg 18) sourceBody655_44 sourceBody655_45

def sourceBody655_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_46 sourceBody655_11

def sourceBody655_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 42)

def sourceBody655_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 26)

def sourceBody655_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 40)

def sourceBody655_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 22)

def sourceBody655_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 36)

def sourceBody655_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 4332616871279656263#64)

def sourceBody655_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 10917124144477883021#64)

def sourceBody655_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 13281191951274694749#64)

def sourceBody655_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 3486998266802970665#64)

def sourceBody655_57 : WordLangProgHOL (BitVec 64) :=
.call (some (([26, 40, 22, 36]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody655_0, 655, 6)) (some 116) ([28, 42, 18, 30, 24, 38, 20, 34]) (some (28, sourceBody655_30, 655, 7))

def sourceBody655_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_57 sourceBody655_11

def sourceBody655_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_58 sourceBody655_0

def sourceBody655_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_56 sourceBody655_59

def sourceBody655_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_55 sourceBody655_60

def sourceBody655_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_54 sourceBody655_61

def sourceBody655_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_53 sourceBody655_62

def sourceBody655_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_52 sourceBody655_63

def sourceBody655_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_51 sourceBody655_64

def sourceBody655_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_50 sourceBody655_65

def sourceBody655_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_49 sourceBody655_66

def sourceBody655_68 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody655_67 sourceBody655_0

def sourceBody655_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_68 sourceBody655_11

def sourceBody655_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_69 sourceBody655_0

def sourceBody655_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_48 sourceBody655_70

def sourceBody655_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_47 sourceBody655_71

def sourceBody655_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_43 sourceBody655_72

def sourceBody655_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_42 sourceBody655_73

def sourceBody655_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [28, 42, 18, 30]

def sourceBody655_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_75 sourceBody655_0

def sourceBody655_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_52 sourceBody655_76

def sourceBody655_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_51 sourceBody655_77

def sourceBody655_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_50 sourceBody655_78

def sourceBody655_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_49 sourceBody655_79

def sourceBody655_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_74 sourceBody655_80

def sourceBody655_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_41 sourceBody655_81

def sourceBody655_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_0 sourceBody655_82

def sourceBody655_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_0 sourceBody655_83

def sourceBody655_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_0 sourceBody655_84

def sourceBody655_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_0 sourceBody655_85

def sourceBody655_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_0 sourceBody655_86

def sourceBody655_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_0 sourceBody655_87

def sourceBody655_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_0 sourceBody655_88

def sourceBody655_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_0 sourceBody655_89

def sourceBody655_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_21 sourceBody655_90

def sourceBody655_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_0 sourceBody655_91

def sourceBody655_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody655_0 sourceBody655_92

def source655 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (655, 9, sourceBody655_93)
end InitECandidate.Proofs.WordStages
