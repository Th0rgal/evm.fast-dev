import InitECandidate.Proofs.WordStages.Source623
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody639_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody639_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 2)

def sourceBody639_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 4)

def sourceBody639_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 6)

def sourceBody639_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 8)

def sourceBody639_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 10)

def sourceBody639_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 12)

def sourceBody639_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody639_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 16)

def sourceBody639_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody639_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody639_0, 639, 2)) (some 106) ([26, 40, 22, 36, 28, 42, 18, 30]) (some (26, sourceBody639_9, 639, 3))

def sourceBody639_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody639_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_10 sourceBody639_11

def sourceBody639_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_12 sourceBody639_0

def sourceBody639_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_8 sourceBody639_13

def sourceBody639_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_7 sourceBody639_14

def sourceBody639_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_6 sourceBody639_15

def sourceBody639_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_5 sourceBody639_16

def sourceBody639_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_4 sourceBody639_17

def sourceBody639_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_3 sourceBody639_18

def sourceBody639_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_2 sourceBody639_19

def sourceBody639_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_1 sourceBody639_20

def sourceBody639_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 2)

def sourceBody639_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 4)

def sourceBody639_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody639_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 8)

def sourceBody639_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody639_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 12)

def sourceBody639_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody639_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody639_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody639_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([26, 40, 22, 36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody639_0, 639, 4)) (some 117) ([28, 42, 18, 30, 24, 38, 20, 34]) (some (28, sourceBody639_30, 639, 5))

def sourceBody639_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_31 sourceBody639_11

def sourceBody639_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_32 sourceBody639_0

def sourceBody639_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_29 sourceBody639_33

def sourceBody639_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_28 sourceBody639_34

def sourceBody639_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_27 sourceBody639_35

def sourceBody639_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_26 sourceBody639_36

def sourceBody639_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_25 sourceBody639_37

def sourceBody639_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_24 sourceBody639_38

def sourceBody639_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_23 sourceBody639_39

def sourceBody639_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_22 sourceBody639_40

def sourceBody639_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 32)

def sourceBody639_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody639_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody639_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody639_46 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 42 (Flapjack.WordRegImm.reg 18) sourceBody639_44 sourceBody639_45

def sourceBody639_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_46 sourceBody639_11

def sourceBody639_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 42)

def sourceBody639_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 26)

def sourceBody639_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 40)

def sourceBody639_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 22)

def sourceBody639_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 36)

def sourceBody639_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 18446744073709551615#64)

def sourceBody639_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 4294967295#64)

def sourceBody639_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody639_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 18446744069414584321#64)

def sourceBody639_57 : WordLangProgHOL (BitVec 64) :=
.call (some (([26, 40, 22, 36]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody639_0, 639, 6)) (some 116) ([28, 42, 18, 30, 24, 38, 20, 34]) (some (28, sourceBody639_30, 639, 7))

def sourceBody639_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_57 sourceBody639_11

def sourceBody639_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_58 sourceBody639_0

def sourceBody639_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_56 sourceBody639_59

def sourceBody639_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_55 sourceBody639_60

def sourceBody639_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_54 sourceBody639_61

def sourceBody639_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_53 sourceBody639_62

def sourceBody639_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_52 sourceBody639_63

def sourceBody639_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_51 sourceBody639_64

def sourceBody639_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_50 sourceBody639_65

def sourceBody639_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_49 sourceBody639_66

def sourceBody639_68 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody639_67 sourceBody639_0

def sourceBody639_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_68 sourceBody639_11

def sourceBody639_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_69 sourceBody639_0

def sourceBody639_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_48 sourceBody639_70

def sourceBody639_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_47 sourceBody639_71

def sourceBody639_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_43 sourceBody639_72

def sourceBody639_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_42 sourceBody639_73

def sourceBody639_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [28, 42, 18, 30]

def sourceBody639_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_75 sourceBody639_0

def sourceBody639_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_52 sourceBody639_76

def sourceBody639_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_51 sourceBody639_77

def sourceBody639_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_50 sourceBody639_78

def sourceBody639_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_49 sourceBody639_79

def sourceBody639_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_74 sourceBody639_80

def sourceBody639_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_41 sourceBody639_81

def sourceBody639_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_0 sourceBody639_82

def sourceBody639_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_0 sourceBody639_83

def sourceBody639_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_0 sourceBody639_84

def sourceBody639_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_0 sourceBody639_85

def sourceBody639_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_0 sourceBody639_86

def sourceBody639_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_0 sourceBody639_87

def sourceBody639_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_0 sourceBody639_88

def sourceBody639_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_0 sourceBody639_89

def sourceBody639_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_21 sourceBody639_90

def sourceBody639_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_0 sourceBody639_91

def sourceBody639_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody639_0 sourceBody639_92

def source639 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (639, 9, sourceBody639_93)
end InitECandidate.Proofs.WordStages
