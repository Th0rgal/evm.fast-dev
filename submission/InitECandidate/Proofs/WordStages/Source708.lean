import InitECandidate.Proofs.WordStages.Source692
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody708_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody708_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody708_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 4)

def sourceBody708_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody708_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 8)

def sourceBody708_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody708_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 12)

def sourceBody708_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody708_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody708_0, 708, 2)) (some 701) ([16, 36, 26, 46, 22, 42]) (some (16, sourceBody708_7, 708, 3))

def sourceBody708_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody708_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_8 sourceBody708_9

def sourceBody708_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_10 sourceBody708_0

def sourceBody708_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_6 sourceBody708_11

def sourceBody708_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_5 sourceBody708_12

def sourceBody708_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_4 sourceBody708_13

def sourceBody708_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_3 sourceBody708_14

def sourceBody708_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_2 sourceBody708_15

def sourceBody708_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_1 sourceBody708_16

def sourceBody708_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 48)

def sourceBody708_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody708_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody708_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody708_22 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 36 (Flapjack.WordRegImm.reg 26) sourceBody708_20 sourceBody708_21

def sourceBody708_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_22 sourceBody708_9

def sourceBody708_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 36)

def sourceBody708_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody708_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody708_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody708_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody708_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody708_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16, 36, 26, 46, 22, 42]

def sourceBody708_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_30 sourceBody708_0

def sourceBody708_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_29 sourceBody708_31

def sourceBody708_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_28 sourceBody708_32

def sourceBody708_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_27 sourceBody708_33

def sourceBody708_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_26 sourceBody708_34

def sourceBody708_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_21 sourceBody708_35

def sourceBody708_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_25 sourceBody708_36

def sourceBody708_38 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 46 (Flapjack.WordRegImm.imm 0#64) sourceBody708_37 sourceBody708_0

def sourceBody708_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_38 sourceBody708_9

def sourceBody708_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_39 sourceBody708_0

def sourceBody708_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_24 sourceBody708_40

def sourceBody708_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_23 sourceBody708_41

def sourceBody708_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_19 sourceBody708_42

def sourceBody708_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_18 sourceBody708_43

def sourceBody708_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 13402431016077863595#64)

def sourceBody708_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 2210141511517208575#64)

def sourceBody708_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 7435674573564081700#64)

def sourceBody708_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 7239337960414712511#64)

def sourceBody708_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 5412103778470702295#64)

def sourceBody708_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1873798617647539866#64)

def sourceBody708_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 2)

def sourceBody708_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 4)

def sourceBody708_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 6)

def sourceBody708_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody708_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 10)

def sourceBody708_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 12)

def sourceBody708_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 52

def sourceBody708_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 36, 26, 46, 22, 42, 32]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody708_0, 708, 4)) (some 705) ([52, 14, 34, 24, 44, 20, 40, 30, 50, 18, 38, 28]) (some (52, sourceBody708_57, 708, 5))

def sourceBody708_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_58 sourceBody708_9

def sourceBody708_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_59 sourceBody708_0

def sourceBody708_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_56 sourceBody708_60

def sourceBody708_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_55 sourceBody708_61

def sourceBody708_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_54 sourceBody708_62

def sourceBody708_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_53 sourceBody708_63

def sourceBody708_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_52 sourceBody708_64

def sourceBody708_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_51 sourceBody708_65

def sourceBody708_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_50 sourceBody708_66

def sourceBody708_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_49 sourceBody708_67

def sourceBody708_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_48 sourceBody708_68

def sourceBody708_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_47 sourceBody708_69

def sourceBody708_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_46 sourceBody708_70

def sourceBody708_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_45 sourceBody708_71

def sourceBody708_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 16)

def sourceBody708_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 36)

def sourceBody708_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 26)

def sourceBody708_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 46)

def sourceBody708_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 22)

def sourceBody708_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 42)

def sourceBody708_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [52, 14, 34, 24, 44, 20]

def sourceBody708_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_79 sourceBody708_0

def sourceBody708_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_78 sourceBody708_80

def sourceBody708_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_77 sourceBody708_81

def sourceBody708_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_76 sourceBody708_82

def sourceBody708_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_75 sourceBody708_83

def sourceBody708_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_74 sourceBody708_84

def sourceBody708_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_73 sourceBody708_85

def sourceBody708_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_72 sourceBody708_86

def sourceBody708_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_0 sourceBody708_87

def sourceBody708_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_0 sourceBody708_88

def sourceBody708_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_0 sourceBody708_89

def sourceBody708_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_0 sourceBody708_90

def sourceBody708_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_0 sourceBody708_91

def sourceBody708_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_0 sourceBody708_92

def sourceBody708_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_0 sourceBody708_93

def sourceBody708_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_0 sourceBody708_94

def sourceBody708_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_0 sourceBody708_95

def sourceBody708_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_0 sourceBody708_96

def sourceBody708_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_0 sourceBody708_97

def sourceBody708_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_0 sourceBody708_98

def sourceBody708_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_0 sourceBody708_99

def sourceBody708_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_0 sourceBody708_100

def sourceBody708_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_44 sourceBody708_101

def sourceBody708_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_17 sourceBody708_102

def sourceBody708_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_0 sourceBody708_103

def sourceBody708_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody708_0 sourceBody708_104

def source708 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (708, 7, sourceBody708_105)
end InitECandidate.Proofs.WordStages
