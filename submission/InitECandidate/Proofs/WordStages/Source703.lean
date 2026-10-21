import InitECandidate.Proofs.WordStages.Source687
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody703_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 12)

def sourceBody703_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 24)

def sourceBody703_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody703_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody703_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.reg 32) sourceBody703_2 sourceBody703_3

def sourceBody703_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody703_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_4 sourceBody703_5

def sourceBody703_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody703_8 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 28 (Flapjack.WordRegImm.reg 32) sourceBody703_2 sourceBody703_3

def sourceBody703_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_8 sourceBody703_5

def sourceBody703_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody703_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30]

def sourceBody703_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody703_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_11 sourceBody703_12

def sourceBody703_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_10 sourceBody703_13

def sourceBody703_15 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody703_14 sourceBody703_12

def sourceBody703_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_15 sourceBody703_5

def sourceBody703_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_16 sourceBody703_12

def sourceBody703_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_7 sourceBody703_17

def sourceBody703_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_9 sourceBody703_18

def sourceBody703_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_1 sourceBody703_19

def sourceBody703_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_0 sourceBody703_20

def sourceBody703_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody703_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_22 sourceBody703_13

def sourceBody703_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_21 sourceBody703_23

def sourceBody703_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody703_24 sourceBody703_12

def sourceBody703_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_25 sourceBody703_5

def sourceBody703_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_26 sourceBody703_12

def sourceBody703_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_7 sourceBody703_27

def sourceBody703_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_6 sourceBody703_28

def sourceBody703_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_1 sourceBody703_29

def sourceBody703_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_0 sourceBody703_30

def sourceBody703_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 10)

def sourceBody703_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 22)

def sourceBody703_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_33 sourceBody703_19

def sourceBody703_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_32 sourceBody703_34

def sourceBody703_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_35 sourceBody703_23

def sourceBody703_37 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody703_36 sourceBody703_12

def sourceBody703_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_37 sourceBody703_5

def sourceBody703_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_38 sourceBody703_12

def sourceBody703_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_7 sourceBody703_39

def sourceBody703_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_6 sourceBody703_40

def sourceBody703_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_33 sourceBody703_41

def sourceBody703_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_32 sourceBody703_42

def sourceBody703_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_31 sourceBody703_43

def sourceBody703_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 8)

def sourceBody703_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 20)

def sourceBody703_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_46 sourceBody703_19

def sourceBody703_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_45 sourceBody703_47

def sourceBody703_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_48 sourceBody703_23

def sourceBody703_50 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody703_49 sourceBody703_12

def sourceBody703_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_50 sourceBody703_5

def sourceBody703_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_51 sourceBody703_12

def sourceBody703_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_7 sourceBody703_52

def sourceBody703_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_6 sourceBody703_53

def sourceBody703_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_46 sourceBody703_54

def sourceBody703_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_45 sourceBody703_55

def sourceBody703_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_44 sourceBody703_56

def sourceBody703_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 6)

def sourceBody703_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 18)

def sourceBody703_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_59 sourceBody703_19

def sourceBody703_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_58 sourceBody703_60

def sourceBody703_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_61 sourceBody703_23

def sourceBody703_63 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody703_62 sourceBody703_12

def sourceBody703_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_63 sourceBody703_5

def sourceBody703_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_64 sourceBody703_12

def sourceBody703_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_7 sourceBody703_65

def sourceBody703_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_6 sourceBody703_66

def sourceBody703_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_59 sourceBody703_67

def sourceBody703_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_58 sourceBody703_68

def sourceBody703_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_57 sourceBody703_69

def sourceBody703_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody703_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 16)

def sourceBody703_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_72 sourceBody703_19

def sourceBody703_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_71 sourceBody703_73

def sourceBody703_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_74 sourceBody703_23

def sourceBody703_76 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody703_75 sourceBody703_12

def sourceBody703_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_76 sourceBody703_5

def sourceBody703_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_77 sourceBody703_12

def sourceBody703_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_7 sourceBody703_78

def sourceBody703_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_6 sourceBody703_79

def sourceBody703_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_72 sourceBody703_80

def sourceBody703_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_71 sourceBody703_81

def sourceBody703_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_70 sourceBody703_82

def sourceBody703_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 2)

def sourceBody703_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 14)

def sourceBody703_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_85 sourceBody703_19

def sourceBody703_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_84 sourceBody703_86

def sourceBody703_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_83 sourceBody703_87

def sourceBody703_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody703_88 sourceBody703_23

def source703 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (703, 13, sourceBody703_89)
end InitECandidate.Proofs.WordStages
