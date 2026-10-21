import InitECandidate.Proofs.WordStages.Source645
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody661_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody661_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody661_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody661_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody661_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody661_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody661_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody661_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody661_0, 661, 2)) (some 137) ([32]) (some (32, sourceBody661_6, 661, 3))

def sourceBody661_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody661_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_7 sourceBody661_8

def sourceBody661_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_9 sourceBody661_0

def sourceBody661_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_5 sourceBody661_10

def sourceBody661_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody661_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 20)

def sourceBody661_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody661_15 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 16 (Flapjack.WordRegImm.reg 30) sourceBody661_14 sourceBody661_12

def sourceBody661_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_15 sourceBody661_8

def sourceBody661_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody661_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody661_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 32)

def sourceBody661_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_19 sourceBody661_0

def sourceBody661_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_20 sourceBody661_0

def sourceBody661_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_18 sourceBody661_21

def sourceBody661_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_0 sourceBody661_22

def sourceBody661_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 22)

def sourceBody661_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 34)

def sourceBody661_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 14)

def sourceBody661_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 28)

def sourceBody661_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 22)

def sourceBody661_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 34)

def sourceBody661_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 14)

def sourceBody661_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody661_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([22, 34, 14, 28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody661_0, 661, 4)) (some 654) ([32, 16, 30, 24, 36, 12, 26, 18]) (some (32, sourceBody661_6, 661, 5))

def sourceBody661_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_32 sourceBody661_8

def sourceBody661_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_33 sourceBody661_0

def sourceBody661_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_31 sourceBody661_34

def sourceBody661_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_30 sourceBody661_35

def sourceBody661_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_29 sourceBody661_36

def sourceBody661_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_28 sourceBody661_37

def sourceBody661_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_27 sourceBody661_38

def sourceBody661_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_26 sourceBody661_39

def sourceBody661_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_25 sourceBody661_40

def sourceBody661_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_24 sourceBody661_41

def sourceBody661_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_23 sourceBody661_42

def sourceBody661_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 10) (Flapjack.WordLangExpHOL.var 20),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody661_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody661_46 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 30) sourceBody661_14 sourceBody661_12

def sourceBody661_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_46 sourceBody661_8

def sourceBody661_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 2)

def sourceBody661_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody661_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody661_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody661_52 : WordLangProgHOL (BitVec 64) :=
.call (some (([22, 34, 14, 28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody661_0, 661, 6)) (some 654) ([32, 16, 30, 24, 36, 12, 26, 18]) (some (32, sourceBody661_6, 661, 7))

def sourceBody661_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_52 sourceBody661_8

def sourceBody661_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_53 sourceBody661_0

def sourceBody661_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_51 sourceBody661_54

def sourceBody661_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_50 sourceBody661_55

def sourceBody661_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_49 sourceBody661_56

def sourceBody661_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_48 sourceBody661_57

def sourceBody661_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_27 sourceBody661_58

def sourceBody661_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_26 sourceBody661_59

def sourceBody661_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_25 sourceBody661_60

def sourceBody661_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_24 sourceBody661_61

def sourceBody661_63 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody661_62 sourceBody661_0

def sourceBody661_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_63 sourceBody661_8

def sourceBody661_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_64 sourceBody661_0

def sourceBody661_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_17 sourceBody661_65

def sourceBody661_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_47 sourceBody661_66

def sourceBody661_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_45 sourceBody661_67

def sourceBody661_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_44 sourceBody661_68

def sourceBody661_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_43 sourceBody661_69

def sourceBody661_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody661_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_70 sourceBody661_71

def sourceBody661_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody661_74 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody661_72 sourceBody661_73

def sourceBody661_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_74 sourceBody661_8

def sourceBody661_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_75 sourceBody661_0

def sourceBody661_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_17 sourceBody661_76

def sourceBody661_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_16 sourceBody661_77

def sourceBody661_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_13 sourceBody661_78

def sourceBody661_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_12 sourceBody661_79

def sourceBody661_81 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln) sourceBody661_80 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody661_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_81 sourceBody661_8

def sourceBody661_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_8 sourceBody661_82

def sourceBody661_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [32, 16, 30, 24]

def sourceBody661_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_84 sourceBody661_0

def sourceBody661_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_27 sourceBody661_85

def sourceBody661_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_26 sourceBody661_86

def sourceBody661_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_25 sourceBody661_87

def sourceBody661_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_24 sourceBody661_88

def sourceBody661_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_83 sourceBody661_89

def sourceBody661_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_11 sourceBody661_90

def sourceBody661_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_0 sourceBody661_91

def sourceBody661_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_0 sourceBody661_92

def sourceBody661_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_4 sourceBody661_93

def sourceBody661_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_0 sourceBody661_94

def sourceBody661_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_3 sourceBody661_95

def sourceBody661_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_0 sourceBody661_96

def sourceBody661_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_2 sourceBody661_97

def sourceBody661_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_0 sourceBody661_98

def sourceBody661_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_1 sourceBody661_99

def sourceBody661_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody661_0 sourceBody661_100

def source661 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (661, 6, sourceBody661_101)
end InitECandidate.Proofs.WordStages
