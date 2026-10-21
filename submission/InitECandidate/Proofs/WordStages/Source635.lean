import InitECandidate.Proofs.WordStages.Source619
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody635_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody635_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody635_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 4)

def sourceBody635_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody635_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody635_0, 635, 2)) (some 126) ([24, 34]) (some (24, sourceBody635_3, 635, 3))

def sourceBody635_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody635_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_4 sourceBody635_5

def sourceBody635_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_6 sourceBody635_0

def sourceBody635_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_2 sourceBody635_7

def sourceBody635_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_1 sourceBody635_8

def sourceBody635_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 30)

def sourceBody635_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody635_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody635_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody635_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 34 (Flapjack.WordRegImm.reg 20) sourceBody635_12 sourceBody635_13

def sourceBody635_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_14 sourceBody635_5

def sourceBody635_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 34)

def sourceBody635_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 10)

def sourceBody635_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody635_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 30)
    (Flapjack.WordLangExpHOL.const 3#64))

def sourceBody635_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody635_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody635_0, 635, 4)) (some 77) ([34, 20, 32]) (some (34, sourceBody635_20, 635, 5))

def sourceBody635_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_21 sourceBody635_5

def sourceBody635_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_22 sourceBody635_0

def sourceBody635_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_19 sourceBody635_23

def sourceBody635_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_18 sourceBody635_24

def sourceBody635_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_17 sourceBody635_25

def sourceBody635_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_0 sourceBody635_26

def sourceBody635_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_0 sourceBody635_27

def sourceBody635_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 30)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody635_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 30])
    (Flapjack.WordLangExpHOL.const 3#64))

def sourceBody635_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody635_0, 635, 6)) (some 78) ([34, 20]) (some (34, sourceBody635_20, 635, 7))

def sourceBody635_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_31 sourceBody635_5

def sourceBody635_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_32 sourceBody635_0

def sourceBody635_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_30 sourceBody635_33

def sourceBody635_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_29 sourceBody635_34

def sourceBody635_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_0 sourceBody635_35

def sourceBody635_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_0 sourceBody635_36

def sourceBody635_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_28 sourceBody635_37

def sourceBody635_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody635_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody635_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_40 sourceBody635_0

def sourceBody635_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_39 sourceBody635_41

def sourceBody635_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_38 sourceBody635_42

def sourceBody635_44 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody635_43 sourceBody635_0

def sourceBody635_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_44 sourceBody635_5

def sourceBody635_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_45 sourceBody635_0

def sourceBody635_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_16 sourceBody635_46

def sourceBody635_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_15 sourceBody635_47

def sourceBody635_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_11 sourceBody635_48

def sourceBody635_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_10 sourceBody635_49

def sourceBody635_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 12)

def sourceBody635_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 10)

def sourceBody635_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 2)

def sourceBody635_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody635_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 6)

def sourceBody635_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody635_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 14)

def sourceBody635_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 16)

def sourceBody635_59 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody635_0, 635, 8)) (some 634) ([34, 20, 32, 26, 36, 18, 28, 22]) (some (34, sourceBody635_20, 635, 9))

def sourceBody635_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_59 sourceBody635_5

def sourceBody635_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_60 sourceBody635_0

def sourceBody635_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_58 sourceBody635_61

def sourceBody635_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_57 sourceBody635_62

def sourceBody635_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_56 sourceBody635_63

def sourceBody635_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_55 sourceBody635_64

def sourceBody635_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_54 sourceBody635_65

def sourceBody635_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_53 sourceBody635_66

def sourceBody635_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_52 sourceBody635_67

def sourceBody635_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_51 sourceBody635_68

def sourceBody635_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_0 sourceBody635_69

def sourceBody635_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_0 sourceBody635_70

def sourceBody635_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_50 sourceBody635_71

def sourceBody635_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_72 sourceBody635_42

def sourceBody635_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_9 sourceBody635_73

def sourceBody635_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_0 sourceBody635_74

def sourceBody635_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody635_0 sourceBody635_75

def source635 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (635, 9, sourceBody635_76)
end InitECandidate.Proofs.WordStages
