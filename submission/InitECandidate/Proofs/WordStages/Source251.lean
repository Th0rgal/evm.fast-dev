import InitECandidate.Proofs.WordStages.Source235
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody251_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody251_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 2)

def sourceBody251_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody251_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody251_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody251_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody251_0, 251, 2)) (some 247) ([22, 10, 16]) (some (22, sourceBody251_4, 251, 3))

def sourceBody251_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody251_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_5 sourceBody251_6

def sourceBody251_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_7 sourceBody251_0

def sourceBody251_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_3 sourceBody251_8

def sourceBody251_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_2 sourceBody251_9

def sourceBody251_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_1 sourceBody251_10

def sourceBody251_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody251_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody251_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody251_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody251_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody251_17 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 16 (Flapjack.WordRegImm.reg 12) sourceBody251_15 sourceBody251_16

def sourceBody251_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_17 sourceBody251_6

def sourceBody251_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody251_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody251_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 22)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody251_22 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 16 (Flapjack.WordRegImm.reg 12) sourceBody251_15 sourceBody251_16

def sourceBody251_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_22 sourceBody251_6

def sourceBody251_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 70#64)

def sourceBody251_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody251_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody251_0, 251, 4)) (some 245) ([16]) (some (16, sourceBody251_25, 251, 5))

def sourceBody251_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_26 sourceBody251_6

def sourceBody251_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_27 sourceBody251_0

def sourceBody251_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_24 sourceBody251_28

def sourceBody251_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_0 sourceBody251_29

def sourceBody251_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_0 sourceBody251_30

def sourceBody251_32 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody251_31 sourceBody251_0

def sourceBody251_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_32 sourceBody251_6

def sourceBody251_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_33 sourceBody251_0

def sourceBody251_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_19 sourceBody251_34

def sourceBody251_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_23 sourceBody251_35

def sourceBody251_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_21 sourceBody251_36

def sourceBody251_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_20 sourceBody251_37

def sourceBody251_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody251_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody251_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_40 sourceBody251_0

def sourceBody251_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_41 sourceBody251_0

def sourceBody251_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_39 sourceBody251_42

def sourceBody251_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_0 sourceBody251_43

def sourceBody251_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_38 sourceBody251_44

def sourceBody251_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody251_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_45 sourceBody251_46

def sourceBody251_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody251_49 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody251_47 sourceBody251_48

def sourceBody251_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_49 sourceBody251_6

def sourceBody251_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_50 sourceBody251_0

def sourceBody251_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_19 sourceBody251_51

def sourceBody251_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_18 sourceBody251_52

def sourceBody251_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_14 sourceBody251_53

def sourceBody251_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_13 sourceBody251_54

def sourceBody251_56 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln) sourceBody251_55 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    Flapjack.Spt.ln)
  PUnit.unit Flapjack.Spt.ln)

def sourceBody251_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_56 sourceBody251_6

def sourceBody251_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_6 sourceBody251_57

def sourceBody251_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody251_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody251_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10, 16]

def sourceBody251_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_61 sourceBody251_0

def sourceBody251_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_60 sourceBody251_62

def sourceBody251_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_59 sourceBody251_63

def sourceBody251_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_58 sourceBody251_64

def sourceBody251_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_12 sourceBody251_65

def sourceBody251_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_0 sourceBody251_66

def sourceBody251_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_11 sourceBody251_67

def sourceBody251_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_0 sourceBody251_68

def sourceBody251_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_0 sourceBody251_69

def sourceBody251_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_0 sourceBody251_70

def sourceBody251_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody251_0 sourceBody251_71

def source251 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (251, 5, sourceBody251_72)
end InitECandidate.Proofs.WordStages
