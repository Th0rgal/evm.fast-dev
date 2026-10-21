import InitECandidate.Proofs.WordStages.Source340
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody356_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody356_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody356_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody356_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody356_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody356_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody356_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody356_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody356_8 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 14 (Flapjack.WordRegImm.reg 28) sourceBody356_6 sourceBody356_7

def sourceBody356_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_8 sourceBody356_3

def sourceBody356_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 14)

def sourceBody356_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody356_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody356_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 28 28 20 14))

def sourceBody356_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody356_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 33#64)

def sourceBody356_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 12 12 6 18))

def sourceBody356_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_16 sourceBody356_0

def sourceBody356_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_15 sourceBody356_17

def sourceBody356_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_14 sourceBody356_18

def sourceBody356_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_13 sourceBody356_19

def sourceBody356_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_12 sourceBody356_20

def sourceBody356_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_11 sourceBody356_21

def sourceBody356_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 12)

def sourceBody356_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody356_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody356_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody356_0, 356, 2)) (some 180) ([22]) (some (22, sourceBody356_25, 356, 3))

def sourceBody356_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_26 sourceBody356_3

def sourceBody356_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_27 sourceBody356_0

def sourceBody356_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_24 sourceBody356_28

def sourceBody356_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.const 21#64, Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 26])

def sourceBody356_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 22)

def sourceBody356_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody356_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody356_0, 356, 4)) (some 180) ([30]) (some (30, sourceBody356_32, 356, 5))

def sourceBody356_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_33 sourceBody356_3

def sourceBody356_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_34 sourceBody356_0

def sourceBody356_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_31 sourceBody356_35

def sourceBody356_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.var 22])

def sourceBody356_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 30)

def sourceBody356_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_38 sourceBody356_0

def sourceBody356_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_39 sourceBody356_0

def sourceBody356_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_37 sourceBody356_40

def sourceBody356_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_0 sourceBody356_41

def sourceBody356_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody356_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 30)

def sourceBody356_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_44 sourceBody356_0

def sourceBody356_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_45 sourceBody356_0

def sourceBody356_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_43 sourceBody356_46

def sourceBody356_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_0 sourceBody356_47

def sourceBody356_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_42 sourceBody356_48

def sourceBody356_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_36 sourceBody356_49

def sourceBody356_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_0 sourceBody356_50

def sourceBody356_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_0 sourceBody356_51

def sourceBody356_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_30 sourceBody356_52

def sourceBody356_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_0 sourceBody356_53

def sourceBody356_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_29 sourceBody356_54

def sourceBody356_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_0 sourceBody356_55

def sourceBody356_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_0 sourceBody356_56

def sourceBody356_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_23 sourceBody356_57

def sourceBody356_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_22 sourceBody356_58

def sourceBody356_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody356_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_59 sourceBody356_60

def sourceBody356_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody356_63 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody356_61 sourceBody356_62

def sourceBody356_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_63 sourceBody356_3

def sourceBody356_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_64 sourceBody356_0

def sourceBody356_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_10 sourceBody356_65

def sourceBody356_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_9 sourceBody356_66

def sourceBody356_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_5 sourceBody356_67

def sourceBody356_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_4 sourceBody356_68

def sourceBody356_70 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody356_69 (Flapjack.Spt.bs
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody356_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_70 sourceBody356_3

def sourceBody356_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_3 sourceBody356_71

def sourceBody356_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody356_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody356_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_74 sourceBody356_0

def sourceBody356_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_73 sourceBody356_75

def sourceBody356_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_72 sourceBody356_76

def sourceBody356_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_2 sourceBody356_77

def sourceBody356_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_0 sourceBody356_78

def sourceBody356_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_1 sourceBody356_79

def sourceBody356_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody356_0 sourceBody356_80

def source356 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (356, 3, sourceBody356_81)
end InitECandidate.Proofs.WordStages
