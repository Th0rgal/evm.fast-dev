import InitECandidate.Proofs.WordStages.Source344
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody360_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody360_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody360_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody360_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody360_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody360_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody360_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody360_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody360_8 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 18) sourceBody360_6 sourceBody360_7

def sourceBody360_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_8 sourceBody360_3

def sourceBody360_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody360_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 120#64)

def sourceBody360_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 6 6 10 18))

def sourceBody360_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 6])

def sourceBody360_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody360_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody360_0, 360, 2)) (some 359) ([12]) (some (10, sourceBody360_14, 360, 3))

def sourceBody360_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_15 sourceBody360_3

def sourceBody360_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_16 sourceBody360_0

def sourceBody360_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_13 sourceBody360_17

def sourceBody360_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_12 sourceBody360_18

def sourceBody360_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_11 sourceBody360_19

def sourceBody360_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_4 sourceBody360_20

def sourceBody360_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody360_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody360_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody360_0, 360, 4)) (some 180) ([18]) (some (18, sourceBody360_23, 360, 5))

def sourceBody360_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_24 sourceBody360_3

def sourceBody360_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_25 sourceBody360_0

def sourceBody360_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_22 sourceBody360_26

def sourceBody360_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 14])

def sourceBody360_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody360_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_29 sourceBody360_0

def sourceBody360_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_30 sourceBody360_0

def sourceBody360_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_28 sourceBody360_31

def sourceBody360_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_0 sourceBody360_32

def sourceBody360_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody360_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 18)

def sourceBody360_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_35 sourceBody360_0

def sourceBody360_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_36 sourceBody360_0

def sourceBody360_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_34 sourceBody360_37

def sourceBody360_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_0 sourceBody360_38

def sourceBody360_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_33 sourceBody360_39

def sourceBody360_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_27 sourceBody360_40

def sourceBody360_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_0 sourceBody360_41

def sourceBody360_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_0 sourceBody360_42

def sourceBody360_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_21 sourceBody360_43

def sourceBody360_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_0 sourceBody360_44

def sourceBody360_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_0 sourceBody360_45

def sourceBody360_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody360_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_46 sourceBody360_47

def sourceBody360_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody360_50 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody360_48 sourceBody360_49

def sourceBody360_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_50 sourceBody360_3

def sourceBody360_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_51 sourceBody360_0

def sourceBody360_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_10 sourceBody360_52

def sourceBody360_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_9 sourceBody360_53

def sourceBody360_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_5 sourceBody360_54

def sourceBody360_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_4 sourceBody360_55

def sourceBody360_57 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody360_56 (Flapjack.Spt.bs
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody360_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_57 sourceBody360_3

def sourceBody360_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_3 sourceBody360_58

def sourceBody360_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody360_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody360_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_61 sourceBody360_0

def sourceBody360_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_60 sourceBody360_62

def sourceBody360_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_59 sourceBody360_63

def sourceBody360_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_2 sourceBody360_64

def sourceBody360_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_0 sourceBody360_65

def sourceBody360_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_1 sourceBody360_66

def sourceBody360_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody360_0 sourceBody360_67

def source360 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (360, 3, sourceBody360_68)
end InitECandidate.Proofs.WordStages
