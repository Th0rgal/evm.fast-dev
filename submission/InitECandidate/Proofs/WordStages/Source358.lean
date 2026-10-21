import InitECandidate.Proofs.WordStages.Source342
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody358_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody358_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody358_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 33#64)

def sourceBody358_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 20 20 18 14))

def sourceBody358_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody358_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody358_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody358_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody358_0, 358, 2)) (some 178) ([8, 16]) (some (18, sourceBody358_6, 358, 3))

def sourceBody358_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody358_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_7 sourceBody358_8

def sourceBody358_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_9 sourceBody358_0

def sourceBody358_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_5 sourceBody358_10

def sourceBody358_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_4 sourceBody358_11

def sourceBody358_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_3 sourceBody358_12

def sourceBody358_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_2 sourceBody358_13

def sourceBody358_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_1 sourceBody358_14

def sourceBody358_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 10])

def sourceBody358_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody358_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody358_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody358_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody358_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody358_22 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 8 (Flapjack.WordRegImm.reg 16) sourceBody358_20 sourceBody358_21

def sourceBody358_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_22 sourceBody358_8

def sourceBody358_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody358_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 18)

def sourceBody358_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 4,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody358_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody358_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody358_29 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody358_0, 358, 4)) (some 176) ([20, 8, 16]) (some (20, sourceBody358_28, 358, 5))

def sourceBody358_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_29 sourceBody358_8

def sourceBody358_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_30 sourceBody358_0

def sourceBody358_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_27 sourceBody358_31

def sourceBody358_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_26 sourceBody358_32

def sourceBody358_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_25 sourceBody358_33

def sourceBody358_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 10])

def sourceBody358_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody358_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_36 sourceBody358_0

def sourceBody358_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_37 sourceBody358_0

def sourceBody358_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_35 sourceBody358_38

def sourceBody358_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_0 sourceBody358_39

def sourceBody358_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_34 sourceBody358_40

def sourceBody358_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody358_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody358_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_43 sourceBody358_0

def sourceBody358_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_44 sourceBody358_0

def sourceBody358_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_42 sourceBody358_45

def sourceBody358_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_0 sourceBody358_46

def sourceBody358_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_41 sourceBody358_47

def sourceBody358_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody358_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_48 sourceBody358_49

def sourceBody358_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody358_52 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody358_50 sourceBody358_51

def sourceBody358_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_52 sourceBody358_8

def sourceBody358_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_53 sourceBody358_0

def sourceBody358_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_24 sourceBody358_54

def sourceBody358_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_23 sourceBody358_55

def sourceBody358_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_19 sourceBody358_56

def sourceBody358_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_18 sourceBody358_57

def sourceBody358_59 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit Flapjack.Spt.ln) sourceBody358_58 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln)
  PUnit.unit Flapjack.Spt.ln)

def sourceBody358_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_59 sourceBody358_8

def sourceBody358_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_8 sourceBody358_60

def sourceBody358_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 2])

def sourceBody358_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody358_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_63 sourceBody358_0

def sourceBody358_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_62 sourceBody358_64

def sourceBody358_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_61 sourceBody358_65

def sourceBody358_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_17 sourceBody358_66

def sourceBody358_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_0 sourceBody358_67

def sourceBody358_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_16 sourceBody358_68

def sourceBody358_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_0 sourceBody358_69

def sourceBody358_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_15 sourceBody358_70

def sourceBody358_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_0 sourceBody358_71

def sourceBody358_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody358_0 sourceBody358_72

def source358 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (358, 4, sourceBody358_73)
end InitECandidate.Proofs.WordStages
