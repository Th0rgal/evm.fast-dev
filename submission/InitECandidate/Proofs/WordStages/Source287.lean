import InitECandidate.Proofs.WordStages.Source271
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody287_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody287_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody287_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody287_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody287_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody287_0, 287, 2)) (some 92) ([16, 24]) (some (16, sourceBody287_3, 287, 3))

def sourceBody287_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody287_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_4 sourceBody287_5

def sourceBody287_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_6 sourceBody287_0

def sourceBody287_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_2 sourceBody287_7

def sourceBody287_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_1 sourceBody287_8

def sourceBody287_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody287_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody287_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody287_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody287_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody287_15 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 18) sourceBody287_13 sourceBody287_14

def sourceBody287_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_15 sourceBody287_5

def sourceBody287_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody287_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 16])

def sourceBody287_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 24 (Flapjack.WordLangAddr.addr 24 0#64))

def sourceBody287_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 16])

def sourceBody287_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 10 (Flapjack.WordLangAddr.addr 10 0#64))

def sourceBody287_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 24)

def sourceBody287_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody287_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody287_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody287_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.reg 22) sourceBody287_24 sourceBody287_25

def sourceBody287_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_26 sourceBody287_5

def sourceBody287_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody287_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody287_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody287_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_30 sourceBody287_0

def sourceBody287_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_29 sourceBody287_31

def sourceBody287_33 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody287_32 sourceBody287_0

def sourceBody287_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_33 sourceBody287_5

def sourceBody287_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_34 sourceBody287_0

def sourceBody287_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_28 sourceBody287_35

def sourceBody287_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_27 sourceBody287_36

def sourceBody287_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_23 sourceBody287_37

def sourceBody287_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_22 sourceBody287_38

def sourceBody287_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_21 sourceBody287_39

def sourceBody287_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_20 sourceBody287_40

def sourceBody287_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_19 sourceBody287_41

def sourceBody287_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_18 sourceBody287_42

def sourceBody287_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody287_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody287_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_45 sourceBody287_0

def sourceBody287_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_46 sourceBody287_0

def sourceBody287_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_44 sourceBody287_47

def sourceBody287_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_0 sourceBody287_48

def sourceBody287_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_43 sourceBody287_49

def sourceBody287_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody287_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_50 sourceBody287_51

def sourceBody287_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody287_54 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody287_52 sourceBody287_53

def sourceBody287_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_54 sourceBody287_5

def sourceBody287_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_55 sourceBody287_0

def sourceBody287_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_17 sourceBody287_56

def sourceBody287_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_16 sourceBody287_57

def sourceBody287_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_12 sourceBody287_58

def sourceBody287_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_11 sourceBody287_59

def sourceBody287_61 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody287_60 (Flapjack.Spt.bs
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody287_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_61 sourceBody287_5

def sourceBody287_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_5 sourceBody287_62

def sourceBody287_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 20)

def sourceBody287_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_64 sourceBody287_31

def sourceBody287_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_63 sourceBody287_65

def sourceBody287_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_10 sourceBody287_66

def sourceBody287_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_0 sourceBody287_67

def sourceBody287_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_9 sourceBody287_68

def sourceBody287_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_0 sourceBody287_69

def sourceBody287_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody287_0 sourceBody287_70

def source287 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (287, 5, sourceBody287_71)
end InitECandidate.Proofs.WordStages
