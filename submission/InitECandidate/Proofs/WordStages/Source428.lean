import InitECandidate.Proofs.WordStages.Source412
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody428_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody428_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody428_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody428_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody428_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody428_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody428_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody428_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody428_8 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 12 (Flapjack.WordRegImm.reg 22) sourceBody428_6 sourceBody428_7

def sourceBody428_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_8 sourceBody428_3

def sourceBody428_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody428_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody428_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody428_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody428_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 12, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody428_0, 428, 2)) (some 197) ([6, 14]) (some (6, sourceBody428_13, 428, 3))

def sourceBody428_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_14 sourceBody428_3

def sourceBody428_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_15 sourceBody428_0

def sourceBody428_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_12 sourceBody428_16

def sourceBody428_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_11 sourceBody428_17

def sourceBody428_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody428_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody428_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody428_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody428_23 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.reg 10) sourceBody428_21 sourceBody428_22

def sourceBody428_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_23 sourceBody428_3

def sourceBody428_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody428_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody428_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody428_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 22)

def sourceBody428_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody428_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody428_0, 428, 4)) (some 192) ([14, 10, 20]) (some (14, sourceBody428_29, 428, 5))

def sourceBody428_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_30 sourceBody428_3

def sourceBody428_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_31 sourceBody428_0

def sourceBody428_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_28 sourceBody428_32

def sourceBody428_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_27 sourceBody428_33

def sourceBody428_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_26 sourceBody428_34

def sourceBody428_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_0 sourceBody428_35

def sourceBody428_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_0 sourceBody428_36

def sourceBody428_38 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody428_37 sourceBody428_0

def sourceBody428_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_38 sourceBody428_3

def sourceBody428_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_39 sourceBody428_0

def sourceBody428_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_25 sourceBody428_40

def sourceBody428_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_24 sourceBody428_41

def sourceBody428_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_20 sourceBody428_42

def sourceBody428_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_19 sourceBody428_43

def sourceBody428_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody428_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody428_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_46 sourceBody428_0

def sourceBody428_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_47 sourceBody428_0

def sourceBody428_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_45 sourceBody428_48

def sourceBody428_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_0 sourceBody428_49

def sourceBody428_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_44 sourceBody428_50

def sourceBody428_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_18 sourceBody428_51

def sourceBody428_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_0 sourceBody428_52

def sourceBody428_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_0 sourceBody428_53

def sourceBody428_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_0 sourceBody428_54

def sourceBody428_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_0 sourceBody428_55

def sourceBody428_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_0 sourceBody428_56

def sourceBody428_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_0 sourceBody428_57

def sourceBody428_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody428_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_58 sourceBody428_59

def sourceBody428_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody428_62 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody428_60 sourceBody428_61

def sourceBody428_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_62 sourceBody428_3

def sourceBody428_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_63 sourceBody428_0

def sourceBody428_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_10 sourceBody428_64

def sourceBody428_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_9 sourceBody428_65

def sourceBody428_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_5 sourceBody428_66

def sourceBody428_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_4 sourceBody428_67

def sourceBody428_69 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln) sourceBody428_68 (Flapjack.Spt.ls PUnit.unit)

def sourceBody428_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_69 sourceBody428_3

def sourceBody428_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_3 sourceBody428_70

def sourceBody428_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody428_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody428_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_73 sourceBody428_0

def sourceBody428_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_72 sourceBody428_74

def sourceBody428_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_71 sourceBody428_75

def sourceBody428_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_2 sourceBody428_76

def sourceBody428_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_0 sourceBody428_77

def sourceBody428_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_1 sourceBody428_78

def sourceBody428_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody428_0 sourceBody428_79

def source428 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (428, 3, sourceBody428_80)
end InitECandidate.Proofs.WordStages
