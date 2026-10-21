import InitECandidate.Proofs.WordStages.Source250
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody266_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody266_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody266_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody266_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody266_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody266_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 8]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody266_0, 266, 2)) (some 265) ([16, 12, 20]) (some (16, sourceBody266_4, 266, 3))

def sourceBody266_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody266_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_5 sourceBody266_6

def sourceBody266_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_7 sourceBody266_0

def sourceBody266_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_3 sourceBody266_8

def sourceBody266_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_2 sourceBody266_9

def sourceBody266_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_1 sourceBody266_10

def sourceBody266_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody266_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody266_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody266_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody266_16 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 12 (Flapjack.WordRegImm.reg 20) sourceBody266_14 sourceBody266_15

def sourceBody266_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_16 sourceBody266_6

def sourceBody266_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody266_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody266_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 16)

def sourceBody266_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_20 sourceBody266_0

def sourceBody266_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_21 sourceBody266_0

def sourceBody266_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_19 sourceBody266_22

def sourceBody266_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_0 sourceBody266_23

def sourceBody266_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody266_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_25 sourceBody266_4

def sourceBody266_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_24 sourceBody266_26

def sourceBody266_28 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody266_27 sourceBody266_0

def sourceBody266_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_28 sourceBody266_6

def sourceBody266_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_29 sourceBody266_0

def sourceBody266_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_18 sourceBody266_30

def sourceBody266_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_17 sourceBody266_31

def sourceBody266_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_13 sourceBody266_32

def sourceBody266_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_12 sourceBody266_33

def sourceBody266_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody266_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody266_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody266_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody266_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 6 (Flapjack.WordRegImm.reg 14) sourceBody266_37 sourceBody266_38

def sourceBody266_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_39 sourceBody266_6

def sourceBody266_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody266_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 12])

def sourceBody266_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 20 (Flapjack.WordLangAddr.addr 20 0#64))

def sourceBody266_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_43 sourceBody266_0

def sourceBody266_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_42 sourceBody266_44

def sourceBody266_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.var 20])

def sourceBody266_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody266_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_47 sourceBody266_0

def sourceBody266_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_48 sourceBody266_0

def sourceBody266_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_46 sourceBody266_49

def sourceBody266_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_45 sourceBody266_50

def sourceBody266_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody266_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 20)

def sourceBody266_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_53 sourceBody266_0

def sourceBody266_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_54 sourceBody266_0

def sourceBody266_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_52 sourceBody266_55

def sourceBody266_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_0 sourceBody266_56

def sourceBody266_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_51 sourceBody266_57

def sourceBody266_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody266_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_58 sourceBody266_59

def sourceBody266_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody266_62 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody266_60 sourceBody266_61

def sourceBody266_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_62 sourceBody266_6

def sourceBody266_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_63 sourceBody266_0

def sourceBody266_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_41 sourceBody266_64

def sourceBody266_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_40 sourceBody266_65

def sourceBody266_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_36 sourceBody266_66

def sourceBody266_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_18 sourceBody266_67

def sourceBody266_69 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody266_68 (Flapjack.Spt.bs
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody266_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_69 sourceBody266_6

def sourceBody266_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_6 sourceBody266_70

def sourceBody266_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody266_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody266_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_73 sourceBody266_0

def sourceBody266_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_72 sourceBody266_74

def sourceBody266_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_71 sourceBody266_75

def sourceBody266_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_15 sourceBody266_76

def sourceBody266_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_0 sourceBody266_77

def sourceBody266_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_35 sourceBody266_78

def sourceBody266_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_0 sourceBody266_79

def sourceBody266_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_34 sourceBody266_80

def sourceBody266_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_11 sourceBody266_81

def sourceBody266_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_0 sourceBody266_82

def sourceBody266_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_0 sourceBody266_83

def sourceBody266_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_0 sourceBody266_84

def sourceBody266_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody266_0 sourceBody266_85

def source266 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (266, 3, sourceBody266_86)
end InitECandidate.Proofs.WordStages
