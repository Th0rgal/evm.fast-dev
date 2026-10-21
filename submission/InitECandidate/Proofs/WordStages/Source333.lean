import InitECandidate.Proofs.WordStages.Source317
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody333_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody333_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody333_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody333_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody333_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody333_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([20, 16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody333_0, 333, 2)) (some 331) ([24, 10, 18]) (some (24, sourceBody333_4, 333, 3))

def sourceBody333_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody333_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_5 sourceBody333_6

def sourceBody333_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_7 sourceBody333_0

def sourceBody333_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_3 sourceBody333_8

def sourceBody333_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_2 sourceBody333_9

def sourceBody333_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_1 sourceBody333_10

def sourceBody333_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody333_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody333_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody333_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody333_16 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 18) sourceBody333_14 sourceBody333_15

def sourceBody333_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_16 sourceBody333_6

def sourceBody333_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody333_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody333_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 24)

def sourceBody333_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_20 sourceBody333_0

def sourceBody333_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_21 sourceBody333_0

def sourceBody333_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_19 sourceBody333_22

def sourceBody333_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_0 sourceBody333_23

def sourceBody333_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody333_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_25 sourceBody333_4

def sourceBody333_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_24 sourceBody333_26

def sourceBody333_28 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody333_27 sourceBody333_0

def sourceBody333_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_28 sourceBody333_6

def sourceBody333_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_29 sourceBody333_0

def sourceBody333_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_18 sourceBody333_30

def sourceBody333_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_17 sourceBody333_31

def sourceBody333_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_13 sourceBody333_32

def sourceBody333_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_12 sourceBody333_33

def sourceBody333_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody333_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 16)

def sourceBody333_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody333_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody333_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 14 (Flapjack.WordRegImm.reg 22) sourceBody333_37 sourceBody333_38

def sourceBody333_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_39 sourceBody333_6

def sourceBody333_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody333_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.var 10])

def sourceBody333_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 18 (Flapjack.WordLangAddr.addr 18 0#64))

def sourceBody333_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_43 sourceBody333_0

def sourceBody333_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_42 sourceBody333_44

def sourceBody333_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.var 18])

def sourceBody333_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody333_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_47 sourceBody333_0

def sourceBody333_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_48 sourceBody333_0

def sourceBody333_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_46 sourceBody333_49

def sourceBody333_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_45 sourceBody333_50

def sourceBody333_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody333_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody333_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_53 sourceBody333_0

def sourceBody333_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_54 sourceBody333_0

def sourceBody333_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_52 sourceBody333_55

def sourceBody333_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_0 sourceBody333_56

def sourceBody333_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_51 sourceBody333_57

def sourceBody333_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody333_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_58 sourceBody333_59

def sourceBody333_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody333_62 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody333_60 sourceBody333_61

def sourceBody333_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_62 sourceBody333_6

def sourceBody333_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_63 sourceBody333_0

def sourceBody333_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_41 sourceBody333_64

def sourceBody333_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_40 sourceBody333_65

def sourceBody333_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_36 sourceBody333_66

def sourceBody333_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_18 sourceBody333_67

def sourceBody333_69 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody333_68 (Flapjack.Spt.bs
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody333_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_69 sourceBody333_6

def sourceBody333_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_6 sourceBody333_70

def sourceBody333_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody333_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody333_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_73 sourceBody333_0

def sourceBody333_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_72 sourceBody333_74

def sourceBody333_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_71 sourceBody333_75

def sourceBody333_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_15 sourceBody333_76

def sourceBody333_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_0 sourceBody333_77

def sourceBody333_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_35 sourceBody333_78

def sourceBody333_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_0 sourceBody333_79

def sourceBody333_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_34 sourceBody333_80

def sourceBody333_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_11 sourceBody333_81

def sourceBody333_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_0 sourceBody333_82

def sourceBody333_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_0 sourceBody333_83

def sourceBody333_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_0 sourceBody333_84

def sourceBody333_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody333_0 sourceBody333_85

def source333 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (333, 5, sourceBody333_86)
end InitECandidate.Proofs.WordStages
