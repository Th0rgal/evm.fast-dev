import InitECandidate.Proofs.WordStages.Source315
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody331_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody331_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody331_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody331_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody331_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 20, 16, 24]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody331_0, 331, 2)) (some 161) ([8, 18]) (some (8, sourceBody331_3, 331, 3))

def sourceBody331_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody331_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_4 sourceBody331_5

def sourceBody331_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_6 sourceBody331_0

def sourceBody331_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_2 sourceBody331_7

def sourceBody331_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_1 sourceBody331_8

def sourceBody331_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody331_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody331_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody331_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody331_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.reg 14) sourceBody331_12 sourceBody331_13

def sourceBody331_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_14 sourceBody331_5

def sourceBody331_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody331_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody331_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 8)

def sourceBody331_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_18 sourceBody331_0

def sourceBody331_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_19 sourceBody331_0

def sourceBody331_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_17 sourceBody331_20

def sourceBody331_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_0 sourceBody331_21

def sourceBody331_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody331_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_23 sourceBody331_3

def sourceBody331_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_22 sourceBody331_24

def sourceBody331_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody331_25 sourceBody331_0

def sourceBody331_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_26 sourceBody331_5

def sourceBody331_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_27 sourceBody331_0

def sourceBody331_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_16 sourceBody331_28

def sourceBody331_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_15 sourceBody331_29

def sourceBody331_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_11 sourceBody331_30

def sourceBody331_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_10 sourceBody331_31

def sourceBody331_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody331_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 18 (Flapjack.WordRegImm.reg 14) sourceBody331_12 sourceBody331_13

def sourceBody331_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_34 sourceBody331_5

def sourceBody331_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 20)

def sourceBody331_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 8 (Flapjack.WordLangAddr.addr 8 0#64))

def sourceBody331_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody331_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody331_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody331_41 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 22) sourceBody331_40 sourceBody331_11

def sourceBody331_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_41 sourceBody331_5

def sourceBody331_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody331_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 11#64)

def sourceBody331_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_44 sourceBody331_20

def sourceBody331_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_0 sourceBody331_45

def sourceBody331_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_46 sourceBody331_24

def sourceBody331_48 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody331_47 sourceBody331_0

def sourceBody331_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_48 sourceBody331_5

def sourceBody331_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_49 sourceBody331_0

def sourceBody331_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_43 sourceBody331_50

def sourceBody331_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_42 sourceBody331_51

def sourceBody331_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_39 sourceBody331_52

def sourceBody331_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_38 sourceBody331_53

def sourceBody331_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_37 sourceBody331_54

def sourceBody331_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_36 sourceBody331_55

def sourceBody331_57 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody331_56 sourceBody331_0

def sourceBody331_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_57 sourceBody331_5

def sourceBody331_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_58 sourceBody331_0

def sourceBody331_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_16 sourceBody331_59

def sourceBody331_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_35 sourceBody331_60

def sourceBody331_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_33 sourceBody331_61

def sourceBody331_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_13 sourceBody331_62

def sourceBody331_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_32 sourceBody331_63

def sourceBody331_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody331_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody331_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_66 sourceBody331_20

def sourceBody331_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_0 sourceBody331_67

def sourceBody331_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_68 sourceBody331_24

def sourceBody331_70 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody331_69 sourceBody331_0

def sourceBody331_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_70 sourceBody331_5

def sourceBody331_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_71 sourceBody331_0

def sourceBody331_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_16 sourceBody331_72

def sourceBody331_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_35 sourceBody331_73

def sourceBody331_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_33 sourceBody331_74

def sourceBody331_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_65 sourceBody331_75

def sourceBody331_77 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody331_76 sourceBody331_0

def sourceBody331_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_77 sourceBody331_5

def sourceBody331_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_78 sourceBody331_0

def sourceBody331_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_16 sourceBody331_79

def sourceBody331_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_15 sourceBody331_80

def sourceBody331_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_11 sourceBody331_81

def sourceBody331_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_65 sourceBody331_82

def sourceBody331_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_64 sourceBody331_83

def sourceBody331_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody331_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8, 18]

def sourceBody331_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_86 sourceBody331_0

def sourceBody331_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_85 sourceBody331_87

def sourceBody331_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_36 sourceBody331_88

def sourceBody331_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_84 sourceBody331_89

def sourceBody331_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_9 sourceBody331_90

def sourceBody331_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_0 sourceBody331_91

def sourceBody331_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_0 sourceBody331_92

def sourceBody331_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_0 sourceBody331_93

def sourceBody331_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_0 sourceBody331_94

def sourceBody331_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_0 sourceBody331_95

def sourceBody331_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_0 sourceBody331_96

def sourceBody331_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_0 sourceBody331_97

def sourceBody331_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody331_0 sourceBody331_98

def source331 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (331, 4, sourceBody331_99)
end InitECandidate.Proofs.WordStages
