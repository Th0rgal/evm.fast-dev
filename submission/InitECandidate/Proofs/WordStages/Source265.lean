import InitECandidate.Proofs.WordStages.Source249
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody265_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody265_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody265_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody265_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody265_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 20, 16, 24]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody265_0, 265, 2)) (some 161) ([8, 18]) (some (8, sourceBody265_3, 265, 3))

def sourceBody265_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody265_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_4 sourceBody265_5

def sourceBody265_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_6 sourceBody265_0

def sourceBody265_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_2 sourceBody265_7

def sourceBody265_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_1 sourceBody265_8

def sourceBody265_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody265_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody265_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody265_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody265_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.reg 14) sourceBody265_12 sourceBody265_13

def sourceBody265_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_14 sourceBody265_5

def sourceBody265_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody265_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody265_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 8)

def sourceBody265_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_18 sourceBody265_0

def sourceBody265_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_19 sourceBody265_0

def sourceBody265_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_17 sourceBody265_20

def sourceBody265_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_0 sourceBody265_21

def sourceBody265_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody265_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_23 sourceBody265_3

def sourceBody265_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_22 sourceBody265_24

def sourceBody265_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody265_25 sourceBody265_0

def sourceBody265_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_26 sourceBody265_5

def sourceBody265_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_27 sourceBody265_0

def sourceBody265_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_16 sourceBody265_28

def sourceBody265_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_15 sourceBody265_29

def sourceBody265_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_11 sourceBody265_30

def sourceBody265_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_10 sourceBody265_31

def sourceBody265_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody265_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 20)

def sourceBody265_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 8 (Flapjack.WordLangAddr.addr 8 0#64))

def sourceBody265_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody265_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody265_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody265_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 22) sourceBody265_38 sourceBody265_11

def sourceBody265_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_39 sourceBody265_5

def sourceBody265_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody265_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody265_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_42 sourceBody265_20

def sourceBody265_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_0 sourceBody265_43

def sourceBody265_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_44 sourceBody265_24

def sourceBody265_46 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody265_45 sourceBody265_0

def sourceBody265_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_46 sourceBody265_5

def sourceBody265_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_47 sourceBody265_0

def sourceBody265_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_41 sourceBody265_48

def sourceBody265_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_40 sourceBody265_49

def sourceBody265_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_37 sourceBody265_50

def sourceBody265_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_36 sourceBody265_51

def sourceBody265_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_35 sourceBody265_52

def sourceBody265_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_34 sourceBody265_53

def sourceBody265_55 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody265_54 sourceBody265_0

def sourceBody265_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_55 sourceBody265_5

def sourceBody265_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_56 sourceBody265_0

def sourceBody265_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_16 sourceBody265_57

def sourceBody265_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_15 sourceBody265_58

def sourceBody265_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_11 sourceBody265_59

def sourceBody265_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_33 sourceBody265_60

def sourceBody265_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_32 sourceBody265_61

def sourceBody265_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody265_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody265_65 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 18 (Flapjack.WordRegImm.reg 14) sourceBody265_12 sourceBody265_13

def sourceBody265_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_65 sourceBody265_5

def sourceBody265_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_23 sourceBody265_20

def sourceBody265_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_0 sourceBody265_67

def sourceBody265_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_68 sourceBody265_24

def sourceBody265_70 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody265_69 sourceBody265_0

def sourceBody265_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_70 sourceBody265_5

def sourceBody265_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_71 sourceBody265_0

def sourceBody265_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_16 sourceBody265_72

def sourceBody265_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_66 sourceBody265_73

def sourceBody265_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_64 sourceBody265_74

def sourceBody265_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_63 sourceBody265_75

def sourceBody265_77 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody265_76 sourceBody265_0

def sourceBody265_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_77 sourceBody265_5

def sourceBody265_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_78 sourceBody265_0

def sourceBody265_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_16 sourceBody265_79

def sourceBody265_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_15 sourceBody265_80

def sourceBody265_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_11 sourceBody265_81

def sourceBody265_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_63 sourceBody265_82

def sourceBody265_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_62 sourceBody265_83

def sourceBody265_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8, 18]

def sourceBody265_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_85 sourceBody265_0

def sourceBody265_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_33 sourceBody265_86

def sourceBody265_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_34 sourceBody265_87

def sourceBody265_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_84 sourceBody265_88

def sourceBody265_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_9 sourceBody265_89

def sourceBody265_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_0 sourceBody265_90

def sourceBody265_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_0 sourceBody265_91

def sourceBody265_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_0 sourceBody265_92

def sourceBody265_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_0 sourceBody265_93

def sourceBody265_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_0 sourceBody265_94

def sourceBody265_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_0 sourceBody265_95

def sourceBody265_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_0 sourceBody265_96

def sourceBody265_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody265_0 sourceBody265_97

def source265 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (265, 4, sourceBody265_98)
end InitECandidate.Proofs.WordStages
