import InitECandidate.Proofs.WordStages.Source448
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody464_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody464_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 23#64)

def sourceBody464_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody464_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody464_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 28) sourceBody464_2 sourceBody464_3

def sourceBody464_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody464_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_4 sourceBody464_5

def sourceBody464_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody464_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody464_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [32]

def sourceBody464_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody464_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_9 sourceBody464_10

def sourceBody464_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_8 sourceBody464_11

def sourceBody464_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody464_12 sourceBody464_10

def sourceBody464_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_13 sourceBody464_5

def sourceBody464_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_14 sourceBody464_10

def sourceBody464_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_7 sourceBody464_15

def sourceBody464_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_6 sourceBody464_16

def sourceBody464_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_1 sourceBody464_17

def sourceBody464_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_0 sourceBody464_18

def sourceBody464_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 2)

def sourceBody464_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 32 (Flapjack.WordLangAddr.addr 32 0#64))

def sourceBody464_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 32)

def sourceBody464_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 239#64)

def sourceBody464_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody464_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody464_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 28 (Flapjack.WordRegImm.reg 20) sourceBody464_24 sourceBody464_25

def sourceBody464_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_26 sourceBody464_5

def sourceBody464_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody464_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody464_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody464_31 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.reg 26) sourceBody464_30 sourceBody464_28

def sourceBody464_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_31 sourceBody464_5

def sourceBody464_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody464_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 18 (Flapjack.WordLangAddr.addr 18 0#64))

def sourceBody464_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody464_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody464_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody464_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody464_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 30) sourceBody464_37 sourceBody464_38

def sourceBody464_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_39 sourceBody464_5

def sourceBody464_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody464_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody464_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody464_44 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.reg 6) sourceBody464_43 sourceBody464_41

def sourceBody464_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_44 sourceBody464_5

def sourceBody464_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody464_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 24 (Flapjack.WordLangAddr.addr 24 0#64))

def sourceBody464_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 24)

def sourceBody464_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody464_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody464_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody464_52 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 34 (Flapjack.WordRegImm.reg 14) sourceBody464_50 sourceBody464_51

def sourceBody464_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_52 sourceBody464_5

def sourceBody464_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody464_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 34)

def sourceBody464_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody464_57 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.reg 36) sourceBody464_56 sourceBody464_54

def sourceBody464_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_57 sourceBody464_5

def sourceBody464_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.var 22])

def sourceBody464_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody464_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_60 sourceBody464_11

def sourceBody464_62 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody464_61 sourceBody464_10

def sourceBody464_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_62 sourceBody464_5

def sourceBody464_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_63 sourceBody464_10

def sourceBody464_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_59 sourceBody464_64

def sourceBody464_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_58 sourceBody464_65

def sourceBody464_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_55 sourceBody464_66

def sourceBody464_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_54 sourceBody464_67

def sourceBody464_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_53 sourceBody464_68

def sourceBody464_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_49 sourceBody464_69

def sourceBody464_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_48 sourceBody464_70

def sourceBody464_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_47 sourceBody464_71

def sourceBody464_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_46 sourceBody464_72

def sourceBody464_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_45 sourceBody464_73

def sourceBody464_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_42 sourceBody464_74

def sourceBody464_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_41 sourceBody464_75

def sourceBody464_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_40 sourceBody464_76

def sourceBody464_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_36 sourceBody464_77

def sourceBody464_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_35 sourceBody464_78

def sourceBody464_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_34 sourceBody464_79

def sourceBody464_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_33 sourceBody464_80

def sourceBody464_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_32 sourceBody464_81

def sourceBody464_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_29 sourceBody464_82

def sourceBody464_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_28 sourceBody464_83

def sourceBody464_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_27 sourceBody464_84

def sourceBody464_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_23 sourceBody464_85

def sourceBody464_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_22 sourceBody464_86

def sourceBody464_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_21 sourceBody464_87

def sourceBody464_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_20 sourceBody464_88

def sourceBody464_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_19 sourceBody464_89

def sourceBody464_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody464_90 sourceBody464_12

def source464 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (464, 3, sourceBody464_91)
end InitECandidate.Proofs.WordStages
