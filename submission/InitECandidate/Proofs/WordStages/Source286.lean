import InitECandidate.Proofs.WordStages.Source270
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody286_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody286_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 6)
    (Flapjack.WordLangExpHOL.const 1#64))

def sourceBody286_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody286_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody286_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody286_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody286_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody286_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 16) sourceBody286_5 sourceBody286_6

def sourceBody286_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody286_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_7 sourceBody286_8

def sourceBody286_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody286_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 8)

def sourceBody286_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 18)
    (Flapjack.WordLangExpHOL.const 4#64))

def sourceBody286_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 10 (Flapjack.WordLangAddr.addr 22 0#64))

def sourceBody286_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_13 sourceBody286_0

def sourceBody286_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_12 sourceBody286_14

def sourceBody286_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_11 sourceBody286_15

def sourceBody286_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 2)

def sourceBody286_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 22 (Flapjack.WordLangAddr.addr 22 0#64))

def sourceBody286_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody286_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 1#64])
        (Flapjack.WordLangExpHOL.const 4#64),
      Flapjack.WordLangExpHOL.var 22])

def sourceBody286_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 16 (Flapjack.WordLangAddr.addr 10 0#64))

def sourceBody286_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_21 sourceBody286_0

def sourceBody286_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_20 sourceBody286_22

def sourceBody286_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_19 sourceBody286_23

def sourceBody286_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_18 sourceBody286_24

def sourceBody286_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_17 sourceBody286_25

def sourceBody286_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody286_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_27 sourceBody286_0

def sourceBody286_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_28 sourceBody286_0

def sourceBody286_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_26 sourceBody286_29

def sourceBody286_31 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody286_16 sourceBody286_30

def sourceBody286_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_31 sourceBody286_8

def sourceBody286_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_32 sourceBody286_0

def sourceBody286_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_10 sourceBody286_33

def sourceBody286_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_9 sourceBody286_34

def sourceBody286_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_4 sourceBody286_35

def sourceBody286_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_3 sourceBody286_36

def sourceBody286_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody286_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody286_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody286_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody286_42 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 16 (Flapjack.WordRegImm.reg 12) sourceBody286_41 sourceBody286_4

def sourceBody286_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_42 sourceBody286_8

def sourceBody286_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody286_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 14])

def sourceBody286_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 10 (Flapjack.WordLangAddr.addr 10 0#64))

def sourceBody286_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody286_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 16 (Flapjack.WordLangAddr.addr 16 0#64))

def sourceBody286_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 22])

def sourceBody286_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 10)
        (Flapjack.WordLangExpHOL.const 4#64),
      Flapjack.WordLangExpHOL.var 16])

def sourceBody286_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 20 (Flapjack.WordLangAddr.addr 12 0#64))

def sourceBody286_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_51 sourceBody286_0

def sourceBody286_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_50 sourceBody286_52

def sourceBody286_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_49 sourceBody286_53

def sourceBody286_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_48 sourceBody286_54

def sourceBody286_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_47 sourceBody286_55

def sourceBody286_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_46 sourceBody286_56

def sourceBody286_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_45 sourceBody286_57

def sourceBody286_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody286_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody286_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_60 sourceBody286_0

def sourceBody286_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_61 sourceBody286_0

def sourceBody286_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_59 sourceBody286_62

def sourceBody286_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_0 sourceBody286_63

def sourceBody286_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_58 sourceBody286_64

def sourceBody286_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody286_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody286_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_67 sourceBody286_0

def sourceBody286_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_68 sourceBody286_0

def sourceBody286_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_66 sourceBody286_69

def sourceBody286_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_0 sourceBody286_70

def sourceBody286_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_65 sourceBody286_71

def sourceBody286_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody286_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_72 sourceBody286_73

def sourceBody286_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody286_76 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody286_74 sourceBody286_75

def sourceBody286_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_76 sourceBody286_8

def sourceBody286_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_77 sourceBody286_0

def sourceBody286_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_44 sourceBody286_78

def sourceBody286_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_43 sourceBody286_79

def sourceBody286_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_40 sourceBody286_80

def sourceBody286_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_39 sourceBody286_81

def sourceBody286_83 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln) sourceBody286_82 (Flapjack.Spt.bs
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    Flapjack.Spt.ln)
  PUnit.unit Flapjack.Spt.ln)

def sourceBody286_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_83 sourceBody286_8

def sourceBody286_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_8 sourceBody286_84

def sourceBody286_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 22)

def sourceBody286_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody286_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_87 sourceBody286_0

def sourceBody286_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_86 sourceBody286_88

def sourceBody286_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_85 sourceBody286_89

def sourceBody286_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_38 sourceBody286_90

def sourceBody286_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_0 sourceBody286_91

def sourceBody286_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_37 sourceBody286_92

def sourceBody286_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_2 sourceBody286_93

def sourceBody286_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_0 sourceBody286_94

def sourceBody286_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_1 sourceBody286_95

def sourceBody286_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody286_0 sourceBody286_96

def source286 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (286, 5, sourceBody286_97)
end InitECandidate.Proofs.WordStages
