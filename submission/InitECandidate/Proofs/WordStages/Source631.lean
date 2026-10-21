import InitECandidate.Proofs.WordStages.Source615
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody631_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody631_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 3#64])
    (Flapjack.WordLangExpHOL.const 2#64))

def sourceBody631_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody631_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody631_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody631_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody631_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody631_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody631_8 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 22 (Flapjack.WordRegImm.reg 8) sourceBody631_6 sourceBody631_7

def sourceBody631_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_8 sourceBody631_3

def sourceBody631_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody631_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 18)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody631_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 22)

def sourceBody631_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 14) 8

def sourceBody631_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_13 sourceBody631_0

def sourceBody631_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_12 sourceBody631_14

def sourceBody631_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_15 sourceBody631_0

def sourceBody631_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_7 sourceBody631_16

def sourceBody631_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_0 sourceBody631_17

def sourceBody631_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_11 sourceBody631_18

def sourceBody631_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_0 sourceBody631_19

def sourceBody631_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody631_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody631_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_22 sourceBody631_0

def sourceBody631_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_23 sourceBody631_0

def sourceBody631_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_21 sourceBody631_24

def sourceBody631_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_0 sourceBody631_25

def sourceBody631_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_20 sourceBody631_26

def sourceBody631_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody631_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_27 sourceBody631_28

def sourceBody631_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody631_31 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody631_29 sourceBody631_30

def sourceBody631_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_31 sourceBody631_3

def sourceBody631_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_32 sourceBody631_0

def sourceBody631_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_10 sourceBody631_33

def sourceBody631_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_9 sourceBody631_34

def sourceBody631_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_5 sourceBody631_35

def sourceBody631_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_4 sourceBody631_36

def sourceBody631_38 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit Flapjack.Spt.ln) sourceBody631_37 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody631_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_38 sourceBody631_3

def sourceBody631_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_3 sourceBody631_39

def sourceBody631_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_2 sourceBody631_0

def sourceBody631_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_41 sourceBody631_0

def sourceBody631_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_40 sourceBody631_42

def sourceBody631_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody631_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64],
      Flapjack.WordLangExpHOL.var 18])

def sourceBody631_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 14)
          (Flapjack.WordLangExpHOL.const 2#64))
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody631_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 18])

def sourceBody631_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 16 (Flapjack.WordLangAddr.addr 16 0#64))

def sourceBody631_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_48 sourceBody631_0

def sourceBody631_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_47 sourceBody631_49

def sourceBody631_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 22),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
        (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
            [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 3#64])
          (Flapjack.WordLangExpHOL.const 3#64))])

def sourceBody631_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody631_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 20

def sourceBody631_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_53 sourceBody631_0

def sourceBody631_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_52 sourceBody631_54

def sourceBody631_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_55 sourceBody631_0

def sourceBody631_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_51 sourceBody631_56

def sourceBody631_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_50 sourceBody631_57

def sourceBody631_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_12 sourceBody631_58

def sourceBody631_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_0 sourceBody631_59

def sourceBody631_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody631_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody631_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_62 sourceBody631_0

def sourceBody631_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_63 sourceBody631_0

def sourceBody631_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_61 sourceBody631_64

def sourceBody631_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_0 sourceBody631_65

def sourceBody631_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_60 sourceBody631_66

def sourceBody631_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_46 sourceBody631_67

def sourceBody631_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_0 sourceBody631_68

def sourceBody631_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_45 sourceBody631_69

def sourceBody631_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_0 sourceBody631_70

def sourceBody631_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_71 sourceBody631_28

def sourceBody631_73 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody631_72 sourceBody631_30

def sourceBody631_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_73 sourceBody631_3

def sourceBody631_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_74 sourceBody631_0

def sourceBody631_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_10 sourceBody631_75

def sourceBody631_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_9 sourceBody631_76

def sourceBody631_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_44 sourceBody631_77

def sourceBody631_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_4 sourceBody631_78

def sourceBody631_80 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit Flapjack.Spt.ln) sourceBody631_79 (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
  PUnit.unit Flapjack.Spt.ln)

def sourceBody631_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_80 sourceBody631_3

def sourceBody631_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_3 sourceBody631_81

def sourceBody631_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_43 sourceBody631_82

def sourceBody631_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody631_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody631_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_85 sourceBody631_0

def sourceBody631_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_84 sourceBody631_86

def sourceBody631_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_83 sourceBody631_87

def sourceBody631_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_2 sourceBody631_88

def sourceBody631_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_0 sourceBody631_89

def sourceBody631_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_1 sourceBody631_90

def sourceBody631_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody631_0 sourceBody631_91

def source631 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (631, 4, sourceBody631_92)
end InitECandidate.Proofs.WordStages
