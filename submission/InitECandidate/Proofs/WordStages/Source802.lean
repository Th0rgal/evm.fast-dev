import InitECandidate.Proofs.WordStages.Source786
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody802_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody802_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 14 (Flapjack.WordLangAddr.addr 14 0#64))

def sourceBody802_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody802_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 192#64)

def sourceBody802_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody802_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody802_6 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.WordRegImm.reg 10) sourceBody802_4 sourceBody802_5

def sourceBody802_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody802_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_6 sourceBody802_7

def sourceBody802_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody802_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody802_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody802_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 47#64)

def sourceBody802_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody802_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody802_10, 802, 2)) (some 80) ([8, 12]) (some (8, sourceBody802_13, 802, 3))

def sourceBody802_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_14 sourceBody802_7

def sourceBody802_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_15 sourceBody802_10

def sourceBody802_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_12 sourceBody802_16

def sourceBody802_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_11 sourceBody802_17

def sourceBody802_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody802_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody802_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody802_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody802_10, 802, 4)) (some 762) ([12]) (some (12, sourceBody802_21, 802, 5))

def sourceBody802_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_22 sourceBody802_7

def sourceBody802_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_23 sourceBody802_10

def sourceBody802_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_20 sourceBody802_24

def sourceBody802_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_10 sourceBody802_25

def sourceBody802_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_10 sourceBody802_26

def sourceBody802_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody802_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody802_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_29 sourceBody802_10

def sourceBody802_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_28 sourceBody802_30

def sourceBody802_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_27 sourceBody802_31

def sourceBody802_33 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody802_32 sourceBody802_10

def sourceBody802_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_33 sourceBody802_7

def sourceBody802_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_34 sourceBody802_10

def sourceBody802_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_9 sourceBody802_35

def sourceBody802_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_8 sourceBody802_36

def sourceBody802_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_19 sourceBody802_37

def sourceBody802_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_2 sourceBody802_38

def sourceBody802_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_18 sourceBody802_39

def sourceBody802_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_10 sourceBody802_40

def sourceBody802_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_10 sourceBody802_41

def sourceBody802_43 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody802_42 sourceBody802_10

def sourceBody802_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_43 sourceBody802_7

def sourceBody802_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_44 sourceBody802_10

def sourceBody802_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_9 sourceBody802_45

def sourceBody802_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_8 sourceBody802_46

def sourceBody802_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_3 sourceBody802_47

def sourceBody802_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_2 sourceBody802_48

def sourceBody802_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_1 sourceBody802_49

def sourceBody802_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_0 sourceBody802_50

def sourceBody802_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody802_53 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody802_10, 802, 6)) (some 801) ([8, 12]) (some (8, sourceBody802_13, 802, 7))

def sourceBody802_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_53 sourceBody802_7

def sourceBody802_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_54 sourceBody802_10

def sourceBody802_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_20 sourceBody802_55

def sourceBody802_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_52 sourceBody802_56

def sourceBody802_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody802_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody802_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_59 sourceBody802_30

def sourceBody802_61 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody802_60 sourceBody802_10

def sourceBody802_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_61 sourceBody802_7

def sourceBody802_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_62 sourceBody802_10

def sourceBody802_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_9 sourceBody802_63

def sourceBody802_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_8 sourceBody802_64

def sourceBody802_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_58 sourceBody802_65

def sourceBody802_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_2 sourceBody802_66

def sourceBody802_68 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody802_10, 802, 8)) (some 763) ([12]) (some (12, sourceBody802_21, 802, 9))

def sourceBody802_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_68 sourceBody802_7

def sourceBody802_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_69 sourceBody802_10

def sourceBody802_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_20 sourceBody802_70

def sourceBody802_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody802_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody802_74 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 16) sourceBody802_19 sourceBody802_58

def sourceBody802_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_74 sourceBody802_7

def sourceBody802_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody802_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody802_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_77 sourceBody802_10

def sourceBody802_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_5 sourceBody802_78

def sourceBody802_80 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody802_79 sourceBody802_10

def sourceBody802_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_80 sourceBody802_7

def sourceBody802_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_81 sourceBody802_10

def sourceBody802_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_76 sourceBody802_82

def sourceBody802_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_75 sourceBody802_83

def sourceBody802_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_73 sourceBody802_84

def sourceBody802_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_72 sourceBody802_85

def sourceBody802_87 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 773) ([0, 12]) (none)

def sourceBody802_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_87 sourceBody802_10

def sourceBody802_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_20 sourceBody802_88

def sourceBody802_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_86 sourceBody802_89

def sourceBody802_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_71 sourceBody802_90

def sourceBody802_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_10 sourceBody802_91

def sourceBody802_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_10 sourceBody802_92

def sourceBody802_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_67 sourceBody802_93

def sourceBody802_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_57 sourceBody802_94

def sourceBody802_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_10 sourceBody802_95

def sourceBody802_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_10 sourceBody802_96

def sourceBody802_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody802_51 sourceBody802_97

def source802 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (802, 3, sourceBody802_98)
end InitECandidate.Proofs.WordStages
