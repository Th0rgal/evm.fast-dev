import InitECandidate.Proofs.WordStages.Source292
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody308_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody308_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody308_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody308_0, 308, 2)) (some 294) ([]) (some (20, sourceBody308_1, 308, 3))

def sourceBody308_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody308_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_2 sourceBody308_3

def sourceBody308_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_4 sourceBody308_0

def sourceBody308_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody308_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody308_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody308_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody308_10 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 28 (Flapjack.WordRegImm.reg 18) sourceBody308_8 sourceBody308_9

def sourceBody308_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_10 sourceBody308_3

def sourceBody308_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody308_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 160#64])

def sourceBody308_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 6)

def sourceBody308_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody308_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 20) 18

def sourceBody308_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_16 sourceBody308_0

def sourceBody308_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_15 sourceBody308_17

def sourceBody308_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_18 sourceBody308_0

def sourceBody308_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_14 sourceBody308_19

def sourceBody308_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_0 sourceBody308_20

def sourceBody308_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_13 sourceBody308_21

def sourceBody308_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_0 sourceBody308_22

def sourceBody308_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 168#64])

def sourceBody308_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 8)

def sourceBody308_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_25 sourceBody308_19

def sourceBody308_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_0 sourceBody308_26

def sourceBody308_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_24 sourceBody308_27

def sourceBody308_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_0 sourceBody308_28

def sourceBody308_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_23 sourceBody308_29

def sourceBody308_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody308_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody308_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody308_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 8)

def sourceBody308_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody308_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody308_0, 308, 4)) (some 292) ([28, 18, 26, 22]) (some (28, sourceBody308_35, 308, 5))

def sourceBody308_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_36 sourceBody308_3

def sourceBody308_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_37 sourceBody308_0

def sourceBody308_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_34 sourceBody308_38

def sourceBody308_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_33 sourceBody308_39

def sourceBody308_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_32 sourceBody308_40

def sourceBody308_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_31 sourceBody308_41

def sourceBody308_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 2)

def sourceBody308_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 28 (Flapjack.WordLangAddr.addr 28 0#64))

def sourceBody308_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_44 sourceBody308_0

def sourceBody308_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_43 sourceBody308_45

def sourceBody308_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 32#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 28)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody308_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 20)

def sourceBody308_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody308_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 18) 22

def sourceBody308_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_50 sourceBody308_0

def sourceBody308_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_49 sourceBody308_51

def sourceBody308_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_52 sourceBody308_0

def sourceBody308_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_48 sourceBody308_53

def sourceBody308_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_0 sourceBody308_54

def sourceBody308_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_47 sourceBody308_55

def sourceBody308_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_46 sourceBody308_56

def sourceBody308_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_42 sourceBody308_57

def sourceBody308_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_0 sourceBody308_58

def sourceBody308_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_0 sourceBody308_59

def sourceBody308_61 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody308_30 sourceBody308_60

def sourceBody308_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_61 sourceBody308_3

def sourceBody308_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_62 sourceBody308_0

def sourceBody308_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_12 sourceBody308_63

def sourceBody308_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_11 sourceBody308_64

def sourceBody308_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_7 sourceBody308_65

def sourceBody308_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_6 sourceBody308_66

def sourceBody308_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 12)

def sourceBody308_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 14)

def sourceBody308_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_69 sourceBody308_19

def sourceBody308_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_0 sourceBody308_70

def sourceBody308_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_13 sourceBody308_71

def sourceBody308_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_0 sourceBody308_72

def sourceBody308_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 16)

def sourceBody308_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_74 sourceBody308_19

def sourceBody308_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_0 sourceBody308_75

def sourceBody308_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_24 sourceBody308_76

def sourceBody308_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_0 sourceBody308_77

def sourceBody308_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_73 sourceBody308_78

def sourceBody308_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody308_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody308_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 14)

def sourceBody308_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 16)

def sourceBody308_84 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody308_0, 308, 6)) (some 292) ([28, 18, 26, 22]) (some (28, sourceBody308_35, 308, 7))

def sourceBody308_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_84 sourceBody308_3

def sourceBody308_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_85 sourceBody308_0

def sourceBody308_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_83 sourceBody308_86

def sourceBody308_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_82 sourceBody308_87

def sourceBody308_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_81 sourceBody308_88

def sourceBody308_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_80 sourceBody308_89

def sourceBody308_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 10)

def sourceBody308_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_91 sourceBody308_45

def sourceBody308_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_92 sourceBody308_56

def sourceBody308_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_90 sourceBody308_93

def sourceBody308_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_0 sourceBody308_94

def sourceBody308_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_0 sourceBody308_95

def sourceBody308_97 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody308_79 sourceBody308_96

def sourceBody308_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_97 sourceBody308_3

def sourceBody308_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_98 sourceBody308_0

def sourceBody308_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_12 sourceBody308_99

def sourceBody308_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_11 sourceBody308_100

def sourceBody308_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_7 sourceBody308_101

def sourceBody308_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_68 sourceBody308_102

def sourceBody308_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_67 sourceBody308_103

def sourceBody308_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody308_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody308_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_106 sourceBody308_0

def sourceBody308_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_105 sourceBody308_107

def sourceBody308_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_104 sourceBody308_108

def sourceBody308_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_5 sourceBody308_109

def sourceBody308_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_0 sourceBody308_110

def sourceBody308_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody308_0 sourceBody308_111

def source308 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (308, 9, sourceBody308_112)
end InitECandidate.Proofs.WordStages
