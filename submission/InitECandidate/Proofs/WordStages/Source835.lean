import InitECandidate.Proofs.WordStages.Source819
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody835_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody835_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody835_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 256#64)

def sourceBody835_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody835_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody835_0, 835, 2)) (some 78) ([8, 18]) (some (8, sourceBody835_3, 835, 3))

def sourceBody835_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody835_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_4 sourceBody835_5

def sourceBody835_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_6 sourceBody835_0

def sourceBody835_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_2 sourceBody835_7

def sourceBody835_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_1 sourceBody835_8

def sourceBody835_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_0 sourceBody835_9

def sourceBody835_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_0 sourceBody835_10

def sourceBody835_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody835_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody835_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody835_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody835_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 20)

def sourceBody835_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody835_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody835_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 24 (Flapjack.WordRegImm.reg 6) sourceBody835_17 sourceBody835_18

def sourceBody835_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_19 sourceBody835_5

def sourceBody835_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody835_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 18)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody835_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody835_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody835_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody835_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody835_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody835_0, 835, 4)) (some 834) ([6, 16, 12]) (some (6, sourceBody835_26, 835, 5))

def sourceBody835_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_27 sourceBody835_5

def sourceBody835_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_28 sourceBody835_0

def sourceBody835_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_25 sourceBody835_29

def sourceBody835_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_24 sourceBody835_30

def sourceBody835_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_23 sourceBody835_31

def sourceBody835_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_0 sourceBody835_32

def sourceBody835_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_0 sourceBody835_33

def sourceBody835_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody835_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody835_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody835_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 24)

def sourceBody835_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody835_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody835_41 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 12 (Flapjack.WordRegImm.reg 22) sourceBody835_39 sourceBody835_40

def sourceBody835_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_41 sourceBody835_5

def sourceBody835_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody835_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody835_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 8#64]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 6)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody835_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody835_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody835_48 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody835_0, 835, 6)) (some 834) ([12, 22, 10]) (some (12, sourceBody835_47, 835, 7))

def sourceBody835_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_48 sourceBody835_5

def sourceBody835_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_49 sourceBody835_0

def sourceBody835_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_46 sourceBody835_50

def sourceBody835_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_45 sourceBody835_51

def sourceBody835_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_44 sourceBody835_52

def sourceBody835_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_0 sourceBody835_53

def sourceBody835_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_0 sourceBody835_54

def sourceBody835_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody835_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody835_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_57 sourceBody835_0

def sourceBody835_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_58 sourceBody835_0

def sourceBody835_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_56 sourceBody835_59

def sourceBody835_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_0 sourceBody835_60

def sourceBody835_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_55 sourceBody835_61

def sourceBody835_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody835_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_62 sourceBody835_63

def sourceBody835_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody835_66 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody835_64 sourceBody835_65

def sourceBody835_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_66 sourceBody835_5

def sourceBody835_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_67 sourceBody835_0

def sourceBody835_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_43 sourceBody835_68

def sourceBody835_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_42 sourceBody835_69

def sourceBody835_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_38 sourceBody835_70

def sourceBody835_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_37 sourceBody835_71

def sourceBody835_73 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody835_72 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody835_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_73 sourceBody835_5

def sourceBody835_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_5 sourceBody835_74

def sourceBody835_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody835_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody835_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_77 sourceBody835_0

def sourceBody835_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_78 sourceBody835_0

def sourceBody835_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_76 sourceBody835_79

def sourceBody835_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_0 sourceBody835_80

def sourceBody835_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_75 sourceBody835_81

def sourceBody835_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_36 sourceBody835_82

def sourceBody835_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_0 sourceBody835_83

def sourceBody835_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_35 sourceBody835_84

def sourceBody835_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_0 sourceBody835_85

def sourceBody835_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_34 sourceBody835_86

def sourceBody835_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_22 sourceBody835_87

def sourceBody835_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_0 sourceBody835_88

def sourceBody835_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_89 sourceBody835_63

def sourceBody835_91 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody835_90 sourceBody835_65

def sourceBody835_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_91 sourceBody835_5

def sourceBody835_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_92 sourceBody835_0

def sourceBody835_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_21 sourceBody835_93

def sourceBody835_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_20 sourceBody835_94

def sourceBody835_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_16 sourceBody835_95

def sourceBody835_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_15 sourceBody835_96

def sourceBody835_98 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln) sourceBody835_97 (Flapjack.Spt.ls PUnit.unit)

def sourceBody835_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_98 sourceBody835_5

def sourceBody835_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_5 sourceBody835_99

def sourceBody835_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody835_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody835_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_102 sourceBody835_0

def sourceBody835_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_101 sourceBody835_103

def sourceBody835_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_100 sourceBody835_104

def sourceBody835_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_14 sourceBody835_105

def sourceBody835_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_0 sourceBody835_106

def sourceBody835_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_13 sourceBody835_107

def sourceBody835_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_0 sourceBody835_108

def sourceBody835_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_12 sourceBody835_109

def sourceBody835_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_0 sourceBody835_110

def sourceBody835_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody835_11 sourceBody835_111

def source835 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (835, 3, sourceBody835_112)
end InitECandidate.Proofs.WordStages
