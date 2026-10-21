import InitECandidate.Proofs.WordStages.Source797
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody813_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody813_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody813_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([50]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody813_0, 813, 2)) (some 69) ([]) (some (14, sourceBody813_1, 813, 3))

def sourceBody813_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody813_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_2 sourceBody813_3

def sourceBody813_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_4 sourceBody813_0

def sourceBody813_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody813_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody813_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody813_0, 813, 4)) (some 68) ([42]) (some (42, sourceBody813_7, 813, 5))

def sourceBody813_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_8 sourceBody813_3

def sourceBody813_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_9 sourceBody813_0

def sourceBody813_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_6 sourceBody813_10

def sourceBody813_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 144#64)

def sourceBody813_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody813_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody813_0, 813, 6)) (some 68) ([28]) (some (28, sourceBody813_13, 813, 7))

def sourceBody813_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_14 sourceBody813_3

def sourceBody813_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_15 sourceBody813_0

def sourceBody813_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_12 sourceBody813_16

def sourceBody813_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 144#64)

def sourceBody813_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 58

def sourceBody813_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody813_0, 813, 8)) (some 68) ([58]) (some (58, sourceBody813_19, 813, 9))

def sourceBody813_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_20 sourceBody813_3

def sourceBody813_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_21 sourceBody813_0

def sourceBody813_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_18 sourceBody813_22

def sourceBody813_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody813_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 48#64)

def sourceBody813_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody813_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody813_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([58]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody813_0, 813, 10)) (some 153) ([10, 38, 24]) (some (10, sourceBody813_27, 813, 11))

def sourceBody813_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_28 sourceBody813_3

def sourceBody813_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_29 sourceBody813_0

def sourceBody813_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_26 sourceBody813_30

def sourceBody813_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_25 sourceBody813_31

def sourceBody813_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_24 sourceBody813_32

def sourceBody813_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_33

def sourceBody813_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_34

def sourceBody813_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 14)

def sourceBody813_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody813_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 10 (Flapjack.WordLangAddr.addr 58 0#64))

def sourceBody813_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_38 sourceBody813_0

def sourceBody813_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_37 sourceBody813_39

def sourceBody813_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_36 sourceBody813_40

def sourceBody813_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_35 sourceBody813_41

def sourceBody813_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody813_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 2)

def sourceBody813_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody813_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([58]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody813_0, 813, 12)) (some 79) ([10, 38, 24]) (some (10, sourceBody813_27, 813, 13))

def sourceBody813_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_46 sourceBody813_3

def sourceBody813_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_47 sourceBody813_0

def sourceBody813_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_45 sourceBody813_48

def sourceBody813_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_44 sourceBody813_49

def sourceBody813_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_43 sourceBody813_50

def sourceBody813_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 58)

def sourceBody813_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody813_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody813_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody813_56 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 38 (Flapjack.WordRegImm.reg 24) sourceBody813_54 sourceBody813_55

def sourceBody813_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_56 sourceBody813_3

def sourceBody813_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 38)

def sourceBody813_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 50)

def sourceBody813_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody813_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody813_0, 813, 14)) (some 70) ([38]) (some (38, sourceBody813_60, 813, 15))

def sourceBody813_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_61 sourceBody813_3

def sourceBody813_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_62 sourceBody813_0

def sourceBody813_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_59 sourceBody813_63

def sourceBody813_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_64

def sourceBody813_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_65

def sourceBody813_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody813_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_67 sourceBody813_0

def sourceBody813_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_37 sourceBody813_68

def sourceBody813_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_66 sourceBody813_69

def sourceBody813_71 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 54 (Flapjack.WordRegImm.imm 0#64) sourceBody813_70 sourceBody813_0

def sourceBody813_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_71 sourceBody813_3

def sourceBody813_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_72 sourceBody813_0

def sourceBody813_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_58 sourceBody813_73

def sourceBody813_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_57 sourceBody813_74

def sourceBody813_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_53 sourceBody813_75

def sourceBody813_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_52 sourceBody813_76

def sourceBody813_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody813_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 42)

def sourceBody813_80 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody813_0, 813, 16)) (some 802) ([38, 24]) (some (38, sourceBody813_60, 813, 17))

def sourceBody813_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_80 sourceBody813_3

def sourceBody813_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_81 sourceBody813_0

def sourceBody813_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_79 sourceBody813_82

def sourceBody813_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_78 sourceBody813_83

def sourceBody813_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody813_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody813_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody813_88 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 54) sourceBody813_87 sourceBody813_53

def sourceBody813_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_88 sourceBody813_3

def sourceBody813_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody813_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 50)

def sourceBody813_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody813_93 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody813_0, 813, 18)) (some 70) ([24]) (some (24, sourceBody813_92, 813, 19))

def sourceBody813_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_93 sourceBody813_3

def sourceBody813_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_94 sourceBody813_0

def sourceBody813_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_91 sourceBody813_95

def sourceBody813_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_96

def sourceBody813_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_97

def sourceBody813_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [38]

def sourceBody813_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_99 sourceBody813_0

def sourceBody813_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_54 sourceBody813_100

def sourceBody813_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_98 sourceBody813_101

def sourceBody813_103 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody813_102 sourceBody813_0

def sourceBody813_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_103 sourceBody813_3

def sourceBody813_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_104 sourceBody813_0

def sourceBody813_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_90 sourceBody813_105

def sourceBody813_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_89 sourceBody813_106

def sourceBody813_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_86 sourceBody813_107

def sourceBody813_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_85 sourceBody813_108

def sourceBody813_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 144#64])

def sourceBody813_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 28)

def sourceBody813_112 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody813_0, 813, 20)) (some 802) ([38, 24]) (some (38, sourceBody813_60, 813, 21))

def sourceBody813_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_112 sourceBody813_3

def sourceBody813_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_113 sourceBody813_0

def sourceBody813_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_111 sourceBody813_114

def sourceBody813_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_110 sourceBody813_115

def sourceBody813_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_109 sourceBody813_116

def sourceBody813_118 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody813_0, 813, 22)) (some 70) ([24]) (some (24, sourceBody813_92, 813, 23))

def sourceBody813_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_118 sourceBody813_3

def sourceBody813_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_119 sourceBody813_0

def sourceBody813_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_91 sourceBody813_120

def sourceBody813_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_121

def sourceBody813_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_122

def sourceBody813_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_123 sourceBody813_101

def sourceBody813_125 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody813_124 sourceBody813_0

def sourceBody813_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_125 sourceBody813_3

def sourceBody813_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_126 sourceBody813_0

def sourceBody813_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_90 sourceBody813_127

def sourceBody813_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_89 sourceBody813_128

def sourceBody813_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_86 sourceBody813_129

def sourceBody813_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_85 sourceBody813_130

def sourceBody813_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_117 sourceBody813_131

def sourceBody813_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody813_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody813_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody813_136 : WordLangProgHOL (BitVec 64) :=
.call (some (([38, 24, 54, 18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody813_0, 813, 24)) (some 146) ([46, 32]) (some (46, sourceBody813_135, 813, 25))

def sourceBody813_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_136 sourceBody813_3

def sourceBody813_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_137 sourceBody813_0

def sourceBody813_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_134 sourceBody813_138

def sourceBody813_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_133 sourceBody813_139

def sourceBody813_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody813_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody813_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody813_144 : WordLangProgHOL (BitVec 64) :=
.call (some (([46, 32, 62, 8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody813_0, 813, 26)) (some 146) ([36, 22]) (some (36, sourceBody813_143, 813, 27))

def sourceBody813_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_144 sourceBody813_3

def sourceBody813_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_145 sourceBody813_0

def sourceBody813_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_142 sourceBody813_146

def sourceBody813_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_141 sourceBody813_147

def sourceBody813_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 392#64]),
        Flapjack.WordLangExpHOL.const 1344#64]))

def sourceBody813_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 392#64]),
            Flapjack.WordLangExpHOL.const 1344#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody813_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 392#64]),
            Flapjack.WordLangExpHOL.const 1344#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody813_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 392#64]),
            Flapjack.WordLangExpHOL.const 1344#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody813_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 38)

def sourceBody813_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 24)

def sourceBody813_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 54)

def sourceBody813_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 18)

def sourceBody813_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 36)

def sourceBody813_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 22)

def sourceBody813_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 52)

def sourceBody813_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 16)

def sourceBody813_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody813_162 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody813_0, 813, 28)) (some 106) ([30, 60, 12, 40, 26, 56, 20, 48]) (some (30, sourceBody813_161, 813, 29))

def sourceBody813_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_162 sourceBody813_3

def sourceBody813_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_163 sourceBody813_0

def sourceBody813_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_160 sourceBody813_164

def sourceBody813_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_159 sourceBody813_165

def sourceBody813_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_158 sourceBody813_166

def sourceBody813_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_157 sourceBody813_167

def sourceBody813_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_156 sourceBody813_168

def sourceBody813_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_155 sourceBody813_169

def sourceBody813_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_154 sourceBody813_170

def sourceBody813_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_153 sourceBody813_171

def sourceBody813_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 46)

def sourceBody813_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 32)

def sourceBody813_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 62)

def sourceBody813_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 8)

def sourceBody813_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 36)

def sourceBody813_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 22)

def sourceBody813_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 52)

def sourceBody813_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody813_181 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 60

def sourceBody813_182 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody813_0, 813, 30)) (some 106) ([60, 12, 40, 26, 56, 20, 48, 34]) (some (60, sourceBody813_181, 813, 31))

def sourceBody813_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_182 sourceBody813_3

def sourceBody813_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_183 sourceBody813_0

def sourceBody813_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_180 sourceBody813_184

def sourceBody813_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_179 sourceBody813_185

def sourceBody813_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_178 sourceBody813_186

def sourceBody813_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_177 sourceBody813_187

def sourceBody813_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_176 sourceBody813_188

def sourceBody813_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_175 sourceBody813_189

def sourceBody813_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_174 sourceBody813_190

def sourceBody813_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_173 sourceBody813_191

def sourceBody813_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 44)

def sourceBody813_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody813_195 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody813_196 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody813_197 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.WordRegImm.reg 40) sourceBody813_195 sourceBody813_196

def sourceBody813_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_197 sourceBody813_3

def sourceBody813_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 30)

def sourceBody813_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody813_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody813_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody813_203 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 56 (Flapjack.WordRegImm.reg 20) sourceBody813_201 sourceBody813_202

def sourceBody813_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_203 sourceBody813_3

def sourceBody813_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody813_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.var 56])

def sourceBody813_207 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody813_208 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.reg 64) sourceBody813_207 sourceBody813_205

def sourceBody813_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_208 sourceBody813_3

def sourceBody813_210 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 34)

def sourceBody813_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 50)

def sourceBody813_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody813_213 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody813_0, 813, 32)) (some 70) ([12]) (some (12, sourceBody813_212, 813, 33))

def sourceBody813_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_213 sourceBody813_3

def sourceBody813_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_214 sourceBody813_0

def sourceBody813_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_211 sourceBody813_215

def sourceBody813_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_216

def sourceBody813_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_217

def sourceBody813_219 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody813_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [60]

def sourceBody813_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_220 sourceBody813_0

def sourceBody813_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_219 sourceBody813_221

def sourceBody813_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_218 sourceBody813_222

def sourceBody813_224 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody813_223 sourceBody813_0

def sourceBody813_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_224 sourceBody813_3

def sourceBody813_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_225 sourceBody813_0

def sourceBody813_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_210 sourceBody813_226

def sourceBody813_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_209 sourceBody813_227

def sourceBody813_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_206 sourceBody813_228

def sourceBody813_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_205 sourceBody813_229

def sourceBody813_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_204 sourceBody813_230

def sourceBody813_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_200 sourceBody813_231

def sourceBody813_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_199 sourceBody813_232

def sourceBody813_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_198 sourceBody813_233

def sourceBody813_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_194 sourceBody813_234

def sourceBody813_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_193 sourceBody813_235

def sourceBody813_237 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 42)

def sourceBody813_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody813_239 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody813_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 28)

def sourceBody813_241 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody813_0, 813, 34)) (some 804) ([12, 40, 26, 56]) (some (12, sourceBody813_212, 813, 35))

def sourceBody813_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_241 sourceBody813_3

def sourceBody813_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_242 sourceBody813_0

def sourceBody813_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_240 sourceBody813_243

def sourceBody813_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_239 sourceBody813_244

def sourceBody813_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_238 sourceBody813_245

def sourceBody813_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_237 sourceBody813_246

def sourceBody813_248 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 50)

def sourceBody813_249 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody813_250 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody813_0, 813, 36)) (some 70) ([40]) (some (40, sourceBody813_249, 813, 37))

def sourceBody813_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_250 sourceBody813_3

def sourceBody813_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_251 sourceBody813_0

def sourceBody813_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_248 sourceBody813_252

def sourceBody813_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_253

def sourceBody813_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_254

def sourceBody813_256 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 60)

def sourceBody813_257 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody813_258 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody813_259 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 40 (Flapjack.WordRegImm.reg 26) sourceBody813_258 sourceBody813_194

def sourceBody813_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_259 sourceBody813_3

def sourceBody813_261 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 40)

def sourceBody813_262 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody813_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_262 sourceBody813_0

def sourceBody813_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_195 sourceBody813_263

def sourceBody813_265 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 56 (Flapjack.WordRegImm.imm 0#64) sourceBody813_264 sourceBody813_0

def sourceBody813_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_265 sourceBody813_3

def sourceBody813_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_266 sourceBody813_0

def sourceBody813_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_261 sourceBody813_267

def sourceBody813_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_260 sourceBody813_268

def sourceBody813_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_257 sourceBody813_269

def sourceBody813_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_256 sourceBody813_270

def sourceBody813_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_255 sourceBody813_271

def sourceBody813_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 4)

def sourceBody813_274 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody813_275 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody813_0, 813, 38)) (some 78) ([40, 26]) (some (40, sourceBody813_249, 813, 39))

def sourceBody813_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_275 sourceBody813_3

def sourceBody813_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_276 sourceBody813_0

def sourceBody813_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_274 sourceBody813_277

def sourceBody813_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_273 sourceBody813_278

def sourceBody813_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_279

def sourceBody813_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_280

def sourceBody813_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_272 sourceBody813_281

def sourceBody813_283 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 30#64])

def sourceBody813_284 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody813_285 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 40 (Flapjack.WordLangAddr.addr 12 0#64))

def sourceBody813_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_285 sourceBody813_0

def sourceBody813_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_284 sourceBody813_286

def sourceBody813_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_283 sourceBody813_287

def sourceBody813_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_282 sourceBody813_288

def sourceBody813_290 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 36)

def sourceBody813_291 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 22)

def sourceBody813_292 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 52)

def sourceBody813_293 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody813_294 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody813_295 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody813_0, 813, 40)) (some 147) ([40, 26, 56, 20, 48]) (some (40, sourceBody813_249, 813, 41))

def sourceBody813_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_295 sourceBody813_3

def sourceBody813_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_296 sourceBody813_0

def sourceBody813_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_294 sourceBody813_297

def sourceBody813_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_293 sourceBody813_298

def sourceBody813_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_292 sourceBody813_299

def sourceBody813_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_291 sourceBody813_300

def sourceBody813_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_290 sourceBody813_301

def sourceBody813_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_302

def sourceBody813_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_303

def sourceBody813_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_289 sourceBody813_304

def sourceBody813_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_196 sourceBody813_263

def sourceBody813_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_305 sourceBody813_306

def sourceBody813_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_247 sourceBody813_307

def sourceBody813_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_308

def sourceBody813_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_309

def sourceBody813_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_236 sourceBody813_310

def sourceBody813_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_192 sourceBody813_311

def sourceBody813_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_312

def sourceBody813_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_313

def sourceBody813_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_172 sourceBody813_314

def sourceBody813_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_315

def sourceBody813_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_316

def sourceBody813_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_152 sourceBody813_317

def sourceBody813_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_318

def sourceBody813_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_151 sourceBody813_319

def sourceBody813_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_320

def sourceBody813_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_150 sourceBody813_321

def sourceBody813_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_322

def sourceBody813_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_149 sourceBody813_323

def sourceBody813_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_324

def sourceBody813_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_148 sourceBody813_325

def sourceBody813_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_326

def sourceBody813_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_327

def sourceBody813_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_328

def sourceBody813_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_329

def sourceBody813_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_330

def sourceBody813_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_331

def sourceBody813_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_332

def sourceBody813_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_333

def sourceBody813_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_140 sourceBody813_334

def sourceBody813_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_335

def sourceBody813_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_336

def sourceBody813_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_337

def sourceBody813_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_338

def sourceBody813_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_339

def sourceBody813_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_340

def sourceBody813_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_341

def sourceBody813_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_342

def sourceBody813_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_132 sourceBody813_343

def sourceBody813_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_84 sourceBody813_344

def sourceBody813_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_345

def sourceBody813_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_346

def sourceBody813_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_77 sourceBody813_347

def sourceBody813_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_51 sourceBody813_348

def sourceBody813_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_349

def sourceBody813_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_350

def sourceBody813_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_42 sourceBody813_351

def sourceBody813_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_23 sourceBody813_352

def sourceBody813_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_353

def sourceBody813_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_354

def sourceBody813_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_17 sourceBody813_355

def sourceBody813_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_356

def sourceBody813_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_357

def sourceBody813_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_11 sourceBody813_358

def sourceBody813_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_359

def sourceBody813_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_360

def sourceBody813_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_5 sourceBody813_361

def sourceBody813_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_362

def sourceBody813_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody813_0 sourceBody813_363

def source813 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (813, 3, sourceBody813_364)
end InitECandidate.Proofs.WordStages
