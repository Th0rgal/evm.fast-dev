import InitECandidate.Proofs.WordStages.Source763
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody779_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody779_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 4)

def sourceBody779_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody779_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 2)) (some 775) ([36]) (some (36, sourceBody779_2, 779, 3))

def sourceBody779_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody779_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_3 sourceBody779_4

def sourceBody779_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_5 sourceBody779_0

def sourceBody779_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_1 sourceBody779_6

def sourceBody779_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody779_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody779_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody779_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody779_12 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 46) sourceBody779_10 sourceBody779_11

def sourceBody779_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_12 sourceBody779_4

def sourceBody779_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 24)

def sourceBody779_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody779_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 6)

def sourceBody779_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody779_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody779_0, 779, 4)) (some 776) ([24, 46]) (some (24, sourceBody779_17, 779, 5))

def sourceBody779_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_18 sourceBody779_4

def sourceBody779_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_19 sourceBody779_0

def sourceBody779_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_16 sourceBody779_20

def sourceBody779_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_15 sourceBody779_21

def sourceBody779_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_22

def sourceBody779_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_23

def sourceBody779_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody779_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [36]

def sourceBody779_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_26 sourceBody779_0

def sourceBody779_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_25 sourceBody779_27

def sourceBody779_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_24 sourceBody779_28

def sourceBody779_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody779_29 sourceBody779_0

def sourceBody779_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_30 sourceBody779_4

def sourceBody779_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_31 sourceBody779_0

def sourceBody779_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_14 sourceBody779_32

def sourceBody779_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_13 sourceBody779_33

def sourceBody779_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_9 sourceBody779_34

def sourceBody779_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_8 sourceBody779_35

def sourceBody779_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 6)

def sourceBody779_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 6)) (some 775) ([24]) (some (24, sourceBody779_17, 779, 7))

def sourceBody779_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_38 sourceBody779_4

def sourceBody779_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_39 sourceBody779_0

def sourceBody779_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_37 sourceBody779_40

def sourceBody779_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 36)

def sourceBody779_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody779_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody779_45 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 46 (Flapjack.WordRegImm.reg 10) sourceBody779_9 sourceBody779_44

def sourceBody779_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_45 sourceBody779_4

def sourceBody779_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 46)

def sourceBody779_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 2)

def sourceBody779_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody779_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody779_51 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody779_0, 779, 8)) (some 776) ([46, 10]) (some (46, sourceBody779_50, 779, 9))

def sourceBody779_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_51 sourceBody779_4

def sourceBody779_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_52 sourceBody779_0

def sourceBody779_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_49 sourceBody779_53

def sourceBody779_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_48 sourceBody779_54

def sourceBody779_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_55

def sourceBody779_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_56

def sourceBody779_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody779_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_58 sourceBody779_0

def sourceBody779_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_11 sourceBody779_59

def sourceBody779_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_57 sourceBody779_60

def sourceBody779_62 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody779_61 sourceBody779_0

def sourceBody779_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_62 sourceBody779_4

def sourceBody779_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_63 sourceBody779_0

def sourceBody779_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_47 sourceBody779_64

def sourceBody779_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_46 sourceBody779_65

def sourceBody779_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_43 sourceBody779_66

def sourceBody779_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_42 sourceBody779_67

def sourceBody779_69 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 10)) (some 69) ([]) (some (46, sourceBody779_50, 779, 11))

def sourceBody779_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_69 sourceBody779_4

def sourceBody779_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_70 sourceBody779_0

def sourceBody779_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1152#64)

def sourceBody779_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody779_74 : WordLangProgHOL (BitVec 64) :=
.call (some (([46]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 12)) (some 68) ([10]) (some (10, sourceBody779_73, 779, 13))

def sourceBody779_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_74 sourceBody779_4

def sourceBody779_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_75 sourceBody779_0

def sourceBody779_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_72 sourceBody779_76

def sourceBody779_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 46)

def sourceBody779_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 46, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody779_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 46, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody779_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 46, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody779_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 46, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody779_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 46, Flapjack.WordLangExpHOL.const 480#64])

def sourceBody779_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 46, Flapjack.WordLangExpHOL.const 576#64])

def sourceBody779_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 46, Flapjack.WordLangExpHOL.const 672#64])

def sourceBody779_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 46, Flapjack.WordLangExpHOL.const 768#64])

def sourceBody779_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 46, Flapjack.WordLangExpHOL.const 864#64])

def sourceBody779_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 46, Flapjack.WordLangExpHOL.const 960#64])

def sourceBody779_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 46, Flapjack.WordLangExpHOL.const 1056#64])

def sourceBody779_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 10)

def sourceBody779_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody779_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody779_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody779_94 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 14)) (some 735) ([38, 26, 48]) (some (38, sourceBody779_93, 779, 15))

def sourceBody779_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_94 sourceBody779_4

def sourceBody779_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_95 sourceBody779_0

def sourceBody779_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_92 sourceBody779_96

def sourceBody779_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_91 sourceBody779_97

def sourceBody779_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_90 sourceBody779_98

def sourceBody779_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_99

def sourceBody779_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_100

def sourceBody779_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 32)

def sourceBody779_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody779_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody779_105 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 16)) (some 735) ([38, 26, 48]) (some (38, sourceBody779_93, 779, 17))

def sourceBody779_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_105 sourceBody779_4

def sourceBody779_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_106 sourceBody779_0

def sourceBody779_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_104 sourceBody779_107

def sourceBody779_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_103 sourceBody779_108

def sourceBody779_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_102 sourceBody779_109

def sourceBody779_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_110

def sourceBody779_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_111

def sourceBody779_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_101 sourceBody779_112

def sourceBody779_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 22)

def sourceBody779_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody779_116 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 18)) (some 735) ([38, 26, 48]) (some (38, sourceBody779_93, 779, 19))

def sourceBody779_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_116 sourceBody779_4

def sourceBody779_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_117 sourceBody779_0

def sourceBody779_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_92 sourceBody779_118

def sourceBody779_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_115 sourceBody779_119

def sourceBody779_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_114 sourceBody779_120

def sourceBody779_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_121

def sourceBody779_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_122

def sourceBody779_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_113 sourceBody779_123

def sourceBody779_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 44)

def sourceBody779_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 4)

def sourceBody779_127 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 20)) (some 735) ([38, 26, 48]) (some (38, sourceBody779_93, 779, 21))

def sourceBody779_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_127 sourceBody779_4

def sourceBody779_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_128 sourceBody779_0

def sourceBody779_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_104 sourceBody779_129

def sourceBody779_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_126 sourceBody779_130

def sourceBody779_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_125 sourceBody779_131

def sourceBody779_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_132

def sourceBody779_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_133

def sourceBody779_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_124 sourceBody779_134

def sourceBody779_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 44)

def sourceBody779_137 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 22)) (some 729) ([38, 26]) (some (38, sourceBody779_93, 779, 23))

def sourceBody779_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_137 sourceBody779_4

def sourceBody779_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_138 sourceBody779_0

def sourceBody779_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_136 sourceBody779_139

def sourceBody779_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_114 sourceBody779_140

def sourceBody779_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 16)

def sourceBody779_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody779_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody779_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody779_146 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 26 (Flapjack.WordRegImm.reg 48) sourceBody779_144 sourceBody779_145

def sourceBody779_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_146 sourceBody779_4

def sourceBody779_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 26)

def sourceBody779_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody779_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 32)

def sourceBody779_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody779_152 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 24)) (some 729) ([26, 48]) (some (26, sourceBody779_151, 779, 25))

def sourceBody779_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_152 sourceBody779_4

def sourceBody779_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_153 sourceBody779_0

def sourceBody779_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_150 sourceBody779_154

def sourceBody779_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_149 sourceBody779_155

def sourceBody779_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 24)

def sourceBody779_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 48

def sourceBody779_159 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 26)) (some 70) ([48]) (some (48, sourceBody779_158, 779, 27))

def sourceBody779_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_159 sourceBody779_4

def sourceBody779_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_160 sourceBody779_0

def sourceBody779_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_157 sourceBody779_161

def sourceBody779_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_162

def sourceBody779_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_163

def sourceBody779_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 38)

def sourceBody779_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody779_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody779_168 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 48 (Flapjack.WordRegImm.reg 12) sourceBody779_143 sourceBody779_167

def sourceBody779_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_168 sourceBody779_4

def sourceBody779_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 48)

def sourceBody779_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 2)

def sourceBody779_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody779_173 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody779_0, 779, 28)) (some 778) ([48, 12]) (some (48, sourceBody779_158, 779, 29))

def sourceBody779_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_173 sourceBody779_4

def sourceBody779_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_174 sourceBody779_0

def sourceBody779_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_172 sourceBody779_175

def sourceBody779_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_171 sourceBody779_176

def sourceBody779_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_177

def sourceBody779_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_178

def sourceBody779_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody779_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_180 sourceBody779_0

def sourceBody779_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_145 sourceBody779_181

def sourceBody779_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_179 sourceBody779_182

def sourceBody779_184 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.imm 0#64) sourceBody779_183 sourceBody779_0

def sourceBody779_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_184 sourceBody779_4

def sourceBody779_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_185 sourceBody779_0

def sourceBody779_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_170 sourceBody779_186

def sourceBody779_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_169 sourceBody779_187

def sourceBody779_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_166 sourceBody779_188

def sourceBody779_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_165 sourceBody779_189

def sourceBody779_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_164 sourceBody779_190

def sourceBody779_192 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody779_0, 779, 30)) (some 774) ([48]) (some (48, sourceBody779_158, 779, 31))

def sourceBody779_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_192 sourceBody779_4

def sourceBody779_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_193 sourceBody779_0

def sourceBody779_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_171 sourceBody779_194

def sourceBody779_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_195

def sourceBody779_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_196

def sourceBody779_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_191 sourceBody779_197

def sourceBody779_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_198 sourceBody779_182

def sourceBody779_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_156 sourceBody779_199

def sourceBody779_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_200

def sourceBody779_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_201

def sourceBody779_203 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody779_202 sourceBody779_0

def sourceBody779_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_203 sourceBody779_4

def sourceBody779_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_204 sourceBody779_0

def sourceBody779_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_148 sourceBody779_205

def sourceBody779_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_147 sourceBody779_206

def sourceBody779_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_143 sourceBody779_207

def sourceBody779_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_142 sourceBody779_208

def sourceBody779_210 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 18)

def sourceBody779_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 10)

def sourceBody779_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 32)

def sourceBody779_213 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 32)) (some 731) ([26, 48, 12]) (some (26, sourceBody779_151, 779, 33))

def sourceBody779_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_213 sourceBody779_4

def sourceBody779_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_214 sourceBody779_0

def sourceBody779_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_212 sourceBody779_215

def sourceBody779_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_211 sourceBody779_216

def sourceBody779_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_210 sourceBody779_217

def sourceBody779_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_218

def sourceBody779_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_219

def sourceBody779_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_209 sourceBody779_220

def sourceBody779_222 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 40)

def sourceBody779_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 22)

def sourceBody779_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 44)

def sourceBody779_225 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 34)) (some 731) ([26, 48, 12]) (some (26, sourceBody779_151, 779, 35))

def sourceBody779_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_225 sourceBody779_4

def sourceBody779_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_226 sourceBody779_0

def sourceBody779_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_224 sourceBody779_227

def sourceBody779_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_223 sourceBody779_228

def sourceBody779_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_222 sourceBody779_229

def sourceBody779_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_230

def sourceBody779_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_231

def sourceBody779_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_221 sourceBody779_232

def sourceBody779_234 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody779_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 40)

def sourceBody779_236 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 36)) (some 736) ([26, 48]) (some (26, sourceBody779_151, 779, 37))

def sourceBody779_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_236 sourceBody779_4

def sourceBody779_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_237 sourceBody779_0

def sourceBody779_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_235 sourceBody779_238

def sourceBody779_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_234 sourceBody779_239

def sourceBody779_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_240

def sourceBody779_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_241

def sourceBody779_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_233 sourceBody779_242

def sourceBody779_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 50)

def sourceBody779_245 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 28)

def sourceBody779_246 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 38)) (some 735) ([26, 48, 12]) (some (26, sourceBody779_151, 779, 39))

def sourceBody779_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_246 sourceBody779_4

def sourceBody779_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_247 sourceBody779_0

def sourceBody779_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_224 sourceBody779_248

def sourceBody779_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_245 sourceBody779_249

def sourceBody779_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_244 sourceBody779_250

def sourceBody779_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_251

def sourceBody779_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_252

def sourceBody779_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_243 sourceBody779_253

def sourceBody779_255 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 8)

def sourceBody779_256 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 28)

def sourceBody779_257 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 40)) (some 735) ([26, 48, 12]) (some (26, sourceBody779_151, 779, 41))

def sourceBody779_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_257 sourceBody779_4

def sourceBody779_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_258 sourceBody779_0

def sourceBody779_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_256 sourceBody779_259

def sourceBody779_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_235 sourceBody779_260

def sourceBody779_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_255 sourceBody779_261

def sourceBody779_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_262

def sourceBody779_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_263

def sourceBody779_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_254 sourceBody779_264

def sourceBody779_266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody779_267 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody779_268 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 42)) (some 735) ([26, 48, 12]) (some (26, sourceBody779_151, 779, 43))

def sourceBody779_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_268 sourceBody779_4

def sourceBody779_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_269 sourceBody779_0

def sourceBody779_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_267 sourceBody779_270

def sourceBody779_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_92 sourceBody779_271

def sourceBody779_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_266 sourceBody779_272

def sourceBody779_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_273

def sourceBody779_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_274

def sourceBody779_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_265 sourceBody779_275

def sourceBody779_277 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 20)

def sourceBody779_278 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 18)

def sourceBody779_279 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 44)) (some 736) ([26, 48]) (some (26, sourceBody779_151, 779, 45))

def sourceBody779_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_279 sourceBody779_4

def sourceBody779_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_280 sourceBody779_0

def sourceBody779_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_278 sourceBody779_281

def sourceBody779_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_277 sourceBody779_282

def sourceBody779_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_283

def sourceBody779_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_284

def sourceBody779_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_276 sourceBody779_285

def sourceBody779_287 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 20)

def sourceBody779_288 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 30)

def sourceBody779_289 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 46)) (some 735) ([26, 48, 12]) (some (26, sourceBody779_151, 779, 47))

def sourceBody779_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_289 sourceBody779_4

def sourceBody779_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_290 sourceBody779_0

def sourceBody779_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_288 sourceBody779_291

def sourceBody779_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_287 sourceBody779_292

def sourceBody779_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_277 sourceBody779_293

def sourceBody779_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_294

def sourceBody779_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_295

def sourceBody779_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_286 sourceBody779_296

def sourceBody779_298 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody779_299 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 48)) (some 731) ([26, 48, 12]) (some (26, sourceBody779_151, 779, 49))

def sourceBody779_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_299 sourceBody779_4

def sourceBody779_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_300 sourceBody779_0

def sourceBody779_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_298 sourceBody779_301

def sourceBody779_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_287 sourceBody779_302

def sourceBody779_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_277 sourceBody779_303

def sourceBody779_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_304

def sourceBody779_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_305

def sourceBody779_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_297 sourceBody779_306

def sourceBody779_308 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 42)

def sourceBody779_309 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 50)

def sourceBody779_310 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 50)

def sourceBody779_311 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 50)) (some 730) ([26, 48, 12]) (some (26, sourceBody779_151, 779, 51))

def sourceBody779_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_311 sourceBody779_4

def sourceBody779_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_312 sourceBody779_0

def sourceBody779_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_310 sourceBody779_313

def sourceBody779_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_309 sourceBody779_314

def sourceBody779_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_308 sourceBody779_315

def sourceBody779_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_316

def sourceBody779_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_317

def sourceBody779_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_307 sourceBody779_318

def sourceBody779_320 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 42)

def sourceBody779_321 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 52)) (some 731) ([26, 48, 12]) (some (26, sourceBody779_151, 779, 53))

def sourceBody779_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_321 sourceBody779_4

def sourceBody779_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_322 sourceBody779_0

def sourceBody779_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_320 sourceBody779_323

def sourceBody779_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_287 sourceBody779_324

def sourceBody779_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_277 sourceBody779_325

def sourceBody779_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_326

def sourceBody779_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_327

def sourceBody779_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_319 sourceBody779_328

def sourceBody779_330 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 20)

def sourceBody779_331 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 54)) (some 735) ([26, 48, 12]) (some (26, sourceBody779_151, 779, 55))

def sourceBody779_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_331 sourceBody779_4

def sourceBody779_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_332 sourceBody779_0

def sourceBody779_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_330 sourceBody779_333

def sourceBody779_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_235 sourceBody779_334

def sourceBody779_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_308 sourceBody779_335

def sourceBody779_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_336

def sourceBody779_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_337

def sourceBody779_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_329 sourceBody779_338

def sourceBody779_340 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 56)) (some 731) ([26, 48, 12]) (some (26, sourceBody779_151, 779, 57))

def sourceBody779_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_340 sourceBody779_4

def sourceBody779_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_341 sourceBody779_0

def sourceBody779_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_330 sourceBody779_342

def sourceBody779_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_309 sourceBody779_343

def sourceBody779_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_149 sourceBody779_344

def sourceBody779_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_345

def sourceBody779_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_346

def sourceBody779_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_339 sourceBody779_347

def sourceBody779_349 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody779_350 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 58)) (some 735) ([26, 48, 12]) (some (26, sourceBody779_151, 779, 59))

def sourceBody779_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_350 sourceBody779_4

def sourceBody779_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_351 sourceBody779_0

def sourceBody779_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_349 sourceBody779_352

def sourceBody779_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_278 sourceBody779_353

def sourceBody779_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_149 sourceBody779_354

def sourceBody779_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_355

def sourceBody779_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_356

def sourceBody779_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_348 sourceBody779_357

def sourceBody779_359 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 32)

def sourceBody779_360 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 8)

def sourceBody779_361 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 60)) (some 735) ([26, 48, 12]) (some (26, sourceBody779_151, 779, 61))

def sourceBody779_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_361 sourceBody779_4

def sourceBody779_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_362 sourceBody779_0

def sourceBody779_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_212 sourceBody779_363

def sourceBody779_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_360 sourceBody779_364

def sourceBody779_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_359 sourceBody779_365

def sourceBody779_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_366

def sourceBody779_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_367

def sourceBody779_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_358 sourceBody779_368

def sourceBody779_370 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 62)) (some 731) ([26, 48, 12]) (some (26, sourceBody779_151, 779, 63))

def sourceBody779_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_370 sourceBody779_4

def sourceBody779_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_371 sourceBody779_0

def sourceBody779_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_212 sourceBody779_372

def sourceBody779_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_211 sourceBody779_373

def sourceBody779_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_149 sourceBody779_374

def sourceBody779_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_375

def sourceBody779_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_376

def sourceBody779_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_369 sourceBody779_377

def sourceBody779_379 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 64)) (some 735) ([26, 48, 12]) (some (26, sourceBody779_151, 779, 65))

def sourceBody779_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_379 sourceBody779_4

def sourceBody779_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_380 sourceBody779_0

def sourceBody779_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_288 sourceBody779_381

def sourceBody779_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_360 sourceBody779_382

def sourceBody779_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_266 sourceBody779_383

def sourceBody779_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_384

def sourceBody779_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_385

def sourceBody779_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_378 sourceBody779_386

def sourceBody779_388 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 2)

def sourceBody779_389 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 42)

def sourceBody779_390 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 66)) (some 725) ([26, 48]) (some (26, sourceBody779_151, 779, 67))

def sourceBody779_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_390 sourceBody779_4

def sourceBody779_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_391 sourceBody779_0

def sourceBody779_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_389 sourceBody779_392

def sourceBody779_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_388 sourceBody779_393

def sourceBody779_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_394

def sourceBody779_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_395

def sourceBody779_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_387 sourceBody779_396

def sourceBody779_398 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody779_399 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 68)) (some 725) ([26, 48]) (some (26, sourceBody779_151, 779, 69))

def sourceBody779_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_399 sourceBody779_4

def sourceBody779_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_400 sourceBody779_0

def sourceBody779_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_211 sourceBody779_401

def sourceBody779_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_398 sourceBody779_402

def sourceBody779_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_403

def sourceBody779_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_404

def sourceBody779_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_397 sourceBody779_405

def sourceBody779_407 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody779_408 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 30)

def sourceBody779_409 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody779_0, 779, 70)) (some 725) ([26, 48]) (some (26, sourceBody779_151, 779, 71))

def sourceBody779_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_409 sourceBody779_4

def sourceBody779_411 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_410 sourceBody779_0

def sourceBody779_412 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_408 sourceBody779_411

def sourceBody779_413 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_407 sourceBody779_412

def sourceBody779_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_413

def sourceBody779_415 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_414

def sourceBody779_416 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_406 sourceBody779_415

def sourceBody779_417 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 24)

def sourceBody779_418 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody779_0, 779, 72)) (some 70) ([26]) (some (26, sourceBody779_151, 779, 73))

def sourceBody779_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_418 sourceBody779_4

def sourceBody779_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_419 sourceBody779_0

def sourceBody779_421 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_417 sourceBody779_420

def sourceBody779_422 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_421

def sourceBody779_423 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_422

def sourceBody779_424 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_416 sourceBody779_423

def sourceBody779_425 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody779_426 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [38]

def sourceBody779_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_426 sourceBody779_0

def sourceBody779_428 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_425 sourceBody779_427

def sourceBody779_429 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_424 sourceBody779_428

def sourceBody779_430 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_141 sourceBody779_429

def sourceBody779_431 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_430

def sourceBody779_432 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_431

def sourceBody779_433 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_135 sourceBody779_432

def sourceBody779_434 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_89 sourceBody779_433

def sourceBody779_435 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_434

def sourceBody779_436 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_88 sourceBody779_435

def sourceBody779_437 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_436

def sourceBody779_438 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_87 sourceBody779_437

def sourceBody779_439 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_438

def sourceBody779_440 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_86 sourceBody779_439

def sourceBody779_441 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_440

def sourceBody779_442 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_85 sourceBody779_441

def sourceBody779_443 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_442

def sourceBody779_444 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_84 sourceBody779_443

def sourceBody779_445 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_444

def sourceBody779_446 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_83 sourceBody779_445

def sourceBody779_447 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_446

def sourceBody779_448 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_82 sourceBody779_447

def sourceBody779_449 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_448

def sourceBody779_450 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_81 sourceBody779_449

def sourceBody779_451 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_450

def sourceBody779_452 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_80 sourceBody779_451

def sourceBody779_453 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_452

def sourceBody779_454 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_79 sourceBody779_453

def sourceBody779_455 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_454

def sourceBody779_456 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_78 sourceBody779_455

def sourceBody779_457 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_456

def sourceBody779_458 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_77 sourceBody779_457

def sourceBody779_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_458

def sourceBody779_460 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_459

def sourceBody779_461 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_71 sourceBody779_460

def sourceBody779_462 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_461

def sourceBody779_463 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_462

def sourceBody779_464 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_68 sourceBody779_463

def sourceBody779_465 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_41 sourceBody779_464

def sourceBody779_466 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_465

def sourceBody779_467 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_466

def sourceBody779_468 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_36 sourceBody779_467

def sourceBody779_469 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_7 sourceBody779_468

def sourceBody779_470 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_469

def sourceBody779_471 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody779_0 sourceBody779_470

def source779 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (779, 4, sourceBody779_471)
end InitECandidate.Proofs.WordStages
