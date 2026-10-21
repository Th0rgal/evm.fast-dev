import InitECandidate.Proofs.WordStages.Source263
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody279_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody279_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 4)
    (Flapjack.WordLangExpHOL.const 1#64))

def sourceBody279_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 2)

def sourceBody279_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 4)

def sourceBody279_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody279_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody279_0, 279, 2)) (some 278) ([40, 80]) (some (40, sourceBody279_4, 279, 3))

def sourceBody279_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody279_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_5 sourceBody279_6

def sourceBody279_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_7 sourceBody279_0

def sourceBody279_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_3 sourceBody279_8

def sourceBody279_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_2 sourceBody279_9

def sourceBody279_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 60)

def sourceBody279_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody279_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody279_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody279_15 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 80 (Flapjack.WordRegImm.reg 30) sourceBody279_13 sourceBody279_14

def sourceBody279_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_15 sourceBody279_6

def sourceBody279_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 80)

def sourceBody279_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody279_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 40)

def sourceBody279_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_19 sourceBody279_0

def sourceBody279_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_20 sourceBody279_0

def sourceBody279_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_18 sourceBody279_21

def sourceBody279_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_22

def sourceBody279_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody279_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_24 sourceBody279_4

def sourceBody279_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_23 sourceBody279_25

def sourceBody279_27 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 70 (Flapjack.WordRegImm.imm 0#64) sourceBody279_26 sourceBody279_0

def sourceBody279_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_27 sourceBody279_6

def sourceBody279_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_28 sourceBody279_0

def sourceBody279_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_17 sourceBody279_29

def sourceBody279_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_16 sourceBody279_30

def sourceBody279_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_12 sourceBody279_31

def sourceBody279_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_11 sourceBody279_32

def sourceBody279_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 6)

def sourceBody279_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 20)

def sourceBody279_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 8)

def sourceBody279_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 10)

def sourceBody279_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 12)

def sourceBody279_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 14)

def sourceBody279_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [40, 80, 30, 70]

def sourceBody279_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_40 sourceBody279_0

def sourceBody279_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_39 sourceBody279_41

def sourceBody279_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_38 sourceBody279_42

def sourceBody279_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_37 sourceBody279_43

def sourceBody279_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_36 sourceBody279_44

def sourceBody279_46 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 70 (Flapjack.WordRegImm.imm 0#64) sourceBody279_45 sourceBody279_0

def sourceBody279_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_46 sourceBody279_6

def sourceBody279_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_47 sourceBody279_0

def sourceBody279_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_17 sourceBody279_48

def sourceBody279_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_16 sourceBody279_49

def sourceBody279_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_35 sourceBody279_50

def sourceBody279_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_34 sourceBody279_51

def sourceBody279_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_33 sourceBody279_52

def sourceBody279_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 20)

def sourceBody279_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 50

def sourceBody279_56 : WordLangProgHOL (BitVec 64) :=
.call (some (([40, 80, 30, 70]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody279_0, 279, 4)) (some 99) ([50]) (some (50, sourceBody279_55, 279, 5))

def sourceBody279_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_56 sourceBody279_6

def sourceBody279_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_57 sourceBody279_0

def sourceBody279_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_54 sourceBody279_58

def sourceBody279_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody279_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody279_62 : WordLangProgHOL (BitVec 64) :=
.call (some (([50, 90, 18, 58]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody279_0, 279, 6)) (some 99) ([38]) (some (38, sourceBody279_61, 279, 7))

def sourceBody279_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_62 sourceBody279_6

def sourceBody279_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_63 sourceBody279_0

def sourceBody279_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_60 sourceBody279_64

def sourceBody279_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 20)

def sourceBody279_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 6)

def sourceBody279_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody279_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody279_70 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 78 (Flapjack.WordRegImm.reg 28) sourceBody279_68 sourceBody279_69

def sourceBody279_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_70 sourceBody279_6

def sourceBody279_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 78)

def sourceBody279_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 20])

def sourceBody279_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 48

def sourceBody279_75 : WordLangProgHOL (BitVec 64) :=
.call (some (([38, 78, 28, 68]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody279_0, 279, 8)) (some 99) ([48]) (some (48, sourceBody279_74, 279, 9))

def sourceBody279_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_75 sourceBody279_6

def sourceBody279_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_76 sourceBody279_0

def sourceBody279_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_73 sourceBody279_77

def sourceBody279_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 8)

def sourceBody279_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 84 (Flapjack.WordLangExpHOL.var 10)

def sourceBody279_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 12)

def sourceBody279_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 14)

def sourceBody279_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 38)

def sourceBody279_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 92 (Flapjack.WordLangExpHOL.var 78)

def sourceBody279_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 28)

def sourceBody279_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 68)

def sourceBody279_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody279_88 : WordLangProgHOL (BitVec 64) :=
.call (some (([48, 88, 24, 64]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody279_0, 279, 10)) (some 120) ([44, 84, 34, 74, 54, 92, 16, 56]) (some (44, sourceBody279_87, 279, 11))

def sourceBody279_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_88 sourceBody279_6

def sourceBody279_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_89 sourceBody279_0

def sourceBody279_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_86 sourceBody279_90

def sourceBody279_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_85 sourceBody279_91

def sourceBody279_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_84 sourceBody279_92

def sourceBody279_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_83 sourceBody279_93

def sourceBody279_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_82 sourceBody279_94

def sourceBody279_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_81 sourceBody279_95

def sourceBody279_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_80 sourceBody279_96

def sourceBody279_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_79 sourceBody279_97

def sourceBody279_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 48)

def sourceBody279_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 92 (Flapjack.WordLangExpHOL.var 88)

def sourceBody279_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody279_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 64)

def sourceBody279_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 40)

def sourceBody279_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 80)

def sourceBody279_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody279_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 70)

def sourceBody279_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 54

def sourceBody279_108 : WordLangProgHOL (BitVec 64) :=
.call (some (([44, 84, 34, 74]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody279_0, 279, 12)) (some 130) ([54, 92, 16, 56, 36, 76, 26, 66]) (some (54, sourceBody279_107, 279, 13))

def sourceBody279_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_108 sourceBody279_6

def sourceBody279_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_109 sourceBody279_0

def sourceBody279_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_106 sourceBody279_110

def sourceBody279_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_105 sourceBody279_111

def sourceBody279_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_104 sourceBody279_112

def sourceBody279_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_103 sourceBody279_113

def sourceBody279_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_102 sourceBody279_114

def sourceBody279_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_101 sourceBody279_115

def sourceBody279_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_100 sourceBody279_116

def sourceBody279_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_99 sourceBody279_117

def sourceBody279_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 44)

def sourceBody279_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 84)

def sourceBody279_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 34)

def sourceBody279_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 74)

def sourceBody279_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 50)

def sourceBody279_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 86 (Flapjack.WordLangExpHOL.var 90)

def sourceBody279_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody279_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 58)

def sourceBody279_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody279_128 : WordLangProgHOL (BitVec 64) :=
.call (some (([54, 92, 16, 56]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody279_0, 279, 14)) (some 130) ([36, 76, 26, 66, 46, 86, 22, 62]) (some (36, sourceBody279_127, 279, 15))

def sourceBody279_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_128 sourceBody279_6

def sourceBody279_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_129 sourceBody279_0

def sourceBody279_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_126 sourceBody279_130

def sourceBody279_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_125 sourceBody279_131

def sourceBody279_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_124 sourceBody279_132

def sourceBody279_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_123 sourceBody279_133

def sourceBody279_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_122 sourceBody279_134

def sourceBody279_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_121 sourceBody279_135

def sourceBody279_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_120 sourceBody279_136

def sourceBody279_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_119 sourceBody279_137

def sourceBody279_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 54)

def sourceBody279_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 92)

def sourceBody279_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 16)

def sourceBody279_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 56)

def sourceBody279_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 76

def sourceBody279_144 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln) PUnit.unit
          Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody279_0, 279, 16)) (some 102) ([76, 26, 66, 46]) (some (76, sourceBody279_143, 279, 17))

def sourceBody279_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_144 sourceBody279_6

def sourceBody279_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_145 sourceBody279_0

def sourceBody279_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_142 sourceBody279_146

def sourceBody279_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_141 sourceBody279_147

def sourceBody279_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_140 sourceBody279_148

def sourceBody279_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_139 sourceBody279_149

def sourceBody279_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 36)

def sourceBody279_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody279_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody279_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody279_155 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.reg 66) sourceBody279_153 sourceBody279_154

def sourceBody279_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_155 sourceBody279_6

def sourceBody279_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 26)

def sourceBody279_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody279_159 : WordLangProgHOL (BitVec 64) :=
.call (some (([54, 92, 16, 56]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody279_0, 279, 18)) (some 99) ([76]) (some (76, sourceBody279_143, 279, 19))

def sourceBody279_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_159 sourceBody279_6

def sourceBody279_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_160 sourceBody279_0

def sourceBody279_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_158 sourceBody279_161

def sourceBody279_163 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 46 (Flapjack.WordRegImm.imm 0#64) sourceBody279_162 sourceBody279_0

def sourceBody279_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_163 sourceBody279_6

def sourceBody279_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_164 sourceBody279_0

def sourceBody279_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_157 sourceBody279_165

def sourceBody279_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_156 sourceBody279_166

def sourceBody279_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_152 sourceBody279_167

def sourceBody279_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_151 sourceBody279_168

def sourceBody279_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 86 (Flapjack.WordLangExpHOL.var 8)

def sourceBody279_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody279_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 12)

def sourceBody279_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 14)

def sourceBody279_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.var 54)

def sourceBody279_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 92)

def sourceBody279_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 16)

def sourceBody279_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 56)

def sourceBody279_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 86

def sourceBody279_179 : WordLangProgHOL (BitVec 64) :=
.call (some (([76, 26, 66, 46]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody279_0, 279, 20)) (some 116) ([86, 22, 62, 42, 82, 32, 72, 52]) (some (86, sourceBody279_178, 279, 21))

def sourceBody279_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_179 sourceBody279_6

def sourceBody279_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_180 sourceBody279_0

def sourceBody279_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_177 sourceBody279_181

def sourceBody279_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_176 sourceBody279_182

def sourceBody279_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_175 sourceBody279_183

def sourceBody279_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_174 sourceBody279_184

def sourceBody279_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_173 sourceBody279_185

def sourceBody279_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_172 sourceBody279_186

def sourceBody279_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_171 sourceBody279_187

def sourceBody279_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_170 sourceBody279_188

def sourceBody279_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 86 (Flapjack.WordLangExpHOL.var 76)

def sourceBody279_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody279_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 66)

def sourceBody279_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 46)

def sourceBody279_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [86, 22, 62, 42]

def sourceBody279_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_194 sourceBody279_0

def sourceBody279_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_193 sourceBody279_195

def sourceBody279_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_192 sourceBody279_196

def sourceBody279_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_191 sourceBody279_197

def sourceBody279_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_190 sourceBody279_198

def sourceBody279_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_189 sourceBody279_199

def sourceBody279_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_200

def sourceBody279_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_201

def sourceBody279_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_202

def sourceBody279_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_203

def sourceBody279_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_204

def sourceBody279_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_205

def sourceBody279_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_206

def sourceBody279_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_207

def sourceBody279_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_169 sourceBody279_208

def sourceBody279_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_150 sourceBody279_209

def sourceBody279_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_210

def sourceBody279_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_211

def sourceBody279_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_138 sourceBody279_212

def sourceBody279_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_213

def sourceBody279_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_214

def sourceBody279_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_215

def sourceBody279_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_216

def sourceBody279_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_217

def sourceBody279_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_218

def sourceBody279_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_219

def sourceBody279_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_220

def sourceBody279_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_118 sourceBody279_221

def sourceBody279_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_222

def sourceBody279_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_223

def sourceBody279_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_224

def sourceBody279_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_225

def sourceBody279_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_226

def sourceBody279_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_227

def sourceBody279_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_228

def sourceBody279_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_229

def sourceBody279_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_98 sourceBody279_230

def sourceBody279_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_231

def sourceBody279_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_232

def sourceBody279_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_233

def sourceBody279_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_234

def sourceBody279_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_235

def sourceBody279_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_236

def sourceBody279_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_237

def sourceBody279_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_238

def sourceBody279_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_78 sourceBody279_239

def sourceBody279_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_240

def sourceBody279_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_241

def sourceBody279_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_242

def sourceBody279_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_243

def sourceBody279_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_244

def sourceBody279_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_245

def sourceBody279_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_246

def sourceBody279_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_247

def sourceBody279_249 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 68 (Flapjack.WordRegImm.imm 0#64) sourceBody279_248 sourceBody279_0

def sourceBody279_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_249 sourceBody279_6

def sourceBody279_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_250 sourceBody279_0

def sourceBody279_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_72 sourceBody279_251

def sourceBody279_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_71 sourceBody279_252

def sourceBody279_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_67 sourceBody279_253

def sourceBody279_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_66 sourceBody279_254

def sourceBody279_256 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.var 6])

def sourceBody279_257 : WordLangProgHOL (BitVec 64) :=
.call (some (([38, 78, 28, 68]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody279_0, 279, 22)) (some 99) ([48]) (some (48, sourceBody279_74, 279, 23))

def sourceBody279_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_257 sourceBody279_6

def sourceBody279_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_258 sourceBody279_0

def sourceBody279_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_256 sourceBody279_259

def sourceBody279_261 : WordLangProgHOL (BitVec 64) :=
.call (some (([48, 88, 24, 64]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody279_0, 279, 24)) (some 120) ([44, 84, 34, 74, 54, 92, 16, 56]) (some (44, sourceBody279_87, 279, 25))

def sourceBody279_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_261 sourceBody279_6

def sourceBody279_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_262 sourceBody279_0

def sourceBody279_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_86 sourceBody279_263

def sourceBody279_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_85 sourceBody279_264

def sourceBody279_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_84 sourceBody279_265

def sourceBody279_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_83 sourceBody279_266

def sourceBody279_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_82 sourceBody279_267

def sourceBody279_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_81 sourceBody279_268

def sourceBody279_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_80 sourceBody279_269

def sourceBody279_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_79 sourceBody279_270

def sourceBody279_272 : WordLangProgHOL (BitVec 64) :=
.call (some (([44, 84, 34, 74]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody279_0, 279, 26)) (some 130) ([54, 92, 16, 56, 36, 76, 26, 66]) (some (54, sourceBody279_107, 279, 27))

def sourceBody279_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_272 sourceBody279_6

def sourceBody279_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_273 sourceBody279_0

def sourceBody279_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_106 sourceBody279_274

def sourceBody279_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_105 sourceBody279_275

def sourceBody279_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_104 sourceBody279_276

def sourceBody279_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_103 sourceBody279_277

def sourceBody279_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_102 sourceBody279_278

def sourceBody279_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_101 sourceBody279_279

def sourceBody279_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_100 sourceBody279_280

def sourceBody279_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_99 sourceBody279_281

def sourceBody279_283 : WordLangProgHOL (BitVec 64) :=
.call (some (([54, 92, 16, 56]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody279_0, 279, 28)) (some 130) ([36, 76, 26, 66, 46, 86, 22, 62]) (some (36, sourceBody279_127, 279, 29))

def sourceBody279_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_283 sourceBody279_6

def sourceBody279_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_284 sourceBody279_0

def sourceBody279_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_126 sourceBody279_285

def sourceBody279_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_125 sourceBody279_286

def sourceBody279_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_124 sourceBody279_287

def sourceBody279_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_123 sourceBody279_288

def sourceBody279_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_122 sourceBody279_289

def sourceBody279_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_121 sourceBody279_290

def sourceBody279_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_120 sourceBody279_291

def sourceBody279_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_119 sourceBody279_292

def sourceBody279_294 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 8)

def sourceBody279_295 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 86 (Flapjack.WordLangExpHOL.var 10)

def sourceBody279_296 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 12)

def sourceBody279_297 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 14)

def sourceBody279_298 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 54)

def sourceBody279_299 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.var 92)

def sourceBody279_300 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 16)

def sourceBody279_301 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 56)

def sourceBody279_302 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody279_303 : WordLangProgHOL (BitVec 64) :=
.call (some (([36, 76, 26, 66]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody279_0, 279, 30)) (some 117) ([46, 86, 22, 62, 42, 82, 32, 72]) (some (46, sourceBody279_302, 279, 31))

def sourceBody279_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_303 sourceBody279_6

def sourceBody279_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_304 sourceBody279_0

def sourceBody279_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_301 sourceBody279_305

def sourceBody279_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_300 sourceBody279_306

def sourceBody279_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_299 sourceBody279_307

def sourceBody279_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_298 sourceBody279_308

def sourceBody279_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_297 sourceBody279_309

def sourceBody279_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_296 sourceBody279_310

def sourceBody279_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_295 sourceBody279_311

def sourceBody279_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_294 sourceBody279_312

def sourceBody279_314 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 36)

def sourceBody279_315 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [46, 86, 22, 62]

def sourceBody279_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_315 sourceBody279_0

def sourceBody279_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_192 sourceBody279_316

def sourceBody279_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_191 sourceBody279_317

def sourceBody279_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_190 sourceBody279_318

def sourceBody279_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_314 sourceBody279_319

def sourceBody279_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_313 sourceBody279_320

def sourceBody279_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_321

def sourceBody279_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_322

def sourceBody279_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_323

def sourceBody279_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_324

def sourceBody279_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_325

def sourceBody279_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_326

def sourceBody279_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_327

def sourceBody279_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_328

def sourceBody279_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_293 sourceBody279_329

def sourceBody279_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_330

def sourceBody279_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_331

def sourceBody279_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_332

def sourceBody279_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_333

def sourceBody279_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_334

def sourceBody279_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_335

def sourceBody279_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_336

def sourceBody279_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_337

def sourceBody279_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_282 sourceBody279_338

def sourceBody279_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_339

def sourceBody279_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_340

def sourceBody279_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_341

def sourceBody279_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_342

def sourceBody279_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_343

def sourceBody279_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_344

def sourceBody279_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_345

def sourceBody279_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_346

def sourceBody279_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_271 sourceBody279_347

def sourceBody279_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_348

def sourceBody279_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_349

def sourceBody279_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_350

def sourceBody279_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_351

def sourceBody279_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_352

def sourceBody279_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_353

def sourceBody279_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_354

def sourceBody279_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_355

def sourceBody279_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_260 sourceBody279_356

def sourceBody279_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_357

def sourceBody279_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_358

def sourceBody279_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_359

def sourceBody279_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_360

def sourceBody279_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_361

def sourceBody279_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_362

def sourceBody279_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_363

def sourceBody279_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_364

def sourceBody279_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_255 sourceBody279_365

def sourceBody279_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_65 sourceBody279_366

def sourceBody279_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_367

def sourceBody279_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_368

def sourceBody279_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_369

def sourceBody279_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_370

def sourceBody279_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_371

def sourceBody279_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_372

def sourceBody279_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_373

def sourceBody279_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_374

def sourceBody279_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_59 sourceBody279_375

def sourceBody279_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_376

def sourceBody279_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_377

def sourceBody279_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_378

def sourceBody279_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_379

def sourceBody279_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_380

def sourceBody279_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_381

def sourceBody279_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_382

def sourceBody279_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_383

def sourceBody279_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_53 sourceBody279_384

def sourceBody279_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_10 sourceBody279_385

def sourceBody279_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_386

def sourceBody279_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_387

def sourceBody279_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_1 sourceBody279_388

def sourceBody279_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody279_0 sourceBody279_389

def source279 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (279, 8, sourceBody279_390)
end InitECandidate.Proofs.WordStages
