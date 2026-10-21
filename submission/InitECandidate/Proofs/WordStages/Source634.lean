import InitECandidate.Proofs.WordStages.Source618
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody634_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody634_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody634_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody634_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody634_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody634_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody634_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody634_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 46) sourceBody634_5 sourceBody634_6

def sourceBody634_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody634_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_7 sourceBody634_8

def sourceBody634_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 24)

def sourceBody634_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 10))

def sourceBody634_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 8)

def sourceBody634_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_12 sourceBody634_0

def sourceBody634_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_13 sourceBody634_0

def sourceBody634_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody634_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 30)

def sourceBody634_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody634_18 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 36 (Flapjack.WordRegImm.reg 56) sourceBody634_17 sourceBody634_15

def sourceBody634_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_18 sourceBody634_8

def sourceBody634_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 36)

def sourceBody634_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody634_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 46)

def sourceBody634_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_22 sourceBody634_0

def sourceBody634_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_23 sourceBody634_0

def sourceBody634_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_21 sourceBody634_24

def sourceBody634_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_25

def sourceBody634_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 24)

def sourceBody634_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 30)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody634_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 50)

def sourceBody634_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 56

def sourceBody634_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([46, 36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody634_0, 634, 2)) (some 123) ([56, 18, 38]) (some (56, sourceBody634_30, 634, 3))

def sourceBody634_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_31 sourceBody634_8

def sourceBody634_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_32 sourceBody634_0

def sourceBody634_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_29 sourceBody634_33

def sourceBody634_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_28 sourceBody634_34

def sourceBody634_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_27 sourceBody634_35

def sourceBody634_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 30)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody634_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 46)

def sourceBody634_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 18)

def sourceBody634_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 56) 38

def sourceBody634_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_40 sourceBody634_0

def sourceBody634_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_39 sourceBody634_41

def sourceBody634_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_42 sourceBody634_0

def sourceBody634_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_38 sourceBody634_43

def sourceBody634_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_44

def sourceBody634_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_37 sourceBody634_45

def sourceBody634_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_46

def sourceBody634_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 36)

def sourceBody634_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_48 sourceBody634_0

def sourceBody634_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_49 sourceBody634_0

def sourceBody634_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_47 sourceBody634_50

def sourceBody634_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_36 sourceBody634_51

def sourceBody634_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_52

def sourceBody634_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_53

def sourceBody634_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_54

def sourceBody634_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_55

def sourceBody634_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_26 sourceBody634_56

def sourceBody634_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody634_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_57 sourceBody634_58

def sourceBody634_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody634_61 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody634_59 sourceBody634_60

def sourceBody634_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_61 sourceBody634_8

def sourceBody634_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_62 sourceBody634_0

def sourceBody634_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_20 sourceBody634_63

def sourceBody634_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_19 sourceBody634_64

def sourceBody634_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_16 sourceBody634_65

def sourceBody634_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_15 sourceBody634_66

def sourceBody634_68 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody634_67 (Flapjack.Spt.bs
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody634_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_68 sourceBody634_8

def sourceBody634_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_8 sourceBody634_69

def sourceBody634_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_14 sourceBody634_70

def sourceBody634_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 4)

def sourceBody634_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 36)

def sourceBody634_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 46) 56

def sourceBody634_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_74 sourceBody634_0

def sourceBody634_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_73 sourceBody634_75

def sourceBody634_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_76 sourceBody634_0

def sourceBody634_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_10 sourceBody634_77

def sourceBody634_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_78

def sourceBody634_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_72 sourceBody634_79

def sourceBody634_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_80

def sourceBody634_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_71 sourceBody634_81

def sourceBody634_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody634_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [46]

def sourceBody634_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_84 sourceBody634_0

def sourceBody634_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_83 sourceBody634_85

def sourceBody634_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_82 sourceBody634_86

def sourceBody634_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_6 sourceBody634_87

def sourceBody634_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_88

def sourceBody634_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_11 sourceBody634_89

def sourceBody634_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_90

def sourceBody634_92 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody634_91 sourceBody634_0

def sourceBody634_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_92 sourceBody634_8

def sourceBody634_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_93 sourceBody634_0

def sourceBody634_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_10 sourceBody634_94

def sourceBody634_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_9 sourceBody634_95

def sourceBody634_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_4 sourceBody634_96

def sourceBody634_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_3 sourceBody634_97

def sourceBody634_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody634_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody634_101 : WordLangProgHOL (BitVec 64) :=
.call (some (([50]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody634_0, 634, 4)) (some 122) ([24]) (some (24, sourceBody634_100, 634, 5))

def sourceBody634_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_101 sourceBody634_8

def sourceBody634_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_102 sourceBody634_0

def sourceBody634_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_99 sourceBody634_103

def sourceBody634_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody634_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_105 sourceBody634_0

def sourceBody634_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_106 sourceBody634_0

def sourceBody634_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 40)

def sourceBody634_109 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 46 (Flapjack.WordRegImm.reg 36) sourceBody634_4 sourceBody634_83

def sourceBody634_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_109 sourceBody634_8

def sourceBody634_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 46)

def sourceBody634_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 16,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody634_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
        [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 10,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
                    (Flapjack.WordLangExpHOL.const 3#64)]))
            (Flapjack.WordLangExpHOL.var 50),
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
            (Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 10,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                      [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 1#64])
                    (Flapjack.WordLangExpHOL.const 3#64)]))
            (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
              [Flapjack.WordLangExpHOL.const 32#64, Flapjack.WordLangExpHOL.var 50])],
      Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody634_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 46)

def sourceBody634_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 24) 36

def sourceBody634_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_115 sourceBody634_0

def sourceBody634_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_114 sourceBody634_116

def sourceBody634_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_117 sourceBody634_0

def sourceBody634_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_113 sourceBody634_118

def sourceBody634_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_119

def sourceBody634_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_112 sourceBody634_120

def sourceBody634_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_121

def sourceBody634_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody634_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 24)

def sourceBody634_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_124 sourceBody634_0

def sourceBody634_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_125 sourceBody634_0

def sourceBody634_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_123 sourceBody634_126

def sourceBody634_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_127

def sourceBody634_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_122 sourceBody634_128

def sourceBody634_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_129 sourceBody634_58

def sourceBody634_131 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 56 (Flapjack.WordRegImm.imm 0#64) sourceBody634_130 sourceBody634_60

def sourceBody634_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_131 sourceBody634_8

def sourceBody634_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_132 sourceBody634_0

def sourceBody634_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_111 sourceBody634_133

def sourceBody634_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_110 sourceBody634_134

def sourceBody634_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_108 sourceBody634_135

def sourceBody634_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_83 sourceBody634_136

def sourceBody634_138 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody634_137 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody634_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_138 sourceBody634_8

def sourceBody634_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_8 sourceBody634_139

def sourceBody634_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_107 sourceBody634_140

def sourceBody634_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody634_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 10))
        (Flapjack.WordLangExpHOL.var 50),
      Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody634_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_143 sourceBody634_118

def sourceBody634_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_144

def sourceBody634_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_142 sourceBody634_145

def sourceBody634_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_146

def sourceBody634_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_141 sourceBody634_147

def sourceBody634_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 14,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody634_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
    (Flapjack.WordLangExpHOL.load
      (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.var 6,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
              [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64])
            (Flapjack.WordLangExpHOL.const 3#64)]))
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.const 32#64, Flapjack.WordLangExpHOL.var 50]))

def sourceBody634_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_150 sourceBody634_118

def sourceBody634_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_151

def sourceBody634_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_149 sourceBody634_152

def sourceBody634_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_153

def sourceBody634_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_148 sourceBody634_154

def sourceBody634_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody634_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_156 sourceBody634_0

def sourceBody634_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_157 sourceBody634_0

def sourceBody634_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_155 sourceBody634_158

def sourceBody634_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 14,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody634_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
        [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 6,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
                    (Flapjack.WordLangExpHOL.const 3#64)]))
            (Flapjack.WordLangExpHOL.var 50),
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
            (Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 6,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                      [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 1#64])
                    (Flapjack.WordLangExpHOL.const 3#64)]))
            (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
              [Flapjack.WordLangExpHOL.const 32#64, Flapjack.WordLangExpHOL.var 50])],
      Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody634_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_161 sourceBody634_118

def sourceBody634_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_162

def sourceBody634_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_160 sourceBody634_163

def sourceBody634_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_164

def sourceBody634_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_165 sourceBody634_128

def sourceBody634_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_166 sourceBody634_58

def sourceBody634_168 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 56 (Flapjack.WordRegImm.imm 0#64) sourceBody634_167 sourceBody634_60

def sourceBody634_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_168 sourceBody634_8

def sourceBody634_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_169 sourceBody634_0

def sourceBody634_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_111 sourceBody634_170

def sourceBody634_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_110 sourceBody634_171

def sourceBody634_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_108 sourceBody634_172

def sourceBody634_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_83 sourceBody634_173

def sourceBody634_175 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody634_174 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody634_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_175 sourceBody634_8

def sourceBody634_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_8 sourceBody634_176

def sourceBody634_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_159 sourceBody634_177

def sourceBody634_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody634_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 6))
        (Flapjack.WordLangExpHOL.var 50),
      Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody634_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_180 sourceBody634_118

def sourceBody634_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_181

def sourceBody634_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_179 sourceBody634_182

def sourceBody634_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_183

def sourceBody634_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_178 sourceBody634_184

def sourceBody634_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody634_187 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 2#64])
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody634_188 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 12],
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody634_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_188 sourceBody634_0

def sourceBody634_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_189 sourceBody634_0

def sourceBody634_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody634_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 30)

def sourceBody634_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody634_194 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 56 (Flapjack.WordRegImm.reg 18) sourceBody634_193 sourceBody634_191

def sourceBody634_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_194 sourceBody634_8

def sourceBody634_196 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 56)

def sourceBody634_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody634_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 36)

def sourceBody634_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_198 sourceBody634_0

def sourceBody634_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_199 sourceBody634_0

def sourceBody634_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_197 sourceBody634_200

def sourceBody634_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_201

def sourceBody634_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.var 12])
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody634_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.var 12],
              Flapjack.WordLangExpHOL.const 1#64])
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody634_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.var 12],
              Flapjack.WordLangExpHOL.const 2#64])
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody634_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 36)

def sourceBody634_207 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 24)

def sourceBody634_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody634_209 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody634_210 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 22 (Flapjack.WordRegImm.reg 44) sourceBody634_208 sourceBody634_209

def sourceBody634_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_210 sourceBody634_8

def sourceBody634_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 22)

def sourceBody634_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 4294967295#64)

def sourceBody634_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_213 sourceBody634_0

def sourceBody634_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_214 sourceBody634_0

def sourceBody634_216 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 38)

def sourceBody634_217 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 24)

def sourceBody634_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 44 44 48 22))

def sourceBody634_219 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
        [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
            (Flapjack.WordLangExpHOL.const 32#64),
          Flapjack.WordLangExpHOL.var 56],
      Flapjack.WordLangExpHOL.var 44])

def sourceBody634_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_219 sourceBody634_0

def sourceBody634_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_218 sourceBody634_220

def sourceBody634_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_217 sourceBody634_221

def sourceBody634_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_216 sourceBody634_222

def sourceBody634_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_223 sourceBody634_0

def sourceBody634_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_215 sourceBody634_224

def sourceBody634_226 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 36)

def sourceBody634_227 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 56)

def sourceBody634_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 24)

def sourceBody634_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody634_230 : WordLangProgHOL (BitVec 64) :=
.call (some (([48, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody634_0, 634, 6)) (some 123) ([44, 34, 54]) (some (44, sourceBody634_229, 634, 7))

def sourceBody634_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_230 sourceBody634_8

def sourceBody634_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_231 sourceBody634_0

def sourceBody634_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_228 sourceBody634_232

def sourceBody634_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_227 sourceBody634_233

def sourceBody634_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_226 sourceBody634_234

def sourceBody634_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 48)

def sourceBody634_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_236 sourceBody634_0

def sourceBody634_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_237 sourceBody634_0

def sourceBody634_239 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 22)

def sourceBody634_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_239 sourceBody634_0

def sourceBody634_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_240 sourceBody634_0

def sourceBody634_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_238 sourceBody634_241

def sourceBody634_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_235 sourceBody634_242

def sourceBody634_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_243

def sourceBody634_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_244

def sourceBody634_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_245

def sourceBody634_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_246

def sourceBody634_248 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.imm 0#64) sourceBody634_225 sourceBody634_247

def sourceBody634_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_248 sourceBody634_8

def sourceBody634_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_249 sourceBody634_0

def sourceBody634_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_212 sourceBody634_250

def sourceBody634_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_211 sourceBody634_251

def sourceBody634_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_207 sourceBody634_252

def sourceBody634_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_206 sourceBody634_253

def sourceBody634_255 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody634_256 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 48)

def sourceBody634_257 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody634_258 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody634_259 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody634_260 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 44 (Flapjack.WordRegImm.reg 34) sourceBody634_258 sourceBody634_259

def sourceBody634_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_260 sourceBody634_8

def sourceBody634_262 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 44)

def sourceBody634_263 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody634_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_263 sourceBody634_0

def sourceBody634_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_264 sourceBody634_0

def sourceBody634_266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 28)

def sourceBody634_267 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 4294967296#64)

def sourceBody634_268 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 44 (Flapjack.WordRegImm.reg 34) sourceBody634_258 sourceBody634_259

def sourceBody634_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_268 sourceBody634_8

def sourceBody634_270 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 38)

def sourceBody634_271 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 46)

def sourceBody634_272 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 34 34 22 44))

def sourceBody634_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 28)
        (Flapjack.WordLangExpHOL.const 32#64),
      Flapjack.WordLangExpHOL.var 18])

def sourceBody634_274 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 34)

def sourceBody634_275 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody634_276 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody634_277 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 20 (Flapjack.WordRegImm.reg 42) sourceBody634_275 sourceBody634_276

def sourceBody634_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_277 sourceBody634_8

def sourceBody634_279 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 20)

def sourceBody634_280 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody634_281 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 22)

def sourceBody634_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_281 sourceBody634_0

def sourceBody634_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_282 sourceBody634_0

def sourceBody634_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_280 sourceBody634_283

def sourceBody634_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_284

def sourceBody634_286 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.var 24])

def sourceBody634_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_286 sourceBody634_241

def sourceBody634_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_287

def sourceBody634_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_285 sourceBody634_288

def sourceBody634_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_255 sourceBody634_0

def sourceBody634_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_290 sourceBody634_0

def sourceBody634_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_289 sourceBody634_291

def sourceBody634_293 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody634_292 sourceBody634_0

def sourceBody634_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_293 sourceBody634_8

def sourceBody634_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_294 sourceBody634_0

def sourceBody634_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_279 sourceBody634_295

def sourceBody634_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_278 sourceBody634_296

def sourceBody634_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_274 sourceBody634_297

def sourceBody634_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_273 sourceBody634_298

def sourceBody634_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_272 sourceBody634_299

def sourceBody634_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_271 sourceBody634_300

def sourceBody634_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_270 sourceBody634_301

def sourceBody634_303 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 54 (Flapjack.WordRegImm.imm 0#64) sourceBody634_302 sourceBody634_0

def sourceBody634_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_303 sourceBody634_8

def sourceBody634_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_304 sourceBody634_0

def sourceBody634_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_262 sourceBody634_305

def sourceBody634_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_269 sourceBody634_306

def sourceBody634_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_267 sourceBody634_307

def sourceBody634_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_266 sourceBody634_308

def sourceBody634_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_265 sourceBody634_309

def sourceBody634_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_310 sourceBody634_58

def sourceBody634_312 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 54 (Flapjack.WordRegImm.imm 0#64) sourceBody634_311 sourceBody634_60

def sourceBody634_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_312 sourceBody634_8

def sourceBody634_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_313 sourceBody634_0

def sourceBody634_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_262 sourceBody634_314

def sourceBody634_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_261 sourceBody634_315

def sourceBody634_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_257 sourceBody634_316

def sourceBody634_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_256 sourceBody634_317

def sourceBody634_319 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
  PUnit.unit Flapjack.Spt.ln) sourceBody634_318 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody634_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_319 sourceBody634_8

def sourceBody634_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_8 sourceBody634_320

def sourceBody634_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_1 sourceBody634_0

def sourceBody634_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_322 sourceBody634_0

def sourceBody634_324 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 40)

def sourceBody634_325 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 12)

def sourceBody634_326 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody634_327 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 34 (Flapjack.WordRegImm.reg 54) sourceBody634_257 sourceBody634_326

def sourceBody634_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_327 sourceBody634_8

def sourceBody634_329 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 34)

def sourceBody634_330 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 38)

def sourceBody634_331 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody634_332 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 54 54 44 34))

def sourceBody634_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_332 sourceBody634_0

def sourceBody634_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_331 sourceBody634_333

def sourceBody634_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_330 sourceBody634_334

def sourceBody634_336 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 54)

def sourceBody634_337 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
        [Flapjack.WordLangExpHOL.load
            (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.var 14,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.var 30])
                  (Flapjack.WordLangExpHOL.const 3#64)]),
          Flapjack.WordLangExpHOL.var 22],
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
        [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 4294967295#64]])

def sourceBody634_338 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 14,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.var 30])
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody634_339 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody634_340 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 52)

def sourceBody634_341 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 32) 26

def sourceBody634_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_341 sourceBody634_0

def sourceBody634_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_340 sourceBody634_342

def sourceBody634_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_343 sourceBody634_0

def sourceBody634_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_339 sourceBody634_344

def sourceBody634_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_345

def sourceBody634_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_338 sourceBody634_346

def sourceBody634_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_347

def sourceBody634_349 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 20)
        (Flapjack.WordLangExpHOL.const 32#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.asr (Flapjack.WordLangExpHOL.var 42)
        (Flapjack.WordLangExpHOL.const 32#64)])

def sourceBody634_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_349 sourceBody634_0

def sourceBody634_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_350 sourceBody634_0

def sourceBody634_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_348 sourceBody634_351

def sourceBody634_353 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody634_354 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 32)

def sourceBody634_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_354 sourceBody634_0

def sourceBody634_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_355 sourceBody634_0

def sourceBody634_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_353 sourceBody634_356

def sourceBody634_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_357

def sourceBody634_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_352 sourceBody634_358

def sourceBody634_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_337 sourceBody634_359

def sourceBody634_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_360

def sourceBody634_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_336 sourceBody634_361

def sourceBody634_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_335 sourceBody634_362

def sourceBody634_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_363 sourceBody634_58

def sourceBody634_365 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody634_364 sourceBody634_60

def sourceBody634_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_365 sourceBody634_8

def sourceBody634_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_366 sourceBody634_0

def sourceBody634_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_329 sourceBody634_367

def sourceBody634_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_328 sourceBody634_368

def sourceBody634_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_325 sourceBody634_369

def sourceBody634_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_324 sourceBody634_370

def sourceBody634_372 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
  PUnit.unit Flapjack.Spt.ln) sourceBody634_371 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody634_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_372 sourceBody634_8

def sourceBody634_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_8 sourceBody634_373

def sourceBody634_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_323 sourceBody634_374

def sourceBody634_376 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.var 22])

def sourceBody634_377 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody634_378 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody634_379 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 54 (Flapjack.WordRegImm.reg 20) sourceBody634_377 sourceBody634_378

def sourceBody634_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_379 sourceBody634_8

def sourceBody634_381 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 54)

def sourceBody634_382 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 30)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody634_383 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody634_384 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 34) 20

def sourceBody634_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_384 sourceBody634_0

def sourceBody634_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_336 sourceBody634_385

def sourceBody634_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_386 sourceBody634_0

def sourceBody634_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_383 sourceBody634_387

def sourceBody634_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_388

def sourceBody634_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_382 sourceBody634_389

def sourceBody634_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_390

def sourceBody634_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_209 sourceBody634_0

def sourceBody634_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_392 sourceBody634_0

def sourceBody634_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_391 sourceBody634_393

def sourceBody634_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_394 sourceBody634_323

def sourceBody634_396 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 40)

def sourceBody634_397 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody634_398 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 54 (Flapjack.WordRegImm.reg 20) sourceBody634_377 sourceBody634_378

def sourceBody634_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_398 sourceBody634_8

def sourceBody634_400 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 14,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.var 30])
              (Flapjack.WordLangExpHOL.const 3#64)]),
      Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 16,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
              (Flapjack.WordLangExpHOL.const 3#64)]),
      Flapjack.WordLangExpHOL.var 22])

def sourceBody634_401 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 14,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.var 30])
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody634_402 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody634_403 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 20)

def sourceBody634_404 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 54) 42

def sourceBody634_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_404 sourceBody634_0

def sourceBody634_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_403 sourceBody634_405

def sourceBody634_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_406 sourceBody634_0

def sourceBody634_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_402 sourceBody634_407

def sourceBody634_409 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_408

def sourceBody634_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_401 sourceBody634_409

def sourceBody634_411 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_410

def sourceBody634_412 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 34)
    (Flapjack.WordLangExpHOL.const 32#64))

def sourceBody634_413 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_412 sourceBody634_0

def sourceBody634_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_413 sourceBody634_0

def sourceBody634_415 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_411 sourceBody634_414

def sourceBody634_416 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody634_417 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 54)

def sourceBody634_418 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_417 sourceBody634_0

def sourceBody634_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_418 sourceBody634_0

def sourceBody634_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_416 sourceBody634_419

def sourceBody634_421 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_420

def sourceBody634_422 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_415 sourceBody634_421

def sourceBody634_423 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_400 sourceBody634_422

def sourceBody634_424 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_423

def sourceBody634_425 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_424 sourceBody634_58

def sourceBody634_426 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.imm 0#64) sourceBody634_425 sourceBody634_60

def sourceBody634_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_426 sourceBody634_8

def sourceBody634_428 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_427 sourceBody634_0

def sourceBody634_429 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_381 sourceBody634_428

def sourceBody634_430 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_399 sourceBody634_429

def sourceBody634_431 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_397 sourceBody634_430

def sourceBody634_432 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_396 sourceBody634_431

def sourceBody634_433 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
  PUnit.unit Flapjack.Spt.ln) sourceBody634_432 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody634_434 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_433 sourceBody634_8

def sourceBody634_435 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_8 sourceBody634_434

def sourceBody634_436 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_395 sourceBody634_435

def sourceBody634_437 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 14,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.var 12])
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody634_438 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 44, Flapjack.WordLangExpHOL.var 22],
      Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody634_439 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_438 sourceBody634_387

def sourceBody634_440 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_439

def sourceBody634_441 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_437 sourceBody634_440

def sourceBody634_442 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_441

def sourceBody634_443 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_436 sourceBody634_442

def sourceBody634_444 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 38)

def sourceBody634_445 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_444 sourceBody634_387

def sourceBody634_446 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_445

def sourceBody634_447 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_382 sourceBody634_446

def sourceBody634_448 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_447

def sourceBody634_449 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_262 sourceBody634_387

def sourceBody634_450 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_449

def sourceBody634_451 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_437 sourceBody634_450

def sourceBody634_452 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_451

def sourceBody634_453 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_448 sourceBody634_452

def sourceBody634_454 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.imm 0#64) sourceBody634_443 sourceBody634_453

def sourceBody634_455 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_454 sourceBody634_8

def sourceBody634_456 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_455 sourceBody634_0

def sourceBody634_457 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_381 sourceBody634_456

def sourceBody634_458 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_380 sourceBody634_457

def sourceBody634_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_276 sourceBody634_458

def sourceBody634_460 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_262 sourceBody634_459

def sourceBody634_461 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_376 sourceBody634_460

def sourceBody634_462 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_461

def sourceBody634_463 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_375 sourceBody634_462

def sourceBody634_464 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_209 sourceBody634_463

def sourceBody634_465 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_464

def sourceBody634_466 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_321 sourceBody634_465

def sourceBody634_467 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_255 sourceBody634_466

def sourceBody634_468 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_467

def sourceBody634_469 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_254 sourceBody634_468

def sourceBody634_470 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_469

def sourceBody634_471 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_470

def sourceBody634_472 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_471

def sourceBody634_473 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_472

def sourceBody634_474 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_205 sourceBody634_473

def sourceBody634_475 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_474

def sourceBody634_476 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_204 sourceBody634_475

def sourceBody634_477 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_476

def sourceBody634_478 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_203 sourceBody634_477

def sourceBody634_479 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_478

def sourceBody634_480 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_202 sourceBody634_479

def sourceBody634_481 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_480 sourceBody634_58

def sourceBody634_482 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.imm 0#64) sourceBody634_481 sourceBody634_60

def sourceBody634_483 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_482 sourceBody634_8

def sourceBody634_484 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_483 sourceBody634_0

def sourceBody634_485 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_196 sourceBody634_484

def sourceBody634_486 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_195 sourceBody634_485

def sourceBody634_487 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_192 sourceBody634_486

def sourceBody634_488 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_191 sourceBody634_487

def sourceBody634_489 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody634_488 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody634_490 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_489 sourceBody634_8

def sourceBody634_491 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_8 sourceBody634_490

def sourceBody634_492 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_190 sourceBody634_491

def sourceBody634_493 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_492 sourceBody634_190

def sourceBody634_494 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody634_495 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 30)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody634_496 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 56)

def sourceBody634_497 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 36) 18

def sourceBody634_498 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_497 sourceBody634_0

def sourceBody634_499 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_496 sourceBody634_498

def sourceBody634_500 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_499 sourceBody634_0

def sourceBody634_501 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_191 sourceBody634_500

def sourceBody634_502 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_501

def sourceBody634_503 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_495 sourceBody634_502

def sourceBody634_504 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_503

def sourceBody634_505 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody634_506 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_505 sourceBody634_200

def sourceBody634_507 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_506

def sourceBody634_508 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_504 sourceBody634_507

def sourceBody634_509 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_508 sourceBody634_58

def sourceBody634_510 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.imm 0#64) sourceBody634_509 sourceBody634_60

def sourceBody634_511 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_510 sourceBody634_8

def sourceBody634_512 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_511 sourceBody634_0

def sourceBody634_513 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_196 sourceBody634_512

def sourceBody634_514 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_195 sourceBody634_513

def sourceBody634_515 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_494 sourceBody634_514

def sourceBody634_516 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_16 sourceBody634_515

def sourceBody634_517 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody634_516 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody634_518 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_517 sourceBody634_8

def sourceBody634_519 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_8 sourceBody634_518

def sourceBody634_520 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_493 sourceBody634_519

def sourceBody634_521 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_520 sourceBody634_323

def sourceBody634_522 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 40)

def sourceBody634_523 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody634_524 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 4,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody634_525 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
        (Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.var 14,
              Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
                (Flapjack.WordLangExpHOL.const 3#64)]))
        (Flapjack.WordLangExpHOL.var 50),
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
        [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.var 14,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                      [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 1#64])
                    (Flapjack.WordLangExpHOL.const 3#64)]))
            (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
              [Flapjack.WordLangExpHOL.const 32#64, Flapjack.WordLangExpHOL.var 50]),
          Flapjack.WordLangExpHOL.const 4294967295#64]])

def sourceBody634_526 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_525 sourceBody634_500

def sourceBody634_527 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_526

def sourceBody634_528 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_524 sourceBody634_527

def sourceBody634_529 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_528

def sourceBody634_530 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody634_531 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 36)

def sourceBody634_532 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_531 sourceBody634_0

def sourceBody634_533 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_532 sourceBody634_0

def sourceBody634_534 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_530 sourceBody634_533

def sourceBody634_535 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_534

def sourceBody634_536 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_529 sourceBody634_535

def sourceBody634_537 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_536 sourceBody634_58

def sourceBody634_538 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.imm 0#64) sourceBody634_537 sourceBody634_60

def sourceBody634_539 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_538 sourceBody634_8

def sourceBody634_540 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_539 sourceBody634_0

def sourceBody634_541 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_196 sourceBody634_540

def sourceBody634_542 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_195 sourceBody634_541

def sourceBody634_543 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_523 sourceBody634_542

def sourceBody634_544 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_522 sourceBody634_543

def sourceBody634_545 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody634_544 (Flapjack.Spt.ls PUnit.unit)

def sourceBody634_546 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_545 sourceBody634_8

def sourceBody634_547 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_8 sourceBody634_546

def sourceBody634_548 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_521 sourceBody634_547

def sourceBody634_549 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [36]

def sourceBody634_550 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_549 sourceBody634_0

def sourceBody634_551 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_15 sourceBody634_550

def sourceBody634_552 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_548 sourceBody634_551

def sourceBody634_553 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_187 sourceBody634_552

def sourceBody634_554 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_553

def sourceBody634_555 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_186 sourceBody634_554

def sourceBody634_556 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_555

def sourceBody634_557 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_185 sourceBody634_556

def sourceBody634_558 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_104 sourceBody634_557

def sourceBody634_559 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_558

def sourceBody634_560 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_559

def sourceBody634_561 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_98 sourceBody634_560

def sourceBody634_562 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_2 sourceBody634_561

def sourceBody634_563 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_562

def sourceBody634_564 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_1 sourceBody634_563

def sourceBody634_565 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody634_0 sourceBody634_564

def source634 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (634, 9, sourceBody634_565)
end InitECandidate.Proofs.WordStages
