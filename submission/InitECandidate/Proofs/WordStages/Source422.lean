import InitECandidate.Proofs.WordStages.Source406
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody422_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody422_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody422_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 4)

def sourceBody422_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody422_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody422_0, 422, 2)) (some 388) ([14, 22]) (some (14, sourceBody422_3, 422, 3))

def sourceBody422_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody422_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_4 sourceBody422_5

def sourceBody422_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_6 sourceBody422_0

def sourceBody422_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_2 sourceBody422_7

def sourceBody422_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_1 sourceBody422_8

def sourceBody422_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 6)

def sourceBody422_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody422_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody422_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody422_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody422_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody422_0, 422, 4)) (some 102) ([22, 18, 26, 16]) (some (22, sourceBody422_14, 422, 5))

def sourceBody422_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_15 sourceBody422_5

def sourceBody422_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_16 sourceBody422_0

def sourceBody422_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_13 sourceBody422_17

def sourceBody422_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_12 sourceBody422_18

def sourceBody422_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_11 sourceBody422_19

def sourceBody422_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_10 sourceBody422_20

def sourceBody422_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody422_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody422_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody422_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody422_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.reg 26) sourceBody422_24 sourceBody422_25

def sourceBody422_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_26 sourceBody422_5

def sourceBody422_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody422_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 184#64]),
        Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody422_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody422_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody422_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody422_0, 422, 6)) (some 385) ([18, 26]) (some (18, sourceBody422_31, 422, 7))

def sourceBody422_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_32 sourceBody422_5

def sourceBody422_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_33 sourceBody422_0

def sourceBody422_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_30 sourceBody422_34

def sourceBody422_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_29 sourceBody422_35

def sourceBody422_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_0 sourceBody422_36

def sourceBody422_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_0 sourceBody422_37

def sourceBody422_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody422_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [22]

def sourceBody422_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_40 sourceBody422_0

def sourceBody422_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_39 sourceBody422_41

def sourceBody422_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_38 sourceBody422_42

def sourceBody422_44 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody422_43 sourceBody422_0

def sourceBody422_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_44 sourceBody422_5

def sourceBody422_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_45 sourceBody422_0

def sourceBody422_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_28 sourceBody422_46

def sourceBody422_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_27 sourceBody422_47

def sourceBody422_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_23 sourceBody422_48

def sourceBody422_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_22 sourceBody422_49

def sourceBody422_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody422_52 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody422_0, 422, 8)) (some 68) ([18]) (some (18, sourceBody422_31, 422, 9))

def sourceBody422_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_52 sourceBody422_5

def sourceBody422_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_53 sourceBody422_0

def sourceBody422_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_51 sourceBody422_54

def sourceBody422_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 22)

def sourceBody422_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody422_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody422_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody422_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody422_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 26)

def sourceBody422_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 18) 30

def sourceBody422_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_62 sourceBody422_0

def sourceBody422_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_61 sourceBody422_63

def sourceBody422_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 16)

def sourceBody422_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 8#64])
  30

def sourceBody422_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_66 sourceBody422_0

def sourceBody422_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_65 sourceBody422_67

def sourceBody422_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 24)

def sourceBody422_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 16#64])
  30

def sourceBody422_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_70 sourceBody422_0

def sourceBody422_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_69 sourceBody422_71

def sourceBody422_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 20)

def sourceBody422_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 24#64])
  30

def sourceBody422_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_74 sourceBody422_0

def sourceBody422_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_73 sourceBody422_75

def sourceBody422_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_76 sourceBody422_0

def sourceBody422_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_72 sourceBody422_77

def sourceBody422_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_68 sourceBody422_78

def sourceBody422_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_64 sourceBody422_79

def sourceBody422_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_60 sourceBody422_80

def sourceBody422_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_0 sourceBody422_81

def sourceBody422_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_59 sourceBody422_82

def sourceBody422_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_0 sourceBody422_83

def sourceBody422_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_58 sourceBody422_84

def sourceBody422_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_0 sourceBody422_85

def sourceBody422_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_57 sourceBody422_86

def sourceBody422_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_0 sourceBody422_87

def sourceBody422_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_56 sourceBody422_88

def sourceBody422_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_0 sourceBody422_89

def sourceBody422_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 184#64]),
        Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody422_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 28)

def sourceBody422_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 22)

def sourceBody422_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody422_95 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody422_0, 422, 10)) (some 384) ([26, 16, 24]) (some (26, sourceBody422_94, 422, 11))

def sourceBody422_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_95 sourceBody422_5

def sourceBody422_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_96 sourceBody422_0

def sourceBody422_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_93 sourceBody422_97

def sourceBody422_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_92 sourceBody422_98

def sourceBody422_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_91 sourceBody422_99

def sourceBody422_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_0 sourceBody422_100

def sourceBody422_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_0 sourceBody422_101

def sourceBody422_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_90 sourceBody422_102

def sourceBody422_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody422_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_104 sourceBody422_0

def sourceBody422_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_25 sourceBody422_105

def sourceBody422_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_103 sourceBody422_106

def sourceBody422_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_55 sourceBody422_107

def sourceBody422_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_0 sourceBody422_108

def sourceBody422_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_0 sourceBody422_109

def sourceBody422_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_50 sourceBody422_110

def sourceBody422_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_21 sourceBody422_111

def sourceBody422_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_0 sourceBody422_112

def sourceBody422_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_0 sourceBody422_113

def sourceBody422_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_9 sourceBody422_114

def sourceBody422_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_0 sourceBody422_115

def sourceBody422_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody422_0 sourceBody422_116

def source422 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (422, 7, sourceBody422_117)
end InitECandidate.Proofs.WordStages
