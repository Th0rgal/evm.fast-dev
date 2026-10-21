import InitECandidate.Proofs.WordStages.Source461
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody477_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody477_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 2)

def sourceBody477_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 4)

def sourceBody477_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 6)

def sourceBody477_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 8)

def sourceBody477_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 10)

def sourceBody477_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 12)

def sourceBody477_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 14)

def sourceBody477_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 16)

def sourceBody477_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 54

def sourceBody477_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([46, 40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody477_0, 477, 2)) (some 476) ([54, 36, 50, 44, 58, 34, 48, 42]) (some (54, sourceBody477_9, 477, 3))

def sourceBody477_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody477_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_10 sourceBody477_11

def sourceBody477_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_12 sourceBody477_0

def sourceBody477_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_8 sourceBody477_13

def sourceBody477_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_7 sourceBody477_14

def sourceBody477_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_6 sourceBody477_15

def sourceBody477_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_5 sourceBody477_16

def sourceBody477_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_4 sourceBody477_17

def sourceBody477_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_3 sourceBody477_18

def sourceBody477_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_2 sourceBody477_19

def sourceBody477_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_1 sourceBody477_20

def sourceBody477_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 46)

def sourceBody477_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 18446744073709551615#64)

def sourceBody477_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody477_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody477_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 36 (Flapjack.WordRegImm.reg 50) sourceBody477_24 sourceBody477_25

def sourceBody477_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_26 sourceBody477_11

def sourceBody477_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 36)

def sourceBody477_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 46)

def sourceBody477_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 40)

def sourceBody477_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [54, 36]

def sourceBody477_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_31 sourceBody477_0

def sourceBody477_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_30 sourceBody477_32

def sourceBody477_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_29 sourceBody477_33

def sourceBody477_35 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 44 (Flapjack.WordRegImm.imm 0#64) sourceBody477_34 sourceBody477_0

def sourceBody477_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_35 sourceBody477_11

def sourceBody477_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_36 sourceBody477_0

def sourceBody477_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_28 sourceBody477_37

def sourceBody477_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_27 sourceBody477_38

def sourceBody477_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_23 sourceBody477_39

def sourceBody477_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_22 sourceBody477_40

def sourceBody477_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody477_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody477_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 54, Flapjack.WordLangExpHOL.var 40])

def sourceBody477_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 50)

def sourceBody477_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 36) 44

def sourceBody477_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_46 sourceBody477_0

def sourceBody477_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_45 sourceBody477_47

def sourceBody477_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_48 sourceBody477_0

def sourceBody477_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_44 sourceBody477_49

def sourceBody477_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_0 sourceBody477_50

def sourceBody477_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_43 sourceBody477_51

def sourceBody477_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_0 sourceBody477_52

def sourceBody477_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 18)

def sourceBody477_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 20)

def sourceBody477_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 22)

def sourceBody477_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 24)

def sourceBody477_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 26)

def sourceBody477_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 28)

def sourceBody477_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 30)

def sourceBody477_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 32)

def sourceBody477_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody477_63 : WordLangProgHOL (BitVec 64) :=
.call (some (([36, 50]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody477_0, 477, 4)) (some 476) ([44, 58, 34, 48, 42, 56, 38, 52]) (some (44, sourceBody477_62, 477, 5))

def sourceBody477_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_63 sourceBody477_11

def sourceBody477_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_64 sourceBody477_0

def sourceBody477_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_61 sourceBody477_65

def sourceBody477_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_60 sourceBody477_66

def sourceBody477_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_59 sourceBody477_67

def sourceBody477_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_58 sourceBody477_68

def sourceBody477_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_57 sourceBody477_69

def sourceBody477_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_56 sourceBody477_70

def sourceBody477_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_55 sourceBody477_71

def sourceBody477_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_54 sourceBody477_72

def sourceBody477_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody477_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 54)

def sourceBody477_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 58)

def sourceBody477_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 44) 34

def sourceBody477_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_77 sourceBody477_0

def sourceBody477_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_76 sourceBody477_78

def sourceBody477_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_79 sourceBody477_0

def sourceBody477_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_75 sourceBody477_80

def sourceBody477_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_0 sourceBody477_81

def sourceBody477_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_74 sourceBody477_82

def sourceBody477_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_0 sourceBody477_83

def sourceBody477_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 36)

def sourceBody477_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 18446744073709551615#64)

def sourceBody477_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody477_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody477_89 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 58 (Flapjack.WordRegImm.reg 34) sourceBody477_87 sourceBody477_88

def sourceBody477_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_89 sourceBody477_11

def sourceBody477_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 58)

def sourceBody477_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 50)

def sourceBody477_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [44, 58]

def sourceBody477_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_93 sourceBody477_0

def sourceBody477_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_92 sourceBody477_94

def sourceBody477_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_28 sourceBody477_95

def sourceBody477_97 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.imm 0#64) sourceBody477_96 sourceBody477_0

def sourceBody477_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_97 sourceBody477_11

def sourceBody477_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_98 sourceBody477_0

def sourceBody477_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_91 sourceBody477_99

def sourceBody477_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_90 sourceBody477_100

def sourceBody477_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_86 sourceBody477_101

def sourceBody477_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_85 sourceBody477_102

def sourceBody477_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_84 sourceBody477_103

def sourceBody477_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 46, Flapjack.WordLangExpHOL.var 36])

def sourceBody477_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.var 50])

def sourceBody477_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_106 sourceBody477_94

def sourceBody477_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_105 sourceBody477_107

def sourceBody477_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_104 sourceBody477_108

def sourceBody477_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_73 sourceBody477_109

def sourceBody477_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_0 sourceBody477_110

def sourceBody477_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_0 sourceBody477_111

def sourceBody477_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_0 sourceBody477_112

def sourceBody477_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_0 sourceBody477_113

def sourceBody477_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_53 sourceBody477_114

def sourceBody477_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_42 sourceBody477_115

def sourceBody477_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_0 sourceBody477_116

def sourceBody477_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_41 sourceBody477_117

def sourceBody477_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_21 sourceBody477_118

def sourceBody477_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_0 sourceBody477_119

def sourceBody477_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_0 sourceBody477_120

def sourceBody477_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_0 sourceBody477_121

def sourceBody477_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody477_0 sourceBody477_122

def source477 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (477, 17, sourceBody477_123)
end InitECandidate.Proofs.WordStages
