import InitECandidate.Proofs.WordStages.Source236
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody252_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody252_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody252_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody252_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody252_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 16 (Flapjack.WordRegImm.reg 54) sourceBody252_2 sourceBody252_3

def sourceBody252_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody252_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_4 sourceBody252_5

def sourceBody252_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody252_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody252_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody252_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([64]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody252_8, 252, 2)) (some 245) ([16]) (some (16, sourceBody252_9, 252, 3))

def sourceBody252_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_10 sourceBody252_5

def sourceBody252_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_11 sourceBody252_8

def sourceBody252_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_2 sourceBody252_12

def sourceBody252_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_13

def sourceBody252_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_14

def sourceBody252_16 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.imm 0#64) sourceBody252_15 sourceBody252_8

def sourceBody252_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_16 sourceBody252_5

def sourceBody252_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_17 sourceBody252_8

def sourceBody252_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_7 sourceBody252_18

def sourceBody252_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_6 sourceBody252_19

def sourceBody252_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_1 sourceBody252_20

def sourceBody252_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_0 sourceBody252_21

def sourceBody252_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 2)

def sourceBody252_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 64 (Flapjack.WordLangAddr.addr 64 0#64))

def sourceBody252_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 64)

def sourceBody252_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 21#64)

def sourceBody252_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody252_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody252_29 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 54 (Flapjack.WordRegImm.reg 34) sourceBody252_27 sourceBody252_28

def sourceBody252_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_29 sourceBody252_5

def sourceBody252_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody252_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 74 (Flapjack.WordLangAddr.addr 74 0#64))

def sourceBody252_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 74)

def sourceBody252_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody252_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody252_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody252_37 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.reg 30) sourceBody252_35 sourceBody252_36

def sourceBody252_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_37 sourceBody252_5

def sourceBody252_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody252_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or [Flapjack.WordLangExpHOL.var 54, Flapjack.WordLangExpHOL.var 48])

def sourceBody252_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody252_42 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.reg 60) sourceBody252_41 sourceBody252_39

def sourceBody252_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_42 sourceBody252_5

def sourceBody252_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 22)

def sourceBody252_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody252_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([64]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody252_8, 252, 4)) (some 245) ([16]) (some (16, sourceBody252_9, 252, 5))

def sourceBody252_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_46 sourceBody252_5

def sourceBody252_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_47 sourceBody252_8

def sourceBody252_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_45 sourceBody252_48

def sourceBody252_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_49

def sourceBody252_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_50

def sourceBody252_52 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.imm 0#64) sourceBody252_51 sourceBody252_8

def sourceBody252_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_52 sourceBody252_5

def sourceBody252_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_53 sourceBody252_8

def sourceBody252_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_44 sourceBody252_54

def sourceBody252_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_43 sourceBody252_55

def sourceBody252_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_40 sourceBody252_56

def sourceBody252_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_39 sourceBody252_57

def sourceBody252_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_38 sourceBody252_58

def sourceBody252_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_34 sourceBody252_59

def sourceBody252_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_33 sourceBody252_60

def sourceBody252_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_32 sourceBody252_61

def sourceBody252_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_31 sourceBody252_62

def sourceBody252_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_30 sourceBody252_63

def sourceBody252_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_26 sourceBody252_64

def sourceBody252_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_25 sourceBody252_65

def sourceBody252_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_24 sourceBody252_66

def sourceBody252_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_23 sourceBody252_67

def sourceBody252_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_22 sourceBody252_68

def sourceBody252_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody252_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 64)

def sourceBody252_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_71 sourceBody252_8

def sourceBody252_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_72 sourceBody252_8

def sourceBody252_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_70 sourceBody252_73

def sourceBody252_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_74

def sourceBody252_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_69 sourceBody252_75

def sourceBody252_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody252_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 64)

def sourceBody252_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_78 sourceBody252_8

def sourceBody252_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_79 sourceBody252_8

def sourceBody252_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_77 sourceBody252_80

def sourceBody252_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_81

def sourceBody252_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_76 sourceBody252_82

def sourceBody252_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody252_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 80#64)

def sourceBody252_86 : WordLangProgHOL (BitVec 64) :=
.call (some (([64]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody252_8, 252, 6)) (some 245) ([16]) (some (16, sourceBody252_9, 252, 7))

def sourceBody252_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_86 sourceBody252_5

def sourceBody252_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_87 sourceBody252_8

def sourceBody252_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_85 sourceBody252_88

def sourceBody252_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_89

def sourceBody252_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_90

def sourceBody252_92 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.imm 0#64) sourceBody252_91 sourceBody252_8

def sourceBody252_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_92 sourceBody252_5

def sourceBody252_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_93 sourceBody252_8

def sourceBody252_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_7 sourceBody252_94

def sourceBody252_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_6 sourceBody252_95

def sourceBody252_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_84 sourceBody252_96

def sourceBody252_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_0 sourceBody252_97

def sourceBody252_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_83 sourceBody252_98

def sourceBody252_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody252_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody252_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 16 (Flapjack.WordLangAddr.addr 16 0#64))

def sourceBody252_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody252_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 54 (Flapjack.WordLangAddr.addr 54 0#64))

def sourceBody252_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody252_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 34 (Flapjack.WordLangAddr.addr 34 0#64))

def sourceBody252_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody252_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_32 sourceBody252_8

def sourceBody252_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_107 sourceBody252_108

def sourceBody252_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_106 sourceBody252_109

def sourceBody252_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_105 sourceBody252_110

def sourceBody252_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_104 sourceBody252_111

def sourceBody252_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_103 sourceBody252_112

def sourceBody252_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_102 sourceBody252_113

def sourceBody252_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_101 sourceBody252_114

def sourceBody252_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 16,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 54)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 34)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 74)
        (Flapjack.WordLangExpHOL.const 24#64)])

def sourceBody252_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 10)

def sourceBody252_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 64) 48

def sourceBody252_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_118 sourceBody252_8

def sourceBody252_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_117 sourceBody252_119

def sourceBody252_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_120 sourceBody252_8

def sourceBody252_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_116 sourceBody252_121

def sourceBody252_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_115 sourceBody252_122

def sourceBody252_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_100 sourceBody252_123

def sourceBody252_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_124

def sourceBody252_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_99 sourceBody252_125

def sourceBody252_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 112#64]),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody252_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 4#64])

def sourceBody252_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody252_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody252_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody252_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_131 sourceBody252_108

def sourceBody252_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_106 sourceBody252_132

def sourceBody252_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_130 sourceBody252_133

def sourceBody252_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_104 sourceBody252_134

def sourceBody252_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_129 sourceBody252_135

def sourceBody252_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_102 sourceBody252_136

def sourceBody252_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_128 sourceBody252_137

def sourceBody252_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_138 sourceBody252_122

def sourceBody252_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_127 sourceBody252_139

def sourceBody252_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_140

def sourceBody252_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_126 sourceBody252_141

def sourceBody252_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody252_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody252_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 4)

def sourceBody252_146 : WordLangProgHOL (BitVec 64) :=
.call (some (([64]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody252_8, 252, 8)) (some 246) ([16, 54, 34, 74]) (some (16, sourceBody252_9, 252, 9))

def sourceBody252_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_146 sourceBody252_5

def sourceBody252_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_147 sourceBody252_8

def sourceBody252_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_145 sourceBody252_148

def sourceBody252_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_144 sourceBody252_149

def sourceBody252_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_1 sourceBody252_150

def sourceBody252_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_143 sourceBody252_151

def sourceBody252_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_152

def sourceBody252_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_153

def sourceBody252_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_142 sourceBody252_154

def sourceBody252_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.load
      (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
        [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
              Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
          Flapjack.WordLangExpHOL.const 112#64])))

def sourceBody252_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 112#64]),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody252_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody252_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody252_160 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody252_8, 252, 10)) (some 68) ([34]) (some (34, sourceBody252_159, 252, 11))

def sourceBody252_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_160 sourceBody252_5

def sourceBody252_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_161 sourceBody252_8

def sourceBody252_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_158 sourceBody252_162

def sourceBody252_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 54, Flapjack.WordLangExpHOL.const 88#64])

def sourceBody252_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody252_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody252_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 10 (Flapjack.WordLangAddr.addr 10 0#64))

def sourceBody252_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody252_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 48 (Flapjack.WordLangAddr.addr 48 0#64))

def sourceBody252_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody252_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 30 (Flapjack.WordLangAddr.addr 30 0#64))

def sourceBody252_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 4#64])

def sourceBody252_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 70 (Flapjack.WordLangAddr.addr 70 0#64))

def sourceBody252_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody252_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 22 (Flapjack.WordLangAddr.addr 22 0#64))

def sourceBody252_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 2#64])

def sourceBody252_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 60 (Flapjack.WordLangAddr.addr 60 0#64))

def sourceBody252_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 3#64])

def sourceBody252_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 40 (Flapjack.WordLangAddr.addr 40 0#64))

def sourceBody252_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_179 sourceBody252_8

def sourceBody252_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_178 sourceBody252_180

def sourceBody252_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_177 sourceBody252_181

def sourceBody252_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_176 sourceBody252_182

def sourceBody252_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_175 sourceBody252_183

def sourceBody252_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_174 sourceBody252_184

def sourceBody252_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_173 sourceBody252_185

def sourceBody252_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_172 sourceBody252_186

def sourceBody252_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_171 sourceBody252_187

def sourceBody252_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_170 sourceBody252_188

def sourceBody252_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_169 sourceBody252_189

def sourceBody252_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_168 sourceBody252_190

def sourceBody252_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_167 sourceBody252_191

def sourceBody252_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_166 sourceBody252_192

def sourceBody252_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_32 sourceBody252_193

def sourceBody252_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_165 sourceBody252_194

def sourceBody252_196 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 74,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 10)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 48)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 30)
        (Flapjack.WordLangExpHOL.const 24#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
          [Flapjack.WordLangExpHOL.var 70,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 22)
              (Flapjack.WordLangExpHOL.const 8#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 60)
              (Flapjack.WordLangExpHOL.const 16#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
              (Flapjack.WordLangExpHOL.const 24#64)])
        (Flapjack.WordLangExpHOL.const 32#64)])

def sourceBody252_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 80)

def sourceBody252_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 34) 8

def sourceBody252_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_198 sourceBody252_8

def sourceBody252_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_197 sourceBody252_199

def sourceBody252_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_200 sourceBody252_8

def sourceBody252_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_196 sourceBody252_201

def sourceBody252_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_195 sourceBody252_202

def sourceBody252_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_164 sourceBody252_203

def sourceBody252_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_204

def sourceBody252_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 64])

def sourceBody252_207 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.var 64])

def sourceBody252_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 44#64)

def sourceBody252_209 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 48 (Flapjack.WordRegImm.reg 30) sourceBody252_35 sourceBody252_36

def sourceBody252_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_209 sourceBody252_5

def sourceBody252_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 48)

def sourceBody252_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 81#64)

def sourceBody252_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 48

def sourceBody252_214 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody252_8, 252, 12)) (some 245) ([48]) (some (48, sourceBody252_213, 252, 13))

def sourceBody252_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_214 sourceBody252_5

def sourceBody252_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_215 sourceBody252_8

def sourceBody252_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_212 sourceBody252_216

def sourceBody252_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_217

def sourceBody252_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_218

def sourceBody252_220 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 70 (Flapjack.WordRegImm.imm 0#64) sourceBody252_219 sourceBody252_8

def sourceBody252_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_220 sourceBody252_5

def sourceBody252_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_221 sourceBody252_8

def sourceBody252_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_211 sourceBody252_222

def sourceBody252_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_210 sourceBody252_223

def sourceBody252_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_208 sourceBody252_224

def sourceBody252_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_33 sourceBody252_225

def sourceBody252_227 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 34)

def sourceBody252_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody252_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody252_230 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody252_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_173 sourceBody252_8

def sourceBody252_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_230 sourceBody252_231

def sourceBody252_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_171 sourceBody252_232

def sourceBody252_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_229 sourceBody252_233

def sourceBody252_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_169 sourceBody252_234

def sourceBody252_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_228 sourceBody252_235

def sourceBody252_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_167 sourceBody252_236

def sourceBody252_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_227 sourceBody252_237

def sourceBody252_239 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 10,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 48)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 30)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 70)
        (Flapjack.WordLangExpHOL.const 24#64)])

def sourceBody252_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 4#64])

def sourceBody252_241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody252_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody252_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 80 (Flapjack.WordLangAddr.addr 80 0#64))

def sourceBody252_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody252_245 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 8 (Flapjack.WordLangAddr.addr 8 0#64))

def sourceBody252_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_245 sourceBody252_8

def sourceBody252_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_244 sourceBody252_246

def sourceBody252_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_243 sourceBody252_247

def sourceBody252_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_242 sourceBody252_248

def sourceBody252_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_179 sourceBody252_249

def sourceBody252_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_241 sourceBody252_250

def sourceBody252_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_177 sourceBody252_251

def sourceBody252_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_240 sourceBody252_252

def sourceBody252_254 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 60,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 80)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
        (Flapjack.WordLangExpHOL.const 24#64)])

def sourceBody252_255 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody252_256 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 28 (Flapjack.WordLangAddr.addr 28 0#64))

def sourceBody252_257 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 40#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody252_258 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 68 (Flapjack.WordLangAddr.addr 68 0#64))

def sourceBody252_259 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 40#64, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody252_260 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 20 (Flapjack.WordLangAddr.addr 20 0#64))

def sourceBody252_261 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 40#64, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody252_262 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 58 (Flapjack.WordLangAddr.addr 58 0#64))

def sourceBody252_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_262 sourceBody252_8

def sourceBody252_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_261 sourceBody252_263

def sourceBody252_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_260 sourceBody252_264

def sourceBody252_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_259 sourceBody252_265

def sourceBody252_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_258 sourceBody252_266

def sourceBody252_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_257 sourceBody252_267

def sourceBody252_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_256 sourceBody252_268

def sourceBody252_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_255 sourceBody252_269

def sourceBody252_271 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 28,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 68)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 20)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 58)
        (Flapjack.WordLangExpHOL.const 24#64)])

def sourceBody252_272 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody252_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 22)

def sourceBody252_274 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 14)

def sourceBody252_275 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 78) 52

def sourceBody252_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_275 sourceBody252_8

def sourceBody252_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_274 sourceBody252_276

def sourceBody252_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_277 sourceBody252_8

def sourceBody252_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_273 sourceBody252_278

def sourceBody252_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_279

def sourceBody252_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_272 sourceBody252_280

def sourceBody252_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_281

def sourceBody252_283 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 112#64]),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody252_284 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 46)

def sourceBody252_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_284 sourceBody252_278

def sourceBody252_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_285

def sourceBody252_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_283 sourceBody252_286

def sourceBody252_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_287

def sourceBody252_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_282 sourceBody252_288

def sourceBody252_290 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 112#64]),
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody252_291 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 38)

def sourceBody252_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_291 sourceBody252_278

def sourceBody252_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_292

def sourceBody252_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_290 sourceBody252_293

def sourceBody252_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_294

def sourceBody252_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_289 sourceBody252_295

def sourceBody252_297 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody252_298 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody252_299 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 44#64)

def sourceBody252_300 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 74)

def sourceBody252_301 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody252_302 : WordLangProgHOL (BitVec 64) :=
.call (some (([78]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody252_8, 252, 14)) (some 246) ([14, 52, 32, 72]) (some (14, sourceBody252_301, 252, 15))

def sourceBody252_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_302 sourceBody252_5

def sourceBody252_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_303 sourceBody252_8

def sourceBody252_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_300 sourceBody252_304

def sourceBody252_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_299 sourceBody252_305

def sourceBody252_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_298 sourceBody252_306

def sourceBody252_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_297 sourceBody252_307

def sourceBody252_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_308

def sourceBody252_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_309

def sourceBody252_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_296 sourceBody252_310

def sourceBody252_312 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.var 22])

def sourceBody252_313 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 46, Flapjack.WordLangExpHOL.var 22])

def sourceBody252_314 : WordLangProgHOL (BitVec 64) :=
.call (some (([78]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody252_8, 252, 16)) (some 249) ([14, 52]) (some (14, sourceBody252_301, 252, 17))

def sourceBody252_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_314 sourceBody252_5

def sourceBody252_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_315 sourceBody252_8

def sourceBody252_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_313 sourceBody252_316

def sourceBody252_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_312 sourceBody252_317

def sourceBody252_319 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 54, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody252_320 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 78)

def sourceBody252_321 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 52)

def sourceBody252_322 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 14) 32

def sourceBody252_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_322 sourceBody252_8

def sourceBody252_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_321 sourceBody252_323

def sourceBody252_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_324 sourceBody252_8

def sourceBody252_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_320 sourceBody252_325

def sourceBody252_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_326

def sourceBody252_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_319 sourceBody252_327

def sourceBody252_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_328

def sourceBody252_330 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.var 46])

def sourceBody252_331 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody252_332 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.const 9223372036854775807#64)

def sourceBody252_333 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 52

def sourceBody252_334 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody252_8, 252, 18)) (some 248) ([52, 32, 72]) (some (52, sourceBody252_333, 252, 19))

def sourceBody252_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_334 sourceBody252_5

def sourceBody252_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_335 sourceBody252_8

def sourceBody252_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_332 sourceBody252_336

def sourceBody252_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_331 sourceBody252_337

def sourceBody252_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_330 sourceBody252_338

def sourceBody252_340 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 54, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody252_341 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.var 46])

def sourceBody252_342 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 32)

def sourceBody252_343 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 52) 72

def sourceBody252_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_343 sourceBody252_8

def sourceBody252_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_342 sourceBody252_344

def sourceBody252_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_345 sourceBody252_8

def sourceBody252_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_341 sourceBody252_346

def sourceBody252_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_347

def sourceBody252_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_340 sourceBody252_348

def sourceBody252_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_349

def sourceBody252_351 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 54, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody252_352 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 14)

def sourceBody252_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_352 sourceBody252_346

def sourceBody252_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_353

def sourceBody252_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_351 sourceBody252_354

def sourceBody252_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_355

def sourceBody252_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_350 sourceBody252_356

def sourceBody252_358 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 54, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody252_359 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody252_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_359 sourceBody252_346

def sourceBody252_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_360

def sourceBody252_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_358 sourceBody252_361

def sourceBody252_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_362

def sourceBody252_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_357 sourceBody252_363

def sourceBody252_365 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.var 38])

def sourceBody252_366 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 74, Flapjack.WordLangExpHOL.var 38])

def sourceBody252_367 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody252_368 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody252_8, 252, 20)) (some 250) ([32, 72]) (some (32, sourceBody252_367, 252, 21))

def sourceBody252_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_368 sourceBody252_5

def sourceBody252_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_369 sourceBody252_8

def sourceBody252_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_366 sourceBody252_370

def sourceBody252_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_365 sourceBody252_371

def sourceBody252_373 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 54, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody252_374 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 52)

def sourceBody252_375 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 72)

def sourceBody252_376 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 32) 24

def sourceBody252_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_376 sourceBody252_8

def sourceBody252_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_375 sourceBody252_377

def sourceBody252_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_378 sourceBody252_8

def sourceBody252_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_374 sourceBody252_379

def sourceBody252_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_380

def sourceBody252_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_373 sourceBody252_381

def sourceBody252_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_382

def sourceBody252_384 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 16])

def sourceBody252_385 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 16])

def sourceBody252_386 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 72)

def sourceBody252_387 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody252_388 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody252_389 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody252_390 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 62 (Flapjack.WordRegImm.reg 42) sourceBody252_388 sourceBody252_389

def sourceBody252_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_390 sourceBody252_5

def sourceBody252_392 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.var 62)

def sourceBody252_393 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 82#64)

def sourceBody252_394 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 62

def sourceBody252_395 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody252_8, 252, 22)) (some 245) ([62]) (some (62, sourceBody252_394, 252, 23))

def sourceBody252_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_395 sourceBody252_5

def sourceBody252_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_396 sourceBody252_8

def sourceBody252_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_393 sourceBody252_397

def sourceBody252_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_398

def sourceBody252_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_399

def sourceBody252_401 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 82 (Flapjack.WordRegImm.imm 0#64) sourceBody252_400 sourceBody252_8

def sourceBody252_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_401 sourceBody252_5

def sourceBody252_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_402 sourceBody252_8

def sourceBody252_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_392 sourceBody252_403

def sourceBody252_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_391 sourceBody252_404

def sourceBody252_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_387 sourceBody252_405

def sourceBody252_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_386 sourceBody252_406

def sourceBody252_408 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody252_409 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 24)

def sourceBody252_410 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody252_411 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody252_412 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody252_413 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 42 (Flapjack.WordRegImm.reg 82) sourceBody252_411 sourceBody252_412

def sourceBody252_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_413 sourceBody252_5

def sourceBody252_415 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 42)

def sourceBody252_416 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 112#64]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody252_417 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 32,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
        (Flapjack.WordLangExpHOL.const 2#64)])

def sourceBody252_418 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 42 (Flapjack.WordLangAddr.addr 42 0#64))

def sourceBody252_419 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 32,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
        (Flapjack.WordLangExpHOL.const 2#64),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody252_420 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 82 (Flapjack.WordLangAddr.addr 82 0#64))

def sourceBody252_421 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 32,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
        (Flapjack.WordLangExpHOL.const 2#64),
      Flapjack.WordLangExpHOL.const 2#64])

def sourceBody252_422 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 6 (Flapjack.WordLangAddr.addr 6 0#64))

def sourceBody252_423 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 32,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
        (Flapjack.WordLangExpHOL.const 2#64),
      Flapjack.WordLangExpHOL.const 3#64])

def sourceBody252_424 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 44 (Flapjack.WordLangAddr.addr 44 0#64))

def sourceBody252_425 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_424 sourceBody252_8

def sourceBody252_426 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_423 sourceBody252_425

def sourceBody252_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_422 sourceBody252_426

def sourceBody252_428 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_421 sourceBody252_427

def sourceBody252_429 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_420 sourceBody252_428

def sourceBody252_430 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_419 sourceBody252_429

def sourceBody252_431 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_418 sourceBody252_430

def sourceBody252_432 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_417 sourceBody252_431

def sourceBody252_433 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 42,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 82)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 6)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 44)
        (Flapjack.WordLangExpHOL.const 24#64)])

def sourceBody252_434 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 26)

def sourceBody252_435 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 62) 66

def sourceBody252_436 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_435 sourceBody252_8

def sourceBody252_437 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_434 sourceBody252_436

def sourceBody252_438 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_437 sourceBody252_8

def sourceBody252_439 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_433 sourceBody252_438

def sourceBody252_440 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_432 sourceBody252_439

def sourceBody252_441 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_416 sourceBody252_440

def sourceBody252_442 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_441

def sourceBody252_443 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody252_444 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 62)

def sourceBody252_445 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_444 sourceBody252_8

def sourceBody252_446 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_445 sourceBody252_8

def sourceBody252_447 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_443 sourceBody252_446

def sourceBody252_448 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_447

def sourceBody252_449 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_442 sourceBody252_448

def sourceBody252_450 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody252_451 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_449 sourceBody252_450

def sourceBody252_452 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody252_453 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody252_451 sourceBody252_452

def sourceBody252_454 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_453 sourceBody252_5

def sourceBody252_455 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_454 sourceBody252_8

def sourceBody252_456 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_415 sourceBody252_455

def sourceBody252_457 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_414 sourceBody252_456

def sourceBody252_458 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_410 sourceBody252_457

def sourceBody252_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_409 sourceBody252_458

def sourceBody252_460 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
  PUnit.unit Flapjack.Spt.ln) sourceBody252_459 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody252_461 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_460 sourceBody252_5

def sourceBody252_462 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_5 sourceBody252_461

def sourceBody252_463 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody252_464 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody252_465 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 72)

def sourceBody252_466 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody252_467 : WordLangProgHOL (BitVec 64) :=
.call (some (([62]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody252_8, 252, 24)) (some 246) ([42, 82, 6, 44]) (some (42, sourceBody252_466, 252, 25))

def sourceBody252_468 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_467 sourceBody252_5

def sourceBody252_469 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_468 sourceBody252_8

def sourceBody252_470 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_465 sourceBody252_469

def sourceBody252_471 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_464 sourceBody252_470

def sourceBody252_472 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_410 sourceBody252_471

def sourceBody252_473 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_463 sourceBody252_472

def sourceBody252_474 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_473

def sourceBody252_475 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_474

def sourceBody252_476 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_462 sourceBody252_475

def sourceBody252_477 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.load
      (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
        [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
              Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
          Flapjack.WordLangExpHOL.const 112#64])))

def sourceBody252_478 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 112#64]),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody252_479 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 112#64]),
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody252_480 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.var 62])

def sourceBody252_481 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.var 62])

def sourceBody252_482 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 9223372036854775807#64)

def sourceBody252_483 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 1024#64)

def sourceBody252_484 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody252_485 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody252_8, 252, 26)) (some 251) ([26, 66, 18, 56]) (some (26, sourceBody252_484, 252, 27))

def sourceBody252_486 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_485 sourceBody252_5

def sourceBody252_487 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_486 sourceBody252_8

def sourceBody252_488 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_483 sourceBody252_487

def sourceBody252_489 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_482 sourceBody252_488

def sourceBody252_490 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_481 sourceBody252_489

def sourceBody252_491 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_480 sourceBody252_490

def sourceBody252_492 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 54, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody252_493 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 6)

def sourceBody252_494 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 66)

def sourceBody252_495 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 26) 18

def sourceBody252_496 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_495 sourceBody252_8

def sourceBody252_497 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_494 sourceBody252_496

def sourceBody252_498 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_497 sourceBody252_8

def sourceBody252_499 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_493 sourceBody252_498

def sourceBody252_500 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_499

def sourceBody252_501 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_492 sourceBody252_500

def sourceBody252_502 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_501

def sourceBody252_503 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 54, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody252_504 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 44)

def sourceBody252_505 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_504 sourceBody252_498

def sourceBody252_506 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_505

def sourceBody252_507 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_503 sourceBody252_506

def sourceBody252_508 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_507

def sourceBody252_509 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_502 sourceBody252_508

def sourceBody252_510 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.var 42])

def sourceBody252_511 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 82, Flapjack.WordLangExpHOL.var 42])

def sourceBody252_512 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 9223372036854775807#64)

def sourceBody252_513 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.const 65536#64)

def sourceBody252_514 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody252_515 : WordLangProgHOL (BitVec 64) :=
.call (some (([26, 66]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody252_8, 252, 28)) (some 251) ([18, 56, 36, 76]) (some (18, sourceBody252_514, 252, 29))

def sourceBody252_516 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_515 sourceBody252_5

def sourceBody252_517 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_516 sourceBody252_8

def sourceBody252_518 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_513 sourceBody252_517

def sourceBody252_519 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_512 sourceBody252_518

def sourceBody252_520 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_511 sourceBody252_519

def sourceBody252_521 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_510 sourceBody252_520

def sourceBody252_522 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 54, Flapjack.WordLangExpHOL.const 56#64])

def sourceBody252_523 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 26)

def sourceBody252_524 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 56)

def sourceBody252_525 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 18) 36

def sourceBody252_526 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_525 sourceBody252_8

def sourceBody252_527 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_524 sourceBody252_526

def sourceBody252_528 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_527 sourceBody252_8

def sourceBody252_529 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_523 sourceBody252_528

def sourceBody252_530 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_529

def sourceBody252_531 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_522 sourceBody252_530

def sourceBody252_532 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_531

def sourceBody252_533 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 54, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody252_534 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 66)

def sourceBody252_535 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_534 sourceBody252_528

def sourceBody252_536 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_535

def sourceBody252_537 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_533 sourceBody252_536

def sourceBody252_538 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_537

def sourceBody252_539 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_532 sourceBody252_538

def sourceBody252_540 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.var 82])

def sourceBody252_541 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 72, Flapjack.WordLangExpHOL.var 82])

def sourceBody252_542 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 256#64)

def sourceBody252_543 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 1024#64)

def sourceBody252_544 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody252_545 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 56]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody252_8, 252, 30)) (some 251) ([36, 76, 12, 50]) (some (36, sourceBody252_544, 252, 31))

def sourceBody252_546 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_545 sourceBody252_5

def sourceBody252_547 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_546 sourceBody252_8

def sourceBody252_548 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_543 sourceBody252_547

def sourceBody252_549 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_542 sourceBody252_548

def sourceBody252_550 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_541 sourceBody252_549

def sourceBody252_551 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_540 sourceBody252_550

def sourceBody252_552 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 54, Flapjack.WordLangExpHOL.const 72#64])

def sourceBody252_553 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 18)

def sourceBody252_554 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 76)

def sourceBody252_555 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 36) 12

def sourceBody252_556 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_555 sourceBody252_8

def sourceBody252_557 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_554 sourceBody252_556

def sourceBody252_558 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_557 sourceBody252_8

def sourceBody252_559 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_553 sourceBody252_558

def sourceBody252_560 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_559

def sourceBody252_561 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_552 sourceBody252_560

def sourceBody252_562 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_561

def sourceBody252_563 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 54, Flapjack.WordLangExpHOL.const 80#64])

def sourceBody252_564 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76 (Flapjack.WordLangExpHOL.var 56)

def sourceBody252_565 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_564 sourceBody252_558

def sourceBody252_566 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_565

def sourceBody252_567 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_563 sourceBody252_566

def sourceBody252_568 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_567

def sourceBody252_569 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_562 sourceBody252_568

def sourceBody252_570 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 54)

def sourceBody252_571 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [36]

def sourceBody252_572 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_571 sourceBody252_8

def sourceBody252_573 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_570 sourceBody252_572

def sourceBody252_574 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_569 sourceBody252_573

def sourceBody252_575 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_551 sourceBody252_574

def sourceBody252_576 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_575

def sourceBody252_577 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_576

def sourceBody252_578 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_577

def sourceBody252_579 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_578

def sourceBody252_580 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_539 sourceBody252_579

def sourceBody252_581 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_521 sourceBody252_580

def sourceBody252_582 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_581

def sourceBody252_583 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_582

def sourceBody252_584 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_583

def sourceBody252_585 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_584

def sourceBody252_586 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_509 sourceBody252_585

def sourceBody252_587 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_491 sourceBody252_586

def sourceBody252_588 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_587

def sourceBody252_589 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_588

def sourceBody252_590 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_589

def sourceBody252_591 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_590

def sourceBody252_592 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_479 sourceBody252_591

def sourceBody252_593 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_592

def sourceBody252_594 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_478 sourceBody252_593

def sourceBody252_595 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_594

def sourceBody252_596 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_477 sourceBody252_595

def sourceBody252_597 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_596

def sourceBody252_598 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_476 sourceBody252_597

def sourceBody252_599 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_408 sourceBody252_598

def sourceBody252_600 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_599

def sourceBody252_601 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_407 sourceBody252_600

def sourceBody252_602 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_385 sourceBody252_601

def sourceBody252_603 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_602

def sourceBody252_604 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_384 sourceBody252_603

def sourceBody252_605 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_604

def sourceBody252_606 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_383 sourceBody252_605

def sourceBody252_607 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_372 sourceBody252_606

def sourceBody252_608 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_607

def sourceBody252_609 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_608

def sourceBody252_610 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_364 sourceBody252_609

def sourceBody252_611 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_339 sourceBody252_610

def sourceBody252_612 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_611

def sourceBody252_613 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_612

def sourceBody252_614 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_329 sourceBody252_613

def sourceBody252_615 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_318 sourceBody252_614

def sourceBody252_616 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_615

def sourceBody252_617 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_616

def sourceBody252_618 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_311 sourceBody252_617

def sourceBody252_619 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_271 sourceBody252_618

def sourceBody252_620 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_270 sourceBody252_619

def sourceBody252_621 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_254 sourceBody252_620

def sourceBody252_622 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_253 sourceBody252_621

def sourceBody252_623 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_239 sourceBody252_622

def sourceBody252_624 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_238 sourceBody252_623

def sourceBody252_625 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_226 sourceBody252_624

def sourceBody252_626 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_207 sourceBody252_625

def sourceBody252_627 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_626

def sourceBody252_628 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_206 sourceBody252_627

def sourceBody252_629 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_628

def sourceBody252_630 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_205 sourceBody252_629

def sourceBody252_631 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_163 sourceBody252_630

def sourceBody252_632 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_631

def sourceBody252_633 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_632

def sourceBody252_634 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_157 sourceBody252_633

def sourceBody252_635 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_634

def sourceBody252_636 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_156 sourceBody252_635

def sourceBody252_637 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_8 sourceBody252_636

def sourceBody252_638 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody252_155 sourceBody252_637

def source252 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (252, 3, sourceBody252_638)
end InitECandidate.Proofs.WordStages
