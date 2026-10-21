import InitECandidate.Proofs.WordStages.Source814
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody830_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody830_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
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
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody830_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody830_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 58)

def sourceBody830_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 213#64)

def sourceBody830_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody830_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody830_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.reg 30) sourceBody830_5 sourceBody830_6

def sourceBody830_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody830_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_7 sourceBody830_8

def sourceBody830_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 48)

def sourceBody830_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody830_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 10)

def sourceBody830_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_12 sourceBody830_0

def sourceBody830_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_13 sourceBody830_0

def sourceBody830_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_11 sourceBody830_14

def sourceBody830_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_15

def sourceBody830_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody830_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody830_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_17 sourceBody830_18

def sourceBody830_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_16 sourceBody830_19

def sourceBody830_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 68 (Flapjack.WordRegImm.imm 0#64) sourceBody830_20 sourceBody830_0

def sourceBody830_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_21 sourceBody830_8

def sourceBody830_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_22 sourceBody830_0

def sourceBody830_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_10 sourceBody830_23

def sourceBody830_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_9 sourceBody830_24

def sourceBody830_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_4 sourceBody830_25

def sourceBody830_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_3 sourceBody830_26

def sourceBody830_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody830_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 10)

def sourceBody830_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 48 (Flapjack.WordLangAddr.addr 48 0#64))

def sourceBody830_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody830_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 30 (Flapjack.WordLangAddr.addr 30 0#64))

def sourceBody830_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody830_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 68 (Flapjack.WordLangAddr.addr 68 0#64))

def sourceBody830_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody830_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 6 (Flapjack.WordLangAddr.addr 6 0#64))

def sourceBody830_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_36 sourceBody830_0

def sourceBody830_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_35 sourceBody830_37

def sourceBody830_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_34 sourceBody830_38

def sourceBody830_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_33 sourceBody830_39

def sourceBody830_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_32 sourceBody830_40

def sourceBody830_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_31 sourceBody830_41

def sourceBody830_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_30 sourceBody830_42

def sourceBody830_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_29 sourceBody830_43

def sourceBody830_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 48)
        (Flapjack.WordLangExpHOL.const 24#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 30)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 68)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.var 6])

def sourceBody830_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 212#64])

def sourceBody830_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 26 (Flapjack.WordLangAddr.addr 26 0#64))

def sourceBody830_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_47 sourceBody830_0

def sourceBody830_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_46 sourceBody830_48

def sourceBody830_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 26)

def sourceBody830_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 44)

def sourceBody830_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 54

def sourceBody830_53 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody830_0, 830, 2)) (some 466) ([54]) (some (54, sourceBody830_52, 830, 3))

def sourceBody830_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_53 sourceBody830_8

def sourceBody830_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_54 sourceBody830_0

def sourceBody830_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_51 sourceBody830_55

def sourceBody830_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_56

def sourceBody830_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_57

def sourceBody830_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody830_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 64)

def sourceBody830_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody830_62 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 54 (Flapjack.WordRegImm.reg 36) sourceBody830_59 sourceBody830_61

def sourceBody830_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_62 sourceBody830_8

def sourceBody830_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 54)

def sourceBody830_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody830_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 16)

def sourceBody830_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_66 sourceBody830_0

def sourceBody830_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_67 sourceBody830_0

def sourceBody830_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_65 sourceBody830_68

def sourceBody830_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_69

def sourceBody830_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody830_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody830_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_71 sourceBody830_72

def sourceBody830_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_70 sourceBody830_73

def sourceBody830_75 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 74 (Flapjack.WordRegImm.imm 0#64) sourceBody830_74 sourceBody830_0

def sourceBody830_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_75 sourceBody830_8

def sourceBody830_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_76 sourceBody830_0

def sourceBody830_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_64 sourceBody830_77

def sourceBody830_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_63 sourceBody830_78

def sourceBody830_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_60 sourceBody830_79

def sourceBody830_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_59 sourceBody830_80

def sourceBody830_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_58 sourceBody830_81

def sourceBody830_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody830_84 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody830_0, 830, 4)) (some 68) ([54]) (some (54, sourceBody830_52, 830, 5))

def sourceBody830_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_84 sourceBody830_8

def sourceBody830_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_85 sourceBody830_0

def sourceBody830_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_83 sourceBody830_86

def sourceBody830_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody830_89 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody830_0, 830, 6)) (some 69) ([]) (some (36, sourceBody830_88, 830, 7))

def sourceBody830_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_89 sourceBody830_8

def sourceBody830_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_90 sourceBody830_0

def sourceBody830_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody830_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 74

def sourceBody830_94 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody830_0, 830, 8)) (some 68) ([74]) (some (74, sourceBody830_93, 830, 9))

def sourceBody830_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_94 sourceBody830_8

def sourceBody830_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_95 sourceBody830_0

def sourceBody830_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_92 sourceBody830_96

def sourceBody830_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody830_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody830_100 : WordLangProgHOL (BitVec 64) :=
.call (some (([74]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody830_0, 830, 10)) (some 68) ([4]) (some (4, sourceBody830_99, 830, 11))

def sourceBody830_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_100 sourceBody830_8

def sourceBody830_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_101 sourceBody830_0

def sourceBody830_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_98 sourceBody830_102

def sourceBody830_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody830_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody830_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody830_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody830_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody830_109 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 24 (Flapjack.WordRegImm.reg 62) sourceBody830_107 sourceBody830_108

def sourceBody830_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_109 sourceBody830_8

def sourceBody830_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 24)

def sourceBody830_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 36,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody830_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody830_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 24 (Flapjack.WordLangAddr.addr 24 0#64))

def sourceBody830_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody830_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 62 (Flapjack.WordLangAddr.addr 62 0#64))

def sourceBody830_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 2#64])

def sourceBody830_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 14 (Flapjack.WordLangAddr.addr 14 0#64))

def sourceBody830_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 3#64])

def sourceBody830_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 52 (Flapjack.WordLangAddr.addr 52 0#64))

def sourceBody830_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 4#64])

def sourceBody830_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 34 (Flapjack.WordLangAddr.addr 34 0#64))

def sourceBody830_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody830_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 72 (Flapjack.WordLangAddr.addr 72 0#64))

def sourceBody830_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody830_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 8 (Flapjack.WordLangAddr.addr 8 0#64))

def sourceBody830_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody830_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 46 (Flapjack.WordLangAddr.addr 46 0#64))

def sourceBody830_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_128 sourceBody830_0

def sourceBody830_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_127 sourceBody830_129

def sourceBody830_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_126 sourceBody830_130

def sourceBody830_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_125 sourceBody830_131

def sourceBody830_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_124 sourceBody830_132

def sourceBody830_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_123 sourceBody830_133

def sourceBody830_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_122 sourceBody830_134

def sourceBody830_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_121 sourceBody830_135

def sourceBody830_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_120 sourceBody830_136

def sourceBody830_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_119 sourceBody830_137

def sourceBody830_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_118 sourceBody830_138

def sourceBody830_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_117 sourceBody830_139

def sourceBody830_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_116 sourceBody830_140

def sourceBody830_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_115 sourceBody830_141

def sourceBody830_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_114 sourceBody830_142

def sourceBody830_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_113 sourceBody830_143

def sourceBody830_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 24,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 62)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 52)
        (Flapjack.WordLangExpHOL.const 24#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
          [Flapjack.WordLangExpHOL.var 34,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 72)
              (Flapjack.WordLangExpHOL.const 8#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
              (Flapjack.WordLangExpHOL.const 16#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 46)
              (Flapjack.WordLangExpHOL.const 24#64)])
        (Flapjack.WordLangExpHOL.const 32#64)])

def sourceBody830_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 28)

def sourceBody830_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 42) 66

def sourceBody830_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_147 sourceBody830_0

def sourceBody830_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_146 sourceBody830_148

def sourceBody830_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_149 sourceBody830_0

def sourceBody830_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_145 sourceBody830_150

def sourceBody830_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_144 sourceBody830_151

def sourceBody830_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_112 sourceBody830_152

def sourceBody830_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_153

def sourceBody830_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody830_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 42)

def sourceBody830_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_156 sourceBody830_0

def sourceBody830_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_157 sourceBody830_0

def sourceBody830_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_155 sourceBody830_158

def sourceBody830_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_159

def sourceBody830_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_154 sourceBody830_160

def sourceBody830_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody830_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_161 sourceBody830_162

def sourceBody830_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody830_165 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody830_163 sourceBody830_164

def sourceBody830_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_165 sourceBody830_8

def sourceBody830_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_166 sourceBody830_0

def sourceBody830_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_111 sourceBody830_167

def sourceBody830_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_110 sourceBody830_168

def sourceBody830_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_106 sourceBody830_169

def sourceBody830_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_105 sourceBody830_170

def sourceBody830_172 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln))
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
  PUnit.unit Flapjack.Spt.ln) sourceBody830_171 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln))
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody830_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_172 sourceBody830_8

def sourceBody830_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_8 sourceBody830_173

def sourceBody830_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_104 sourceBody830_0

def sourceBody830_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_175 sourceBody830_0

def sourceBody830_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_174 sourceBody830_176

def sourceBody830_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody830_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 74,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody830_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 68#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody830_181 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 68#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody830_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 68#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 2#64])

def sourceBody830_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 68#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 3#64])

def sourceBody830_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 68#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 4#64])

def sourceBody830_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 68#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody830_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 68#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody830_187 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 68#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody830_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_187 sourceBody830_129

def sourceBody830_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_126 sourceBody830_188

def sourceBody830_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_186 sourceBody830_189

def sourceBody830_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_124 sourceBody830_190

def sourceBody830_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_185 sourceBody830_191

def sourceBody830_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_122 sourceBody830_192

def sourceBody830_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_184 sourceBody830_193

def sourceBody830_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_120 sourceBody830_194

def sourceBody830_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_183 sourceBody830_195

def sourceBody830_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_118 sourceBody830_196

def sourceBody830_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_182 sourceBody830_197

def sourceBody830_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_116 sourceBody830_198

def sourceBody830_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_181 sourceBody830_199

def sourceBody830_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_114 sourceBody830_200

def sourceBody830_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_180 sourceBody830_201

def sourceBody830_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_202 sourceBody830_151

def sourceBody830_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_179 sourceBody830_203

def sourceBody830_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_204

def sourceBody830_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_205 sourceBody830_160

def sourceBody830_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_206 sourceBody830_162

def sourceBody830_208 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody830_207 sourceBody830_164

def sourceBody830_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_208 sourceBody830_8

def sourceBody830_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_209 sourceBody830_0

def sourceBody830_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_111 sourceBody830_210

def sourceBody830_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_110 sourceBody830_211

def sourceBody830_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_178 sourceBody830_212

def sourceBody830_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_105 sourceBody830_213

def sourceBody830_215 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln))
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
  PUnit.unit Flapjack.Spt.ln) sourceBody830_214 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln))
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody830_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_215 sourceBody830_8

def sourceBody830_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_8 sourceBody830_216

def sourceBody830_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_177 sourceBody830_217

def sourceBody830_219 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 196#64])

def sourceBody830_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 196#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody830_221 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 196#64, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody830_222 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 196#64, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody830_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 196#64, Flapjack.WordLangExpHOL.const 4#64])

def sourceBody830_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 196#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody830_225 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 196#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 2#64])

def sourceBody830_226 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 196#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 3#64])

def sourceBody830_227 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 204#64])

def sourceBody830_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 28 (Flapjack.WordLangAddr.addr 28 0#64))

def sourceBody830_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 204#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody830_230 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 66 (Flapjack.WordLangAddr.addr 66 0#64))

def sourceBody830_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 204#64, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody830_232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 18 (Flapjack.WordLangAddr.addr 18 0#64))

def sourceBody830_233 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 204#64, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody830_234 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 56 (Flapjack.WordLangAddr.addr 56 0#64))

def sourceBody830_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 204#64, Flapjack.WordLangExpHOL.const 4#64])

def sourceBody830_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 38 (Flapjack.WordLangAddr.addr 38 0#64))

def sourceBody830_237 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 204#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody830_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 76 (Flapjack.WordLangAddr.addr 76 0#64))

def sourceBody830_239 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 204#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 2#64])

def sourceBody830_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 2 (Flapjack.WordLangAddr.addr 2 0#64))

def sourceBody830_241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 204#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 3#64])

def sourceBody830_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 40 (Flapjack.WordLangAddr.addr 40 0#64))

def sourceBody830_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 44)

def sourceBody830_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 36)

def sourceBody830_245 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 74)

def sourceBody830_246 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 24,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 62)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 52)
        (Flapjack.WordLangExpHOL.const 24#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
          [Flapjack.WordLangExpHOL.var 34,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 72)
              (Flapjack.WordLangExpHOL.const 8#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
              (Flapjack.WordLangExpHOL.const 16#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 46)
              (Flapjack.WordLangExpHOL.const 24#64)])
        (Flapjack.WordLangExpHOL.const 32#64)])

def sourceBody830_247 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 28,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 66)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 18)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 56)
        (Flapjack.WordLangExpHOL.const 24#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
          [Flapjack.WordLangExpHOL.var 38,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 76)
              (Flapjack.WordLangExpHOL.const 8#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 2)
              (Flapjack.WordLangExpHOL.const 16#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
              (Flapjack.WordLangExpHOL.const 24#64)])
        (Flapjack.WordLangExpHOL.const 32#64)])

def sourceBody830_248 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 64)

def sourceBody830_249 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody830_250 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody830_0, 830, 12)) (some 630) ([22, 60, 12, 50, 32, 70]) (some (24, sourceBody830_249, 830, 13))

def sourceBody830_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_250 sourceBody830_8

def sourceBody830_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_251 sourceBody830_0

def sourceBody830_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_248 sourceBody830_252

def sourceBody830_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_247 sourceBody830_253

def sourceBody830_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_246 sourceBody830_254

def sourceBody830_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_245 sourceBody830_255

def sourceBody830_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_244 sourceBody830_256

def sourceBody830_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_243 sourceBody830_257

def sourceBody830_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_242 sourceBody830_258

def sourceBody830_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_241 sourceBody830_259

def sourceBody830_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_240 sourceBody830_260

def sourceBody830_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_239 sourceBody830_261

def sourceBody830_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_238 sourceBody830_262

def sourceBody830_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_237 sourceBody830_263

def sourceBody830_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_236 sourceBody830_264

def sourceBody830_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_235 sourceBody830_265

def sourceBody830_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_234 sourceBody830_266

def sourceBody830_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_233 sourceBody830_267

def sourceBody830_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_232 sourceBody830_268

def sourceBody830_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_231 sourceBody830_269

def sourceBody830_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_230 sourceBody830_270

def sourceBody830_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_229 sourceBody830_271

def sourceBody830_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_228 sourceBody830_272

def sourceBody830_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_227 sourceBody830_273

def sourceBody830_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_128 sourceBody830_274

def sourceBody830_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_226 sourceBody830_275

def sourceBody830_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_126 sourceBody830_276

def sourceBody830_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_225 sourceBody830_277

def sourceBody830_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_124 sourceBody830_278

def sourceBody830_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_224 sourceBody830_279

def sourceBody830_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_122 sourceBody830_280

def sourceBody830_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_223 sourceBody830_281

def sourceBody830_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_120 sourceBody830_282

def sourceBody830_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_222 sourceBody830_283

def sourceBody830_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_118 sourceBody830_284

def sourceBody830_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_221 sourceBody830_285

def sourceBody830_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_116 sourceBody830_286

def sourceBody830_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_220 sourceBody830_287

def sourceBody830_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_114 sourceBody830_288

def sourceBody830_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_219 sourceBody830_289

def sourceBody830_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_290

def sourceBody830_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_291

def sourceBody830_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_218 sourceBody830_292

def sourceBody830_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_293 sourceBody830_176

def sourceBody830_295 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 16,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody830_296 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 36,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody830_297 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody830_0, 830, 14)) (some 87) ([24, 62]) (some (24, sourceBody830_249, 830, 15))

def sourceBody830_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_297 sourceBody830_8

def sourceBody830_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_298 sourceBody830_0

def sourceBody830_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_296 sourceBody830_299

def sourceBody830_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_295 sourceBody830_300

def sourceBody830_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_301

def sourceBody830_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_302

def sourceBody830_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_303 sourceBody830_160

def sourceBody830_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_304 sourceBody830_162

def sourceBody830_306 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody830_305 sourceBody830_164

def sourceBody830_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_306 sourceBody830_8

def sourceBody830_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_307 sourceBody830_0

def sourceBody830_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_111 sourceBody830_308

def sourceBody830_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_110 sourceBody830_309

def sourceBody830_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_106 sourceBody830_310

def sourceBody830_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_105 sourceBody830_311

def sourceBody830_313 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln))
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
  PUnit.unit Flapjack.Spt.ln) sourceBody830_312 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody830_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_313 sourceBody830_8

def sourceBody830_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_8 sourceBody830_314

def sourceBody830_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_294 sourceBody830_315

def sourceBody830_317 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 54)

def sourceBody830_318 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody830_0, 830, 16)) (some 70) ([24]) (some (24, sourceBody830_249, 830, 17))

def sourceBody830_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_318 sourceBody830_8

def sourceBody830_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_319 sourceBody830_0

def sourceBody830_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_317 sourceBody830_320

def sourceBody830_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_321

def sourceBody830_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_322

def sourceBody830_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_316 sourceBody830_323

def sourceBody830_325 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 120#64])

def sourceBody830_326 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody830_327 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 24)

def sourceBody830_328 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 42) 62

def sourceBody830_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_328 sourceBody830_0

def sourceBody830_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_327 sourceBody830_329

def sourceBody830_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_330 sourceBody830_0

def sourceBody830_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_326 sourceBody830_331

def sourceBody830_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_332

def sourceBody830_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_325 sourceBody830_333

def sourceBody830_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_334

def sourceBody830_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_324 sourceBody830_335

def sourceBody830_337 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody830_338 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody830_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_338 sourceBody830_331

def sourceBody830_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_339

def sourceBody830_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_337 sourceBody830_340

def sourceBody830_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_341

def sourceBody830_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_336 sourceBody830_342

def sourceBody830_344 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody830_345 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [42]

def sourceBody830_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_345 sourceBody830_0

def sourceBody830_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_344 sourceBody830_346

def sourceBody830_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_343 sourceBody830_347

def sourceBody830_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_104 sourceBody830_348

def sourceBody830_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_349

def sourceBody830_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_103 sourceBody830_350

def sourceBody830_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_351

def sourceBody830_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_352

def sourceBody830_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_97 sourceBody830_353

def sourceBody830_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_354

def sourceBody830_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_355

def sourceBody830_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_91 sourceBody830_356

def sourceBody830_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_357

def sourceBody830_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_358

def sourceBody830_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_87 sourceBody830_359

def sourceBody830_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_360

def sourceBody830_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_361

def sourceBody830_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_82 sourceBody830_362

def sourceBody830_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_50 sourceBody830_363

def sourceBody830_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_49 sourceBody830_364

def sourceBody830_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_45 sourceBody830_365

def sourceBody830_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_44 sourceBody830_366

def sourceBody830_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_28 sourceBody830_367

def sourceBody830_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_368

def sourceBody830_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_27 sourceBody830_369

def sourceBody830_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_2 sourceBody830_370

def sourceBody830_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_371

def sourceBody830_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_1 sourceBody830_372

def sourceBody830_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody830_0 sourceBody830_373

def source830 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (830, 1, sourceBody830_374)
end InitECandidate.Proofs.WordStages
