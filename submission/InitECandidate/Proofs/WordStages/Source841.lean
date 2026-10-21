import InitECandidate.Proofs.WordStages.Source825
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody841_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody841_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody841_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody841_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody841_0, 841, 2)) (some 68) ([24]) (some (24, sourceBody841_2, 841, 3))

def sourceBody841_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody841_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_3 sourceBody841_4

def sourceBody841_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_5 sourceBody841_0

def sourceBody841_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_1 sourceBody841_6

def sourceBody841_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 9#64])

def sourceBody841_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody841_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 20 (Flapjack.WordLangAddr.addr 20 0#64))

def sourceBody841_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody841_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 14 (Flapjack.WordLangAddr.addr 14 0#64))

def sourceBody841_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody841_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 28 (Flapjack.WordLangAddr.addr 28 0#64))

def sourceBody841_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody841_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 4 (Flapjack.WordLangAddr.addr 4 0#64))

def sourceBody841_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 4#64])

def sourceBody841_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 18 (Flapjack.WordLangAddr.addr 18 0#64))

def sourceBody841_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody841_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 12 (Flapjack.WordLangAddr.addr 12 0#64))

def sourceBody841_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody841_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 26 (Flapjack.WordLangAddr.addr 26 0#64))

def sourceBody841_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 4#64, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody841_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 8 (Flapjack.WordLangAddr.addr 8 0#64))

def sourceBody841_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 24)

def sourceBody841_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 20,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 28)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 24#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
          [Flapjack.WordLangExpHOL.var 18,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
              (Flapjack.WordLangExpHOL.const 8#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 26)
              (Flapjack.WordLangExpHOL.const 16#64),
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
              (Flapjack.WordLangExpHOL.const 24#64)])
        (Flapjack.WordLangExpHOL.const 32#64)])

def sourceBody841_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody841_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody841_0, 841, 4)) (some 177) ([22, 16]) (some (20, sourceBody841_27, 841, 5))

def sourceBody841_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_28 sourceBody841_4

def sourceBody841_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_29 sourceBody841_0

def sourceBody841_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_26 sourceBody841_30

def sourceBody841_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_25 sourceBody841_31

def sourceBody841_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_24 sourceBody841_32

def sourceBody841_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_23 sourceBody841_33

def sourceBody841_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_22 sourceBody841_34

def sourceBody841_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_21 sourceBody841_35

def sourceBody841_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_20 sourceBody841_36

def sourceBody841_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_19 sourceBody841_37

def sourceBody841_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_18 sourceBody841_38

def sourceBody841_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_17 sourceBody841_39

def sourceBody841_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_16 sourceBody841_40

def sourceBody841_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_15 sourceBody841_41

def sourceBody841_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_14 sourceBody841_42

def sourceBody841_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_13 sourceBody841_43

def sourceBody841_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_12 sourceBody841_44

def sourceBody841_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_11 sourceBody841_45

def sourceBody841_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_10 sourceBody841_46

def sourceBody841_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_9 sourceBody841_47

def sourceBody841_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.var 6])

def sourceBody841_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 20)

def sourceBody841_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_50 sourceBody841_0

def sourceBody841_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_51 sourceBody841_0

def sourceBody841_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_49 sourceBody841_52

def sourceBody841_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_0 sourceBody841_53

def sourceBody841_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody841_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody841_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody841_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody841_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 4#64])

def sourceBody841_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody841_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 2#64])

def sourceBody841_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 3#64])

def sourceBody841_63 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody841_0, 841, 6)) (some 177) ([22, 16]) (some (20, sourceBody841_27, 841, 7))

def sourceBody841_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_63 sourceBody841_4

def sourceBody841_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_64 sourceBody841_0

def sourceBody841_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_26 sourceBody841_65

def sourceBody841_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_25 sourceBody841_66

def sourceBody841_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_24 sourceBody841_67

def sourceBody841_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_62 sourceBody841_68

def sourceBody841_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_22 sourceBody841_69

def sourceBody841_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_61 sourceBody841_70

def sourceBody841_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_20 sourceBody841_71

def sourceBody841_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_60 sourceBody841_72

def sourceBody841_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_18 sourceBody841_73

def sourceBody841_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_59 sourceBody841_74

def sourceBody841_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_16 sourceBody841_75

def sourceBody841_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_58 sourceBody841_76

def sourceBody841_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_14 sourceBody841_77

def sourceBody841_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_57 sourceBody841_78

def sourceBody841_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_12 sourceBody841_79

def sourceBody841_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_56 sourceBody841_80

def sourceBody841_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_10 sourceBody841_81

def sourceBody841_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_55 sourceBody841_82

def sourceBody841_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_54 sourceBody841_83

def sourceBody841_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_84 sourceBody841_54

def sourceBody841_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody841_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody841_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody841_89 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody841_0, 841, 8)) (some 176) ([20, 14, 28]) (some (20, sourceBody841_27, 841, 9))

def sourceBody841_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_89 sourceBody841_4

def sourceBody841_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_90 sourceBody841_0

def sourceBody841_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_88 sourceBody841_91

def sourceBody841_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_87 sourceBody841_92

def sourceBody841_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_86 sourceBody841_93

def sourceBody841_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_85 sourceBody841_94

def sourceBody841_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_95 sourceBody841_54

def sourceBody841_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 36#64])

def sourceBody841_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody841_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody841_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody841_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 4#64])

def sourceBody841_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody841_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 2#64])

def sourceBody841_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 36#64, Flapjack.WordLangExpHOL.const 4#64,
      Flapjack.WordLangExpHOL.const 3#64])

def sourceBody841_105 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody841_0, 841, 10)) (some 177) ([22, 16]) (some (20, sourceBody841_27, 841, 11))

def sourceBody841_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_105 sourceBody841_4

def sourceBody841_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_106 sourceBody841_0

def sourceBody841_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_26 sourceBody841_107

def sourceBody841_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_25 sourceBody841_108

def sourceBody841_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_24 sourceBody841_109

def sourceBody841_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_104 sourceBody841_110

def sourceBody841_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_22 sourceBody841_111

def sourceBody841_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_103 sourceBody841_112

def sourceBody841_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_20 sourceBody841_113

def sourceBody841_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_102 sourceBody841_114

def sourceBody841_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_18 sourceBody841_115

def sourceBody841_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_101 sourceBody841_116

def sourceBody841_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_16 sourceBody841_117

def sourceBody841_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_100 sourceBody841_118

def sourceBody841_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_14 sourceBody841_119

def sourceBody841_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_99 sourceBody841_120

def sourceBody841_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_12 sourceBody841_121

def sourceBody841_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_98 sourceBody841_122

def sourceBody841_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_10 sourceBody841_123

def sourceBody841_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_97 sourceBody841_124

def sourceBody841_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_96 sourceBody841_125

def sourceBody841_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_126 sourceBody841_54

def sourceBody841_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody841_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 24)

def sourceBody841_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody841_131 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody841_0, 841, 12)) (some 836) ([14, 28]) (some (14, sourceBody841_130, 841, 13))

def sourceBody841_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_131 sourceBody841_4

def sourceBody841_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_132 sourceBody841_0

def sourceBody841_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_129 sourceBody841_133

def sourceBody841_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_128 sourceBody841_134

def sourceBody841_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 20)

def sourceBody841_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14, 28]

def sourceBody841_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_137 sourceBody841_0

def sourceBody841_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_136 sourceBody841_138

def sourceBody841_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_128 sourceBody841_139

def sourceBody841_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_135 sourceBody841_140

def sourceBody841_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_0 sourceBody841_141

def sourceBody841_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_0 sourceBody841_142

def sourceBody841_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_127 sourceBody841_143

def sourceBody841_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_48 sourceBody841_144

def sourceBody841_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_0 sourceBody841_145

def sourceBody841_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_0 sourceBody841_146

def sourceBody841_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_8 sourceBody841_147

def sourceBody841_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_0 sourceBody841_148

def sourceBody841_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_7 sourceBody841_149

def sourceBody841_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_0 sourceBody841_150

def sourceBody841_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody841_0 sourceBody841_151

def source841 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (841, 2, sourceBody841_152)
end InitECandidate.Proofs.WordStages
