import InitECandidate.Proofs.WordStages.Source621
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody637_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody637_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 48

def sourceBody637_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 2)) (some 69) ([]) (some (48, sourceBody637_1, 637, 3))

def sourceBody637_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody637_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_2 sourceBody637_3

def sourceBody637_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_4 sourceBody637_0

def sourceBody637_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 3#64])
    (Flapjack.WordLangExpHOL.const 2#64))

def sourceBody637_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 48)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody637_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 60

def sourceBody637_9 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 4)) (some 68) ([60]) (some (60, sourceBody637_8, 637, 5))

def sourceBody637_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_9 sourceBody637_3

def sourceBody637_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_10 sourceBody637_0

def sourceBody637_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_7 sourceBody637_11

def sourceBody637_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody637_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 12)

def sourceBody637_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 34)

def sourceBody637_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody637_17 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 6)) (some 631) ([26, 54, 40]) (some (26, sourceBody637_16, 637, 7))

def sourceBody637_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_17 sourceBody637_3

def sourceBody637_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_18 sourceBody637_0

def sourceBody637_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_15 sourceBody637_19

def sourceBody637_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_14 sourceBody637_20

def sourceBody637_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_13 sourceBody637_21

def sourceBody637_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_22

def sourceBody637_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_23

def sourceBody637_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 34)

def sourceBody637_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 48)

def sourceBody637_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 8)) (some 126) ([26, 54]) (some (26, sourceBody637_16, 637, 9))

def sourceBody637_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_27 sourceBody637_3

def sourceBody637_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_28 sourceBody637_0

def sourceBody637_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_26 sourceBody637_29

def sourceBody637_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_25 sourceBody637_30

def sourceBody637_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 60)

def sourceBody637_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody637_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody637_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody637_36 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 54 (Flapjack.WordRegImm.reg 40) sourceBody637_34 sourceBody637_35

def sourceBody637_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_36 sourceBody637_3

def sourceBody637_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 54)

def sourceBody637_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 14)

def sourceBody637_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 12)

def sourceBody637_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 54

def sourceBody637_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 10)) (some 78) ([54, 40]) (some (54, sourceBody637_41, 637, 11))

def sourceBody637_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_42 sourceBody637_3

def sourceBody637_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_43 sourceBody637_0

def sourceBody637_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_40 sourceBody637_44

def sourceBody637_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_39 sourceBody637_45

def sourceBody637_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_46

def sourceBody637_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_47

def sourceBody637_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 20)

def sourceBody637_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody637_0, 637, 12)) (some 70) ([54]) (some (54, sourceBody637_41, 637, 13))

def sourceBody637_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_50 sourceBody637_3

def sourceBody637_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_51 sourceBody637_0

def sourceBody637_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_49 sourceBody637_52

def sourceBody637_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_53

def sourceBody637_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_54

def sourceBody637_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_48 sourceBody637_55

def sourceBody637_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody637_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody637_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_58 sourceBody637_0

def sourceBody637_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_57 sourceBody637_59

def sourceBody637_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_56 sourceBody637_60

def sourceBody637_62 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 66 (Flapjack.WordRegImm.imm 0#64) sourceBody637_61 sourceBody637_0

def sourceBody637_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_62 sourceBody637_3

def sourceBody637_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_63 sourceBody637_0

def sourceBody637_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_38 sourceBody637_64

def sourceBody637_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_37 sourceBody637_65

def sourceBody637_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_33 sourceBody637_66

def sourceBody637_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_32 sourceBody637_67

def sourceBody637_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 3#64])
    (Flapjack.WordLangExpHOL.const 2#64))

def sourceBody637_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 26)

def sourceBody637_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 60)
    (Flapjack.WordLangExpHOL.const 1#64))

def sourceBody637_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody637_73 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 14)) (some 93) ([40, 66]) (some (40, sourceBody637_72, 637, 15))

def sourceBody637_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_73 sourceBody637_3

def sourceBody637_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_74 sourceBody637_0

def sourceBody637_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_71 sourceBody637_75

def sourceBody637_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_70 sourceBody637_76

def sourceBody637_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 54)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody637_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 66

def sourceBody637_80 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 16)) (some 68) ([66]) (some (66, sourceBody637_79, 637, 17))

def sourceBody637_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_80 sourceBody637_3

def sourceBody637_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_81 sourceBody637_0

def sourceBody637_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_78 sourceBody637_82

def sourceBody637_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 60)
    (Flapjack.WordLangExpHOL.const 3#64))

def sourceBody637_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody637_86 : WordLangProgHOL (BitVec 64) :=
.call (some (([66]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 18)) (some 68) ([18]) (some (18, sourceBody637_85, 637, 19))

def sourceBody637_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_86 sourceBody637_3

def sourceBody637_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_87 sourceBody637_0

def sourceBody637_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_84 sourceBody637_88

def sourceBody637_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 60)
    (Flapjack.WordLangExpHOL.const 3#64))

def sourceBody637_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody637_92 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 20)) (some 68) ([46]) (some (46, sourceBody637_91, 637, 21))

def sourceBody637_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_92 sourceBody637_3

def sourceBody637_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_93 sourceBody637_0

def sourceBody637_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_90 sourceBody637_94

def sourceBody637_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
    (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 60)
      (Flapjack.WordLangExpHOL.const 1#64))
    (Flapjack.WordLangExpHOL.const 3#64))

def sourceBody637_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody637_98 : WordLangProgHOL (BitVec 64) :=
.call (some (([46]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 22)) (some 68) ([32]) (some (32, sourceBody637_97, 637, 23))

def sourceBody637_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_98 sourceBody637_3

def sourceBody637_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_99 sourceBody637_0

def sourceBody637_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_96 sourceBody637_100

def sourceBody637_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 54)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody637_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 58

def sourceBody637_104 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 24)) (some 68) ([58]) (some (58, sourceBody637_103, 637, 25))

def sourceBody637_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_104 sourceBody637_3

def sourceBody637_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_105 sourceBody637_0

def sourceBody637_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_102 sourceBody637_106

def sourceBody637_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 54)
        (Flapjack.WordLangExpHOL.const 3#64),
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody637_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody637_110 : WordLangProgHOL (BitVec 64) :=
.call (some (([58]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 26)) (some 68) ([24]) (some (24, sourceBody637_109, 637, 27))

def sourceBody637_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_110 sourceBody637_3

def sourceBody637_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_111 sourceBody637_0

def sourceBody637_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_108 sourceBody637_112

def sourceBody637_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 60)
    (Flapjack.WordLangExpHOL.const 3#64))

def sourceBody637_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 52

def sourceBody637_116 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 28)) (some 68) ([52]) (some (52, sourceBody637_115, 637, 29))

def sourceBody637_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_116 sourceBody637_3

def sourceBody637_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_117 sourceBody637_0

def sourceBody637_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_114 sourceBody637_118

def sourceBody637_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 2)

def sourceBody637_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 4)

def sourceBody637_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 40)

def sourceBody637_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody637_124 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 30)) (some 631) ([38, 64, 22]) (some (38, sourceBody637_123, 637, 31))

def sourceBody637_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_124 sourceBody637_3

def sourceBody637_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_125 sourceBody637_0

def sourceBody637_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_122 sourceBody637_126

def sourceBody637_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_121 sourceBody637_127

def sourceBody637_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_120 sourceBody637_128

def sourceBody637_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_129

def sourceBody637_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_130

def sourceBody637_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 40)

def sourceBody637_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 26)

def sourceBody637_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 34)

def sourceBody637_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 60)

def sourceBody637_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 66)

def sourceBody637_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 32)

def sourceBody637_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 58)

def sourceBody637_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 24)

def sourceBody637_140 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 32)) (some 635) ([38, 64, 22, 50, 36, 62, 28, 56]) (some (38, sourceBody637_123, 637, 33))

def sourceBody637_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_140 sourceBody637_3

def sourceBody637_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_141 sourceBody637_0

def sourceBody637_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_139 sourceBody637_142

def sourceBody637_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_138 sourceBody637_143

def sourceBody637_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_137 sourceBody637_144

def sourceBody637_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_136 sourceBody637_145

def sourceBody637_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_135 sourceBody637_146

def sourceBody637_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_134 sourceBody637_147

def sourceBody637_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_133 sourceBody637_148

def sourceBody637_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_132 sourceBody637_149

def sourceBody637_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_150

def sourceBody637_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_151

def sourceBody637_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_131 sourceBody637_152

def sourceBody637_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 6)

def sourceBody637_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 8)

def sourceBody637_156 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 34)) (some 636) ([38, 64]) (some (38, sourceBody637_123, 637, 35))

def sourceBody637_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_156 sourceBody637_3

def sourceBody637_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_157 sourceBody637_0

def sourceBody637_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_155 sourceBody637_158

def sourceBody637_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_154 sourceBody637_159

def sourceBody637_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 52)

def sourceBody637_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody637_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody637_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody637_165 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 64 (Flapjack.WordRegImm.reg 22) sourceBody637_163 sourceBody637_164

def sourceBody637_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_165 sourceBody637_3

def sourceBody637_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 64)

def sourceBody637_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 18)

def sourceBody637_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 60)
    (Flapjack.WordLangExpHOL.const 3#64))

def sourceBody637_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 64

def sourceBody637_171 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 36)) (some 78) ([64, 22]) (some (64, sourceBody637_170, 637, 37))

def sourceBody637_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_171 sourceBody637_3

def sourceBody637_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_172 sourceBody637_0

def sourceBody637_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_169 sourceBody637_173

def sourceBody637_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_168 sourceBody637_174

def sourceBody637_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_175

def sourceBody637_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_176

def sourceBody637_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 60)

def sourceBody637_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody637_180 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 64 (Flapjack.WordRegImm.reg 22) sourceBody637_163 sourceBody637_164

def sourceBody637_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_180 sourceBody637_3

def sourceBody637_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody637_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 64)

def sourceBody637_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody637_185 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.reg 62) sourceBody637_184 sourceBody637_182

def sourceBody637_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_185 sourceBody637_3

def sourceBody637_187 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 34))

def sourceBody637_188 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody637_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody637_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody637_191 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 56 (Flapjack.WordRegImm.reg 42) sourceBody637_189 sourceBody637_190

def sourceBody637_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_191 sourceBody637_3

def sourceBody637_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody637_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 56)

def sourceBody637_195 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody637_196 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 44) sourceBody637_195 sourceBody637_193

def sourceBody637_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_196 sourceBody637_3

def sourceBody637_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.var 16])

def sourceBody637_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 18)

def sourceBody637_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 64)

def sourceBody637_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 38) 22

def sourceBody637_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_201 sourceBody637_0

def sourceBody637_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_200 sourceBody637_202

def sourceBody637_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_203 sourceBody637_0

def sourceBody637_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_163 sourceBody637_204

def sourceBody637_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_205

def sourceBody637_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_199 sourceBody637_206

def sourceBody637_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_207

def sourceBody637_209 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody637_0 sourceBody637_208

def sourceBody637_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_209 sourceBody637_3

def sourceBody637_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_210 sourceBody637_0

def sourceBody637_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_198 sourceBody637_211

def sourceBody637_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_197 sourceBody637_212

def sourceBody637_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_194 sourceBody637_213

def sourceBody637_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_193 sourceBody637_214

def sourceBody637_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_192 sourceBody637_215

def sourceBody637_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_188 sourceBody637_216

def sourceBody637_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_187 sourceBody637_217

def sourceBody637_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_186 sourceBody637_218

def sourceBody637_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_183 sourceBody637_219

def sourceBody637_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_182 sourceBody637_220

def sourceBody637_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_181 sourceBody637_221

def sourceBody637_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_179 sourceBody637_222

def sourceBody637_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_178 sourceBody637_223

def sourceBody637_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_177 sourceBody637_224

def sourceBody637_226 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 66)

def sourceBody637_227 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 60)
    (Flapjack.WordLangExpHOL.const 3#64))

def sourceBody637_228 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 38)) (some 77) ([64, 22, 50]) (some (64, sourceBody637_170, 637, 39))

def sourceBody637_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_228 sourceBody637_3

def sourceBody637_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_229 sourceBody637_0

def sourceBody637_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_227 sourceBody637_230

def sourceBody637_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_226 sourceBody637_231

def sourceBody637_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_168 sourceBody637_232

def sourceBody637_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_233

def sourceBody637_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_234

def sourceBody637_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 52)

def sourceBody637_237 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 52, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody637_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 38)

def sourceBody637_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_238 sourceBody637_0

def sourceBody637_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_239 sourceBody637_0

def sourceBody637_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_237 sourceBody637_240

def sourceBody637_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_241

def sourceBody637_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 60)

def sourceBody637_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 18)

def sourceBody637_245 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 60)

def sourceBody637_246 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 46)

def sourceBody637_247 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 40)) (some 633) ([64, 22, 50, 36, 62]) (some (64, sourceBody637_170, 637, 41))

def sourceBody637_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_247 sourceBody637_3

def sourceBody637_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_248 sourceBody637_0

def sourceBody637_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_246 sourceBody637_249

def sourceBody637_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_245 sourceBody637_250

def sourceBody637_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_244 sourceBody637_251

def sourceBody637_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_243 sourceBody637_252

def sourceBody637_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_168 sourceBody637_253

def sourceBody637_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_254

def sourceBody637_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_255

def sourceBody637_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_242 sourceBody637_256

def sourceBody637_258 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 46)

def sourceBody637_259 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 60)
    (Flapjack.WordLangExpHOL.const 1#64))

def sourceBody637_260 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 34)

def sourceBody637_261 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 18)

def sourceBody637_262 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 32)

def sourceBody637_263 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 58)

def sourceBody637_264 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 24)

def sourceBody637_265 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 42)) (some 635) ([64, 22, 50, 36, 62, 28, 56, 42]) (some (64, sourceBody637_170, 637, 43))

def sourceBody637_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_265 sourceBody637_3

def sourceBody637_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_266 sourceBody637_0

def sourceBody637_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_264 sourceBody637_267

def sourceBody637_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_263 sourceBody637_268

def sourceBody637_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_262 sourceBody637_269

def sourceBody637_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_261 sourceBody637_270

def sourceBody637_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_245 sourceBody637_271

def sourceBody637_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_260 sourceBody637_272

def sourceBody637_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_259 sourceBody637_273

def sourceBody637_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_258 sourceBody637_274

def sourceBody637_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_275

def sourceBody637_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_276

def sourceBody637_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_257 sourceBody637_277

def sourceBody637_279 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
        [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 8],
          Flapjack.WordLangExpHOL.const 1#64],
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 52)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody637_280 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 38 (Flapjack.WordLangAddr.addr 38 0#64))

def sourceBody637_281 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 38)
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
          [Flapjack.WordLangExpHOL.var 52, Flapjack.WordLangExpHOL.const 7#64]),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody637_282 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody637_283 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 22 (Flapjack.WordRegImm.reg 50) sourceBody637_179 sourceBody637_162

def sourceBody637_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_283 sourceBody637_3

def sourceBody637_285 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 22)

def sourceBody637_286 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 66)

def sourceBody637_287 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 44)) (some 633) ([64, 22, 50, 36, 62]) (some (64, sourceBody637_170, 637, 45))

def sourceBody637_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_287 sourceBody637_3

def sourceBody637_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_288 sourceBody637_0

def sourceBody637_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_246 sourceBody637_289

def sourceBody637_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_245 sourceBody637_290

def sourceBody637_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_286 sourceBody637_291

def sourceBody637_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_243 sourceBody637_292

def sourceBody637_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_168 sourceBody637_293

def sourceBody637_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_294

def sourceBody637_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_295

def sourceBody637_297 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 46)) (some 635) ([64, 22, 50, 36, 62, 28, 56, 42]) (some (64, sourceBody637_170, 637, 47))

def sourceBody637_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_297 sourceBody637_3

def sourceBody637_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_298 sourceBody637_0

def sourceBody637_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_264 sourceBody637_299

def sourceBody637_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_263 sourceBody637_300

def sourceBody637_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_262 sourceBody637_301

def sourceBody637_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_261 sourceBody637_302

def sourceBody637_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_245 sourceBody637_303

def sourceBody637_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_260 sourceBody637_304

def sourceBody637_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_259 sourceBody637_305

def sourceBody637_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_258 sourceBody637_306

def sourceBody637_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_307

def sourceBody637_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_308

def sourceBody637_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_296 sourceBody637_309

def sourceBody637_311 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody637_310 sourceBody637_0

def sourceBody637_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_311 sourceBody637_3

def sourceBody637_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_312 sourceBody637_0

def sourceBody637_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_285 sourceBody637_313

def sourceBody637_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_284 sourceBody637_314

def sourceBody637_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_282 sourceBody637_315

def sourceBody637_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_281 sourceBody637_316

def sourceBody637_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_280 sourceBody637_317

def sourceBody637_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_279 sourceBody637_318

def sourceBody637_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_278 sourceBody637_319

def sourceBody637_321 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody637_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_320 sourceBody637_321

def sourceBody637_323 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody637_324 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 50 (Flapjack.WordRegImm.imm 0#64) sourceBody637_322 sourceBody637_323

def sourceBody637_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_324 sourceBody637_3

def sourceBody637_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_325 sourceBody637_0

def sourceBody637_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_167 sourceBody637_326

def sourceBody637_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_166 sourceBody637_327

def sourceBody637_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_236 sourceBody637_328

def sourceBody637_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_164 sourceBody637_329

def sourceBody637_331 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody637_330 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody637_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_331 sourceBody637_3

def sourceBody637_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_3 sourceBody637_332

def sourceBody637_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_235 sourceBody637_333

def sourceBody637_335 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 50 (Flapjack.WordRegImm.imm 0#64) sourceBody637_225 sourceBody637_334

def sourceBody637_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_335 sourceBody637_3

def sourceBody637_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_336 sourceBody637_0

def sourceBody637_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_167 sourceBody637_337

def sourceBody637_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_166 sourceBody637_338

def sourceBody637_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_162 sourceBody637_339

def sourceBody637_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_161 sourceBody637_340

def sourceBody637_342 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 14)

def sourceBody637_343 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 12)

def sourceBody637_344 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody637_0, 637, 48)) (some 632) ([64, 22, 50, 36]) (some (64, sourceBody637_170, 637, 49))

def sourceBody637_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_344 sourceBody637_3

def sourceBody637_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_345 sourceBody637_0

def sourceBody637_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_343 sourceBody637_346

def sourceBody637_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_342 sourceBody637_347

def sourceBody637_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_243 sourceBody637_348

def sourceBody637_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_168 sourceBody637_349

def sourceBody637_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_350

def sourceBody637_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_351

def sourceBody637_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_341 sourceBody637_352

def sourceBody637_354 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 20)

def sourceBody637_355 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody637_0, 637, 50)) (some 70) ([64]) (some (64, sourceBody637_170, 637, 51))

def sourceBody637_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_355 sourceBody637_3

def sourceBody637_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_356 sourceBody637_0

def sourceBody637_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_354 sourceBody637_357

def sourceBody637_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_358

def sourceBody637_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_359

def sourceBody637_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_353 sourceBody637_360

def sourceBody637_362 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody637_363 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [38]

def sourceBody637_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_363 sourceBody637_0

def sourceBody637_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_362 sourceBody637_364

def sourceBody637_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_361 sourceBody637_365

def sourceBody637_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_160 sourceBody637_366

def sourceBody637_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_367

def sourceBody637_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_368

def sourceBody637_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_153 sourceBody637_369

def sourceBody637_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_119 sourceBody637_370

def sourceBody637_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_371

def sourceBody637_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_372

def sourceBody637_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_113 sourceBody637_373

def sourceBody637_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_374

def sourceBody637_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_375

def sourceBody637_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_107 sourceBody637_376

def sourceBody637_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_377

def sourceBody637_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_378

def sourceBody637_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_101 sourceBody637_379

def sourceBody637_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_380

def sourceBody637_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_381

def sourceBody637_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_95 sourceBody637_382

def sourceBody637_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_383

def sourceBody637_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_384

def sourceBody637_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_89 sourceBody637_385

def sourceBody637_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_386

def sourceBody637_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_387

def sourceBody637_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_83 sourceBody637_388

def sourceBody637_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_389

def sourceBody637_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_390

def sourceBody637_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_77 sourceBody637_391

def sourceBody637_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_392

def sourceBody637_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_393

def sourceBody637_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_69 sourceBody637_394

def sourceBody637_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_395

def sourceBody637_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_68 sourceBody637_396

def sourceBody637_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_31 sourceBody637_397

def sourceBody637_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_398

def sourceBody637_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_399

def sourceBody637_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_24 sourceBody637_400

def sourceBody637_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_12 sourceBody637_401

def sourceBody637_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_402

def sourceBody637_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_403

def sourceBody637_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_6 sourceBody637_404

def sourceBody637_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_405

def sourceBody637_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_5 sourceBody637_406

def sourceBody637_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_407

def sourceBody637_409 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody637_0 sourceBody637_408

def source637 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (637, 8, sourceBody637_409)
end InitECandidate.Proofs.WordStages
