import InitECandidate.Proofs.FrontendStages.Crep.Translate554
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody570_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.var 3)

def crepBody570_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody570_2 : CrepProg (BitVec 64) :=
.seq crepBody570_0 crepBody570_1

def crepBody570_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.var 12)

def crepBody570_4 : CrepProg (BitVec 64) :=
.seq crepBody570_3 crepBody570_1

def crepBody570_5 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 1#64]) crepBody570_4

def crepBody570_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12, 13], none)) "div64by32"
  [Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.var 10]

def crepBody570_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.var 15)

def crepBody570_8 : CrepProg (BitVec 64) :=
.seq crepBody570_7 crepBody570_1

def crepBody570_9 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 12) crepBody570_8

def crepBody570_10 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64]]) crepBody570_9

def crepBody570_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11 (Flapjack.CrepExp.var 13)

def crepBody570_12 : CrepProg (BitVec 64) :=
.seq crepBody570_11 crepBody570_1

def crepBody570_13 : CrepProg (BitVec 64) :=
.seq crepBody570_10 crepBody570_12

def crepBody570_14 : CrepProg (BitVec 64) :=
.seq crepBody570_6 crepBody570_13

def crepBody570_15 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody570_14

def crepBody570_16 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody570_15

def crepBody570_17 : CrepProg (BitVec 64) :=
.seq crepBody570_5 crepBody570_16

def crepBody570_18 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 9)) crepBody570_17

def crepBody570_19 : CrepProg (BitVec 64) :=
.seq crepBody570_2 crepBody570_18

def crepBody570_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.var 13)

def crepBody570_21 : CrepProg (BitVec 64) :=
.seq crepBody570_20 crepBody570_1

def crepBody570_22 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 11) crepBody570_21

def crepBody570_23 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 1) crepBody570_22

def crepBody570_24 : CrepProg (BitVec 64) :=
.seq crepBody570_19 crepBody570_23

def crepBody570_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody570_26 : CrepProg (BitVec 64) :=
.seq crepBody570_24 crepBody570_25

def crepBody570_27 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody570_26

def crepBody570_28 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 4)) crepBody570_27

def crepBody570_29 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 1#64)) crepBody570_28 crepBody570_1

def crepBody570_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "nlz32"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 4,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64],
              Flapjack.CrepExp.const 8#64]])]

def crepBody570_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8
  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64])

def crepBody570_32 : CrepProg (BitVec 64) :=
.seq crepBody570_31 crepBody570_1

def crepBody570_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.var 12)

def crepBody570_34 : CrepProg (BitVec 64) :=
.seq crepBody570_33 crepBody570_1

def crepBody570_35 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.op Flapjack.BinOp.or
      [Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 4,
                Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]]))
          (Flapjack.CrepExp.var 10),
        Flapjack.CrepExp.shift Flapjack.Shift.lsr
          (Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 4,
                Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 1#64],
                    Flapjack.CrepExp.const 8#64]]))
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.var 10])],
    Flapjack.CrepExp.const 4294967295#64]) crepBody570_34

def crepBody570_36 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]]) crepBody570_35

def crepBody570_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 11)

def crepBody570_38 : CrepProg (BitVec 64) :=
.seq crepBody570_37 crepBody570_1

def crepBody570_39 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 1#64]) crepBody570_38

def crepBody570_40 : CrepProg (BitVec 64) :=
.seq crepBody570_36 crepBody570_39

def crepBody570_41 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 8)) crepBody570_40

def crepBody570_42 : CrepProg (BitVec 64) :=
.seq crepBody570_32 crepBody570_41

def crepBody570_43 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.shift Flapjack.Shift.lsl (Flapjack.CrepExp.load (Flapjack.CrepExp.var 4)) (Flapjack.CrepExp.var 10),
    Flapjack.CrepExp.const 4294967295#64]) crepBody570_34

def crepBody570_44 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 7) crepBody570_43

def crepBody570_45 : CrepProg (BitVec 64) :=
.seq crepBody570_42 crepBody570_44

def crepBody570_46 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.shift Flapjack.Shift.lsr
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 2,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
          [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64],
            Flapjack.CrepExp.const 8#64]]))
  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.var 10])) crepBody570_34

def crepBody570_47 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 8#64]]) crepBody570_46

def crepBody570_48 : CrepProg (BitVec 64) :=
.seq crepBody570_45 crepBody570_47

def crepBody570_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8
  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64])

def crepBody570_50 : CrepProg (BitVec 64) :=
.seq crepBody570_49 crepBody570_1

def crepBody570_51 : CrepProg (BitVec 64) :=
.seq crepBody570_48 crepBody570_50

def crepBody570_52 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.op Flapjack.BinOp.or
      [Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 2,
                Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]]))
          (Flapjack.CrepExp.var 10),
        Flapjack.CrepExp.shift Flapjack.Shift.lsr
          (Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 2,
                Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 1#64],
                    Flapjack.CrepExp.const 8#64]]))
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.var 10])],
    Flapjack.CrepExp.const 4294967295#64]) crepBody570_34

def crepBody570_53 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]]) crepBody570_52

def crepBody570_54 : CrepProg (BitVec 64) :=
.seq crepBody570_53 crepBody570_39

def crepBody570_55 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 8)) crepBody570_54

def crepBody570_56 : CrepProg (BitVec 64) :=
.seq crepBody570_51 crepBody570_55

def crepBody570_57 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.shift Flapjack.Shift.lsl (Flapjack.CrepExp.load (Flapjack.CrepExp.var 2)) (Flapjack.CrepExp.var 10),
    Flapjack.CrepExp.const 4294967295#64]) crepBody570_34

def crepBody570_58 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 6) crepBody570_57

def crepBody570_59 : CrepProg (BitVec 64) :=
.seq crepBody570_56 crepBody570_58

def crepBody570_60 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 5],
      Flapjack.CrepExp.const 1#64])

def crepBody570_61 : CrepProg (BitVec 64) :=
.seq crepBody570_60 crepBody570_1

def crepBody570_62 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.var 13)

def crepBody570_63 : CrepProg (BitVec 64) :=
.seq crepBody570_62 crepBody570_1

def crepBody570_64 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 1#64]) crepBody570_63

def crepBody570_65 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 16 (Flapjack.CrepExp.const 4294967295#64)

def crepBody570_66 : CrepProg (BitVec 64) :=
.seq crepBody570_65 crepBody570_1

def crepBody570_67 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 17
  (Flapjack.CrepExp.op Flapjack.BinOp.sub
    [Flapjack.CrepExp.op Flapjack.BinOp.or
        [Flapjack.CrepExp.shift Flapjack.Shift.lsl (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 32#64),
          Flapjack.CrepExp.var 14],
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 11]])

def crepBody570_68 : CrepProg (BitVec 64) :=
.seq crepBody570_67 crepBody570_1

def crepBody570_69 : CrepProg (BitVec 64) :=
.seq crepBody570_66 crepBody570_68

def crepBody570_70 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18, 19], none)) "div64by32"
  [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 11]

def crepBody570_71 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 16 (Flapjack.CrepExp.var 18)

def crepBody570_72 : CrepProg (BitVec 64) :=
.seq crepBody570_71 crepBody570_1

def crepBody570_73 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 17 (Flapjack.CrepExp.var 19)

def crepBody570_74 : CrepProg (BitVec 64) :=
.seq crepBody570_73 crepBody570_1

def crepBody570_75 : CrepProg (BitVec 64) :=
.seq crepBody570_72 crepBody570_74

def crepBody570_76 : CrepProg (BitVec 64) :=
.seq crepBody570_70 crepBody570_75

def crepBody570_77 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody570_76

def crepBody570_78 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody570_77

def crepBody570_79 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.var 11)) crepBody570_69 crepBody570_78

def crepBody570_80 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 18 (Flapjack.CrepExp.const 0#64)

def crepBody570_81 : CrepProg (BitVec 64) :=
.seq crepBody570_80 crepBody570_1

def crepBody570_82 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 16 (Flapjack.CrepExp.var 19)

def crepBody570_83 : CrepProg (BitVec 64) :=
.seq crepBody570_82 crepBody570_1

def crepBody570_84 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 1#64]) crepBody570_83

def crepBody570_85 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 11]) crepBody570_74

def crepBody570_86 : CrepProg (BitVec 64) :=
.seq crepBody570_84 crepBody570_85

def crepBody570_87 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 18 (Flapjack.CrepExp.const 1#64)

def crepBody570_88 : CrepProg (BitVec 64) :=
.seq crepBody570_87 crepBody570_1

def crepBody570_89 : CrepProg (BitVec 64) :=
.seq crepBody570_86 crepBody570_88

def crepBody570_90 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.shift Flapjack.Shift.lsl (Flapjack.CrepExp.var 17) (Flapjack.CrepExp.const 32#64),
      Flapjack.CrepExp.var 15])
  (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 12])) crepBody570_89 crepBody570_1

def crepBody570_91 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 17) (Flapjack.CrepExp.const 4294967296#64)) crepBody570_90 crepBody570_1

def crepBody570_92 : CrepProg (BitVec 64) :=
.seq crepBody570_81 crepBody570_91

def crepBody570_93 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 18) (Flapjack.CrepExp.const 1#64)) crepBody570_92

def crepBody570_94 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.const 0#64)

def crepBody570_95 : CrepProg (BitVec 64) :=
.seq crepBody570_94 crepBody570_1

def crepBody570_96 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 22) (Flapjack.CrepExp.var 23)

def crepBody570_97 : CrepProg (BitVec 64) :=
.seq crepBody570_96 crepBody570_1

def crepBody570_98 : CrepProg (BitVec 64) :=
.dec 23 (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 21, Flapjack.CrepExp.const 4294967295#64]) crepBody570_97

def crepBody570_99 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9],
        Flapjack.CrepExp.const 8#64]]) crepBody570_98

def crepBody570_100 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 19
  (Flapjack.CrepExp.op Flapjack.BinOp.sub
    [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 20) (Flapjack.CrepExp.const 32#64),
      Flapjack.CrepExp.shift Flapjack.Shift.asr (Flapjack.CrepExp.var 21) (Flapjack.CrepExp.const 32#64)])

def crepBody570_101 : CrepProg (BitVec 64) :=
.seq crepBody570_100 crepBody570_1

def crepBody570_102 : CrepProg (BitVec 64) :=
.seq crepBody570_99 crepBody570_101

def crepBody570_103 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 22)

def crepBody570_104 : CrepProg (BitVec 64) :=
.seq crepBody570_103 crepBody570_1

def crepBody570_105 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 1#64]) crepBody570_104

def crepBody570_106 : CrepProg (BitVec 64) :=
.seq crepBody570_102 crepBody570_105

def crepBody570_107 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.op Flapjack.BinOp.sub
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.var 6,
              Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9],
                  Flapjack.CrepExp.const 8#64]]),
        Flapjack.CrepExp.var 19],
    Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 20, Flapjack.CrepExp.const 4294967295#64]]) crepBody570_106

def crepBody570_108 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
  [Flapjack.CrepExp.var 16,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 7,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]])]) crepBody570_107

def crepBody570_109 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 5)) crepBody570_108

def crepBody570_110 : CrepProg (BitVec 64) :=
.seq crepBody570_95 crepBody570_109

def crepBody570_111 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 21) (Flapjack.CrepExp.var 22)

def crepBody570_112 : CrepProg (BitVec 64) :=
.seq crepBody570_111 crepBody570_1

def crepBody570_113 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 1#64]) crepBody570_112

def crepBody570_114 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64]]) crepBody570_113

def crepBody570_115 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 19 (Flapjack.CrepExp.const 0#64)

def crepBody570_116 : CrepProg (BitVec 64) :=
.seq crepBody570_115 crepBody570_1

def crepBody570_117 : CrepProg (BitVec 64) :=
.seq crepBody570_114 crepBody570_116

def crepBody570_118 : CrepProg (BitVec 64) :=
.seq crepBody570_117 crepBody570_95

def crepBody570_119 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 19
  (Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 21) (Flapjack.CrepExp.const 32#64))

def crepBody570_120 : CrepProg (BitVec 64) :=
.seq crepBody570_119 crepBody570_1

def crepBody570_121 : CrepProg (BitVec 64) :=
.seq crepBody570_99 crepBody570_120

def crepBody570_122 : CrepProg (BitVec 64) :=
.seq crepBody570_121 crepBody570_105

def crepBody570_123 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 6,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9],
              Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 7,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.var 19]) crepBody570_122

def crepBody570_124 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 5)) crepBody570_123

def crepBody570_125 : CrepProg (BitVec 64) :=
.seq crepBody570_118 crepBody570_124

def crepBody570_126 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 20, Flapjack.CrepExp.var 19],
    Flapjack.CrepExp.const 4294967295#64]) crepBody570_112

def crepBody570_127 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 5],
        Flapjack.CrepExp.const 8#64]]) crepBody570_126

def crepBody570_128 : CrepProg (BitVec 64) :=
.seq crepBody570_125 crepBody570_127

def crepBody570_129 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 16) crepBody570_112

def crepBody570_130 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64]]) crepBody570_129

def crepBody570_131 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.var 20) crepBody570_112

def crepBody570_132 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 5],
        Flapjack.CrepExp.const 8#64]]) crepBody570_131

def crepBody570_133 : CrepProg (BitVec 64) :=
.seq crepBody570_130 crepBody570_132

def crepBody570_134 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 20) (Flapjack.CrepExp.const 0#64)) crepBody570_128 crepBody570_133

def crepBody570_135 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 19]) crepBody570_134

def crepBody570_136 : CrepProg (BitVec 64) :=
.seq crepBody570_110 crepBody570_135

def crepBody570_137 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody570_136

def crepBody570_138 : CrepProg (BitVec 64) :=
.seq crepBody570_93 crepBody570_137

def crepBody570_139 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 1#64) crepBody570_138

def crepBody570_140 : CrepProg (BitVec 64) :=
.seq crepBody570_79 crepBody570_139

def crepBody570_141 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.const 0#64) crepBody570_140

def crepBody570_142 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.const 0#64) crepBody570_141

def crepBody570_143 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 6,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
        [Flapjack.CrepExp.op Flapjack.BinOp.sub
            [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 5],
              Flapjack.CrepExp.const 2#64],
          Flapjack.CrepExp.const 8#64]])) crepBody570_142

def crepBody570_144 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 6,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
        [Flapjack.CrepExp.op Flapjack.BinOp.sub
            [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 5],
              Flapjack.CrepExp.const 1#64],
          Flapjack.CrepExp.const 8#64]])) crepBody570_143

def crepBody570_145 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 6,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 5],
          Flapjack.CrepExp.const 8#64]])) crepBody570_144

def crepBody570_146 : CrepProg (BitVec 64) :=
.seq crepBody570_64 crepBody570_145

def crepBody570_147 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 9)) crepBody570_146

def crepBody570_148 : CrepProg (BitVec 64) :=
.seq crepBody570_61 crepBody570_147

def crepBody570_149 : CrepProg (BitVec 64) :=
.seq crepBody570_148 crepBody570_61

def crepBody570_150 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.var 14)

def crepBody570_151 : CrepProg (BitVec 64) :=
.seq crepBody570_150 crepBody570_1

def crepBody570_152 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody570_151

def crepBody570_153 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 8#64]]) crepBody570_152

def crepBody570_154 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 1#64]) crepBody570_63

def crepBody570_155 : CrepProg (BitVec 64) :=
.seq crepBody570_153 crepBody570_154

def crepBody570_156 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 3)) crepBody570_155

def crepBody570_157 : CrepProg (BitVec 64) :=
.seq crepBody570_149 crepBody570_156

def crepBody570_158 : CrepProg (BitVec 64) :=
.seq crepBody570_157 crepBody570_95

def crepBody570_159 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.shift Flapjack.Shift.lsr
      (Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 6,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]]))
      (Flapjack.CrepExp.var 10),
    Flapjack.CrepExp.op Flapjack.BinOp.and
      [Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 6,
                Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 1#64],
                    Flapjack.CrepExp.const 8#64]]))
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.var 10]),
        Flapjack.CrepExp.const 4294967295#64]]) crepBody570_151

def crepBody570_160 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]]) crepBody570_159

def crepBody570_161 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 13)

def crepBody570_162 : CrepProg (BitVec 64) :=
.seq crepBody570_161 crepBody570_1

def crepBody570_163 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 1#64]) crepBody570_162

def crepBody570_164 : CrepProg (BitVec 64) :=
.seq crepBody570_160 crepBody570_163

def crepBody570_165 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 5)) crepBody570_164

def crepBody570_166 : CrepProg (BitVec 64) :=
.seq crepBody570_158 crepBody570_165

def crepBody570_167 : CrepProg (BitVec 64) :=
.seq crepBody570_166 crepBody570_25

def crepBody570_168 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 7,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
        [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 2#64],
          Flapjack.CrepExp.const 8#64]])) crepBody570_167

def crepBody570_169 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 7,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
        [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64],
          Flapjack.CrepExp.const 8#64]])) crepBody570_168

def crepBody570_170 : CrepProg (BitVec 64) :=
.seq crepBody570_59 crepBody570_169

def crepBody570_171 : CrepProg (BitVec 64) :=
.seq crepBody570_30 crepBody570_170

def crepBody570_172 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody570_171

def crepBody570_173 : CrepProg (BitVec 64) :=
.seq crepBody570_29 crepBody570_172

def crepBody570_174 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody570_173

def crepBody570_175 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody570_174

def data570 : CrepProg (BitVec 64) := crepBody570_175
def output570 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [98#8, 110#8, 95#8, 100#8, 105#8, 118#8, 109#8, 110#8, 117#8], [0, 1, 2, 3, 4, 5, 6, 7], crepProgToHOL data570)
end InitECandidate.Proofs.FrontendStages.Crep
