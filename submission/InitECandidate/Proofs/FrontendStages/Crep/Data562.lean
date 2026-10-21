import InitECandidate.Proofs.FrontendStages.Crep.Translate546
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody562_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 4)

def crepBody562_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody562_2 : CrepProg (BitVec 64) :=
.seq crepBody562_0 crepBody562_1

def crepBody562_3 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 4#64]]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 1,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 4#64],
            Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 1,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 4#64],
            Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 1,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 4#64],
            Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64)]) crepBody562_2

def crepBody562_4 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 328#64]),
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 8#64]]) crepBody562_3

def crepBody562_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 2 (Flapjack.CrepExp.var 3)

def crepBody562_6 : CrepProg (BitVec 64) :=
.seq crepBody562_5 crepBody562_1

def crepBody562_7 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 1#64]) crepBody562_6

def crepBody562_8 : CrepProg (BitVec 64) :=
.seq crepBody562_4 crepBody562_7

def crepBody562_9 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 16#64)) crepBody562_8

def crepBody562_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([14], none)) "rmd_f"
  [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody562_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "rmd_k" [Flapjack.CrepExp.var 13]

def crepBody562_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 16 (Flapjack.CrepExp.var 18)

def crepBody562_13 : CrepProg (BitVec 64) :=
.seq crepBody562_12 crepBody562_1

def crepBody562_14 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.op Flapjack.BinOp.and
          [Flapjack.CrepExp.op Flapjack.BinOp.or
              [Flapjack.CrepExp.shift Flapjack.Shift.lsl (Flapjack.CrepExp.var 16) (Flapjack.CrepExp.var 17),
                Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 16)
                  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.var 17])],
            Flapjack.CrepExp.const 4294967295#64],
        Flapjack.CrepExp.var 7],
    Flapjack.CrepExp.const 4294967295#64]) crepBody562_13

def crepBody562_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 7)

def crepBody562_16 : CrepProg (BitVec 64) :=
.seq crepBody562_15 crepBody562_1

def crepBody562_17 : CrepProg (BitVec 64) :=
.seq crepBody562_14 crepBody562_16

def crepBody562_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 6)

def crepBody562_19 : CrepProg (BitVec 64) :=
.seq crepBody562_18 crepBody562_1

def crepBody562_20 : CrepProg (BitVec 64) :=
.seq crepBody562_17 crepBody562_19

def crepBody562_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6
  (Flapjack.CrepExp.op Flapjack.BinOp.and
    [Flapjack.CrepExp.op Flapjack.BinOp.or
        [Flapjack.CrepExp.shift Flapjack.Shift.lsl (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 10#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 5)
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.const 10#64])],
      Flapjack.CrepExp.const 4294967295#64])

def crepBody562_22 : CrepProg (BitVec 64) :=
.seq crepBody562_21 crepBody562_1

def crepBody562_23 : CrepProg (BitVec 64) :=
.seq crepBody562_20 crepBody562_22

def crepBody562_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 4)

def crepBody562_25 : CrepProg (BitVec 64) :=
.seq crepBody562_24 crepBody562_1

def crepBody562_26 : CrepProg (BitVec 64) :=
.seq crepBody562_23 crepBody562_25

def crepBody562_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 16)

def crepBody562_28 : CrepProg (BitVec 64) :=
.seq crepBody562_27 crepBody562_1

def crepBody562_29 : CrepProg (BitVec 64) :=
.seq crepBody562_26 crepBody562_28

def crepBody562_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([18], none)) "rmd_f"
  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 79#64, Flapjack.CrepExp.var 13],
    Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 11]

def crepBody562_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([19], none)) "rmd_kp" [Flapjack.CrepExp.var 13]

def crepBody562_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 20 (Flapjack.CrepExp.var 22)

def crepBody562_33 : CrepProg (BitVec 64) :=
.seq crepBody562_32 crepBody562_1

def crepBody562_34 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.op Flapjack.BinOp.and
          [Flapjack.CrepExp.op Flapjack.BinOp.or
              [Flapjack.CrepExp.shift Flapjack.Shift.lsl (Flapjack.CrepExp.var 20) (Flapjack.CrepExp.var 21),
                Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 20)
                  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.var 21])],
            Flapjack.CrepExp.const 4294967295#64],
        Flapjack.CrepExp.var 12],
    Flapjack.CrepExp.const 4294967295#64]) crepBody562_33

def crepBody562_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 12)

def crepBody562_36 : CrepProg (BitVec 64) :=
.seq crepBody562_35 crepBody562_1

def crepBody562_37 : CrepProg (BitVec 64) :=
.seq crepBody562_34 crepBody562_36

def crepBody562_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 12 (Flapjack.CrepExp.var 11)

def crepBody562_39 : CrepProg (BitVec 64) :=
.seq crepBody562_38 crepBody562_1

def crepBody562_40 : CrepProg (BitVec 64) :=
.seq crepBody562_37 crepBody562_39

def crepBody562_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11
  (Flapjack.CrepExp.op Flapjack.BinOp.and
    [Flapjack.CrepExp.op Flapjack.BinOp.or
        [Flapjack.CrepExp.shift Flapjack.Shift.lsl (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 10#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 10)
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.const 10#64])],
      Flapjack.CrepExp.const 4294967295#64])

def crepBody562_42 : CrepProg (BitVec 64) :=
.seq crepBody562_41 crepBody562_1

def crepBody562_43 : CrepProg (BitVec 64) :=
.seq crepBody562_40 crepBody562_42

def crepBody562_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10 (Flapjack.CrepExp.var 9)

def crepBody562_45 : CrepProg (BitVec 64) :=
.seq crepBody562_44 crepBody562_1

def crepBody562_46 : CrepProg (BitVec 64) :=
.seq crepBody562_43 crepBody562_45

def crepBody562_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.var 20)

def crepBody562_48 : CrepProg (BitVec 64) :=
.seq crepBody562_47 crepBody562_1

def crepBody562_49 : CrepProg (BitVec 64) :=
.seq crepBody562_46 crepBody562_48

def crepBody562_50 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 13 (Flapjack.CrepExp.var 22)

def crepBody562_51 : CrepProg (BitVec 64) :=
.seq crepBody562_50 crepBody562_1

def crepBody562_52 : CrepProg (BitVec 64) :=
.dec 22 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 1#64]) crepBody562_51

def crepBody562_53 : CrepProg (BitVec 64) :=
.seq crepBody562_49 crepBody562_52

def crepBody562_54 : CrepProg (BitVec 64) :=
.dec 21 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.shift Flapjack.Shift.lsr
      (Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.load
              (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
              [Flapjack.CrepExp.op Flapjack.BinOp.add
                  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.const 5#64],
                    Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 4#64)],
                Flapjack.CrepExp.const 8#64]]))
      (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
        [Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 15#64],
          Flapjack.CrepExp.const 4#64]),
    Flapjack.CrepExp.const 15#64]) crepBody562_53

def crepBody562_55 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 18,
        Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 328#64]),
              Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                [Flapjack.CrepExp.op Flapjack.BinOp.and
                    [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                        (Flapjack.CrepExp.load
                          (Flapjack.CrepExp.op Flapjack.BinOp.add
                            [Flapjack.CrepExp.load
                                (Flapjack.CrepExp.op Flapjack.BinOp.sub
                                  [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
                              Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                                [Flapjack.CrepExp.op Flapjack.BinOp.add
                                    [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                                        [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.const 5#64],
                                      Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 13)
                                        (Flapjack.CrepExp.const 4#64)],
                                  Flapjack.CrepExp.const 8#64]]))
                        (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                          [Flapjack.CrepExp.op Flapjack.BinOp.and
                              [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 15#64],
                            Flapjack.CrepExp.const 4#64]),
                      Flapjack.CrepExp.const 15#64],
                  Flapjack.CrepExp.const 8#64]]),
        Flapjack.CrepExp.var 19],
    Flapjack.CrepExp.const 4294967295#64]) crepBody562_54

def crepBody562_56 : CrepProg (BitVec 64) :=
.seq crepBody562_31 crepBody562_55

def crepBody562_57 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.const 0#64) crepBody562_56

def crepBody562_58 : CrepProg (BitVec 64) :=
.seq crepBody562_30 crepBody562_57

def crepBody562_59 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.const 0#64) crepBody562_58

def crepBody562_60 : CrepProg (BitVec 64) :=
.seq crepBody562_29 crepBody562_59

def crepBody562_61 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.shift Flapjack.Shift.lsr
      (Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.load
              (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
              [Flapjack.CrepExp.op Flapjack.BinOp.add
                  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.const 5#64],
                    Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 4#64)],
                Flapjack.CrepExp.const 8#64]]))
      (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
        [Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 15#64],
          Flapjack.CrepExp.const 4#64]),
    Flapjack.CrepExp.const 15#64]) crepBody562_60

def crepBody562_62 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 14,
        Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.load
                (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 328#64]),
              Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                [Flapjack.CrepExp.op Flapjack.BinOp.and
                    [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                        (Flapjack.CrepExp.load
                          (Flapjack.CrepExp.op Flapjack.BinOp.add
                            [Flapjack.CrepExp.load
                                (Flapjack.CrepExp.op Flapjack.BinOp.sub
                                  [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 320#64]),
                              Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                                [Flapjack.CrepExp.op Flapjack.BinOp.add
                                    [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                                        [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 5#64],
                                      Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 13)
                                        (Flapjack.CrepExp.const 4#64)],
                                  Flapjack.CrepExp.const 8#64]]))
                        (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                          [Flapjack.CrepExp.op Flapjack.BinOp.and
                              [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 15#64],
                            Flapjack.CrepExp.const 4#64]),
                      Flapjack.CrepExp.const 15#64],
                  Flapjack.CrepExp.const 8#64]]),
        Flapjack.CrepExp.var 15],
    Flapjack.CrepExp.const 4294967295#64]) crepBody562_61

def crepBody562_63 : CrepProg (BitVec 64) :=
.seq crepBody562_11 crepBody562_62

def crepBody562_64 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody562_63

def crepBody562_65 : CrepProg (BitVec 64) :=
.seq crepBody562_10 crepBody562_64

def crepBody562_66 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody562_65

def crepBody562_67 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.const 80#64)) crepBody562_66

def crepBody562_68 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 19) (Flapjack.CrepExp.var 20)

def crepBody562_69 : CrepProg (BitVec 64) :=
.seq crepBody562_68 crepBody562_1

def crepBody562_70 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 11],
    Flapjack.CrepExp.const 4294967295#64]) crepBody562_69

def crepBody562_71 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.var 0) crepBody562_70

def crepBody562_72 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 16, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 12],
    Flapjack.CrepExp.const 4294967295#64]) crepBody562_69

def crepBody562_73 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64]) crepBody562_72

def crepBody562_74 : CrepProg (BitVec 64) :=
.seq crepBody562_71 crepBody562_73

def crepBody562_75 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 17, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8],
    Flapjack.CrepExp.const 4294967295#64]) crepBody562_69

def crepBody562_76 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64]) crepBody562_75

def crepBody562_77 : CrepProg (BitVec 64) :=
.seq crepBody562_74 crepBody562_76

def crepBody562_78 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 18, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 9],
    Flapjack.CrepExp.const 4294967295#64]) crepBody562_69

def crepBody562_79 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 24#64]) crepBody562_78

def crepBody562_80 : CrepProg (BitVec 64) :=
.seq crepBody562_77 crepBody562_79

def crepBody562_81 : CrepProg (BitVec 64) :=
.dec 20 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 10],
    Flapjack.CrepExp.const 4294967295#64]) crepBody562_69

def crepBody562_82 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64]) crepBody562_81

def crepBody562_83 : CrepProg (BitVec 64) :=
.seq crepBody562_80 crepBody562_82

def crepBody562_84 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody562_85 : CrepProg (BitVec 64) :=
.seq crepBody562_83 crepBody562_84

def crepBody562_86 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64])) crepBody562_85

def crepBody562_87 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 24#64])) crepBody562_86

def crepBody562_88 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64])) crepBody562_87

def crepBody562_89 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64])) crepBody562_88

def crepBody562_90 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 0)) crepBody562_89

def crepBody562_91 : CrepProg (BitVec 64) :=
.seq crepBody562_67 crepBody562_90

def crepBody562_92 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody562_91

def crepBody562_93 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 7) crepBody562_92

def crepBody562_94 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 6) crepBody562_93

def crepBody562_95 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 5) crepBody562_94

def crepBody562_96 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 4) crepBody562_95

def crepBody562_97 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.var 3) crepBody562_96

def crepBody562_98 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64])) crepBody562_97

def crepBody562_99 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 24#64])) crepBody562_98

def crepBody562_100 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 16#64])) crepBody562_99

def crepBody562_101 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64])) crepBody562_100

def crepBody562_102 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.var 0)) crepBody562_101

def crepBody562_103 : CrepProg (BitVec 64) :=
.seq crepBody562_9 crepBody562_102

def crepBody562_104 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody562_103

def data562 : CrepProg (BitVec 64) := crepBody562_104
def output562 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [114#8, 105#8, 112#8, 101#8, 109#8, 100#8, 49#8, 54#8, 48#8, 95#8, 98#8, 108#8, 111#8, 99#8, 107#8], [0, 1], crepProgToHOL data562)
end InitECandidate.Proofs.FrontendStages.Crep
