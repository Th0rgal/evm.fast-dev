import InitECandidate.Proofs.FrontendStages.Crep.Translate550
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody566_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "memcpy"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 368#64]),
    Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 64#64]

def crepBody566_1 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody566_0

def crepBody566_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 368#64]),
        Flapjack.CrepExp.const 64#64],
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 360#64]),
    Flapjack.CrepExp.const 64#64]

def crepBody566_3 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody566_2

def crepBody566_4 : CrepProg (BitVec 64) :=
.seq crepBody566_1 crepBody566_3

def crepBody566_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody566_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody566_7 : CrepProg (BitVec 64) :=
.seq crepBody566_5 crepBody566_6

def crepBody566_8 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.xor
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 368#64]),
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.var 3]) crepBody566_7

def crepBody566_9 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 368#64]),
    Flapjack.CrepExp.const 96#64]) crepBody566_8

def crepBody566_10 : CrepProg (BitVec 64) :=
.seq crepBody566_4 crepBody566_9

def crepBody566_11 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.xor
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 368#64]),
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 13#64, Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.var 4]) crepBody566_7

def crepBody566_12 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 368#64]),
    Flapjack.CrepExp.const 104#64]) crepBody566_11

def crepBody566_13 : CrepProg (BitVec 64) :=
.seq crepBody566_10 crepBody566_12

def crepBody566_14 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.xor
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 368#64]),
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 14#64, Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 1#64]]) crepBody566_7

def crepBody566_15 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 368#64]),
    Flapjack.CrepExp.const 112#64]) crepBody566_14

def crepBody566_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody566_15 crepBody566_6

def crepBody566_17 : CrepProg (BitVec 64) :=
.seq crepBody566_13 crepBody566_16

def crepBody566_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "blake2_g"
  [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 12#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.and
                [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                    (Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.add
                        [Flapjack.CrepExp.load
                            (Flapjack.CrepExp.op Flapjack.BinOp.sub
                              [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
                          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                            [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]]))
                    (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 4#64]),
                  Flapjack.CrepExp.const 15#64],
              Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.and
                [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                    (Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.add
                        [Flapjack.CrepExp.load
                            (Flapjack.CrepExp.op Flapjack.BinOp.sub
                              [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
                          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                            [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]]))
                    (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.const 4#64]),
                  Flapjack.CrepExp.const 15#64],
              Flapjack.CrepExp.const 8#64]])]

def crepBody566_19 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody566_18

def crepBody566_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "blake2_g"
  [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.const 5#64, Flapjack.CrepExp.const 9#64, Flapjack.CrepExp.const 13#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.and
                [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                    (Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.add
                        [Flapjack.CrepExp.load
                            (Flapjack.CrepExp.op Flapjack.BinOp.sub
                              [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
                          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                            [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]]))
                    (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.const 4#64]),
                  Flapjack.CrepExp.const 15#64],
              Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.and
                [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                    (Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.add
                        [Flapjack.CrepExp.load
                            (Flapjack.CrepExp.op Flapjack.BinOp.sub
                              [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
                          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                            [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]]))
                    (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.const 4#64]),
                  Flapjack.CrepExp.const 15#64],
              Flapjack.CrepExp.const 8#64]])]

def crepBody566_21 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody566_20

def crepBody566_22 : CrepProg (BitVec 64) :=
.seq crepBody566_19 crepBody566_21

def crepBody566_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "blake2_g"
  [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.const 6#64, Flapjack.CrepExp.const 10#64, Flapjack.CrepExp.const 14#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.and
                [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                    (Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.add
                        [Flapjack.CrepExp.load
                            (Flapjack.CrepExp.op Flapjack.BinOp.sub
                              [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
                          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                            [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]]))
                    (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 4#64]),
                  Flapjack.CrepExp.const 15#64],
              Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.and
                [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                    (Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.add
                        [Flapjack.CrepExp.load
                            (Flapjack.CrepExp.op Flapjack.BinOp.sub
                              [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
                          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                            [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]]))
                    (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 5#64, Flapjack.CrepExp.const 4#64]),
                  Flapjack.CrepExp.const 15#64],
              Flapjack.CrepExp.const 8#64]])]

def crepBody566_24 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody566_23

def crepBody566_25 : CrepProg (BitVec 64) :=
.seq crepBody566_22 crepBody566_24

def crepBody566_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "blake2_g"
  [Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.const 7#64, Flapjack.CrepExp.const 11#64, Flapjack.CrepExp.const 15#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.and
                [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                    (Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.add
                        [Flapjack.CrepExp.load
                            (Flapjack.CrepExp.op Flapjack.BinOp.sub
                              [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
                          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                            [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]]))
                    (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 6#64, Flapjack.CrepExp.const 4#64]),
                  Flapjack.CrepExp.const 15#64],
              Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.and
                [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                    (Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.add
                        [Flapjack.CrepExp.load
                            (Flapjack.CrepExp.op Flapjack.BinOp.sub
                              [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
                          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                            [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]]))
                    (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 7#64, Flapjack.CrepExp.const 4#64]),
                  Flapjack.CrepExp.const 15#64],
              Flapjack.CrepExp.const 8#64]])]

def crepBody566_27 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody566_26

def crepBody566_28 : CrepProg (BitVec 64) :=
.seq crepBody566_25 crepBody566_27

def crepBody566_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "blake2_g"
  [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 5#64, Flapjack.CrepExp.const 10#64, Flapjack.CrepExp.const 15#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.and
                [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                    (Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.add
                        [Flapjack.CrepExp.load
                            (Flapjack.CrepExp.op Flapjack.BinOp.sub
                              [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
                          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                            [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]]))
                    (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 4#64]),
                  Flapjack.CrepExp.const 15#64],
              Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.and
                [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                    (Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.add
                        [Flapjack.CrepExp.load
                            (Flapjack.CrepExp.op Flapjack.BinOp.sub
                              [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
                          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                            [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]]))
                    (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 9#64, Flapjack.CrepExp.const 4#64]),
                  Flapjack.CrepExp.const 15#64],
              Flapjack.CrepExp.const 8#64]])]

def crepBody566_30 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody566_29

def crepBody566_31 : CrepProg (BitVec 64) :=
.seq crepBody566_28 crepBody566_30

def crepBody566_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "blake2_g"
  [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.const 6#64, Flapjack.CrepExp.const 11#64, Flapjack.CrepExp.const 12#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.and
                [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                    (Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.add
                        [Flapjack.CrepExp.load
                            (Flapjack.CrepExp.op Flapjack.BinOp.sub
                              [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
                          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                            [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]]))
                    (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 10#64, Flapjack.CrepExp.const 4#64]),
                  Flapjack.CrepExp.const 15#64],
              Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.and
                [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                    (Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.add
                        [Flapjack.CrepExp.load
                            (Flapjack.CrepExp.op Flapjack.BinOp.sub
                              [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
                          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                            [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]]))
                    (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 11#64, Flapjack.CrepExp.const 4#64]),
                  Flapjack.CrepExp.const 15#64],
              Flapjack.CrepExp.const 8#64]])]

def crepBody566_33 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody566_32

def crepBody566_34 : CrepProg (BitVec 64) :=
.seq crepBody566_31 crepBody566_33

def crepBody566_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "blake2_g"
  [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.const 7#64, Flapjack.CrepExp.const 8#64, Flapjack.CrepExp.const 13#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.and
                [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                    (Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.add
                        [Flapjack.CrepExp.load
                            (Flapjack.CrepExp.op Flapjack.BinOp.sub
                              [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
                          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                            [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]]))
                    (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 12#64, Flapjack.CrepExp.const 4#64]),
                  Flapjack.CrepExp.const 15#64],
              Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.and
                [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                    (Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.add
                        [Flapjack.CrepExp.load
                            (Flapjack.CrepExp.op Flapjack.BinOp.sub
                              [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
                          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                            [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]]))
                    (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 13#64, Flapjack.CrepExp.const 4#64]),
                  Flapjack.CrepExp.const 15#64],
              Flapjack.CrepExp.const 8#64]])]

def crepBody566_36 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody566_35

def crepBody566_37 : CrepProg (BitVec 64) :=
.seq crepBody566_34 crepBody566_36

def crepBody566_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "blake2_g"
  [Flapjack.CrepExp.const 3#64, Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 9#64, Flapjack.CrepExp.const 14#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.and
                [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                    (Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.add
                        [Flapjack.CrepExp.load
                            (Flapjack.CrepExp.op Flapjack.BinOp.sub
                              [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
                          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                            [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]]))
                    (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 14#64, Flapjack.CrepExp.const 4#64]),
                  Flapjack.CrepExp.const 15#64],
              Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.and
                [Flapjack.CrepExp.shift Flapjack.Shift.lsr
                    (Flapjack.CrepExp.load
                      (Flapjack.CrepExp.op Flapjack.BinOp.add
                        [Flapjack.CrepExp.load
                            (Flapjack.CrepExp.op Flapjack.BinOp.sub
                              [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 352#64]),
                          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                            [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64]]))
                    (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
                      [Flapjack.CrepExp.const 15#64, Flapjack.CrepExp.const 4#64]),
                  Flapjack.CrepExp.const 15#64],
              Flapjack.CrepExp.const 8#64]])]

def crepBody566_39 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody566_38

def crepBody566_40 : CrepProg (BitVec 64) :=
.seq crepBody566_37 crepBody566_39

def crepBody566_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.var 8)

def crepBody566_42 : CrepProg (BitVec 64) :=
.seq crepBody566_41 crepBody566_6

def crepBody566_43 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 1#64]) crepBody566_42

def crepBody566_44 : CrepProg (BitVec 64) :=
.seq crepBody566_40 crepBody566_43

def crepBody566_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 8)

def crepBody566_46 : CrepProg (BitVec 64) :=
.seq crepBody566_45 crepBody566_6

def crepBody566_47 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 1#64]) crepBody566_46

def crepBody566_48 : CrepProg (BitVec 64) :=
.seq crepBody566_44 crepBody566_47

def crepBody566_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.const 0#64)

def crepBody566_50 : CrepProg (BitVec 64) :=
.seq crepBody566_49 crepBody566_6

def crepBody566_51 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 10#64)) crepBody566_50 crepBody566_6

def crepBody566_52 : CrepProg (BitVec 64) :=
.seq crepBody566_48 crepBody566_51

def crepBody566_53 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 0)) crepBody566_52

def crepBody566_54 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 10)

def crepBody566_55 : CrepProg (BitVec 64) :=
.seq crepBody566_54 crepBody566_6

def crepBody566_56 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.xor
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 1,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 368#64]),
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 368#64]),
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64],
              Flapjack.CrepExp.const 8#64]])]) crepBody566_55

def crepBody566_57 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 1,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]]) crepBody566_56

def crepBody566_58 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 9)

def crepBody566_59 : CrepProg (BitVec 64) :=
.seq crepBody566_58 crepBody566_6

def crepBody566_60 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 1#64]) crepBody566_59

def crepBody566_61 : CrepProg (BitVec 64) :=
.seq crepBody566_57 crepBody566_60

def crepBody566_62 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 8#64)) crepBody566_61

def crepBody566_63 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody566_64 : CrepProg (BitVec 64) :=
.seq crepBody566_62 crepBody566_63

def crepBody566_65 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody566_64

def crepBody566_66 : CrepProg (BitVec 64) :=
.seq crepBody566_53 crepBody566_65

def crepBody566_67 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody566_66

def crepBody566_68 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody566_67

def crepBody566_69 : CrepProg (BitVec 64) :=
.seq crepBody566_17 crepBody566_68

def data566 : CrepProg (BitVec 64) := crepBody566_69
def output566 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [98#8, 108#8, 97#8, 107#8, 101#8, 50#8, 98#8, 95#8, 102#8], [0, 1, 2, 3, 4, 5], crepProgToHOL data566)
end InitECandidate.Proofs.FrontendStages.Crep
