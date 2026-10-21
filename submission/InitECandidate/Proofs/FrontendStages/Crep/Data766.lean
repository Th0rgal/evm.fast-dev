import InitECandidate.Proofs.FrontendStages.Crep.Translate750
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody766_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 3)

def crepBody766_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody766_2 : CrepProg (BitVec 64) :=
.seq crepBody766_0 crepBody766_1

def crepBody766_3 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 10#64) crepBody766_2

def crepBody766_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody766_5 : CrepProg (BitVec 64) :=
.seq crepBody766_3 crepBody766_4

def crepBody766_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 213#64)) crepBody766_5 crepBody766_1

def crepBody766_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "charge_gas" [Flapjack.CrepExp.var 4]

def crepBody766_8 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody766_7

def crepBody766_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 6)

def crepBody766_10 : CrepProg (BitVec 64) :=
.seq crepBody766_9 crepBody766_1

def crepBody766_11 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 10#64) crepBody766_10

def crepBody766_12 : CrepProg (BitVec 64) :=
.seq crepBody766_11 crepBody766_4

def crepBody766_13 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 1#64) (Flapjack.CrepExp.var 5)) crepBody766_12 crepBody766_1

def crepBody766_14 : CrepProg (BitVec 64) :=
.seq crepBody766_8 crepBody766_13

def crepBody766_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc" [Flapjack.CrepExp.const 64#64]

def crepBody766_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "heap_mark" []

def crepBody766_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "alloc" [Flapjack.CrepExp.const 64#64]

def crepBody766_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "alloc" [Flapjack.CrepExp.const 128#64]

def crepBody766_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.var 12)

def crepBody766_20 : CrepProg (BitVec 64) :=
.seq crepBody766_19 crepBody766_1

def crepBody766_21 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 4#64,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 4#64,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
            Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 4#64,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
            Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 4#64,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
            Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.op Flapjack.BinOp.or
        [Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 4#64,
                Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
                Flapjack.CrepExp.const 4#64]),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
                  Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 1#64]))
            (Flapjack.CrepExp.const 8#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
                  Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 2#64]))
            (Flapjack.CrepExp.const 16#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 4#64,
                  Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
                  Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 3#64]))
            (Flapjack.CrepExp.const 24#64)])
      (Flapjack.CrepExp.const 32#64)]) crepBody766_20

def crepBody766_22 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 8,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64]]) crepBody766_21

def crepBody766_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10 (Flapjack.CrepExp.var 11)

def crepBody766_24 : CrepProg (BitVec 64) :=
.seq crepBody766_23 crepBody766_1

def crepBody766_25 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 1#64]) crepBody766_24

def crepBody766_26 : CrepProg (BitVec 64) :=
.seq crepBody766_22 crepBody766_25

def crepBody766_27 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 8#64)) crepBody766_26

def crepBody766_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10 (Flapjack.CrepExp.const 0#64)

def crepBody766_29 : CrepProg (BitVec 64) :=
.seq crepBody766_28 crepBody766_1

def crepBody766_30 : CrepProg (BitVec 64) :=
.seq crepBody766_27 crepBody766_29

def crepBody766_31 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 68#64,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 68#64,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
            Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 68#64,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
            Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 68#64,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
            Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.op Flapjack.BinOp.or
        [Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 68#64,
                Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
                Flapjack.CrepExp.const 4#64]),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 68#64,
                  Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
                  Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 1#64]))
            (Flapjack.CrepExp.const 8#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 68#64,
                  Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
                  Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 2#64]))
            (Flapjack.CrepExp.const 16#64),
          Flapjack.CrepExp.shift Flapjack.Shift.lsl
            (Flapjack.CrepExp.loadByte
              (Flapjack.CrepExp.op Flapjack.BinOp.add
                [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 68#64,
                  Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64],
                  Flapjack.CrepExp.const 4#64, Flapjack.CrepExp.const 3#64]))
            (Flapjack.CrepExp.const 24#64)])
      (Flapjack.CrepExp.const 32#64)]) crepBody766_20

def crepBody766_32 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 9,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64]]) crepBody766_31

def crepBody766_33 : CrepProg (BitVec 64) :=
.seq crepBody766_32 crepBody766_25

def crepBody766_34 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 16#64)) crepBody766_33

def crepBody766_35 : CrepProg (BitVec 64) :=
.seq crepBody766_30 crepBody766_34

def crepBody766_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "blake2b_f"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9,
    Flapjack.CrepExp.op Flapjack.BinOp.or
      [Flapjack.CrepExp.loadByte
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 196#64]),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 196#64, Flapjack.CrepExp.const 1#64]))
          (Flapjack.CrepExp.const 8#64),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 196#64, Flapjack.CrepExp.const 2#64]))
          (Flapjack.CrepExp.const 16#64),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 196#64, Flapjack.CrepExp.const 3#64]))
          (Flapjack.CrepExp.const 24#64),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.op Flapjack.BinOp.or
            [Flapjack.CrepExp.loadByte
                (Flapjack.CrepExp.op Flapjack.BinOp.add
                  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 196#64, Flapjack.CrepExp.const 4#64]),
              Flapjack.CrepExp.shift Flapjack.Shift.lsl
                (Flapjack.CrepExp.loadByte
                  (Flapjack.CrepExp.op Flapjack.BinOp.add
                    [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 196#64, Flapjack.CrepExp.const 4#64,
                      Flapjack.CrepExp.const 1#64]))
                (Flapjack.CrepExp.const 8#64),
              Flapjack.CrepExp.shift Flapjack.Shift.lsl
                (Flapjack.CrepExp.loadByte
                  (Flapjack.CrepExp.op Flapjack.BinOp.add
                    [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 196#64, Flapjack.CrepExp.const 4#64,
                      Flapjack.CrepExp.const 2#64]))
                (Flapjack.CrepExp.const 16#64),
              Flapjack.CrepExp.shift Flapjack.Shift.lsl
                (Flapjack.CrepExp.loadByte
                  (Flapjack.CrepExp.op Flapjack.BinOp.add
                    [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 196#64, Flapjack.CrepExp.const 4#64,
                      Flapjack.CrepExp.const 3#64]))
                (Flapjack.CrepExp.const 24#64)])
          (Flapjack.CrepExp.const 32#64)],
    Flapjack.CrepExp.op Flapjack.BinOp.or
      [Flapjack.CrepExp.loadByte
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 204#64]),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 204#64, Flapjack.CrepExp.const 1#64]))
          (Flapjack.CrepExp.const 8#64),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 204#64, Flapjack.CrepExp.const 2#64]))
          (Flapjack.CrepExp.const 16#64),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add
              [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 204#64, Flapjack.CrepExp.const 3#64]))
          (Flapjack.CrepExp.const 24#64),
        Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.op Flapjack.BinOp.or
            [Flapjack.CrepExp.loadByte
                (Flapjack.CrepExp.op Flapjack.BinOp.add
                  [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 204#64, Flapjack.CrepExp.const 4#64]),
              Flapjack.CrepExp.shift Flapjack.Shift.lsl
                (Flapjack.CrepExp.loadByte
                  (Flapjack.CrepExp.op Flapjack.BinOp.add
                    [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 204#64, Flapjack.CrepExp.const 4#64,
                      Flapjack.CrepExp.const 1#64]))
                (Flapjack.CrepExp.const 8#64),
              Flapjack.CrepExp.shift Flapjack.Shift.lsl
                (Flapjack.CrepExp.loadByte
                  (Flapjack.CrepExp.op Flapjack.BinOp.add
                    [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 204#64, Flapjack.CrepExp.const 4#64,
                      Flapjack.CrepExp.const 2#64]))
                (Flapjack.CrepExp.const 16#64),
              Flapjack.CrepExp.shift Flapjack.Shift.lsl
                (Flapjack.CrepExp.loadByte
                  (Flapjack.CrepExp.op Flapjack.BinOp.add
                    [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 204#64, Flapjack.CrepExp.const 4#64,
                      Flapjack.CrepExp.const 3#64]))
                (Flapjack.CrepExp.const 24#64)])
          (Flapjack.CrepExp.const 32#64)],
    Flapjack.CrepExp.var 5]

def crepBody766_37 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody766_36

def crepBody766_38 : CrepProg (BitVec 64) :=
.seq crepBody766_35 crepBody766_37

def crepBody766_39 : CrepProg (BitVec 64) :=
.seq crepBody766_38 crepBody766_29

def crepBody766_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "st_le64"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 6,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64]],
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 8,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64]])]

def crepBody766_41 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody766_40

def crepBody766_42 : CrepProg (BitVec 64) :=
.seq crepBody766_41 crepBody766_25

def crepBody766_43 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 8#64)) crepBody766_42

def crepBody766_44 : CrepProg (BitVec 64) :=
.seq crepBody766_39 crepBody766_43

def crepBody766_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "heap_release" [Flapjack.CrepExp.var 7]

def crepBody766_46 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody766_45

def crepBody766_47 : CrepProg (BitVec 64) :=
.seq crepBody766_44 crepBody766_46

def crepBody766_48 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 6) crepBody766_20

def crepBody766_49 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody766_48

def crepBody766_50 : CrepProg (BitVec 64) :=
.seq crepBody766_47 crepBody766_49

def crepBody766_51 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 64#64) crepBody766_20

def crepBody766_52 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody766_51

def crepBody766_53 : CrepProg (BitVec 64) :=
.seq crepBody766_50 crepBody766_52

def crepBody766_54 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody766_55 : CrepProg (BitVec 64) :=
.seq crepBody766_53 crepBody766_54

def crepBody766_56 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody766_55

def crepBody766_57 : CrepProg (BitVec 64) :=
.seq crepBody766_18 crepBody766_56

def crepBody766_58 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody766_57

def crepBody766_59 : CrepProg (BitVec 64) :=
.seq crepBody766_17 crepBody766_58

def crepBody766_60 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody766_59

def crepBody766_61 : CrepProg (BitVec 64) :=
.seq crepBody766_16 crepBody766_60

def crepBody766_62 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody766_61

def crepBody766_63 : CrepProg (BitVec 64) :=
.seq crepBody766_15 crepBody766_62

def crepBody766_64 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody766_63

def crepBody766_65 : CrepProg (BitVec 64) :=
.seq crepBody766_14 crepBody766_64

def crepBody766_66 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.loadByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 212#64])) crepBody766_65

def crepBody766_67 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.shift Flapjack.Shift.lsl (Flapjack.CrepExp.loadByte (Flapjack.CrepExp.var 3))
      (Flapjack.CrepExp.const 24#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 3#64])]) crepBody766_66

def crepBody766_68 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 88#64])) crepBody766_67

def crepBody766_69 : CrepProg (BitVec 64) :=
.seq crepBody766_6 crepBody766_68

def crepBody766_70 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64])) crepBody766_69

def crepBody766_71 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody766_70

def data766 : CrepProg (BitVec 64) := crepBody766_71
def output766 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 95#8, 98#8, 108#8, 97#8, 107#8, 101#8, 50#8, 102#8], [], crepProgToHOL data766)
end InitECandidate.Proofs.FrontendStages.Crep
