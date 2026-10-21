import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify808
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body824_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 10#64)

def body824_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body824_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 213#64)) body824_0 body824_1

def body824_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "rounds"]

def body824_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 1#64) (Flapjack.Exp.var Flapjack.VarKind.local "f")) body824_0 body824_1

def body824_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "h",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 4#64,
            Flapjack.Exp.panOp Flapjack.PanOp.mul
              [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]]),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 4#64,
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64],
              Flapjack.Exp.const 1#64]))
        (Flapjack.Exp.const 8#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 4#64,
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64],
              Flapjack.Exp.const 2#64]))
        (Flapjack.Exp.const 16#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 4#64,
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64],
              Flapjack.Exp.const 3#64]))
        (Flapjack.Exp.const 24#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.op Flapjack.BinOp.or
          [Flapjack.Exp.loadByte
              (Flapjack.Exp.op Flapjack.BinOp.add
                [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 4#64,
                  Flapjack.Exp.panOp Flapjack.PanOp.mul
                    [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64],
                  Flapjack.Exp.const 4#64]),
            Flapjack.Exp.shift Flapjack.Shift.lsl
              (Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 4#64,
                    Flapjack.Exp.panOp Flapjack.PanOp.mul
                      [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64],
                    Flapjack.Exp.const 4#64, Flapjack.Exp.const 1#64]))
              (Flapjack.Exp.const 8#64),
            Flapjack.Exp.shift Flapjack.Shift.lsl
              (Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 4#64,
                    Flapjack.Exp.panOp Flapjack.PanOp.mul
                      [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64],
                    Flapjack.Exp.const 4#64, Flapjack.Exp.const 2#64]))
              (Flapjack.Exp.const 16#64),
            Flapjack.Exp.shift Flapjack.Shift.lsl
              (Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 4#64,
                    Flapjack.Exp.panOp Flapjack.PanOp.mul
                      [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64],
                    Flapjack.Exp.const 4#64, Flapjack.Exp.const 3#64]))
              (Flapjack.Exp.const 24#64)])
        (Flapjack.Exp.const 32#64)])

def body824_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body824_7 : Prog (BitVec 64) :=
.seq body824_5 body824_6

def body824_8 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 8#64)) body824_7

def body824_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i" (Flapjack.Exp.const 0#64)

def body824_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "m",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 68#64,
            Flapjack.Exp.panOp Flapjack.PanOp.mul
              [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]]),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 68#64,
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64],
              Flapjack.Exp.const 1#64]))
        (Flapjack.Exp.const 8#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 68#64,
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64],
              Flapjack.Exp.const 2#64]))
        (Flapjack.Exp.const 16#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 68#64,
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64],
              Flapjack.Exp.const 3#64]))
        (Flapjack.Exp.const 24#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.op Flapjack.BinOp.or
          [Flapjack.Exp.loadByte
              (Flapjack.Exp.op Flapjack.BinOp.add
                [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 68#64,
                  Flapjack.Exp.panOp Flapjack.PanOp.mul
                    [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64],
                  Flapjack.Exp.const 4#64]),
            Flapjack.Exp.shift Flapjack.Shift.lsl
              (Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 68#64,
                    Flapjack.Exp.panOp Flapjack.PanOp.mul
                      [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64],
                    Flapjack.Exp.const 4#64, Flapjack.Exp.const 1#64]))
              (Flapjack.Exp.const 8#64),
            Flapjack.Exp.shift Flapjack.Shift.lsl
              (Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 68#64,
                    Flapjack.Exp.panOp Flapjack.PanOp.mul
                      [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64],
                    Flapjack.Exp.const 4#64, Flapjack.Exp.const 2#64]))
              (Flapjack.Exp.const 16#64),
            Flapjack.Exp.shift Flapjack.Shift.lsl
              (Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 68#64,
                    Flapjack.Exp.panOp Flapjack.PanOp.mul
                      [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64],
                    Flapjack.Exp.const 4#64, Flapjack.Exp.const 3#64]))
              (Flapjack.Exp.const 24#64)])
        (Flapjack.Exp.const 32#64)])

def body824_11 : Prog (BitVec 64) :=
.seq body824_10 body824_6

def body824_12 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 16#64)) body824_11

def body824_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "blake2b_f"
  [Flapjack.Exp.var Flapjack.VarKind.local "rounds", Flapjack.Exp.var Flapjack.VarKind.local "h",
    Flapjack.Exp.var Flapjack.VarKind.local "m",
    Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 196#64]),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 196#64, Flapjack.Exp.const 1#64]))
          (Flapjack.Exp.const 8#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 196#64, Flapjack.Exp.const 2#64]))
          (Flapjack.Exp.const 16#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 196#64, Flapjack.Exp.const 3#64]))
          (Flapjack.Exp.const 24#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.op Flapjack.BinOp.or
            [Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 196#64, Flapjack.Exp.const 4#64]),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 196#64, Flapjack.Exp.const 4#64,
                      Flapjack.Exp.const 1#64]))
                (Flapjack.Exp.const 8#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 196#64, Flapjack.Exp.const 4#64,
                      Flapjack.Exp.const 2#64]))
                (Flapjack.Exp.const 16#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 196#64, Flapjack.Exp.const 4#64,
                      Flapjack.Exp.const 3#64]))
                (Flapjack.Exp.const 24#64)])
          (Flapjack.Exp.const 32#64)],
    Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 204#64]),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 204#64, Flapjack.Exp.const 1#64]))
          (Flapjack.Exp.const 8#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 204#64, Flapjack.Exp.const 2#64]))
          (Flapjack.Exp.const 16#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 204#64, Flapjack.Exp.const 3#64]))
          (Flapjack.Exp.const 24#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.op Flapjack.BinOp.or
            [Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 204#64, Flapjack.Exp.const 4#64]),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 204#64, Flapjack.Exp.const 4#64,
                      Flapjack.Exp.const 1#64]))
                (Flapjack.Exp.const 8#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 204#64, Flapjack.Exp.const 4#64,
                      Flapjack.Exp.const 2#64]))
                (Flapjack.Exp.const 16#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 204#64, Flapjack.Exp.const 4#64,
                      Flapjack.Exp.const 3#64]))
                (Flapjack.Exp.const 24#64)])
          (Flapjack.Exp.const 32#64)],
    Flapjack.Exp.var Flapjack.VarKind.local "f"]

def body824_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_le64"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "out",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]],
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "h",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])]

def body824_15 : Prog (BitVec 64) :=
.seq body824_14 body824_6

def body824_16 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 8#64)) body824_15

def body824_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body824_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out")

def body824_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 64#64)

def body824_20 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body824_21 : Prog (BitVec 64) :=
.seq body824_19 body824_20

def body824_22 : Prog (BitVec 64) :=
.seq body824_18 body824_21

def body824_23 : Prog (BitVec 64) :=
.seq body824_17 body824_22

def body824_24 : Prog (BitVec 64) :=
.seq body824_16 body824_23

def body824_25 : Prog (BitVec 64) :=
.seq body824_9 body824_24

def body824_26 : Prog (BitVec 64) :=
.seq body824_13 body824_25

def body824_27 : Prog (BitVec 64) :=
.seq body824_12 body824_26

def body824_28 : Prog (BitVec 64) :=
.seq body824_9 body824_27

def body824_29 : Prog (BitVec 64) :=
.seq body824_8 body824_28

def body824_30 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body824_29

def body824_31 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 128#64]) body824_30

def body824_32 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body824_31

def body824_33 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body824_32

def body824_34 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body824_33

def body824_35 : Prog (BitVec 64) :=
.seq body824_4 body824_34

def body824_36 : Prog (BitVec 64) :=
.seq body824_3 body824_35

def body824_37 : Prog (BitVec 64) :=
.dec ("f") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 212#64])) body824_36

def body824_38 : Prog (BitVec 64) :=
.dec ("rounds") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.or
  [Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "data"))
      (Flapjack.Exp.const 24#64),
    Flapjack.Exp.shift Flapjack.Shift.lsl
      (Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 1#64]))
      (Flapjack.Exp.const 16#64),
    Flapjack.Exp.shift Flapjack.Shift.lsl
      (Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 2#64]))
      (Flapjack.Exp.const 8#64),
    Flapjack.Exp.loadByte
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 3#64])]) body824_37

def body824_39 : Prog (BitVec 64) :=
.dec ("data") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64])) body824_38

def body824_40 : Prog (BitVec 64) :=
.seq body824_2 body824_39

def body824_41 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) body824_40

def body824_42 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body824_41

def body824_43 : Prog (BitVec 64) :=
.seq body824_3 body824_4

def body824_44 : Prog (BitVec 64) :=
.seq body824_8 body824_9

def body824_45 : Prog (BitVec 64) :=
.seq body824_44 body824_12

def body824_46 : Prog (BitVec 64) :=
.seq body824_45 body824_13

def body824_47 : Prog (BitVec 64) :=
.seq body824_46 body824_9

def body824_48 : Prog (BitVec 64) :=
.seq body824_47 body824_16

def body824_49 : Prog (BitVec 64) :=
.seq body824_48 body824_17

def body824_50 : Prog (BitVec 64) :=
.seq body824_49 body824_18

def body824_51 : Prog (BitVec 64) :=
.seq body824_50 body824_19

def body824_52 : Prog (BitVec 64) :=
.seq body824_51 body824_20

def body824_53 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body824_52

def body824_54 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 128#64]) body824_53

def body824_55 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body824_54

def body824_56 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body824_55

def body824_57 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body824_56

def body824_58 : Prog (BitVec 64) :=
.seq body824_43 body824_57

def body824_59 : Prog (BitVec 64) :=
.dec ("f") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 212#64])) body824_58

def body824_60 : Prog (BitVec 64) :=
.dec ("rounds") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.or
  [Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "data"))
      (Flapjack.Exp.const 24#64),
    Flapjack.Exp.shift Flapjack.Shift.lsl
      (Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 1#64]))
      (Flapjack.Exp.const 16#64),
    Flapjack.Exp.shift Flapjack.Shift.lsl
      (Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 2#64]))
      (Flapjack.Exp.const 8#64),
    Flapjack.Exp.loadByte
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 3#64])]) body824_59

def body824_61 : Prog (BitVec 64) :=
.dec ("data") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64])) body824_60

def body824_62 : Prog (BitVec 64) :=
.seq body824_2 body824_61

def body824_63 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) body824_62

def body824_64 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body824_63

def originalData824 : Decl (BitVec 64) :=
.function { name := "pre_blake2f", inline := false, exported := false, params := [], body := body824_42, returnShape := (Flapjack.Shape.one) }
def simplifiedData824 : Decl (BitVec 64) :=
.function { name := "pre_blake2f", inline := false, exported := false, params := [], body := body824_64, returnShape := (Flapjack.Shape.one) }
def original824 := Pancake.PanLang.declToHOL originalData824
def simplified824 := Pancake.PanLang.declToHOL simplifiedData824
end InitECandidate.Proofs.FrontendStages.Declarations
