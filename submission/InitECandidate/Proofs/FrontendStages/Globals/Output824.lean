import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data824
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate808
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody824_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 10#64)

def globalBody824_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody824_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 213#64)) globalBody824_0 globalBody824_1

def globalBody824_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "rounds"]

def globalBody824_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 1#64) (Flapjack.Exp.var Flapjack.VarKind.local "f")) globalBody824_0 globalBody824_1

def globalBody824_5 : Prog (BitVec 64) :=
.seq globalBody824_3 globalBody824_4

def globalBody824_6 : Prog (BitVec 64) :=
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

def globalBody824_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody824_8 : Prog (BitVec 64) :=
.seq globalBody824_6 globalBody824_7

def globalBody824_9 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 8#64)) globalBody824_8

def globalBody824_10 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i" (Flapjack.Exp.const 0#64)

def globalBody824_11 : Prog (BitVec 64) :=
.seq globalBody824_9 globalBody824_10

def globalBody824_12 : Prog (BitVec 64) :=
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

def globalBody824_13 : Prog (BitVec 64) :=
.seq globalBody824_12 globalBody824_7

def globalBody824_14 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 16#64)) globalBody824_13

def globalBody824_15 : Prog (BitVec 64) :=
.seq globalBody824_11 globalBody824_14

def globalBody824_16 : Prog (BitVec 64) :=
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

def globalBody824_17 : Prog (BitVec 64) :=
.seq globalBody824_15 globalBody824_16

def globalBody824_18 : Prog (BitVec 64) :=
.seq globalBody824_17 globalBody824_10

def globalBody824_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "st_le64"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "out",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]],
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "h",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])]

def globalBody824_20 : Prog (BitVec 64) :=
.seq globalBody824_19 globalBody824_7

def globalBody824_21 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 8#64)) globalBody824_20

def globalBody824_22 : Prog (BitVec 64) :=
.seq globalBody824_18 globalBody824_21

def globalBody824_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody824_24 : Prog (BitVec 64) :=
.seq globalBody824_22 globalBody824_23

def globalBody824_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 120#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "out")

def globalBody824_26 : Prog (BitVec 64) :=
.seq globalBody824_24 globalBody824_25

def globalBody824_27 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 64#64)

def globalBody824_28 : Prog (BitVec 64) :=
.seq globalBody824_26 globalBody824_27

def globalBody824_29 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody824_30 : Prog (BitVec 64) :=
.seq globalBody824_28 globalBody824_29

def globalBody824_31 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody824_30

def globalBody824_32 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 128#64]) globalBody824_31

def globalBody824_33 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) globalBody824_32

def globalBody824_34 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody824_33

def globalBody824_35 : Prog (BitVec 64) :=
.decCall ("out") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) globalBody824_34

def globalBody824_36 : Prog (BitVec 64) :=
.seq globalBody824_5 globalBody824_35

def globalBody824_37 : Prog (BitVec 64) :=
.dec ("f") (Flapjack.Shape.one) (Flapjack.Exp.loadByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 212#64])) globalBody824_36

def globalBody824_38 : Prog (BitVec 64) :=
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
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 3#64])]) globalBody824_37

def globalBody824_39 : Prog (BitVec 64) :=
.dec ("data") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 88#64])) globalBody824_38

def globalBody824_40 : Prog (BitVec 64) :=
.seq globalBody824_2 globalBody824_39

def globalBody824_41 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 96#64])) globalBody824_40

def globalBody824_42 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 112#64])) globalBody824_41

def globalData824 : Decl (BitVec 64) :=
.function { name := "pre_blake2f", inline := false, exported := false, params := [], body := globalBody824_42, returnShape := (Flapjack.Shape.one) }
def globalOutput824 := Pancake.PanLang.declToHOL globalData824
end InitECandidate.Proofs.FrontendStages.Declarations
