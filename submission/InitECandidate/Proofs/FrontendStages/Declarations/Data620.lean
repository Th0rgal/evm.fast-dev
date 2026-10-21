import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify604
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body620_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.global "b2_v", Flapjack.Exp.var Flapjack.VarKind.local "h",
    Flapjack.Exp.const 64#64]

def body620_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_v", Flapjack.Exp.const 64#64],
    Flapjack.Exp.var Flapjack.VarKind.global "b2_iv", Flapjack.Exp.const 64#64]

def body620_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_v", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.op Flapjack.BinOp.xor
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.global "b2_v",
            Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 12#64, Flapjack.Exp.const 8#64]]),
      Flapjack.Exp.var Flapjack.VarKind.local "t0"])

def body620_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_v", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.op Flapjack.BinOp.xor
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.global "b2_v",
            Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 13#64, Flapjack.Exp.const 8#64]]),
      Flapjack.Exp.var Flapjack.VarKind.local "t1"])

def body620_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "b2_v", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.op Flapjack.BinOp.xor
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.global "b2_v",
            Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 14#64, Flapjack.Exp.const 8#64]]),
      Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 0#64, Flapjack.Exp.const 1#64]])

def body620_5 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body620_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "f") (Flapjack.Exp.const 0#64)) body620_4 body620_5

def body620_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "blake2_g"
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 4#64, Flapjack.Exp.const 8#64, Flapjack.Exp.const 12#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "m",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.op Flapjack.BinOp.and
                [Flapjack.Exp.shift Flapjack.Shift.lsr
                    (Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.add
                        [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma",
                          Flapjack.Exp.panOp Flapjack.PanOp.mul
                            [Flapjack.Exp.var Flapjack.VarKind.local "row", Flapjack.Exp.const 8#64]]))
                    (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 0#64, Flapjack.Exp.const 4#64]),
                  Flapjack.Exp.const 15#64],
              Flapjack.Exp.const 8#64]]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "m",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.op Flapjack.BinOp.and
                [Flapjack.Exp.shift Flapjack.Shift.lsr
                    (Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.add
                        [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma",
                          Flapjack.Exp.panOp Flapjack.PanOp.mul
                            [Flapjack.Exp.var Flapjack.VarKind.local "row", Flapjack.Exp.const 8#64]]))
                    (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 1#64, Flapjack.Exp.const 4#64]),
                  Flapjack.Exp.const 15#64],
              Flapjack.Exp.const 8#64]])]

def body620_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "blake2_g"
  [Flapjack.Exp.const 1#64, Flapjack.Exp.const 5#64, Flapjack.Exp.const 9#64, Flapjack.Exp.const 13#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "m",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.op Flapjack.BinOp.and
                [Flapjack.Exp.shift Flapjack.Shift.lsr
                    (Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.add
                        [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma",
                          Flapjack.Exp.panOp Flapjack.PanOp.mul
                            [Flapjack.Exp.var Flapjack.VarKind.local "row", Flapjack.Exp.const 8#64]]))
                    (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.const 4#64]),
                  Flapjack.Exp.const 15#64],
              Flapjack.Exp.const 8#64]]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "m",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.op Flapjack.BinOp.and
                [Flapjack.Exp.shift Flapjack.Shift.lsr
                    (Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.add
                        [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma",
                          Flapjack.Exp.panOp Flapjack.PanOp.mul
                            [Flapjack.Exp.var Flapjack.VarKind.local "row", Flapjack.Exp.const 8#64]]))
                    (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 3#64, Flapjack.Exp.const 4#64]),
                  Flapjack.Exp.const 15#64],
              Flapjack.Exp.const 8#64]])]

def body620_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "blake2_g"
  [Flapjack.Exp.const 2#64, Flapjack.Exp.const 6#64, Flapjack.Exp.const 10#64, Flapjack.Exp.const 14#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "m",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.op Flapjack.BinOp.and
                [Flapjack.Exp.shift Flapjack.Shift.lsr
                    (Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.add
                        [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma",
                          Flapjack.Exp.panOp Flapjack.PanOp.mul
                            [Flapjack.Exp.var Flapjack.VarKind.local "row", Flapjack.Exp.const 8#64]]))
                    (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 4#64, Flapjack.Exp.const 4#64]),
                  Flapjack.Exp.const 15#64],
              Flapjack.Exp.const 8#64]]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "m",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.op Flapjack.BinOp.and
                [Flapjack.Exp.shift Flapjack.Shift.lsr
                    (Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.add
                        [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma",
                          Flapjack.Exp.panOp Flapjack.PanOp.mul
                            [Flapjack.Exp.var Flapjack.VarKind.local "row", Flapjack.Exp.const 8#64]]))
                    (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 5#64, Flapjack.Exp.const 4#64]),
                  Flapjack.Exp.const 15#64],
              Flapjack.Exp.const 8#64]])]

def body620_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "blake2_g"
  [Flapjack.Exp.const 3#64, Flapjack.Exp.const 7#64, Flapjack.Exp.const 11#64, Flapjack.Exp.const 15#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "m",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.op Flapjack.BinOp.and
                [Flapjack.Exp.shift Flapjack.Shift.lsr
                    (Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.add
                        [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma",
                          Flapjack.Exp.panOp Flapjack.PanOp.mul
                            [Flapjack.Exp.var Flapjack.VarKind.local "row", Flapjack.Exp.const 8#64]]))
                    (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 6#64, Flapjack.Exp.const 4#64]),
                  Flapjack.Exp.const 15#64],
              Flapjack.Exp.const 8#64]]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "m",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.op Flapjack.BinOp.and
                [Flapjack.Exp.shift Flapjack.Shift.lsr
                    (Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.add
                        [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma",
                          Flapjack.Exp.panOp Flapjack.PanOp.mul
                            [Flapjack.Exp.var Flapjack.VarKind.local "row", Flapjack.Exp.const 8#64]]))
                    (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 7#64, Flapjack.Exp.const 4#64]),
                  Flapjack.Exp.const 15#64],
              Flapjack.Exp.const 8#64]])]

def body620_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "blake2_g"
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 5#64, Flapjack.Exp.const 10#64, Flapjack.Exp.const 15#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "m",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.op Flapjack.BinOp.and
                [Flapjack.Exp.shift Flapjack.Shift.lsr
                    (Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.add
                        [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma",
                          Flapjack.Exp.panOp Flapjack.PanOp.mul
                            [Flapjack.Exp.var Flapjack.VarKind.local "row", Flapjack.Exp.const 8#64]]))
                    (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 8#64, Flapjack.Exp.const 4#64]),
                  Flapjack.Exp.const 15#64],
              Flapjack.Exp.const 8#64]]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "m",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.op Flapjack.BinOp.and
                [Flapjack.Exp.shift Flapjack.Shift.lsr
                    (Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.add
                        [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma",
                          Flapjack.Exp.panOp Flapjack.PanOp.mul
                            [Flapjack.Exp.var Flapjack.VarKind.local "row", Flapjack.Exp.const 8#64]]))
                    (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 9#64, Flapjack.Exp.const 4#64]),
                  Flapjack.Exp.const 15#64],
              Flapjack.Exp.const 8#64]])]

def body620_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "blake2_g"
  [Flapjack.Exp.const 1#64, Flapjack.Exp.const 6#64, Flapjack.Exp.const 11#64, Flapjack.Exp.const 12#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "m",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.op Flapjack.BinOp.and
                [Flapjack.Exp.shift Flapjack.Shift.lsr
                    (Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.add
                        [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma",
                          Flapjack.Exp.panOp Flapjack.PanOp.mul
                            [Flapjack.Exp.var Flapjack.VarKind.local "row", Flapjack.Exp.const 8#64]]))
                    (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 10#64, Flapjack.Exp.const 4#64]),
                  Flapjack.Exp.const 15#64],
              Flapjack.Exp.const 8#64]]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "m",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.op Flapjack.BinOp.and
                [Flapjack.Exp.shift Flapjack.Shift.lsr
                    (Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.add
                        [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma",
                          Flapjack.Exp.panOp Flapjack.PanOp.mul
                            [Flapjack.Exp.var Flapjack.VarKind.local "row", Flapjack.Exp.const 8#64]]))
                    (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 11#64, Flapjack.Exp.const 4#64]),
                  Flapjack.Exp.const 15#64],
              Flapjack.Exp.const 8#64]])]

def body620_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "blake2_g"
  [Flapjack.Exp.const 2#64, Flapjack.Exp.const 7#64, Flapjack.Exp.const 8#64, Flapjack.Exp.const 13#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "m",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.op Flapjack.BinOp.and
                [Flapjack.Exp.shift Flapjack.Shift.lsr
                    (Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.add
                        [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma",
                          Flapjack.Exp.panOp Flapjack.PanOp.mul
                            [Flapjack.Exp.var Flapjack.VarKind.local "row", Flapjack.Exp.const 8#64]]))
                    (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 12#64, Flapjack.Exp.const 4#64]),
                  Flapjack.Exp.const 15#64],
              Flapjack.Exp.const 8#64]]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "m",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.op Flapjack.BinOp.and
                [Flapjack.Exp.shift Flapjack.Shift.lsr
                    (Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.add
                        [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma",
                          Flapjack.Exp.panOp Flapjack.PanOp.mul
                            [Flapjack.Exp.var Flapjack.VarKind.local "row", Flapjack.Exp.const 8#64]]))
                    (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 13#64, Flapjack.Exp.const 4#64]),
                  Flapjack.Exp.const 15#64],
              Flapjack.Exp.const 8#64]])]

def body620_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "blake2_g"
  [Flapjack.Exp.const 3#64, Flapjack.Exp.const 4#64, Flapjack.Exp.const 9#64, Flapjack.Exp.const 14#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "m",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.op Flapjack.BinOp.and
                [Flapjack.Exp.shift Flapjack.Shift.lsr
                    (Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.add
                        [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma",
                          Flapjack.Exp.panOp Flapjack.PanOp.mul
                            [Flapjack.Exp.var Flapjack.VarKind.local "row", Flapjack.Exp.const 8#64]]))
                    (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 14#64, Flapjack.Exp.const 4#64]),
                  Flapjack.Exp.const 15#64],
              Flapjack.Exp.const 8#64]]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "m",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.op Flapjack.BinOp.and
                [Flapjack.Exp.shift Flapjack.Shift.lsr
                    (Flapjack.Exp.load Flapjack.Shape.one
                      (Flapjack.Exp.op Flapjack.BinOp.add
                        [Flapjack.Exp.var Flapjack.VarKind.global "b2_sigma",
                          Flapjack.Exp.panOp Flapjack.PanOp.mul
                            [Flapjack.Exp.var Flapjack.VarKind.local "row", Flapjack.Exp.const 8#64]]))
                    (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 15#64, Flapjack.Exp.const 4#64]),
                  Flapjack.Exp.const 15#64],
              Flapjack.Exp.const 8#64]])]

def body620_15 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "r"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 1#64])

def body620_16 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "row"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "row", Flapjack.Exp.const 1#64])

def body620_17 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "row" (Flapjack.Exp.const 0#64)

def body620_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "row") (Flapjack.Exp.const 10#64)) body620_17 body620_5

def body620_19 : Prog (BitVec 64) :=
.seq body620_16 body620_18

def body620_20 : Prog (BitVec 64) :=
.seq body620_15 body620_19

def body620_21 : Prog (BitVec 64) :=
.seq body620_14 body620_20

def body620_22 : Prog (BitVec 64) :=
.seq body620_13 body620_21

def body620_23 : Prog (BitVec 64) :=
.seq body620_12 body620_22

def body620_24 : Prog (BitVec 64) :=
.seq body620_11 body620_23

def body620_25 : Prog (BitVec 64) :=
.seq body620_10 body620_24

def body620_26 : Prog (BitVec 64) :=
.seq body620_9 body620_25

def body620_27 : Prog (BitVec 64) :=
.seq body620_8 body620_26

def body620_28 : Prog (BitVec 64) :=
.seq body620_7 body620_27

def body620_29 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "r")
  (Flapjack.Exp.var Flapjack.VarKind.local "rounds")) body620_28

def body620_30 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "h",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])
  (Flapjack.Exp.op Flapjack.BinOp.xor
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "h",
            Flapjack.Exp.panOp Flapjack.PanOp.mul
              [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]]),
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.global "b2_v",
            Flapjack.Exp.panOp Flapjack.PanOp.mul
              [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]]),
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.global "b2_v",
            Flapjack.Exp.panOp Flapjack.PanOp.mul
              [Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64],
                Flapjack.Exp.const 8#64]])])

def body620_31 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body620_32 : Prog (BitVec 64) :=
.seq body620_30 body620_31

def body620_33 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 8#64)) body620_32

def body620_34 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body620_35 : Prog (BitVec 64) :=
.seq body620_33 body620_34

def body620_36 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body620_35

def body620_37 : Prog (BitVec 64) :=
.seq body620_29 body620_36

def body620_38 : Prog (BitVec 64) :=
.dec ("row") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body620_37

def body620_39 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body620_38

def body620_40 : Prog (BitVec 64) :=
.seq body620_6 body620_39

def body620_41 : Prog (BitVec 64) :=
.seq body620_3 body620_40

def body620_42 : Prog (BitVec 64) :=
.seq body620_2 body620_41

def body620_43 : Prog (BitVec 64) :=
.seq body620_1 body620_42

def body620_44 : Prog (BitVec 64) :=
.seq body620_0 body620_43

def body620_45 : Prog (BitVec 64) :=
.seq body620_0 body620_1

def body620_46 : Prog (BitVec 64) :=
.seq body620_45 body620_2

def body620_47 : Prog (BitVec 64) :=
.seq body620_46 body620_3

def body620_48 : Prog (BitVec 64) :=
.seq body620_47 body620_6

def body620_49 : Prog (BitVec 64) :=
.seq body620_7 body620_8

def body620_50 : Prog (BitVec 64) :=
.seq body620_49 body620_9

def body620_51 : Prog (BitVec 64) :=
.seq body620_50 body620_10

def body620_52 : Prog (BitVec 64) :=
.seq body620_51 body620_11

def body620_53 : Prog (BitVec 64) :=
.seq body620_52 body620_12

def body620_54 : Prog (BitVec 64) :=
.seq body620_53 body620_13

def body620_55 : Prog (BitVec 64) :=
.seq body620_54 body620_14

def body620_56 : Prog (BitVec 64) :=
.seq body620_55 body620_15

def body620_57 : Prog (BitVec 64) :=
.seq body620_56 body620_16

def body620_58 : Prog (BitVec 64) :=
.seq body620_57 body620_18

def body620_59 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "r")
  (Flapjack.Exp.var Flapjack.VarKind.local "rounds")) body620_58

def body620_60 : Prog (BitVec 64) :=
.seq body620_59 body620_36

def body620_61 : Prog (BitVec 64) :=
.dec ("row") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body620_60

def body620_62 : Prog (BitVec 64) :=
.dec ("r") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body620_61

def body620_63 : Prog (BitVec 64) :=
.seq body620_48 body620_62

def originalData620 : Decl (BitVec 64) :=
.function { name := "blake2b_f", inline := false, exported := false, params := [("rounds", Flapjack.Shape.one), ("h", Flapjack.Shape.one), ("m", Flapjack.Shape.one), ("t0", Flapjack.Shape.one),
  ("t1", Flapjack.Shape.one), ("f", Flapjack.Shape.one)], body := body620_44, returnShape := (Flapjack.Shape.one) }
def simplifiedData620 : Decl (BitVec 64) :=
.function { name := "blake2b_f", inline := false, exported := false, params := [("rounds", Flapjack.Shape.one), ("h", Flapjack.Shape.one), ("m", Flapjack.Shape.one), ("t0", Flapjack.Shape.one),
  ("t1", Flapjack.Shape.one), ("f", Flapjack.Shape.one)], body := body620_63, returnShape := (Flapjack.Shape.one) }
def original620 := Pancake.PanLang.declToHOL originalData620
def simplified620 := Pancake.PanLang.declToHOL simplifiedData620
end InitECandidate.Proofs.FrontendStages.Declarations
