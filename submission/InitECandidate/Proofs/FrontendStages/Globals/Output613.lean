import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data613
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate593
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody613_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 328#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "blk",
            Flapjack.Exp.panOp Flapjack.PanOp.mul
              [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 4#64]]),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "blk",
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 4#64],
              Flapjack.Exp.const 1#64]))
        (Flapjack.Exp.const 8#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "blk",
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 4#64],
              Flapjack.Exp.const 2#64]))
        (Flapjack.Exp.const 16#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "blk",
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 4#64],
              Flapjack.Exp.const 3#64]))
        (Flapjack.Exp.const 24#64)])

def globalBody613_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody613_2 : Prog (BitVec 64) :=
.seq globalBody613_0 globalBody613_1

def globalBody613_3 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 16#64)) globalBody613_2

def globalBody613_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "t"
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.op Flapjack.BinOp.and
            [Flapjack.Exp.op Flapjack.BinOp.or
                [Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.var Flapjack.VarKind.local "t")
                    (Flapjack.Exp.var Flapjack.VarKind.local "sl"),
                  Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "t")
                    (Flapjack.Exp.op Flapjack.BinOp.sub
                      [Flapjack.Exp.const 32#64, Flapjack.Exp.var Flapjack.VarKind.local "sl"])],
              Flapjack.Exp.const 4294967295#64],
          Flapjack.Exp.var Flapjack.VarKind.local "e"],
      Flapjack.Exp.const 4294967295#64])

def globalBody613_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "a" (Flapjack.Exp.var Flapjack.VarKind.local "e")

def globalBody613_6 : Prog (BitVec 64) :=
.seq globalBody613_4 globalBody613_5

def globalBody613_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "e" (Flapjack.Exp.var Flapjack.VarKind.local "d")

def globalBody613_8 : Prog (BitVec 64) :=
.seq globalBody613_6 globalBody613_7

def globalBody613_9 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "d"
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.op Flapjack.BinOp.or
        [Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.var Flapjack.VarKind.local "c") (Flapjack.Exp.const 10#64),
          Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "c")
            (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 32#64, Flapjack.Exp.const 10#64])],
      Flapjack.Exp.const 4294967295#64])

def globalBody613_10 : Prog (BitVec 64) :=
.seq globalBody613_8 globalBody613_9

def globalBody613_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "c" (Flapjack.Exp.var Flapjack.VarKind.local "b")

def globalBody613_12 : Prog (BitVec 64) :=
.seq globalBody613_10 globalBody613_11

def globalBody613_13 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "b" (Flapjack.Exp.var Flapjack.VarKind.local "t")

def globalBody613_14 : Prog (BitVec 64) :=
.seq globalBody613_12 globalBody613_13

def globalBody613_15 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "tp"
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.op Flapjack.BinOp.and
            [Flapjack.Exp.op Flapjack.BinOp.or
                [Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.var Flapjack.VarKind.local "tp")
                    (Flapjack.Exp.var Flapjack.VarKind.local "sr"),
                  Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "tp")
                    (Flapjack.Exp.op Flapjack.BinOp.sub
                      [Flapjack.Exp.const 32#64, Flapjack.Exp.var Flapjack.VarKind.local "sr"])],
              Flapjack.Exp.const 4294967295#64],
          Flapjack.Exp.var Flapjack.VarKind.local "ep"],
      Flapjack.Exp.const 4294967295#64])

def globalBody613_16 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "ap" (Flapjack.Exp.var Flapjack.VarKind.local "ep")

def globalBody613_17 : Prog (BitVec 64) :=
.seq globalBody613_15 globalBody613_16

def globalBody613_18 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "ep" (Flapjack.Exp.var Flapjack.VarKind.local "dp")

def globalBody613_19 : Prog (BitVec 64) :=
.seq globalBody613_17 globalBody613_18

def globalBody613_20 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "dp"
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.op Flapjack.BinOp.or
        [Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.var Flapjack.VarKind.local "cp")
            (Flapjack.Exp.const 10#64),
          Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "cp")
            (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 32#64, Flapjack.Exp.const 10#64])],
      Flapjack.Exp.const 4294967295#64])

def globalBody613_21 : Prog (BitVec 64) :=
.seq globalBody613_19 globalBody613_20

def globalBody613_22 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "cp" (Flapjack.Exp.var Flapjack.VarKind.local "bp")

def globalBody613_23 : Prog (BitVec 64) :=
.seq globalBody613_21 globalBody613_22

def globalBody613_24 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "bp" (Flapjack.Exp.var Flapjack.VarKind.local "tp")

def globalBody613_25 : Prog (BitVec 64) :=
.seq globalBody613_23 globalBody613_24

def globalBody613_26 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def globalBody613_27 : Prog (BitVec 64) :=
.seq globalBody613_25 globalBody613_26

def globalBody613_28 : Prog (BitVec 64) :=
.dec ("sr") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.shift Flapjack.Shift.lsr
      (Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.load Flapjack.Shape.one
              (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 320#64]),
            Flapjack.Exp.panOp Flapjack.PanOp.mul
              [Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 3#64, Flapjack.Exp.const 5#64],
                    Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "j")
                      (Flapjack.Exp.const 4#64)],
                Flapjack.Exp.const 8#64]]))
      (Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 15#64],
          Flapjack.Exp.const 4#64]),
    Flapjack.Exp.const 15#64]) globalBody613_27

def globalBody613_29 : Prog (BitVec 64) :=
.dec ("tp") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "ap", Flapjack.Exp.var Flapjack.VarKind.local "fr",
        Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.load Flapjack.Shape.one
                (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 328#64]),
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.op Flapjack.BinOp.and
                    [Flapjack.Exp.shift Flapjack.Shift.lsr
                        (Flapjack.Exp.load Flapjack.Shape.one
                          (Flapjack.Exp.op Flapjack.BinOp.add
                            [Flapjack.Exp.load Flapjack.Shape.one
                                (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 320#64]),
                              Flapjack.Exp.panOp Flapjack.PanOp.mul
                                [Flapjack.Exp.op Flapjack.BinOp.add
                                    [Flapjack.Exp.panOp Flapjack.PanOp.mul
                                        [Flapjack.Exp.const 1#64, Flapjack.Exp.const 5#64],
                                      Flapjack.Exp.shift Flapjack.Shift.lsr
                                        (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 4#64)],
                                  Flapjack.Exp.const 8#64]]))
                        (Flapjack.Exp.panOp Flapjack.PanOp.mul
                          [Flapjack.Exp.op Flapjack.BinOp.and
                              [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 15#64],
                            Flapjack.Exp.const 4#64]),
                      Flapjack.Exp.const 15#64],
                  Flapjack.Exp.const 8#64]]),
        Flapjack.Exp.var Flapjack.VarKind.local "kr"],
    Flapjack.Exp.const 4294967295#64]) globalBody613_28

def globalBody613_30 : Prog (BitVec 64) :=
.decCall ("kr") (Flapjack.Shape.one) ("rmd_kp") ([Flapjack.Exp.var Flapjack.VarKind.local "j"]) globalBody613_29

def globalBody613_31 : Prog (BitVec 64) :=
.decCall ("fr") (Flapjack.Shape.one) ("rmd_f") ([Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 79#64, Flapjack.Exp.var Flapjack.VarKind.local "j"],
  Flapjack.Exp.var Flapjack.VarKind.local "bp", Flapjack.Exp.var Flapjack.VarKind.local "cp",
  Flapjack.Exp.var Flapjack.VarKind.local "dp"]) globalBody613_30

def globalBody613_32 : Prog (BitVec 64) :=
.seq globalBody613_14 globalBody613_31

def globalBody613_33 : Prog (BitVec 64) :=
.dec ("sl") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.shift Flapjack.Shift.lsr
      (Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.load Flapjack.Shape.one
              (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 320#64]),
            Flapjack.Exp.panOp Flapjack.PanOp.mul
              [Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.const 5#64],
                    Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "j")
                      (Flapjack.Exp.const 4#64)],
                Flapjack.Exp.const 8#64]]))
      (Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 15#64],
          Flapjack.Exp.const 4#64]),
    Flapjack.Exp.const 15#64]) globalBody613_32

def globalBody613_34 : Prog (BitVec 64) :=
.dec ("t") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "fl",
        Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.load Flapjack.Shape.one
                (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 328#64]),
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.op Flapjack.BinOp.and
                    [Flapjack.Exp.shift Flapjack.Shift.lsr
                        (Flapjack.Exp.load Flapjack.Shape.one
                          (Flapjack.Exp.op Flapjack.BinOp.add
                            [Flapjack.Exp.load Flapjack.Shape.one
                                (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 320#64]),
                              Flapjack.Exp.panOp Flapjack.PanOp.mul
                                [Flapjack.Exp.op Flapjack.BinOp.add
                                    [Flapjack.Exp.panOp Flapjack.PanOp.mul
                                        [Flapjack.Exp.const 0#64, Flapjack.Exp.const 5#64],
                                      Flapjack.Exp.shift Flapjack.Shift.lsr
                                        (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 4#64)],
                                  Flapjack.Exp.const 8#64]]))
                        (Flapjack.Exp.panOp Flapjack.PanOp.mul
                          [Flapjack.Exp.op Flapjack.BinOp.and
                              [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 15#64],
                            Flapjack.Exp.const 4#64]),
                      Flapjack.Exp.const 15#64],
                  Flapjack.Exp.const 8#64]]),
        Flapjack.Exp.var Flapjack.VarKind.local "kl"],
    Flapjack.Exp.const 4294967295#64]) globalBody613_33

def globalBody613_35 : Prog (BitVec 64) :=
.decCall ("kl") (Flapjack.Shape.one) ("rmd_k") ([Flapjack.Exp.var Flapjack.VarKind.local "j"]) globalBody613_34

def globalBody613_36 : Prog (BitVec 64) :=
.decCall ("fl") (Flapjack.Shape.one) ("rmd_f") ([Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.var Flapjack.VarKind.local "b",
  Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.var Flapjack.VarKind.local "d"]) globalBody613_35

def globalBody613_37 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 80#64)) globalBody613_36

def globalBody613_38 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "hp")
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "h1", Flapjack.Exp.var Flapjack.VarKind.local "c",
          Flapjack.Exp.var Flapjack.VarKind.local "dp"],
      Flapjack.Exp.const 4294967295#64])

def globalBody613_39 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hp", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "h2", Flapjack.Exp.var Flapjack.VarKind.local "d",
          Flapjack.Exp.var Flapjack.VarKind.local "ep"],
      Flapjack.Exp.const 4294967295#64])

def globalBody613_40 : Prog (BitVec 64) :=
.seq globalBody613_38 globalBody613_39

def globalBody613_41 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hp", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "h3", Flapjack.Exp.var Flapjack.VarKind.local "e",
          Flapjack.Exp.var Flapjack.VarKind.local "ap"],
      Flapjack.Exp.const 4294967295#64])

def globalBody613_42 : Prog (BitVec 64) :=
.seq globalBody613_40 globalBody613_41

def globalBody613_43 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hp", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "h4", Flapjack.Exp.var Flapjack.VarKind.local "a",
          Flapjack.Exp.var Flapjack.VarKind.local "bp"],
      Flapjack.Exp.const 4294967295#64])

def globalBody613_44 : Prog (BitVec 64) :=
.seq globalBody613_42 globalBody613_43

def globalBody613_45 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hp", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "h0", Flapjack.Exp.var Flapjack.VarKind.local "b",
          Flapjack.Exp.var Flapjack.VarKind.local "cp"],
      Flapjack.Exp.const 4294967295#64])

def globalBody613_46 : Prog (BitVec 64) :=
.seq globalBody613_44 globalBody613_45

def globalBody613_47 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody613_48 : Prog (BitVec 64) :=
.seq globalBody613_46 globalBody613_47

def globalBody613_49 : Prog (BitVec 64) :=
.dec ("h4") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hp", Flapjack.Exp.const 32#64])) globalBody613_48

def globalBody613_50 : Prog (BitVec 64) :=
.dec ("h3") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hp", Flapjack.Exp.const 24#64])) globalBody613_49

def globalBody613_51 : Prog (BitVec 64) :=
.dec ("h2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hp", Flapjack.Exp.const 16#64])) globalBody613_50

def globalBody613_52 : Prog (BitVec 64) :=
.dec ("h1") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hp", Flapjack.Exp.const 8#64])) globalBody613_51

def globalBody613_53 : Prog (BitVec 64) :=
.dec ("h0") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "hp")) globalBody613_52

def globalBody613_54 : Prog (BitVec 64) :=
.seq globalBody613_37 globalBody613_53

def globalBody613_55 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody613_54

def globalBody613_56 : Prog (BitVec 64) :=
.dec ("ep") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "e") globalBody613_55

def globalBody613_57 : Prog (BitVec 64) :=
.dec ("dp") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "d") globalBody613_56

def globalBody613_58 : Prog (BitVec 64) :=
.dec ("cp") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "c") globalBody613_57

def globalBody613_59 : Prog (BitVec 64) :=
.dec ("bp") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "b") globalBody613_58

def globalBody613_60 : Prog (BitVec 64) :=
.dec ("ap") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "a") globalBody613_59

def globalBody613_61 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hp", Flapjack.Exp.const 32#64])) globalBody613_60

def globalBody613_62 : Prog (BitVec 64) :=
.dec ("d") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hp", Flapjack.Exp.const 24#64])) globalBody613_61

def globalBody613_63 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hp", Flapjack.Exp.const 16#64])) globalBody613_62

def globalBody613_64 : Prog (BitVec 64) :=
.dec ("b") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "hp", Flapjack.Exp.const 8#64])) globalBody613_63

def globalBody613_65 : Prog (BitVec 64) :=
.dec ("a") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "hp")) globalBody613_64

def globalBody613_66 : Prog (BitVec 64) :=
.seq globalBody613_3 globalBody613_65

def globalBody613_67 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody613_66

def globalData613 : Decl (BitVec 64) :=
.function { name := "ripemd160_block", inline := false, exported := false, params := [("hp", Flapjack.Shape.one), ("blk", Flapjack.Shape.one)], body := globalBody613_67, returnShape := (Flapjack.Shape.one) }
def globalOutput613 := Pancake.PanLang.declToHOL globalData613
end InitECandidate.Proofs.FrontendStages.Declarations
