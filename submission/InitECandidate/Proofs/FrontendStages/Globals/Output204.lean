import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data204
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate188
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody204_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 1#64]

def globalBody204_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody204_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "len") (Flapjack.Exp.const 2#64)) globalBody204_0 globalBody204_1

def globalBody204_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 2#64]

def globalBody204_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "p"))
        (Flapjack.Exp.const 21#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 1#64]))
        (Flapjack.Exp.const 1#64)])) globalBody204_3 globalBody204_1

def globalBody204_5 : Prog (BitVec 64) :=
.seq globalBody204_2 globalBody204_4

def globalBody204_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 2#64])

def globalBody204_7 : Prog (BitVec 64) :=
.seq globalBody204_5 globalBody204_6

def globalBody204_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "len"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "len", Flapjack.Exp.const 2#64])

def globalBody204_9 : Prog (BitVec 64) :=
.seq globalBody204_7 globalBody204_8

def globalBody204_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 80#64]

def globalBody204_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "len") (Flapjack.Exp.const 16#64)) globalBody204_10 globalBody204_1

def globalBody204_12 : Prog (BitVec 64) :=
.seq globalBody204_9 globalBody204_11

def globalBody204_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]))
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "p"),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 1#64]))
        (Flapjack.Exp.const 8#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 2#64]))
        (Flapjack.Exp.const 16#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 3#64]))
        (Flapjack.Exp.const 24#64)])

def globalBody204_14 : Prog (BitVec 64) :=
.seq globalBody204_12 globalBody204_13

def globalBody204_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 8#64])
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 4#64]),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 4#64, Flapjack.Exp.const 1#64]))
        (Flapjack.Exp.const 8#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 4#64, Flapjack.Exp.const 2#64]))
        (Flapjack.Exp.const 16#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 4#64, Flapjack.Exp.const 3#64]))
        (Flapjack.Exp.const 24#64)])

def globalBody204_16 : Prog (BitVec 64) :=
.seq globalBody204_14 globalBody204_15

def globalBody204_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_check_offsets"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]),
    Flapjack.Exp.const 2#64, Flapjack.Exp.const 16#64, Flapjack.Exp.var Flapjack.VarKind.local "len"]

def globalBody204_18 : Prog (BitVec 64) :=
.seq globalBody204_16 globalBody204_17

def globalBody204_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 88#64])
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 8#64]),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 8#64, Flapjack.Exp.const 1#64]))
        (Flapjack.Exp.const 8#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 8#64, Flapjack.Exp.const 2#64]))
        (Flapjack.Exp.const 16#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 8#64, Flapjack.Exp.const 3#64]))
        (Flapjack.Exp.const 24#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.op Flapjack.BinOp.or
          [Flapjack.Exp.loadByte
              (Flapjack.Exp.op Flapjack.BinOp.add
                [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 8#64, Flapjack.Exp.const 4#64]),
            Flapjack.Exp.shift Flapjack.Shift.lsl
              (Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 8#64, Flapjack.Exp.const 4#64,
                    Flapjack.Exp.const 1#64]))
              (Flapjack.Exp.const 8#64),
            Flapjack.Exp.shift Flapjack.Shift.lsl
              (Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 8#64, Flapjack.Exp.const 4#64,
                    Flapjack.Exp.const 2#64]))
              (Flapjack.Exp.const 16#64),
            Flapjack.Exp.shift Flapjack.Shift.lsl
              (Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 8#64, Flapjack.Exp.const 4#64,
                    Flapjack.Exp.const 3#64]))
              (Flapjack.Exp.const 24#64)])
        (Flapjack.Exp.const 32#64)])

def globalBody204_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 81#64]

def globalBody204_21 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "nlen") (Flapjack.Exp.const 44#64)) globalBody204_20 globalBody204_1

def globalBody204_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]))
  (Flapjack.Exp.var Flapjack.VarKind.local "o_pl")

def globalBody204_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "o_vh")

def globalBody204_24 : Prog (BitVec 64) :=
.seq globalBody204_22 globalBody204_23

def globalBody204_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "o_rq")

def globalBody204_26 : Prog (BitVec 64) :=
.seq globalBody204_24 globalBody204_25

def globalBody204_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_check_offsets"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]),
    Flapjack.Exp.const 3#64, Flapjack.Exp.const 44#64, Flapjack.Exp.var Flapjack.VarKind.local "nlen"]

def globalBody204_28 : Prog (BitVec 64) :=
.seq globalBody204_26 globalBody204_27

def globalBody204_29 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "pl")

def globalBody204_30 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.var Flapjack.VarKind.local "o_vh"])

def globalBody204_31 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nvh")

def globalBody204_32 : Prog (BitVec 64) :=
.seq globalBody204_30 globalBody204_31

def globalBody204_33 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.const 8#64])

def globalBody204_34 : Prog (BitVec 64) :=
.seq globalBody204_32 globalBody204_33

def globalBody204_35 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "rq")

def globalBody204_36 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 82#64]

def globalBody204_37 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "wlen") (Flapjack.Exp.const 12#64)) globalBody204_36 globalBody204_1

def globalBody204_38 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]])
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "wp",
            Flapjack.Exp.panOp Flapjack.PanOp.mul
              [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 4#64]]),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "wp",
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 4#64],
              Flapjack.Exp.const 1#64]))
        (Flapjack.Exp.const 8#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "wp",
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 4#64],
              Flapjack.Exp.const 2#64]))
        (Flapjack.Exp.const 16#64),
      Flapjack.Exp.shift Flapjack.Shift.lsl
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "wp",
              Flapjack.Exp.panOp Flapjack.PanOp.mul
                [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 4#64],
              Flapjack.Exp.const 3#64]))
        (Flapjack.Exp.const 24#64)])

def globalBody204_39 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody204_40 : Prog (BitVec 64) :=
.seq globalBody204_38 globalBody204_39

def globalBody204_41 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 3#64)) globalBody204_40

def globalBody204_42 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_check_offsets"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]),
    Flapjack.Exp.const 3#64, Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "wlen"]

def globalBody204_43 : Prog (BitVec 64) :=
.seq globalBody204_41 globalBody204_42

def globalBody204_44 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "st0"))

def globalBody204_45 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "st0"))

def globalBody204_46 : Prog (BitVec 64) :=
.seq globalBody204_44 globalBody204_45

def globalBody204_47 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "cd"))

def globalBody204_48 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "cd"))

def globalBody204_49 : Prog (BitVec 64) :=
.seq globalBody204_47 globalBody204_48

def globalBody204_50 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "hd"))

def globalBody204_51 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "hd"))

def globalBody204_52 : Prog (BitVec 64) :=
.seq globalBody204_50 globalBody204_51

def globalBody204_53 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "si")

def globalBody204_54 : Prog (BitVec 64) :=
.seq globalBody204_52 globalBody204_53

def globalBody204_55 : Prog (BitVec 64) :=
.decCall ("hd") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_bytes_list") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "wp", Flapjack.Exp.var Flapjack.VarKind.local "w2"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "wlen", Flapjack.Exp.var Flapjack.VarKind.local "w2"],
  Flapjack.Exp.const 256#64, Flapjack.Exp.const 1024#64]) globalBody204_54

def globalBody204_56 : Prog (BitVec 64) :=
.seq globalBody204_49 globalBody204_55

def globalBody204_57 : Prog (BitVec 64) :=
.decCall ("cd") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_bytes_list") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "wp", Flapjack.Exp.var Flapjack.VarKind.local "w1"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "w2", Flapjack.Exp.var Flapjack.VarKind.local "w1"],
  Flapjack.Exp.const 9223372036854775807#64, Flapjack.Exp.const 65536#64]) globalBody204_56

def globalBody204_58 : Prog (BitVec 64) :=
.seq globalBody204_46 globalBody204_57

def globalBody204_59 : Prog (BitVec 64) :=
.decCall ("st0") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_bytes_list") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "wp", Flapjack.Exp.var Flapjack.VarKind.local "w0"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "w1", Flapjack.Exp.var Flapjack.VarKind.local "w0"],
  Flapjack.Exp.const 9223372036854775807#64, Flapjack.Exp.const 1024#64]) globalBody204_58

def globalBody204_60 : Prog (BitVec 64) :=
.dec ("w2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 16#64])) globalBody204_59

def globalBody204_61 : Prog (BitVec 64) :=
.dec ("w1") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 8#64])) globalBody204_60

def globalBody204_62 : Prog (BitVec 64) :=
.dec ("w0") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]))) globalBody204_61

def globalBody204_63 : Prog (BitVec 64) :=
.seq globalBody204_43 globalBody204_62

def globalBody204_64 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody204_63

def globalBody204_65 : Prog (BitVec 64) :=
.seq globalBody204_37 globalBody204_64

def globalBody204_66 : Prog (BitVec 64) :=
.dec ("wlen") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "len", Flapjack.Exp.var Flapjack.VarKind.local "o_wit"]) globalBody204_65

def globalBody204_67 : Prog (BitVec 64) :=
.dec ("wp") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "o_wit"]) globalBody204_66

def globalBody204_68 : Prog (BitVec 64) :=
.seq globalBody204_35 globalBody204_67

def globalBody204_69 : Prog (BitVec 64) :=
.decCall ("rq") (Flapjack.Shape.one) ("decode_requests") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.var Flapjack.VarKind.local "o_rq"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "nlen", Flapjack.Exp.var Flapjack.VarKind.local "o_rq"]]) globalBody204_68

def globalBody204_70 : Prog (BitVec 64) :=
.seq globalBody204_34 globalBody204_69

def globalBody204_71 : Prog (BitVec 64) :=
.decCall ("nvh") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o_rq", Flapjack.Exp.var Flapjack.VarKind.local "o_vh"],
  Flapjack.Exp.const 32#64, Flapjack.Exp.const 9223372036854775807#64]) globalBody204_70

def globalBody204_72 : Prog (BitVec 64) :=
.seq globalBody204_29 globalBody204_71

def globalBody204_73 : Prog (BitVec 64) :=
.decCall ("pl") (Flapjack.Shape.one) ("decode_payload") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.var Flapjack.VarKind.local "o_pl"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o_vh", Flapjack.Exp.var Flapjack.VarKind.local "o_pl"]]) globalBody204_72

def globalBody204_74 : Prog (BitVec 64) :=
.seq globalBody204_28 globalBody204_73

def globalBody204_75 : Prog (BitVec 64) :=
.dec ("o_rq") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.or
  [Flapjack.Exp.loadByte
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.shift Flapjack.Shift.lsl
      (Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.const 40#64, Flapjack.Exp.const 1#64]))
      (Flapjack.Exp.const 8#64),
    Flapjack.Exp.shift Flapjack.Shift.lsl
      (Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.const 40#64, Flapjack.Exp.const 2#64]))
      (Flapjack.Exp.const 16#64),
    Flapjack.Exp.shift Flapjack.Shift.lsl
      (Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.const 40#64, Flapjack.Exp.const 3#64]))
      (Flapjack.Exp.const 24#64)]) globalBody204_74

def globalBody204_76 : Prog (BitVec 64) :=
.dec ("o_vh") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.or
  [Flapjack.Exp.loadByte
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.const 4#64]),
    Flapjack.Exp.shift Flapjack.Shift.lsl
      (Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.const 4#64, Flapjack.Exp.const 1#64]))
      (Flapjack.Exp.const 8#64),
    Flapjack.Exp.shift Flapjack.Shift.lsl
      (Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.const 4#64, Flapjack.Exp.const 2#64]))
      (Flapjack.Exp.const 16#64),
    Flapjack.Exp.shift Flapjack.Shift.lsl
      (Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.const 4#64, Flapjack.Exp.const 3#64]))
      (Flapjack.Exp.const 24#64)]) globalBody204_75

def globalBody204_77 : Prog (BitVec 64) :=
.dec ("o_pl") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.or
  [Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "np"),
    Flapjack.Exp.shift Flapjack.Shift.lsl
      (Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.const 1#64]))
      (Flapjack.Exp.const 8#64),
    Flapjack.Exp.shift Flapjack.Shift.lsl
      (Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.const 2#64]))
      (Flapjack.Exp.const 16#64),
    Flapjack.Exp.shift Flapjack.Shift.lsl
      (Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.const 3#64]))
      (Flapjack.Exp.const 24#64)]) globalBody204_76

def globalBody204_78 : Prog (BitVec 64) :=
.seq globalBody204_21 globalBody204_77

def globalBody204_79 : Prog (BitVec 64) :=
.dec ("nlen") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "o_wit", Flapjack.Exp.var Flapjack.VarKind.local "o_npr"]) globalBody204_78

def globalBody204_80 : Prog (BitVec 64) :=
.dec ("np") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "o_npr"]) globalBody204_79

def globalBody204_81 : Prog (BitVec 64) :=
.seq globalBody204_19 globalBody204_80

def globalBody204_82 : Prog (BitVec 64) :=
.decCall ("si") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) globalBody204_81

def globalBody204_83 : Prog (BitVec 64) :=
.dec ("o_wit") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 8#64])) globalBody204_82

def globalBody204_84 : Prog (BitVec 64) :=
.dec ("o_npr") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 112#64]))) globalBody204_83

def globalBody204_85 : Prog (BitVec 64) :=
.seq globalBody204_18 globalBody204_84

def globalData204 : Decl (BitVec 64) :=
.function { name := "decode_stateless_input", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := globalBody204_85, returnShape := (Flapjack.Shape.one) }
def globalOutput204 := Pancake.PanLang.declToHOL globalData204
end InitECandidate.Proofs.FrontendStages.Declarations
