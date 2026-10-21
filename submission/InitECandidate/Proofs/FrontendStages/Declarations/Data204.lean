import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify188
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body204_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 1#64]

def body204_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body204_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "len") (Flapjack.Exp.const 2#64)) body204_0 body204_1

def body204_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 2#64]

def body204_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "p"))
        (Flapjack.Exp.const 21#64),
      Flapjack.Exp.cmp Flapjack.Cmp.notEqual
        (Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 1#64]))
        (Flapjack.Exp.const 1#64)])) body204_3 body204_1

def body204_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "p"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 2#64])

def body204_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "len"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "len", Flapjack.Exp.const 2#64])

def body204_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 80#64]

def body204_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "len") (Flapjack.Exp.const 16#64)) body204_7 body204_1

def body204_9 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs")
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

def body204_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 8#64])
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

def body204_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_check_offsets"
  [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 2#64, Flapjack.Exp.const 16#64,
    Flapjack.Exp.var Flapjack.VarKind.local "len"]

def body204_12 : Prog (BitVec 64) :=
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

def body204_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 81#64]

def body204_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "nlen") (Flapjack.Exp.const 44#64)) body204_13 body204_1

def body204_15 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs")
  (Flapjack.Exp.var Flapjack.VarKind.local "o_pl")

def body204_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "o_vh")

def body204_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "o_rq")

def body204_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_check_offsets"
  [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 3#64, Flapjack.Exp.const 44#64,
    Flapjack.Exp.var Flapjack.VarKind.local "nlen"]

def body204_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "pl")

def body204_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.var Flapjack.VarKind.local "o_vh"])

def body204_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nvh")

def body204_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.const 8#64])

def body204_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "rq")

def body204_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_fail" [Flapjack.Exp.const 82#64]

def body204_25 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "wlen") (Flapjack.Exp.const 12#64)) body204_24 body204_1

def body204_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs",
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

def body204_27 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body204_28 : Prog (BitVec 64) :=
.seq body204_26 body204_27

def body204_29 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 3#64)) body204_28

def body204_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ssz_check_offsets"
  [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 3#64, Flapjack.Exp.const 12#64,
    Flapjack.Exp.var Flapjack.VarKind.local "wlen"]

def body204_31 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "st0"))

def body204_32 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "st0"))

def body204_33 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "cd"))

def body204_34 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "cd"))

def body204_35 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "hd"))

def body204_36 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 80#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "hd"))

def body204_37 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "si")

def body204_38 : Prog (BitVec 64) :=
.seq body204_36 body204_37

def body204_39 : Prog (BitVec 64) :=
.seq body204_35 body204_38

def body204_40 : Prog (BitVec 64) :=
.decCall ("hd") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_bytes_list") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "wp", Flapjack.Exp.var Flapjack.VarKind.local "w2"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "wlen", Flapjack.Exp.var Flapjack.VarKind.local "w2"],
  Flapjack.Exp.const 256#64, Flapjack.Exp.const 1024#64]) body204_39

def body204_41 : Prog (BitVec 64) :=
.seq body204_34 body204_40

def body204_42 : Prog (BitVec 64) :=
.seq body204_33 body204_41

def body204_43 : Prog (BitVec 64) :=
.decCall ("cd") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_bytes_list") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "wp", Flapjack.Exp.var Flapjack.VarKind.local "w1"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "w2", Flapjack.Exp.var Flapjack.VarKind.local "w1"],
  Flapjack.Exp.const 9223372036854775807#64, Flapjack.Exp.const 65536#64]) body204_42

def body204_44 : Prog (BitVec 64) :=
.seq body204_32 body204_43

def body204_45 : Prog (BitVec 64) :=
.seq body204_31 body204_44

def body204_46 : Prog (BitVec 64) :=
.decCall ("st0") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_bytes_list") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "wp", Flapjack.Exp.var Flapjack.VarKind.local "w0"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "w1", Flapjack.Exp.var Flapjack.VarKind.local "w0"],
  Flapjack.Exp.const 9223372036854775807#64, Flapjack.Exp.const 1024#64]) body204_45

def body204_47 : Prog (BitVec 64) :=
.dec ("w2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 16#64])) body204_46

def body204_48 : Prog (BitVec 64) :=
.dec ("w1") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 8#64])) body204_47

def body204_49 : Prog (BitVec 64) :=
.dec ("w0") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs")) body204_48

def body204_50 : Prog (BitVec 64) :=
.seq body204_30 body204_49

def body204_51 : Prog (BitVec 64) :=
.seq body204_29 body204_50

def body204_52 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body204_51

def body204_53 : Prog (BitVec 64) :=
.seq body204_25 body204_52

def body204_54 : Prog (BitVec 64) :=
.dec ("wlen") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "len", Flapjack.Exp.var Flapjack.VarKind.local "o_wit"]) body204_53

def body204_55 : Prog (BitVec 64) :=
.dec ("wp") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "o_wit"]) body204_54

def body204_56 : Prog (BitVec 64) :=
.seq body204_23 body204_55

def body204_57 : Prog (BitVec 64) :=
.decCall ("rq") (Flapjack.Shape.one) ("decode_requests") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.var Flapjack.VarKind.local "o_rq"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "nlen", Flapjack.Exp.var Flapjack.VarKind.local "o_rq"]]) body204_56

def body204_58 : Prog (BitVec 64) :=
.seq body204_22 body204_57

def body204_59 : Prog (BitVec 64) :=
.seq body204_21 body204_58

def body204_60 : Prog (BitVec 64) :=
.seq body204_20 body204_59

def body204_61 : Prog (BitVec 64) :=
.decCall ("nvh") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o_rq", Flapjack.Exp.var Flapjack.VarKind.local "o_vh"],
  Flapjack.Exp.const 32#64, Flapjack.Exp.const 9223372036854775807#64]) body204_60

def body204_62 : Prog (BitVec 64) :=
.seq body204_19 body204_61

def body204_63 : Prog (BitVec 64) :=
.decCall ("pl") (Flapjack.Shape.one) ("decode_payload") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.var Flapjack.VarKind.local "o_pl"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o_vh", Flapjack.Exp.var Flapjack.VarKind.local "o_pl"]]) body204_62

def body204_64 : Prog (BitVec 64) :=
.seq body204_18 body204_63

def body204_65 : Prog (BitVec 64) :=
.seq body204_17 body204_64

def body204_66 : Prog (BitVec 64) :=
.seq body204_16 body204_65

def body204_67 : Prog (BitVec 64) :=
.seq body204_15 body204_66

def body204_68 : Prog (BitVec 64) :=
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
      (Flapjack.Exp.const 24#64)]) body204_67

def body204_69 : Prog (BitVec 64) :=
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
      (Flapjack.Exp.const 24#64)]) body204_68

def body204_70 : Prog (BitVec 64) :=
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
      (Flapjack.Exp.const 24#64)]) body204_69

def body204_71 : Prog (BitVec 64) :=
.seq body204_14 body204_70

def body204_72 : Prog (BitVec 64) :=
.dec ("nlen") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "o_wit", Flapjack.Exp.var Flapjack.VarKind.local "o_npr"]) body204_71

def body204_73 : Prog (BitVec 64) :=
.dec ("np") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "o_npr"]) body204_72

def body204_74 : Prog (BitVec 64) :=
.seq body204_12 body204_73

def body204_75 : Prog (BitVec 64) :=
.decCall ("si") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body204_74

def body204_76 : Prog (BitVec 64) :=
.dec ("o_wit") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 8#64])) body204_75

def body204_77 : Prog (BitVec 64) :=
.dec ("o_npr") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs")) body204_76

def body204_78 : Prog (BitVec 64) :=
.seq body204_11 body204_77

def body204_79 : Prog (BitVec 64) :=
.seq body204_10 body204_78

def body204_80 : Prog (BitVec 64) :=
.seq body204_9 body204_79

def body204_81 : Prog (BitVec 64) :=
.seq body204_8 body204_80

def body204_82 : Prog (BitVec 64) :=
.seq body204_6 body204_81

def body204_83 : Prog (BitVec 64) :=
.seq body204_5 body204_82

def body204_84 : Prog (BitVec 64) :=
.seq body204_4 body204_83

def body204_85 : Prog (BitVec 64) :=
.seq body204_2 body204_84

def body204_86 : Prog (BitVec 64) :=
.seq body204_2 body204_4

def body204_87 : Prog (BitVec 64) :=
.seq body204_86 body204_5

def body204_88 : Prog (BitVec 64) :=
.seq body204_87 body204_6

def body204_89 : Prog (BitVec 64) :=
.seq body204_88 body204_8

def body204_90 : Prog (BitVec 64) :=
.seq body204_89 body204_9

def body204_91 : Prog (BitVec 64) :=
.seq body204_90 body204_10

def body204_92 : Prog (BitVec 64) :=
.seq body204_91 body204_11

def body204_93 : Prog (BitVec 64) :=
.seq body204_15 body204_16

def body204_94 : Prog (BitVec 64) :=
.seq body204_93 body204_17

def body204_95 : Prog (BitVec 64) :=
.seq body204_94 body204_18

def body204_96 : Prog (BitVec 64) :=
.seq body204_20 body204_21

def body204_97 : Prog (BitVec 64) :=
.seq body204_96 body204_22

def body204_98 : Prog (BitVec 64) :=
.seq body204_29 body204_30

def body204_99 : Prog (BitVec 64) :=
.seq body204_31 body204_32

def body204_100 : Prog (BitVec 64) :=
.seq body204_33 body204_34

def body204_101 : Prog (BitVec 64) :=
.seq body204_35 body204_36

def body204_102 : Prog (BitVec 64) :=
.seq body204_101 body204_37

def body204_103 : Prog (BitVec 64) :=
.decCall ("hd") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_bytes_list") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "wp", Flapjack.Exp.var Flapjack.VarKind.local "w2"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "wlen", Flapjack.Exp.var Flapjack.VarKind.local "w2"],
  Flapjack.Exp.const 256#64, Flapjack.Exp.const 1024#64]) body204_102

def body204_104 : Prog (BitVec 64) :=
.seq body204_100 body204_103

def body204_105 : Prog (BitVec 64) :=
.decCall ("cd") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_bytes_list") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "wp", Flapjack.Exp.var Flapjack.VarKind.local "w1"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "w2", Flapjack.Exp.var Flapjack.VarKind.local "w1"],
  Flapjack.Exp.const 9223372036854775807#64, Flapjack.Exp.const 65536#64]) body204_104

def body204_106 : Prog (BitVec 64) :=
.seq body204_99 body204_105

def body204_107 : Prog (BitVec 64) :=
.decCall ("st0") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("decode_bytes_list") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "wp", Flapjack.Exp.var Flapjack.VarKind.local "w0"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "w1", Flapjack.Exp.var Flapjack.VarKind.local "w0"],
  Flapjack.Exp.const 9223372036854775807#64, Flapjack.Exp.const 1024#64]) body204_106

def body204_108 : Prog (BitVec 64) :=
.dec ("w2") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 16#64])) body204_107

def body204_109 : Prog (BitVec 64) :=
.dec ("w1") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 8#64])) body204_108

def body204_110 : Prog (BitVec 64) :=
.dec ("w0") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs")) body204_109

def body204_111 : Prog (BitVec 64) :=
.seq body204_98 body204_110

def body204_112 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body204_111

def body204_113 : Prog (BitVec 64) :=
.seq body204_25 body204_112

def body204_114 : Prog (BitVec 64) :=
.dec ("wlen") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "len", Flapjack.Exp.var Flapjack.VarKind.local "o_wit"]) body204_113

def body204_115 : Prog (BitVec 64) :=
.dec ("wp") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "o_wit"]) body204_114

def body204_116 : Prog (BitVec 64) :=
.seq body204_23 body204_115

def body204_117 : Prog (BitVec 64) :=
.decCall ("rq") (Flapjack.Shape.one) ("decode_requests") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.var Flapjack.VarKind.local "o_rq"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "nlen", Flapjack.Exp.var Flapjack.VarKind.local "o_rq"]]) body204_116

def body204_118 : Prog (BitVec 64) :=
.seq body204_97 body204_117

def body204_119 : Prog (BitVec 64) :=
.decCall ("nvh") (Flapjack.Shape.one) ("ssz_fixed_list_count") ([Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o_rq", Flapjack.Exp.var Flapjack.VarKind.local "o_vh"],
  Flapjack.Exp.const 32#64, Flapjack.Exp.const 9223372036854775807#64]) body204_118

def body204_120 : Prog (BitVec 64) :=
.seq body204_19 body204_119

def body204_121 : Prog (BitVec 64) :=
.decCall ("pl") (Flapjack.Shape.one) ("decode_payload") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "np", Flapjack.Exp.var Flapjack.VarKind.local "o_pl"],
  Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "o_vh", Flapjack.Exp.var Flapjack.VarKind.local "o_pl"]]) body204_120

def body204_122 : Prog (BitVec 64) :=
.seq body204_95 body204_121

def body204_123 : Prog (BitVec 64) :=
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
      (Flapjack.Exp.const 24#64)]) body204_122

def body204_124 : Prog (BitVec 64) :=
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
      (Flapjack.Exp.const 24#64)]) body204_123

def body204_125 : Prog (BitVec 64) :=
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
      (Flapjack.Exp.const 24#64)]) body204_124

def body204_126 : Prog (BitVec 64) :=
.seq body204_14 body204_125

def body204_127 : Prog (BitVec 64) :=
.dec ("nlen") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "o_wit", Flapjack.Exp.var Flapjack.VarKind.local "o_npr"]) body204_126

def body204_128 : Prog (BitVec 64) :=
.dec ("np") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "o_npr"]) body204_127

def body204_129 : Prog (BitVec 64) :=
.seq body204_12 body204_128

def body204_130 : Prog (BitVec 64) :=
.decCall ("si") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body204_129

def body204_131 : Prog (BitVec 64) :=
.dec ("o_wit") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs", Flapjack.Exp.const 8#64])) body204_130

def body204_132 : Prog (BitVec 64) :=
.dec ("o_npr") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.global "ssz_offs")) body204_131

def body204_133 : Prog (BitVec 64) :=
.seq body204_92 body204_132

def originalData204 : Decl (BitVec 64) :=
.function { name := "decode_stateless_input", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := body204_85, returnShape := (Flapjack.Shape.one) }
def simplifiedData204 : Decl (BitVec 64) :=
.function { name := "decode_stateless_input", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := body204_133, returnShape := (Flapjack.Shape.one) }
def original204 := Pancake.PanLang.declToHOL originalData204
def simplified204 := Pancake.PanLang.declToHOL simplifiedData204
end InitECandidate.Proofs.FrontendStages.Declarations
