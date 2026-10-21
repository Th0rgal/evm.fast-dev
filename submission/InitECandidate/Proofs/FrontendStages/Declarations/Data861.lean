import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify845
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body861_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 248#64]

def body861_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.const 1#64)

def body861_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 0#64])

def body861_3 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "tmp") (Flapjack.Exp.const 192#64)

def body861_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp", Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "oh"]

def body861_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "oh")

def body861_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 32#64])

def body861_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 52#64])

def body861_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "txr")

def body861_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 84#64])

def body861_10 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 116#64])

def body861_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def body861_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 80#64]))

def body861_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 104#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 88#64]))

def body861_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 112#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 96#64]))

def body861_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 120#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 104#64]))

def body861_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 16#64]))

def body861_17 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 136#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 24#64]))

def body861_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 144#64])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 372#64])

def body861_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero" [Flapjack.Exp.var Flapjack.VarKind.local "z8", Flapjack.Exp.const 8#64]

def body861_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 152#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "z8")

def body861_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "bf")

def body861_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 192#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "wr")

def body861_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 200#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 112#64]))

def body861_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 208#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 120#64]))

def body861_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 216#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 24#64]))

def body861_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 224#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "rh")

def body861_27 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 232#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "bh")

def body861_28 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.const 240#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 128#64]))

def body861_29 : Prog (BitVec 64) :=
Flapjack.Prog.raise "BlockErr" (Flapjack.Exp.const 7#64)

def body861_30 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body861_31 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 8388608#64) (Flapjack.Exp.var Flapjack.VarKind.local "bl")) body861_29 body861_30

def body861_32 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "build_mpt_indexed"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "txr"]

def body861_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "wd_rlp_slices"), none)) "alloc"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "nwd", Flapjack.Exp.const 16#64],
        Flapjack.Exp.const 16#64]]

def body861_34 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "wd_rlp_slices",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]])
  (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "e"))

def body861_35 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.global "wd_rlp_slices",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64],
      Flapjack.Exp.const 8#64])
  (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "e"))

def body861_36 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body861_37 : Prog (BitVec 64) :=
.seq body861_35 body861_36

def body861_38 : Prog (BitVec 64) :=
.seq body861_34 body861_37

def body861_39 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("encode_withdrawal_rlp") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 48#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 44#64]]]) body861_38

def body861_40 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nwd")) body861_39

def body861_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "build_mpt_indexed"
  [Flapjack.Exp.var Flapjack.VarKind.global "wd_rlp_slices", Flapjack.Exp.var Flapjack.VarKind.local "nwd",
    Flapjack.Exp.var Flapjack.VarKind.local "wr"]

def body861_42 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "compute_requests_hash"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "reqs"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "reqs"),
    Flapjack.Exp.var Flapjack.VarKind.local "rh"]

def body861_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 64#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 72#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "bh"]

def body861_44 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "h")

def body861_45 : Prog (BitVec 64) :=
.seq body861_43 body861_44

def body861_46 : Prog (BitVec 64) :=
.seq body861_42 body861_45

def body861_47 : Prog (BitVec 64) :=
.decCall ("reqs") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("encode_execution_requests") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 32#64])]) body861_46

def body861_48 : Prog (BitVec 64) :=
.seq body861_41 body861_47

def body861_49 : Prog (BitVec 64) :=
.seq body861_40 body861_48

def body861_50 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body861_49

def body861_51 : Prog (BitVec 64) :=
.seq body861_33 body861_50

def body861_52 : Prog (BitVec 64) :=
.dec ("nwd") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 56#64])) body861_51

def body861_53 : Prog (BitVec 64) :=
.seq body861_32 body861_52

def body861_54 : Prog (BitVec 64) :=
.seq body861_31 body861_53

def body861_55 : Prog (BitVec 64) :=
.decCall ("bl") (Flapjack.Shape.one) ("block_rlp_length") ([Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.var Flapjack.VarKind.local "pl"]) body861_54

def body861_56 : Prog (BitVec 64) :=
.seq body861_28 body861_55

def body861_57 : Prog (BitVec 64) :=
.seq body861_27 body861_56

def body861_58 : Prog (BitVec 64) :=
.decCall ("bh") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body861_57

def body861_59 : Prog (BitVec 64) :=
.seq body861_26 body861_58

def body861_60 : Prog (BitVec 64) :=
.decCall ("rh") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body861_59

def body861_61 : Prog (BitVec 64) :=
.seq body861_25 body861_60

def body861_62 : Prog (BitVec 64) :=
.seq body861_24 body861_61

def body861_63 : Prog (BitVec 64) :=
.seq body861_23 body861_62

def body861_64 : Prog (BitVec 64) :=
.seq body861_22 body861_63

def body861_65 : Prog (BitVec 64) :=
.decCall ("wr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body861_64

def body861_66 : Prog (BitVec 64) :=
.seq body861_21 body861_65

def body861_67 : Prog (BitVec 64) :=
.dec ("bf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64]),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 1#64]))
          (Flapjack.Exp.const 8#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 2#64]))
          (Flapjack.Exp.const 16#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 3#64]))
          (Flapjack.Exp.const 24#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.op Flapjack.BinOp.or
            [Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 4#64]),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 4#64,
                      Flapjack.Exp.const 1#64]))
                (Flapjack.Exp.const 8#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 4#64,
                      Flapjack.Exp.const 2#64]))
                (Flapjack.Exp.const 16#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 4#64,
                      Flapjack.Exp.const 3#64]))
                (Flapjack.Exp.const 24#64)])
          (Flapjack.Exp.const 32#64)],
    Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 8#64]),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 8#64,
                Flapjack.Exp.const 1#64]))
          (Flapjack.Exp.const 8#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 8#64,
                Flapjack.Exp.const 2#64]))
          (Flapjack.Exp.const 16#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 8#64,
                Flapjack.Exp.const 3#64]))
          (Flapjack.Exp.const 24#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.op Flapjack.BinOp.or
            [Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 8#64,
                    Flapjack.Exp.const 4#64]),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 8#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 1#64]))
                (Flapjack.Exp.const 8#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 8#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 2#64]))
                (Flapjack.Exp.const 16#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 8#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 3#64]))
                (Flapjack.Exp.const 24#64)])
          (Flapjack.Exp.const 32#64)],
    Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 16#64]),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 16#64,
                Flapjack.Exp.const 1#64]))
          (Flapjack.Exp.const 8#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 16#64,
                Flapjack.Exp.const 2#64]))
          (Flapjack.Exp.const 16#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 16#64,
                Flapjack.Exp.const 3#64]))
          (Flapjack.Exp.const 24#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.op Flapjack.BinOp.or
            [Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 16#64,
                    Flapjack.Exp.const 4#64]),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 16#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 1#64]))
                (Flapjack.Exp.const 8#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 16#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 2#64]))
                (Flapjack.Exp.const 16#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 16#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 3#64]))
                (Flapjack.Exp.const 24#64)])
          (Flapjack.Exp.const 32#64)],
    Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 24#64]),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 24#64,
                Flapjack.Exp.const 1#64]))
          (Flapjack.Exp.const 8#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 24#64,
                Flapjack.Exp.const 2#64]))
          (Flapjack.Exp.const 16#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 24#64,
                Flapjack.Exp.const 3#64]))
          (Flapjack.Exp.const 24#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.op Flapjack.BinOp.or
            [Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 24#64,
                    Flapjack.Exp.const 4#64]),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 24#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 1#64]))
                (Flapjack.Exp.const 8#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 24#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 2#64]))
                (Flapjack.Exp.const 16#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 24#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 3#64]))
                (Flapjack.Exp.const 24#64)])
          (Flapjack.Exp.const 32#64)]]) body861_66

def body861_68 : Prog (BitVec 64) :=
.seq body861_20 body861_67

def body861_69 : Prog (BitVec 64) :=
.seq body861_19 body861_68

def body861_70 : Prog (BitVec 64) :=
.decCall ("z8") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 8#64]) body861_69

def body861_71 : Prog (BitVec 64) :=
.seq body861_18 body861_70

def body861_72 : Prog (BitVec 64) :=
.seq body861_17 body861_71

def body861_73 : Prog (BitVec 64) :=
.seq body861_16 body861_72

def body861_74 : Prog (BitVec 64) :=
.seq body861_15 body861_73

def body861_75 : Prog (BitVec 64) :=
.seq body861_14 body861_74

def body861_76 : Prog (BitVec 64) :=
.seq body861_13 body861_75

def body861_77 : Prog (BitVec 64) :=
.seq body861_12 body861_76

def body861_78 : Prog (BitVec 64) :=
.seq body861_11 body861_77

def body861_79 : Prog (BitVec 64) :=
.seq body861_10 body861_78

def body861_80 : Prog (BitVec 64) :=
.seq body861_9 body861_79

def body861_81 : Prog (BitVec 64) :=
.seq body861_8 body861_80

def body861_82 : Prog (BitVec 64) :=
.decCall ("txr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body861_81

def body861_83 : Prog (BitVec 64) :=
.seq body861_7 body861_82

def body861_84 : Prog (BitVec 64) :=
.seq body861_6 body861_83

def body861_85 : Prog (BitVec 64) :=
.seq body861_5 body861_84

def body861_86 : Prog (BitVec 64) :=
.seq body861_4 body861_85

def body861_87 : Prog (BitVec 64) :=
.seq body861_3 body861_86

def body861_88 : Prog (BitVec 64) :=
.decCall ("tmp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 8#64]) body861_87

def body861_89 : Prog (BitVec 64) :=
.decCall ("oh") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body861_88

def body861_90 : Prog (BitVec 64) :=
.seq body861_2 body861_89

def body861_91 : Prog (BitVec 64) :=
.seq body861_1 body861_90

def body861_92 : Prog (BitVec 64) :=
.seq body861_0 body861_91

def body861_93 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 248#64]) body861_92

def body861_94 : Prog (BitVec 64) :=
.dec ("raw") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 0#64])) body861_93

def body861_95 : Prog (BitVec 64) :=
.dec ("pl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 0#64])) body861_94

def body861_96 : Prog (BitVec 64) :=
.seq body861_0 body861_1

def body861_97 : Prog (BitVec 64) :=
.seq body861_96 body861_2

def body861_98 : Prog (BitVec 64) :=
.seq body861_3 body861_4

def body861_99 : Prog (BitVec 64) :=
.seq body861_98 body861_5

def body861_100 : Prog (BitVec 64) :=
.seq body861_99 body861_6

def body861_101 : Prog (BitVec 64) :=
.seq body861_100 body861_7

def body861_102 : Prog (BitVec 64) :=
.seq body861_8 body861_9

def body861_103 : Prog (BitVec 64) :=
.seq body861_102 body861_10

def body861_104 : Prog (BitVec 64) :=
.seq body861_103 body861_11

def body861_105 : Prog (BitVec 64) :=
.seq body861_104 body861_12

def body861_106 : Prog (BitVec 64) :=
.seq body861_105 body861_13

def body861_107 : Prog (BitVec 64) :=
.seq body861_106 body861_14

def body861_108 : Prog (BitVec 64) :=
.seq body861_107 body861_15

def body861_109 : Prog (BitVec 64) :=
.seq body861_108 body861_16

def body861_110 : Prog (BitVec 64) :=
.seq body861_109 body861_17

def body861_111 : Prog (BitVec 64) :=
.seq body861_110 body861_18

def body861_112 : Prog (BitVec 64) :=
.seq body861_19 body861_20

def body861_113 : Prog (BitVec 64) :=
.seq body861_22 body861_23

def body861_114 : Prog (BitVec 64) :=
.seq body861_113 body861_24

def body861_115 : Prog (BitVec 64) :=
.seq body861_114 body861_25

def body861_116 : Prog (BitVec 64) :=
.seq body861_27 body861_28

def body861_117 : Prog (BitVec 64) :=
.seq body861_31 body861_32

def body861_118 : Prog (BitVec 64) :=
.seq body861_34 body861_35

def body861_119 : Prog (BitVec 64) :=
.seq body861_118 body861_36

def body861_120 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("encode_withdrawal_rlp") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 48#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 44#64]]]) body861_119

def body861_121 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "nwd")) body861_120

def body861_122 : Prog (BitVec 64) :=
.seq body861_121 body861_41

def body861_123 : Prog (BitVec 64) :=
.seq body861_42 body861_43

def body861_124 : Prog (BitVec 64) :=
.seq body861_123 body861_44

def body861_125 : Prog (BitVec 64) :=
.decCall ("reqs") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("encode_execution_requests") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 32#64])]) body861_124

def body861_126 : Prog (BitVec 64) :=
.seq body861_122 body861_125

def body861_127 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body861_126

def body861_128 : Prog (BitVec 64) :=
.seq body861_33 body861_127

def body861_129 : Prog (BitVec 64) :=
.dec ("nwd") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 56#64])) body861_128

def body861_130 : Prog (BitVec 64) :=
.seq body861_117 body861_129

def body861_131 : Prog (BitVec 64) :=
.decCall ("bl") (Flapjack.Shape.one) ("block_rlp_length") ([Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.var Flapjack.VarKind.local "pl"]) body861_130

def body861_132 : Prog (BitVec 64) :=
.seq body861_116 body861_131

def body861_133 : Prog (BitVec 64) :=
.decCall ("bh") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body861_132

def body861_134 : Prog (BitVec 64) :=
.seq body861_26 body861_133

def body861_135 : Prog (BitVec 64) :=
.decCall ("rh") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body861_134

def body861_136 : Prog (BitVec 64) :=
.seq body861_115 body861_135

def body861_137 : Prog (BitVec 64) :=
.decCall ("wr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body861_136

def body861_138 : Prog (BitVec 64) :=
.seq body861_21 body861_137

def body861_139 : Prog (BitVec 64) :=
.dec ("bf") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64]),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 1#64]))
          (Flapjack.Exp.const 8#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 2#64]))
          (Flapjack.Exp.const 16#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 3#64]))
          (Flapjack.Exp.const 24#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.op Flapjack.BinOp.or
            [Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 4#64]),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 4#64,
                      Flapjack.Exp.const 1#64]))
                (Flapjack.Exp.const 8#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 4#64,
                      Flapjack.Exp.const 2#64]))
                (Flapjack.Exp.const 16#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 4#64,
                      Flapjack.Exp.const 3#64]))
                (Flapjack.Exp.const 24#64)])
          (Flapjack.Exp.const 32#64)],
    Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 8#64]),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 8#64,
                Flapjack.Exp.const 1#64]))
          (Flapjack.Exp.const 8#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 8#64,
                Flapjack.Exp.const 2#64]))
          (Flapjack.Exp.const 16#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 8#64,
                Flapjack.Exp.const 3#64]))
          (Flapjack.Exp.const 24#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.op Flapjack.BinOp.or
            [Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 8#64,
                    Flapjack.Exp.const 4#64]),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 8#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 1#64]))
                (Flapjack.Exp.const 8#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 8#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 2#64]))
                (Flapjack.Exp.const 16#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 8#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 3#64]))
                (Flapjack.Exp.const 24#64)])
          (Flapjack.Exp.const 32#64)],
    Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 16#64]),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 16#64,
                Flapjack.Exp.const 1#64]))
          (Flapjack.Exp.const 8#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 16#64,
                Flapjack.Exp.const 2#64]))
          (Flapjack.Exp.const 16#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 16#64,
                Flapjack.Exp.const 3#64]))
          (Flapjack.Exp.const 24#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.op Flapjack.BinOp.or
            [Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 16#64,
                    Flapjack.Exp.const 4#64]),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 16#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 1#64]))
                (Flapjack.Exp.const 8#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 16#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 2#64]))
                (Flapjack.Exp.const 16#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 16#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 3#64]))
                (Flapjack.Exp.const 24#64)])
          (Flapjack.Exp.const 32#64)],
    Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 24#64]),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 24#64,
                Flapjack.Exp.const 1#64]))
          (Flapjack.Exp.const 8#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 24#64,
                Flapjack.Exp.const 2#64]))
          (Flapjack.Exp.const 16#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 24#64,
                Flapjack.Exp.const 3#64]))
          (Flapjack.Exp.const 24#64),
        Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.op Flapjack.BinOp.or
            [Flapjack.Exp.loadByte
                (Flapjack.Exp.op Flapjack.BinOp.add
                  [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 24#64,
                    Flapjack.Exp.const 4#64]),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 24#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 1#64]))
                (Flapjack.Exp.const 8#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 24#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 2#64]))
                (Flapjack.Exp.const 16#64),
              Flapjack.Exp.shift Flapjack.Shift.lsl
                (Flapjack.Exp.loadByte
                  (Flapjack.Exp.op Flapjack.BinOp.add
                    [Flapjack.Exp.var Flapjack.VarKind.local "raw", Flapjack.Exp.const 440#64, Flapjack.Exp.const 24#64,
                      Flapjack.Exp.const 4#64, Flapjack.Exp.const 3#64]))
                (Flapjack.Exp.const 24#64)])
          (Flapjack.Exp.const 32#64)]]) body861_138

def body861_140 : Prog (BitVec 64) :=
.seq body861_112 body861_139

def body861_141 : Prog (BitVec 64) :=
.decCall ("z8") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 8#64]) body861_140

def body861_142 : Prog (BitVec 64) :=
.seq body861_111 body861_141

def body861_143 : Prog (BitVec 64) :=
.decCall ("txr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body861_142

def body861_144 : Prog (BitVec 64) :=
.seq body861_101 body861_143

def body861_145 : Prog (BitVec 64) :=
.decCall ("tmp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 8#64]) body861_144

def body861_146 : Prog (BitVec 64) :=
.decCall ("oh") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body861_145

def body861_147 : Prog (BitVec 64) :=
.seq body861_97 body861_146

def body861_148 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 248#64]) body861_147

def body861_149 : Prog (BitVec 64) :=
.dec ("raw") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pl", Flapjack.Exp.const 0#64])) body861_148

def body861_150 : Prog (BitVec 64) :=
.dec ("pl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "si", Flapjack.Exp.const 0#64])) body861_149

def originalData861 : Decl (BitVec 64) :=
.function { name := "payload_header", inline := false, exported := false, params := [("si", Flapjack.Shape.one)], body := body861_95, returnShape := (Flapjack.Shape.one) }
def simplifiedData861 : Decl (BitVec 64) :=
.function { name := "payload_header", inline := false, exported := false, params := [("si", Flapjack.Shape.one)], body := body861_150, returnShape := (Flapjack.Shape.one) }
def original861 := Pancake.PanLang.declToHOL originalData861
def simplified861 := Pancake.PanLang.declToHOL simplifiedData861
end InitECandidate.Proofs.FrontendStages.Declarations
