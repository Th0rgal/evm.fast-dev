import InitECandidate.Proofs.FrontendStages.Crep.Translate167
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody183_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody183_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody183_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody183_0 crepBody183_1

def crepBody183_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "ssz_fail" [Flapjack.CrepExp.const 20#64]

def crepBody183_4 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody183_3

def crepBody183_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 4#64)) crepBody183_4 crepBody183_1

def crepBody183_6 : CrepProg (BitVec 64) :=
.seq crepBody183_2 crepBody183_5

def crepBody183_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "ssz_fail" [Flapjack.CrepExp.const 21#64]

def crepBody183_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody183_7

def crepBody183_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
        (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 3#64])
        (Flapjack.CrepExp.const 0#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 3)])) crepBody183_8 crepBody183_1

def crepBody183_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "ssz_fail" [Flapjack.CrepExp.const 22#64]

def crepBody183_11 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody183_10

def crepBody183_12 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 4)) crepBody183_11 crepBody183_1

def crepBody183_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64]]

def crepBody183_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "ssz_fail" [Flapjack.CrepExp.const 23#64]

def crepBody183_15 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody183_14

def crepBody183_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 3),
      Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 8),
      Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 7)])) crepBody183_15 crepBody183_1

def crepBody183_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.var 10)

def crepBody183_18 : CrepProg (BitVec 64) :=
.seq crepBody183_17 crepBody183_1

def crepBody183_19 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 7]) crepBody183_18

def crepBody183_20 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 1#64],
        Flapjack.CrepExp.const 16#64],
    Flapjack.CrepExp.const 8#64]) crepBody183_19

def crepBody183_21 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.const 0#64) (Flapjack.CrepExp.var 6)) crepBody183_20 crepBody183_1

def crepBody183_22 : CrepProg (BitVec 64) :=
.seq crepBody183_16 crepBody183_21

def crepBody183_23 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 8]) crepBody183_18

def crepBody183_24 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 16#64]]) crepBody183_23

def crepBody183_25 : CrepProg (BitVec 64) :=
.seq crepBody183_22 crepBody183_24

def crepBody183_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 8)

def crepBody183_27 : CrepProg (BitVec 64) :=
.seq crepBody183_26 crepBody183_1

def crepBody183_28 : CrepProg (BitVec 64) :=
.seq crepBody183_25 crepBody183_27

def crepBody183_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6 (Flapjack.CrepExp.var 9)

def crepBody183_30 : CrepProg (BitVec 64) :=
.seq crepBody183_29 crepBody183_1

def crepBody183_31 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 1#64]) crepBody183_30

def crepBody183_32 : CrepProg (BitVec 64) :=
.seq crepBody183_28 crepBody183_31

def crepBody183_33 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 0,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 4#64]]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 4#64],
            Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 4#64],
            Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add
          [Flapjack.CrepExp.var 0,
            Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 4#64],
            Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64)]) crepBody183_32

def crepBody183_34 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 4)) crepBody183_33

def crepBody183_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 9)

def crepBody183_36 : CrepProg (BitVec 64) :=
.seq crepBody183_35 crepBody183_1

def crepBody183_37 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 7]) crepBody183_36

def crepBody183_38 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 5,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64],
        Flapjack.CrepExp.const 16#64],
    Flapjack.CrepExp.const 8#64]) crepBody183_37

def crepBody183_39 : CrepProg (BitVec 64) :=
.seq crepBody183_34 crepBody183_38

def crepBody183_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 4]

def crepBody183_41 : CrepProg (BitVec 64) :=
.seq crepBody183_39 crepBody183_40

def crepBody183_42 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 3) crepBody183_41

def crepBody183_43 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody183_42

def crepBody183_44 : CrepProg (BitVec 64) :=
.seq crepBody183_13 crepBody183_43

def crepBody183_45 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody183_44

def crepBody183_46 : CrepProg (BitVec 64) :=
.seq crepBody183_12 crepBody183_45

def crepBody183_47 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 2#64)) crepBody183_46

def crepBody183_48 : CrepProg (BitVec 64) :=
.seq crepBody183_9 crepBody183_47

def crepBody183_49 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.loadByte (Flapjack.CrepExp.var 0),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 1#64]))
      (Flapjack.CrepExp.const 8#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 2#64]))
      (Flapjack.CrepExp.const 16#64),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl
      (Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 3#64]))
      (Flapjack.CrepExp.const 24#64)]) crepBody183_48

def crepBody183_50 : CrepProg (BitVec 64) :=
.seq crepBody183_6 crepBody183_49

def data183 : CrepProg (BitVec 64) := crepBody183_50
def output183 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [115#8, 115#8, 122#8, 95#8, 115#8, 112#8, 108#8, 105#8, 116#8, 95#8, 118#8, 97#8, 114#8, 95#8, 108#8, 105#8, 115#8,
    116#8], [0, 1, 2], crepProgToHOL data183)
end InitECandidate.Proofs.FrontendStages.Crep
