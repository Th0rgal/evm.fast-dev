import InitECandidate.Proofs.FrontendStages.Crep.Translate401
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody417_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "scratch_alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
          [Flapjack.CrepExp.shift Flapjack.Shift.lsr
              (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 63#64])
              (Flapjack.CrepExp.const 6#64),
            Flapjack.CrepExp.const 8#64],
        Flapjack.CrepExp.const 8#64]]

def crepBody417_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "memzero"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
          [Flapjack.CrepExp.shift Flapjack.Shift.lsr
              (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 63#64])
              (Flapjack.CrepExp.const 6#64),
            Flapjack.CrepExp.const 8#64],
        Flapjack.CrepExp.const 8#64]]

def crepBody417_2 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody417_1

def crepBody417_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody417_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody417_5 : CrepProg (BitVec 64) :=
.seq crepBody417_3 crepBody417_4

def crepBody417_6 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.or
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 2,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
            [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 6#64),
              Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.shift Flapjack.Shift.lsl (Flapjack.CrepExp.const 1#64)
      (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 63#64])]) crepBody417_5

def crepBody417_7 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 6#64),
        Flapjack.CrepExp.const 8#64]]) crepBody417_6

def crepBody417_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 96#64],
      Flapjack.CrepExp.const 2#64])

def crepBody417_9 : CrepProg (BitVec 64) :=
.seq crepBody417_8 crepBody417_4

def crepBody417_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.const 2#64)

def crepBody417_11 : CrepProg (BitVec 64) :=
.seq crepBody417_10 crepBody417_4

def crepBody417_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.const 1#64)

def crepBody417_13 : CrepProg (BitVec 64) :=
.seq crepBody417_12 crepBody417_4

def crepBody417_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 91#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.const 127#64) (Flapjack.CrepExp.var 6))]) crepBody417_13 crepBody417_4

def crepBody417_15 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.loadByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64])) crepBody417_14

def crepBody417_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64])
  (Flapjack.CrepExp.var 1)) crepBody417_15 crepBody417_4

def crepBody417_17 : CrepProg (BitVec 64) :=
.seq crepBody417_11 crepBody417_16

def crepBody417_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 230#64),
      Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 231#64)])) crepBody417_17 crepBody417_4

def crepBody417_19 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 82#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.const 127#64) (Flapjack.CrepExp.var 6))]) crepBody417_13 crepBody417_4

def crepBody417_20 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.loadByte
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64])) crepBody417_19

def crepBody417_21 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64])
  (Flapjack.CrepExp.var 1)) crepBody417_20 crepBody417_4

def crepBody417_22 : CrepProg (BitVec 64) :=
.seq crepBody417_11 crepBody417_21

def crepBody417_23 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 232#64)) crepBody417_22 crepBody417_4

def crepBody417_24 : CrepProg (BitVec 64) :=
.seq crepBody417_18 crepBody417_23

def crepBody417_25 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 96#64)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.notLower (Flapjack.CrepExp.const 127#64) (Flapjack.CrepExp.var 4))]) crepBody417_9 crepBody417_24

def crepBody417_26 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 91#64)) crepBody417_7 crepBody417_25

def crepBody417_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 6)

def crepBody417_28 : CrepProg (BitVec 64) :=
.seq crepBody417_27 crepBody417_4

def crepBody417_29 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 5]) crepBody417_28

def crepBody417_30 : CrepProg (BitVec 64) :=
.seq crepBody417_26 crepBody417_29

def crepBody417_31 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 1#64) crepBody417_30

def crepBody417_32 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.loadByte (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3])) crepBody417_31

def crepBody417_33 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 1)) crepBody417_32

def crepBody417_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 2]

def crepBody417_35 : CrepProg (BitVec 64) :=
.seq crepBody417_33 crepBody417_34

def crepBody417_36 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody417_35

def crepBody417_37 : CrepProg (BitVec 64) :=
.seq crepBody417_2 crepBody417_36

def crepBody417_38 : CrepProg (BitVec 64) :=
.seq crepBody417_0 crepBody417_37

def crepBody417_39 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody417_38

def data417 : CrepProg (BitVec 64) := crepBody417_39
def output417 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [99#8, 111#8, 109#8, 112#8, 117#8, 116#8, 101#8, 95#8, 106#8, 117#8, 109#8, 112#8, 100#8, 101#8, 115#8, 116#8, 115#8], [0, 1], crepProgToHOL data417)
end InitECandidate.Proofs.FrontendStages.Crep
