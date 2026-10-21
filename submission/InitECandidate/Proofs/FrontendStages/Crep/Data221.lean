import InitECandidate.Proofs.FrontendStages.Crep.Translate205
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody221_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "mpt_fail" [Flapjack.CrepExp.const 5#64]

def crepBody221_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody221_0

def crepBody221_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody221_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody221_1 crepBody221_2

def crepBody221_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 1]]

def crepBody221_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.var 6)
  (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 15#64])

def crepBody221_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.const 1#64)

def crepBody221_7 : CrepProg (BitVec 64) :=
.seq crepBody221_6 crepBody221_2

def crepBody221_8 : CrepProg (BitVec 64) :=
.seq crepBody221_5 crepBody221_7

def crepBody221_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody221_8 crepBody221_2

def crepBody221_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "key_to_nibbles"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 1#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7]]

def crepBody221_11 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody221_10

def crepBody221_12 : CrepProg (BitVec 64) :=
.seq crepBody221_9 crepBody221_11

def crepBody221_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 6,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.var 7,
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
          [Flapjack.CrepExp.const 2#64,
            Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 1#64]]],
    Flapjack.CrepExp.var 4]

def crepBody221_14 : CrepProg (BitVec 64) :=
.seq crepBody221_12 crepBody221_13

def crepBody221_15 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody221_14

def crepBody221_16 : CrepProg (BitVec 64) :=
.seq crepBody221_4 crepBody221_15

def crepBody221_17 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody221_16

def crepBody221_18 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64]) crepBody221_17

def crepBody221_19 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 1#64),
    Flapjack.CrepExp.const 1#64]) crepBody221_18

def crepBody221_20 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 4#64)) crepBody221_19

def crepBody221_21 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.loadByte (Flapjack.CrepExp.var 0)) crepBody221_20

def crepBody221_22 : CrepProg (BitVec 64) :=
.seq crepBody221_3 crepBody221_21

def data221 : CrepProg (BitVec 64) := crepBody221_22
def output221 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [99#8, 111#8, 109#8, 112#8, 97#8, 99#8, 116#8, 95#8, 116#8, 111#8, 95#8, 110#8, 105#8, 98#8, 98#8, 108#8, 101#8,
    115#8], [0, 1], crepProgToHOL data221)
end InitECandidate.Proofs.FrontendStages.Crep
