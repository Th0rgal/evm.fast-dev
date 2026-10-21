import InitECandidate.Proofs.FrontendStages.Crep.Translate226
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody242_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "keccak256"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 152#64])]

def crepBody242_1 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody242_0

def crepBody242_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc" [Flapjack.CrepExp.const 64#64]

def crepBody242_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "key_to_nibbles"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 152#64]),
    Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.var 3]

def crepBody242_4 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody242_3

def crepBody242_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 64#64]

def crepBody242_6 : CrepProg (BitVec 64) :=
.seq crepBody242_4 crepBody242_5

def crepBody242_7 : CrepProg (BitVec 64) :=
.seq crepBody242_2 crepBody242_6

def crepBody242_8 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody242_7

def crepBody242_9 : CrepProg (BitVec 64) :=
.seq crepBody242_1 crepBody242_8

def crepBody242_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody242_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 8#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody242_9 crepBody242_10

def crepBody242_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 2]]

def crepBody242_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "key_to_nibbles"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody242_14 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody242_13

def crepBody242_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 3,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.const 2#64, Flapjack.CrepExp.var 2]]

def crepBody242_16 : CrepProg (BitVec 64) :=
.seq crepBody242_14 crepBody242_15

def crepBody242_17 : CrepProg (BitVec 64) :=
.seq crepBody242_12 crepBody242_16

def crepBody242_18 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody242_17

def crepBody242_19 : CrepProg (BitVec 64) :=
.seq crepBody242_11 crepBody242_18

def data242 : CrepProg (BitVec 64) := crepBody242_19
def output242 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [109#8, 112#8, 116#8, 95#8, 110#8, 105#8, 98#8, 98#8, 108#8, 101#8, 95#8, 107#8, 101#8, 121#8], [0, 1, 2], crepProgToHOL data242)
end InitECandidate.Proofs.FrontendStages.Crep
