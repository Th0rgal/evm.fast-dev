import InitECandidate.Proofs.FrontendStages.Crep.Translate521
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody537_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "set_delegation" []

def crepBody537_1 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody537_0

def crepBody537_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "frame_state_gas_used"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64])]

def crepBody537_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 5)

def crepBody537_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody537_5 : CrepProg (BitVec 64) :=
.seq crepBody537_3 crepBody537_4

def crepBody537_6 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 3) crepBody537_5

def crepBody537_7 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 200#64]) crepBody537_6

def crepBody537_8 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 72#64])) crepBody537_5

def crepBody537_9 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64]) crepBody537_8

def crepBody537_10 : CrepProg (BitVec 64) :=
.seq crepBody537_7 crepBody537_9

def crepBody537_11 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody537_5

def crepBody537_12 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 192#64]) crepBody537_11

def crepBody537_13 : CrepProg (BitVec 64) :=
.seq crepBody537_10 crepBody537_12

def crepBody537_14 : CrepProg (BitVec 64) :=
.seq crepBody537_2 crepBody537_13

def crepBody537_15 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody537_14

def crepBody537_16 : CrepProg (BitVec 64) :=
.seq crepBody537_1 crepBody537_15

def crepBody537_17 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 152#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody537_16 crepBody537_4

def crepBody537_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "prepare_dispatch" []

def crepBody537_19 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody537_18

def crepBody537_20 : CrepProg (BitVec 64) :=
.seq crepBody537_17 crepBody537_19

def crepBody537_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody537_22 : CrepProg (BitVec 64) :=
.seq crepBody537_20 crepBody537_21

def crepBody537_23 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64])) crepBody537_22

def crepBody537_24 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
      Flapjack.CrepExp.const 112#64])) crepBody537_23

def data537 : CrepProg (BitVec 64) := crepBody537_24
def output537 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [100#8, 101#8, 112#8, 116#8, 104#8, 48#8, 95#8, 112#8, 114#8, 101#8, 112#8, 97#8, 114#8, 101#8], [], crepProgToHOL data537)
end InitECandidate.Proofs.FrontendStages.Crep
