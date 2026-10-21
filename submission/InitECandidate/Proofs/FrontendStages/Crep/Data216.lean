import InitECandidate.Proofs.FrontendStages.Crep.Translate200
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody216_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody216_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody216_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 120#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody216_0 crepBody216_1

def crepBody216_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 8#64]

def crepBody216_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 3)

def crepBody216_5 : CrepProg (BitVec 64) :=
.seq crepBody216_4 crepBody216_1

def crepBody216_6 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.var 1) crepBody216_5

def crepBody216_7 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 120#64]) crepBody216_6

def crepBody216_8 : CrepProg (BitVec 64) :=
.seq crepBody216_3 crepBody216_7

def crepBody216_9 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody216_8

def crepBody216_10 : CrepProg (BitVec 64) :=
.seq crepBody216_2 crepBody216_9

def crepBody216_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "memzero"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 120#64]),
    Flapjack.CrepExp.const 8#64]

def crepBody216_12 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody216_11

def crepBody216_13 : CrepProg (BitVec 64) :=
.seq crepBody216_10 crepBody216_12

def crepBody216_14 : CrepProg (BitVec 64) :=
.seq crepBody216_13 crepBody216_0

def data216 : CrepProg (BitVec 64) := crepBody216_14
def output216 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [104#8, 101#8, 97#8, 100#8, 101#8, 114#8, 95#8, 105#8, 110#8, 105#8, 116#8], [], crepProgToHOL data216)
end InitECandidate.Proofs.FrontendStages.Crep
