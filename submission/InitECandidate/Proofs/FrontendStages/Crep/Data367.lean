import InitECandidate.Proofs.FrontendStages.Crep.Translate351
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody367_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "alloc" [Flapjack.CrepExp.const 24#64]

def crepBody367_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]]

def crepBody367_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 5)

def crepBody367_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody367_4 : CrepProg (BitVec 64) :=
.seq crepBody367_2 crepBody367_3

def crepBody367_5 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 3) crepBody367_4

def crepBody367_6 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 0#64]) crepBody367_5

def crepBody367_7 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody367_4

def crepBody367_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 8#64]) crepBody367_7

def crepBody367_9 : CrepProg (BitVec 64) :=
.seq crepBody367_6 crepBody367_8

def crepBody367_10 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 1) crepBody367_4

def crepBody367_11 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 16#64]) crepBody367_10

def crepBody367_12 : CrepProg (BitVec 64) :=
.seq crepBody367_9 crepBody367_11

def crepBody367_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 2]

def crepBody367_14 : CrepProg (BitVec 64) :=
.seq crepBody367_12 crepBody367_13

def crepBody367_15 : CrepProg (BitVec 64) :=
.seq crepBody367_1 crepBody367_14

def crepBody367_16 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody367_15

def crepBody367_17 : CrepProg (BitVec 64) :=
.seq crepBody367_0 crepBody367_16

def crepBody367_18 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody367_17

def data367 : CrepProg (BitVec 64) := crepBody367_18
def output367 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [108#8, 115#8, 116#8, 95#8, 110#8, 101#8, 119#8], [0, 1], crepProgToHOL data367)
end InitECandidate.Proofs.FrontendStages.Crep
