import InitECandidate.Proofs.FrontendStages.Crep.Translate352
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody368_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "scratch_alloc" [Flapjack.CrepExp.const 24#64]

def crepBody368_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "scratch_alloc"
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]]

def crepBody368_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 5)

def crepBody368_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody368_4 : CrepProg (BitVec 64) :=
.seq crepBody368_2 crepBody368_3

def crepBody368_5 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 3) crepBody368_4

def crepBody368_6 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 0#64]) crepBody368_5

def crepBody368_7 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody368_4

def crepBody368_8 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 8#64]) crepBody368_7

def crepBody368_9 : CrepProg (BitVec 64) :=
.seq crepBody368_6 crepBody368_8

def crepBody368_10 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.var 1) crepBody368_4

def crepBody368_11 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 16#64]) crepBody368_10

def crepBody368_12 : CrepProg (BitVec 64) :=
.seq crepBody368_9 crepBody368_11

def crepBody368_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 2]

def crepBody368_14 : CrepProg (BitVec 64) :=
.seq crepBody368_12 crepBody368_13

def crepBody368_15 : CrepProg (BitVec 64) :=
.seq crepBody368_1 crepBody368_14

def crepBody368_16 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody368_15

def crepBody368_17 : CrepProg (BitVec 64) :=
.seq crepBody368_0 crepBody368_16

def crepBody368_18 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody368_17

def data368 : CrepProg (BitVec 64) := crepBody368_18
def output368 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [108#8, 115#8, 116#8, 95#8, 110#8, 101#8, 119#8, 95#8, 115#8, 99#8, 114#8, 97#8, 116#8, 99#8, 104#8], [0, 1], crepProgToHOL data368)
end InitECandidate.Proofs.FrontendStages.Crep
