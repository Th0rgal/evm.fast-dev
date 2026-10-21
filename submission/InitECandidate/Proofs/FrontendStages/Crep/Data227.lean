import InitECandidate.Proofs.FrontendStages.Crep.Translate211
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody227_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody227_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 3)

def crepBody227_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody227_3 : CrepProg (BitVec 64) :=
.seq crepBody227_1 crepBody227_2

def crepBody227_4 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody227_3

def crepBody227_5 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 0#64]) crepBody227_4

def crepBody227_6 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64]) crepBody227_4

def crepBody227_7 : CrepProg (BitVec 64) :=
.seq crepBody227_5 crepBody227_6

def crepBody227_8 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 16#64]) crepBody227_4

def crepBody227_9 : CrepProg (BitVec 64) :=
.seq crepBody227_7 crepBody227_8

def crepBody227_10 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.var 0) crepBody227_3

def crepBody227_11 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 24#64]) crepBody227_10

def crepBody227_12 : CrepProg (BitVec 64) :=
.seq crepBody227_9 crepBody227_11

def crepBody227_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 1]

def crepBody227_14 : CrepProg (BitVec 64) :=
.seq crepBody227_12 crepBody227_13

def crepBody227_15 : CrepProg (BitVec 64) :=
.seq crepBody227_0 crepBody227_14

def crepBody227_16 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody227_15

def data227 : CrepProg (BitVec 64) := crepBody227_16
def output227 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [110#8, 111#8, 100#8, 101#8, 95#8, 110#8, 101#8, 119#8, 95#8, 104#8, 97#8, 115#8, 104#8, 101#8, 100#8], [0], crepProgToHOL data227)
end InitECandidate.Proofs.FrontendStages.Crep
