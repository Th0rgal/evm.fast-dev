import InitECandidate.Proofs.FrontendStages.Crep.Translate672
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody688_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "fp6_set_one" [Flapjack.CrepExp.var 0]

def crepBody688_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody688_0

def crepBody688_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "fp6_set_zero"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 288#64]]

def crepBody688_3 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody688_2

def crepBody688_4 : CrepProg (BitVec 64) :=
.seq crepBody688_1 crepBody688_3

def crepBody688_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody688_6 : CrepProg (BitVec 64) :=
.seq crepBody688_4 crepBody688_5

def data688 : CrepProg (BitVec 64) := crepBody688_6
def output688 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [102#8, 112#8, 49#8, 50#8, 95#8, 115#8, 101#8, 116#8, 95#8, 111#8, 110#8, 101#8], [0], crepProgToHOL data688)
end InitECandidate.Proofs.FrontendStages.Crep
