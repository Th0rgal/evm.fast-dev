import InitECandidate.Proofs.FrontendStages.Crep.Translate666
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody682_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "fp2_sub"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]

def crepBody682_1 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody682_0

def crepBody682_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "fp2_sub"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 96#64]]

def crepBody682_3 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody682_2

def crepBody682_4 : CrepProg (BitVec 64) :=
.seq crepBody682_1 crepBody682_3

def crepBody682_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "fp2_sub"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 192#64]]

def crepBody682_6 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody682_5

def crepBody682_7 : CrepProg (BitVec 64) :=
.seq crepBody682_4 crepBody682_6

def crepBody682_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody682_9 : CrepProg (BitVec 64) :=
.seq crepBody682_7 crepBody682_8

def data682 : CrepProg (BitVec 64) := crepBody682_9
def output682 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 112#8, 54#8, 95#8, 115#8, 117#8, 98#8], [0, 1, 2], crepProgToHOL data682)
end InitECandidate.Proofs.FrontendStages.Crep
