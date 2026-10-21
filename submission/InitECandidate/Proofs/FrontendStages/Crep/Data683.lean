import InitECandidate.Proofs.FrontendStages.Crep.Translate667
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody683_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "fp2_neg" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody683_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody683_0

def crepBody683_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "fp2_neg"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]]

def crepBody683_3 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody683_2

def crepBody683_4 : CrepProg (BitVec 64) :=
.seq crepBody683_1 crepBody683_3

def crepBody683_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "fp2_neg"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64]]

def crepBody683_6 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody683_5

def crepBody683_7 : CrepProg (BitVec 64) :=
.seq crepBody683_4 crepBody683_6

def crepBody683_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody683_9 : CrepProg (BitVec 64) :=
.seq crepBody683_7 crepBody683_8

def data683 : CrepProg (BitVec 64) := crepBody683_9
def output683 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 112#8, 54#8, 95#8, 110#8, 101#8, 103#8], [0, 1], crepProgToHOL data683)
end InitECandidate.Proofs.FrontendStages.Crep
