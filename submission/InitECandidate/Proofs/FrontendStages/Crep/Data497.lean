import InitECandidate.Proofs.FrontendStages.Crep.Translate481
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody497_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "get_account" [Flapjack.CrepExp.var 0]

def crepBody497_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3], none)) "get_code"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.var 0]

def crepBody497_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody497_3 : CrepProg (BitVec 64) :=
.seq crepBody497_1 crepBody497_2

def crepBody497_4 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody497_3

def crepBody497_5 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody497_4

def crepBody497_6 : CrepProg (BitVec 64) :=
.seq crepBody497_0 crepBody497_5

def crepBody497_7 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody497_6

def data497 : CrepProg (BitVec 64) := crepBody497_7
def output497 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [101#8, 120#8, 116#8, 95#8, 99#8, 111#8, 100#8, 101#8, 95#8, 111#8, 102#8], [0], crepProgToHOL data497)
end InitECandidate.Proofs.FrontendStages.Crep
