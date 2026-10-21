import InitECandidate.Proofs.FrontendStages.Crep.Translate323
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody339_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "get_account_optional" [Flapjack.CrepExp.var 0]

def crepBody339_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "acct_empty" []

def crepBody339_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody339_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 1#64)) crepBody339_1 crepBody339_2

def crepBody339_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 1]

def crepBody339_5 : CrepProg (BitVec 64) :=
.seq crepBody339_3 crepBody339_4

def crepBody339_6 : CrepProg (BitVec 64) :=
.seq crepBody339_0 crepBody339_5

def crepBody339_7 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody339_6

def data339 : CrepProg (BitVec 64) := crepBody339_7
def output339 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [103#8, 101#8, 116#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8], [0], crepProgToHOL data339)
end InitECandidate.Proofs.FrontendStages.Crep
