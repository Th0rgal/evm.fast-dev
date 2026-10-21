import InitECandidate.Proofs.FrontendStages.Crep.Translate684
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody700_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "memcpy"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 144#64]

def crepBody700_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody700_0

def crepBody700_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody700_3 : CrepProg (BitVec 64) :=
.seq crepBody700_1 crepBody700_2

def data700 : CrepProg (BitVec 64) := crepBody700_3
def output700 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 99#8, 111#8, 112#8, 121#8], [0, 1], crepProgToHOL data700)
end InitECandidate.Proofs.FrontendStages.Crep
