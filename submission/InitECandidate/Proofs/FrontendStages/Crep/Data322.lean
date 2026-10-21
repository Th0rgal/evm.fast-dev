import InitECandidate.Proofs.FrontendStages.Crep.Translate306
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody322_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 16#64])]

def data322 : CrepProg (BitVec 64) := crepBody322_0
def output322 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 115#8, 110#8, 97#8, 112#8, 115#8, 104#8, 111#8, 116#8], [], crepProgToHOL data322)
end InitECandidate.Proofs.FrontendStages.Crep
