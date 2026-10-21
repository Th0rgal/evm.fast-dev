import InitECandidate.Proofs.FrontendStages.Crep.Translate225
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody241_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "decode_witness_to_mpt" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody241_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call none "mpt_new" [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 2]

def crepBody241_2 : CrepProg (BitVec 64) :=
.seq crepBody241_0 crepBody241_1

def crepBody241_3 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody241_2

def data241 : CrepProg (BitVec 64) := crepBody241_3
def output241 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [109#8, 112#8, 116#8, 95#8, 102#8, 114#8, 111#8, 109#8, 95#8, 119#8, 105#8, 116#8, 110#8, 101#8, 115#8, 115#8], [0, 1, 2], crepProgToHOL data241)
end InitECandidate.Proofs.FrontendStages.Crep
