import InitECandidate.Proofs.FrontendStages.Crep.Translate646
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody662_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "memzero" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64]

def crepBody662_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody662_0

def crepBody662_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody662_3 : CrepProg (BitVec 64) :=
.seq crepBody662_1 crepBody662_2

def data662 : CrepProg (BitVec 64) := crepBody662_3
def output662 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [102#8, 112#8, 50#8, 95#8, 115#8, 101#8, 116#8, 95#8, 122#8, 101#8, 114#8, 111#8], [0], crepProgToHOL data662)
end InitECandidate.Proofs.FrontendStages.Crep
