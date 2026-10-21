import InitECandidate.Proofs.FrontendStages.Crep.Translate311
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody327_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 56#64]

def crepBody327_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "memcpy"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 56#64]

def crepBody327_2 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody327_1

def crepBody327_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 1]

def crepBody327_4 : CrepProg (BitVec 64) :=
.seq crepBody327_2 crepBody327_3

def crepBody327_5 : CrepProg (BitVec 64) :=
.seq crepBody327_0 crepBody327_4

def crepBody327_6 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody327_5

def data327 : CrepProg (BitVec 64) := crepBody327_6
def output327 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [97#8, 99#8, 99#8, 116#8, 95#8, 99#8, 111#8, 112#8, 121#8], [0], crepProgToHOL data327)
end InitECandidate.Proofs.FrontendStages.Crep
