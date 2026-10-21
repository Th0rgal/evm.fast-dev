import InitECandidate.Proofs.FrontendStages.Crep.Translate775
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody791_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 200#64]

def crepBody791_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "memzero" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 200#64]

def crepBody791_2 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody791_1

def crepBody791_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 1]

def crepBody791_4 : CrepProg (BitVec 64) :=
.seq crepBody791_2 crepBody791_3

def crepBody791_5 : CrepProg (BitVec 64) :=
.seq crepBody791_0 crepBody791_4

def crepBody791_6 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody791_5

def data791 : CrepProg (BitVec 64) := crepBody791_6
def output791 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [116#8, 101#8, 95#8, 110#8, 101#8, 119#8], [], crepProgToHOL data791)
end InitECandidate.Proofs.FrontendStages.Crep
