import InitECandidate.Proofs.FrontendStages.Crep.Translate404
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody420_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "scratch_alloc" [Flapjack.CrepExp.const 176#64]

def crepBody420_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "memzero" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 176#64]

def crepBody420_2 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody420_1

def crepBody420_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 1]

def crepBody420_4 : CrepProg (BitVec 64) :=
.seq crepBody420_2 crepBody420_3

def crepBody420_5 : CrepProg (BitVec 64) :=
.seq crepBody420_0 crepBody420_4

def crepBody420_6 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody420_5

def data420 : CrepProg (BitVec 64) := crepBody420_6
def output420 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [109#8, 115#8, 103#8, 95#8, 110#8, 101#8, 119#8, 95#8, 115#8, 99#8, 114#8, 97#8, 116#8, 99#8, 104#8], [], crepProgToHOL data420)
end InitECandidate.Proofs.FrontendStages.Crep
