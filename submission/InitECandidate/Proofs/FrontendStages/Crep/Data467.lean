import InitECandidate.Proofs.FrontendStages.Crep.Translate451
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody467_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3, 4], none)) "stack_pop" []

def crepBody467_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "charge_gas" [Flapjack.CrepExp.const 2#64]

def crepBody467_2 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody467_1

def crepBody467_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody467_4 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody467_3

def crepBody467_5 : CrepProg (BitVec 64) :=
.seq crepBody467_2 crepBody467_4

def crepBody467_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody467_7 : CrepProg (BitVec 64) :=
.seq crepBody467_5 crepBody467_6

def crepBody467_8 : CrepProg (BitVec 64) :=
.seq crepBody467_0 crepBody467_7

def crepBody467_9 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody467_8

def crepBody467_10 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody467_9

def crepBody467_11 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody467_10

def crepBody467_12 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody467_11

def data467 : CrepProg (BitVec 64) := crepBody467_12
def output467 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 112#8, 111#8, 112#8], [], crepProgToHOL data467)
end InitECandidate.Proofs.FrontendStages.Crep
