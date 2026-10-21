import InitECandidate.Proofs.FrontendStages.Crep.Translate371
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody387_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "update_builder_from_tx" []

def crepBody387_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody387_0

def crepBody387_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "merge_tx_into_block" []

def crepBody387_3 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody387_2

def crepBody387_4 : CrepProg (BitVec 64) :=
.seq crepBody387_1 crepBody387_3

def crepBody387_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody387_6 : CrepProg (BitVec 64) :=
.seq crepBody387_4 crepBody387_5

def data387 : CrepProg (BitVec 64) := crepBody387_6
def output387 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [105#8, 110#8, 99#8, 111#8, 114#8, 112#8, 111#8, 114#8, 97#8, 116#8, 101#8, 95#8, 116#8, 120#8, 95#8, 105#8, 110#8,
    116#8, 111#8, 95#8, 98#8, 108#8, 111#8, 99#8, 107#8], [], crepProgToHOL data387)
end InitECandidate.Proofs.FrontendStages.Crep
