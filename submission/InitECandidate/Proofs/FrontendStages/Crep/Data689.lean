import InitECandidate.Proofs.FrontendStages.Crep.Translate673
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody689_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "heap_mark" []

def crepBody689_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "alloc" [Flapjack.CrepExp.const 576#64]

def crepBody689_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "fp12_set_one" [Flapjack.CrepExp.var 2]

def crepBody689_3 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody689_2

def crepBody689_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "memeq"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 576#64]

def crepBody689_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_release" [Flapjack.CrepExp.var 1]

def crepBody689_6 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody689_5

def crepBody689_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody689_8 : CrepProg (BitVec 64) :=
.seq crepBody689_6 crepBody689_7

def crepBody689_9 : CrepProg (BitVec 64) :=
.seq crepBody689_4 crepBody689_8

def crepBody689_10 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody689_9

def crepBody689_11 : CrepProg (BitVec 64) :=
.seq crepBody689_3 crepBody689_10

def crepBody689_12 : CrepProg (BitVec 64) :=
.seq crepBody689_1 crepBody689_11

def crepBody689_13 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody689_12

def crepBody689_14 : CrepProg (BitVec 64) :=
.seq crepBody689_0 crepBody689_13

def crepBody689_15 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody689_14

def data689 : CrepProg (BitVec 64) := crepBody689_15
def output689 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 112#8, 49#8, 50#8, 95#8, 105#8, 115#8, 95#8, 111#8, 110#8, 101#8], [0], crepProgToHOL data689)
end InitECandidate.Proofs.FrontendStages.Crep
