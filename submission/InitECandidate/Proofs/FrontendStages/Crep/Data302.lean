import InitECandidate.Proofs.FrontendStages.Crep.Translate286
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody302_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "heap_mark" []

def crepBody302_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6], none)) "tx_encode_generic"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2]

def crepBody302_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "keccak256"
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 3]

def crepBody302_3 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody302_2

def crepBody302_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "heap_release" [Flapjack.CrepExp.var 4]

def crepBody302_5 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody302_4

def crepBody302_6 : CrepProg (BitVec 64) :=
.seq crepBody302_3 crepBody302_5

def crepBody302_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody302_8 : CrepProg (BitVec 64) :=
.seq crepBody302_6 crepBody302_7

def crepBody302_9 : CrepProg (BitVec 64) :=
.seq crepBody302_1 crepBody302_8

def crepBody302_10 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody302_9

def crepBody302_11 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody302_10

def crepBody302_12 : CrepProg (BitVec 64) :=
.seq crepBody302_0 crepBody302_11

def crepBody302_13 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody302_12

def data302 : CrepProg (BitVec 64) := crepBody302_13
def output302 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [116#8, 120#8, 95#8, 115#8, 105#8, 103#8, 110#8, 105#8, 110#8, 103#8, 95#8, 104#8, 97#8, 115#8, 104#8, 95#8, 109#8,
    111#8, 100#8, 101#8], [0, 1, 2, 3], crepProgToHOL data302)
end InitECandidate.Proofs.FrontendStages.Crep
