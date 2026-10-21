import InitECandidate.Proofs.FrontendStages.Crep.Translate314
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody330_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1, 2, 3], none)) "ws_account_leaf" [Flapjack.CrepExp.var 0]

def crepBody330_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody330_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody330_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody330_1 crepBody330_2

def crepBody330_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 56#64]

def crepBody330_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "decode_account_from_leaf"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4]

def crepBody330_6 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody330_5

def crepBody330_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 4]

def crepBody330_8 : CrepProg (BitVec 64) :=
.seq crepBody330_6 crepBody330_7

def crepBody330_9 : CrepProg (BitVec 64) :=
.seq crepBody330_4 crepBody330_8

def crepBody330_10 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody330_9

def crepBody330_11 : CrepProg (BitVec 64) :=
.seq crepBody330_3 crepBody330_10

def crepBody330_12 : CrepProg (BitVec 64) :=
.seq crepBody330_0 crepBody330_11

def crepBody330_13 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody330_12

def crepBody330_14 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody330_13

def crepBody330_15 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody330_14

def data330 : CrepProg (BitVec 64) := crepBody330_15
def output330 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [119#8, 115#8, 95#8, 103#8, 101#8, 116#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 111#8, 112#8,
    116#8, 105#8, 111#8, 110#8, 97#8, 108#8], [0], crepProgToHOL data330)
end InitECandidate.Proofs.FrontendStages.Crep
