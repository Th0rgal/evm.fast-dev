import InitECandidate.Proofs.FrontendStages.Crep.Translate334
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody350_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "get_account_optional" [Flapjack.CrepExp.var 0]

def crepBody350_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody350_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody350_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 1#64)) crepBody350_1 crepBody350_2

def crepBody350_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "acct_is_empty" [Flapjack.CrepExp.var 1]

def crepBody350_5 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody350_1 crepBody350_2

def crepBody350_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody350_7 : CrepProg (BitVec 64) :=
.seq crepBody350_5 crepBody350_6

def crepBody350_8 : CrepProg (BitVec 64) :=
.seq crepBody350_4 crepBody350_7

def crepBody350_9 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody350_8

def crepBody350_10 : CrepProg (BitVec 64) :=
.seq crepBody350_3 crepBody350_9

def crepBody350_11 : CrepProg (BitVec 64) :=
.seq crepBody350_0 crepBody350_10

def crepBody350_12 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody350_11

def data350 : CrepProg (BitVec 64) := crepBody350_12
def output350 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [105#8, 115#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 97#8, 108#8, 105#8, 118#8, 101#8], [0], crepProgToHOL data350)
end InitECandidate.Proofs.FrontendStages.Crep
