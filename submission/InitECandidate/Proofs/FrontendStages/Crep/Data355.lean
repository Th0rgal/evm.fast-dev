import InitECandidate.Proofs.FrontendStages.Crep.Translate339
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody355_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "set_account" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody355_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody355_0

def crepBody355_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "acct_is_empty" [Flapjack.CrepExp.var 1]

def crepBody355_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "destroy_account" [Flapjack.CrepExp.var 0]

def crepBody355_4 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody355_3

def crepBody355_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody355_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody355_4 crepBody355_5

def crepBody355_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody355_8 : CrepProg (BitVec 64) :=
.seq crepBody355_6 crepBody355_7

def crepBody355_9 : CrepProg (BitVec 64) :=
.seq crepBody355_2 crepBody355_8

def crepBody355_10 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody355_9

def crepBody355_11 : CrepProg (BitVec 64) :=
.seq crepBody355_1 crepBody355_10

def data355 : CrepProg (BitVec 64) := crepBody355_11
def output355 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [109#8, 111#8, 100#8, 105#8, 102#8, 121#8, 95#8, 115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 99#8, 111#8, 109#8, 109#8,
    105#8, 116#8], [0, 1], crepProgToHOL data355)
end InitECandidate.Proofs.FrontendStages.Crep
