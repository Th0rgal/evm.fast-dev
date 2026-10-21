import InitECandidate.Proofs.FrontendStages.Crep.Translate697
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody713_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "fp2_copy" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody713_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody713_0

def crepBody713_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "fp2_copy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 192#64]]

def crepBody713_3 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody713_2

def crepBody713_4 : CrepProg (BitVec 64) :=
.seq crepBody713_1 crepBody713_3

def crepBody713_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody713_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.var 1)) crepBody713_4 crepBody713_5

def crepBody713_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "fp2_neg"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 96#64],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 96#64]]

def crepBody713_8 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody713_7

def crepBody713_9 : CrepProg (BitVec 64) :=
.seq crepBody713_6 crepBody713_8

def crepBody713_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody713_11 : CrepProg (BitVec 64) :=
.seq crepBody713_9 crepBody713_10

def data713 : CrepProg (BitVec 64) := crepBody713_11
def output713 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 110#8, 101#8, 103#8], [0, 1], crepProgToHOL data713)
end InitECandidate.Proofs.FrontendStages.Crep
