import InitECandidate.Proofs.FrontendStages.Crep.Translate412
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody428_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "warm_address" [Flapjack.CrepExp.var 0]

def crepBody428_1 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody428_0

def crepBody428_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody428_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 3000#64)) crepBody428_1 crepBody428_2

def crepBody428_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody428_5 : CrepProg (BitVec 64) :=
.seq crepBody428_3 crepBody428_4

def data428 : CrepProg (BitVec 64) := crepBody428_5
def output428 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [119#8, 97#8, 114#8, 109#8, 95#8, 97#8, 102#8, 116#8, 101#8, 114#8, 95#8, 99#8, 104#8, 97#8, 114#8, 103#8, 101#8], [0, 1], crepProgToHOL data428)
end InitECandidate.Proofs.FrontendStages.Crep
