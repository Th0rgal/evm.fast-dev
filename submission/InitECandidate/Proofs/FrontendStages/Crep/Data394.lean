import InitECandidate.Proofs.FrontendStages.Crep.Translate378
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody394_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 18446744073709551615#64]

def crepBody394_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody394_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.op Flapjack.BinOp.or [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3])
  (Flapjack.CrepExp.const 0#64)) crepBody394_0 crepBody394_1

def crepBody394_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 0]

def crepBody394_4 : CrepProg (BitVec 64) :=
.seq crepBody394_2 crepBody394_3

def data394 : CrepProg (BitVec 64) := crepBody394_4
def output394 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [115#8, 97#8, 116#8, 95#8, 119#8, 111#8, 114#8, 100#8], [0, 1, 2, 3], crepProgToHOL data394)
end InitECandidate.Proofs.FrontendStages.Crep
