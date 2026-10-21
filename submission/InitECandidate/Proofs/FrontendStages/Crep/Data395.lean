import InitECandidate.Proofs.FrontendStages.Crep.Translate379
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody395_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 18446744073709551615#64]

def crepBody395_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody395_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 0)) crepBody395_0 crepBody395_1

def crepBody395_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 2]

def crepBody395_4 : CrepProg (BitVec 64) :=
.seq crepBody395_2 crepBody395_3

def crepBody395_5 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]) crepBody395_4

def data395 : CrepProg (BitVec 64) := crepBody395_5
def output395 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [97#8, 100#8, 100#8, 95#8, 115#8, 97#8, 116#8], [0, 1], crepProgToHOL data395)
end InitECandidate.Proofs.FrontendStages.Crep
