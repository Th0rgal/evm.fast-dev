import InitECandidate.Proofs.FrontendStages.Crep.Translate621
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody637_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1#64]

def crepBody637_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody637_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3,
      Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5])
  (Flapjack.CrepExp.const 0#64)) crepBody637_0 crepBody637_1

def crepBody637_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody637_4 : CrepProg (BitVec 64) :=
.seq crepBody637_2 crepBody637_3

def data637 : CrepProg (BitVec 64) := crepBody637_4
def output637 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 108#8, 115#8, 95#8, 102#8, 112#8, 95#8, 105#8, 115#8, 95#8, 122#8, 101#8, 114#8, 111#8], [0, 1, 2, 3, 4, 5], crepProgToHOL data637)
end InitECandidate.Proofs.FrontendStages.Crep
