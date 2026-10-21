import InitECandidate.Proofs.FrontendStages.Crep.Translate380
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody396_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 0]

def crepBody396_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody396_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody396_0 crepBody396_1

def crepBody396_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "add_sat"
  [Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.var 1]]

def crepBody396_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 2]

def crepBody396_5 : CrepProg (BitVec 64) :=
.seq crepBody396_3 crepBody396_4

def crepBody396_6 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody396_5

def crepBody396_7 : CrepProg (BitVec 64) :=
.seq crepBody396_2 crepBody396_6

def crepBody396_8 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 31#64]) crepBody396_7

def data396 : CrepProg (BitVec 64) := crepBody396_8
def output396 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [99#8, 101#8, 105#8, 108#8, 51#8, 50#8], [0], crepProgToHOL data396)
end InitECandidate.Proofs.FrontendStages.Crep
