import InitECandidate.Proofs.FrontendStages.Crep.Translate544
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody560_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody560_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody560_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 16#64)) crepBody560_0 crepBody560_1

def crepBody560_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1518500249#64]

def crepBody560_4 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 32#64)) crepBody560_3 crepBody560_1

def crepBody560_5 : CrepProg (BitVec 64) :=
.seq crepBody560_2 crepBody560_4

def crepBody560_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1859775393#64]

def crepBody560_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 48#64)) crepBody560_6 crepBody560_1

def crepBody560_8 : CrepProg (BitVec 64) :=
.seq crepBody560_5 crepBody560_7

def crepBody560_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 2400959708#64]

def crepBody560_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 64#64)) crepBody560_9 crepBody560_1

def crepBody560_11 : CrepProg (BitVec 64) :=
.seq crepBody560_8 crepBody560_10

def crepBody560_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 2840853838#64]

def crepBody560_13 : CrepProg (BitVec 64) :=
.seq crepBody560_11 crepBody560_12

def data560 : CrepProg (BitVec 64) := crepBody560_13
def output560 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [114#8, 109#8, 100#8, 95#8, 107#8], [0], crepProgToHOL data560)
end InitECandidate.Proofs.FrontendStages.Crep
