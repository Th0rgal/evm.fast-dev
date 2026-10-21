import InitECandidate.Proofs.FrontendStages.Crep.Translate545
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody561_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1352829926#64]

def crepBody561_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody561_2 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 16#64)) crepBody561_0 crepBody561_1

def crepBody561_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1548603684#64]

def crepBody561_4 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 32#64)) crepBody561_3 crepBody561_1

def crepBody561_5 : CrepProg (BitVec 64) :=
.seq crepBody561_2 crepBody561_4

def crepBody561_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 1836072691#64]

def crepBody561_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 48#64)) crepBody561_6 crepBody561_1

def crepBody561_8 : CrepProg (BitVec 64) :=
.seq crepBody561_5 crepBody561_7

def crepBody561_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 2053994217#64]

def crepBody561_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 64#64)) crepBody561_9 crepBody561_1

def crepBody561_11 : CrepProg (BitVec 64) :=
.seq crepBody561_8 crepBody561_10

def crepBody561_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody561_13 : CrepProg (BitVec 64) :=
.seq crepBody561_11 crepBody561_12

def data561 : CrepProg (BitVec 64) := crepBody561_13
def output561 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [114#8, 109#8, 100#8, 95#8, 107#8, 112#8], [0], crepProgToHOL data561)
end InitECandidate.Proofs.FrontendStages.Crep
