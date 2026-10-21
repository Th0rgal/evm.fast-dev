import InitECandidate.Proofs.FrontendStages.Crep.Translate440
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody456_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.var 2)

def crepBody456_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody456_2 : CrepProg (BitVec 64) :=
.seq crepBody456_0 crepBody456_1

def crepBody456_3 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody456_2

def crepBody456_4 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 104#64]) crepBody456_3

def crepBody456_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "pc_add" [Flapjack.CrepExp.const 1#64]

def crepBody456_6 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody456_5

def crepBody456_7 : CrepProg (BitVec 64) :=
.seq crepBody456_4 crepBody456_6

def crepBody456_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody456_9 : CrepProg (BitVec 64) :=
.seq crepBody456_7 crepBody456_8

def data456 : CrepProg (BitVec 64) := crepBody456_9
def output456 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 116#8, 111#8, 112#8], [], crepProgToHOL data456)
end InitECandidate.Proofs.FrontendStages.Crep
