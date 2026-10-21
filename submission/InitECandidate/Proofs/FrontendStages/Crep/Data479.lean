import InitECandidate.Proofs.FrontendStages.Crep.Translate463
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody479_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "sk_make" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody479_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "htab_has"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
          Flapjack.CrepExp.const 176#64]),
    Flapjack.CrepExp.var 2]

def crepBody479_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody479_3 : CrepProg (BitVec 64) :=
.seq crepBody479_1 crepBody479_2

def crepBody479_4 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody479_3

def crepBody479_5 : CrepProg (BitVec 64) :=
.seq crepBody479_0 crepBody479_4

def crepBody479_6 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody479_5

def data479 : CrepProg (BitVec 64) := crepBody479_6
def output479 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [105#8, 115#8, 95#8, 119#8, 97#8, 114#8, 109#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8, 95#8, 107#8,
    101#8, 121#8], [0, 1], crepProgToHOL data479)
end InitECandidate.Proofs.FrontendStages.Crep
