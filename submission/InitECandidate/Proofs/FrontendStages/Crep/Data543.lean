import InitECandidate.Proofs.FrontendStages.Crep.Translate527
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody543_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "htab_truncate"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 168#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 264#64])]

def crepBody543_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody543_0

def crepBody543_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "htab_truncate"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 176#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 272#64])]

def crepBody543_3 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody543_2

def crepBody543_4 : CrepProg (BitVec 64) :=
.seq crepBody543_1 crepBody543_3

def crepBody543_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody543_6 : CrepProg (BitVec 64) :=
.seq crepBody543_4 crepBody543_5

def data543 : CrepProg (BitVec 64) := crepBody543_6
def output543 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [114#8, 111#8, 108#8, 108#8, 98#8, 97#8, 99#8, 107#8, 95#8, 99#8, 104#8, 105#8, 108#8, 100#8, 95#8, 97#8, 99#8, 99#8,
    101#8, 115#8, 115#8], [0], crepProgToHOL data543)
end InitECandidate.Proofs.FrontendStages.Crep
