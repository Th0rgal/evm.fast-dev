import InitECandidate.Proofs.FrontendStages.Crep.Translate411
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody427_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "is_warm_address" [Flapjack.CrepExp.var 0]

def crepBody427_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 100#64]

def crepBody427_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody427_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 0#64)) crepBody427_1 crepBody427_2

def crepBody427_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 3000#64]

def crepBody427_5 : CrepProg (BitVec 64) :=
.seq crepBody427_3 crepBody427_4

def crepBody427_6 : CrepProg (BitVec 64) :=
.seq crepBody427_0 crepBody427_5

def crepBody427_7 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody427_6

def data427 : CrepProg (BitVec 64) := crepBody427_7
def output427 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [97#8, 99#8, 99#8, 101#8, 115#8, 115#8, 95#8, 103#8, 97#8, 115#8, 95#8, 99#8, 111#8, 115#8, 116#8], [0], crepProgToHOL data427)
end InitECandidate.Proofs.FrontendStages.Crep
