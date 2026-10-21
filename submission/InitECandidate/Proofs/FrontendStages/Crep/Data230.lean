import InitECandidate.Proofs.FrontendStages.Crep.Translate214
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody230_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "alloc" [Flapjack.CrepExp.const 176#64]

def crepBody230_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2], none)) "memzero" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 176#64]

def crepBody230_2 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody230_1

def crepBody230_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.var 3)

def crepBody230_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody230_5 : CrepProg (BitVec 64) :=
.seq crepBody230_3 crepBody230_4

def crepBody230_6 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 3#64) crepBody230_5

def crepBody230_7 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 0#64]) crepBody230_6

def crepBody230_8 : CrepProg (BitVec 64) :=
.seq crepBody230_2 crepBody230_7

def crepBody230_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 1]

def crepBody230_10 : CrepProg (BitVec 64) :=
.seq crepBody230_8 crepBody230_9

def crepBody230_11 : CrepProg (BitVec 64) :=
.seq crepBody230_0 crepBody230_10

def crepBody230_12 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody230_11

def data230 : CrepProg (BitVec 64) := crepBody230_12
def output230 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [110#8, 111#8, 100#8, 101#8, 95#8, 110#8, 101#8, 119#8, 95#8, 98#8, 114#8, 97#8, 110#8, 99#8, 104#8], [], crepProgToHOL data230)
end InitECandidate.Proofs.FrontendStages.Crep
