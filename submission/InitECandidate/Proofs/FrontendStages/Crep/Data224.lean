import InitECandidate.Proofs.FrontendStages.Crep.Translate208
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody224_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3]]

def crepBody224_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "memcpy"
  [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody224_2 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody224_1

def crepBody224_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 1], Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.var 3]

def crepBody224_4 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody224_3

def crepBody224_5 : CrepProg (BitVec 64) :=
.seq crepBody224_2 crepBody224_4

def crepBody224_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 4]

def crepBody224_7 : CrepProg (BitVec 64) :=
.seq crepBody224_5 crepBody224_6

def crepBody224_8 : CrepProg (BitVec 64) :=
.seq crepBody224_0 crepBody224_7

def crepBody224_9 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody224_8

def data224 : CrepProg (BitVec 64) := crepBody224_9
def output224 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [110#8, 105#8, 98#8, 98#8, 108#8, 101#8, 115#8, 95#8, 99#8, 111#8, 110#8, 99#8, 97#8, 116#8], [0, 1, 2, 3], crepProgToHOL data224)
end InitECandidate.Proofs.FrontendStages.Crep
