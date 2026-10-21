import InitECandidate.Proofs.FrontendStages.Crep.Translate368
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody384_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4, 5], none)) "htab_get"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 216#64]),
    Flapjack.CrepExp.var 0]

def crepBody384_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody384_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody384_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody384_1 crepBody384_2

def crepBody384_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "bal_list_remove_idx"
  [Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 1]),
    Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody384_5 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody384_4

def crepBody384_6 : CrepProg (BitVec 64) :=
.seq crepBody384_3 crepBody384_5

def crepBody384_7 : CrepProg (BitVec 64) :=
.seq crepBody384_6 crepBody384_1

def crepBody384_8 : CrepProg (BitVec 64) :=
.seq crepBody384_0 crepBody384_7

def crepBody384_9 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody384_8

def crepBody384_10 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody384_9

def data384 : CrepProg (BitVec 64) := crepBody384_10
def output384 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [98#8, 97#8, 108#8, 95#8, 114#8, 101#8, 109#8, 111#8, 118#8, 101#8, 95#8, 99#8, 104#8, 97#8, 110#8, 103#8, 101#8], [0, 1, 2, 3], crepProgToHOL data384)
end InitECandidate.Proofs.FrontendStages.Crep
