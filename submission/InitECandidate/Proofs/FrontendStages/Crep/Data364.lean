import InitECandidate.Proofs.FrontendStages.Crep.Translate348
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody364_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4, 5, 6], none)) "htab_item" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3]

def crepBody364_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "htab_set"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody364_2 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody364_1

def crepBody364_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody364_4 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody364_2 crepBody364_3

def crepBody364_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 7)

def crepBody364_6 : CrepProg (BitVec 64) :=
.seq crepBody364_5 crepBody364_3

def crepBody364_7 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64]) crepBody364_6

def crepBody364_8 : CrepProg (BitVec 64) :=
.seq crepBody364_4 crepBody364_7

def crepBody364_9 : CrepProg (BitVec 64) :=
.seq crepBody364_0 crepBody364_8

def crepBody364_10 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody364_9

def crepBody364_11 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody364_10

def crepBody364_12 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody364_11

def crepBody364_13 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 2)) crepBody364_12

def crepBody364_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody364_15 : CrepProg (BitVec 64) :=
.seq crepBody364_13 crepBody364_14

def crepBody364_16 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody364_15

def crepBody364_17 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 24#64])) crepBody364_16

def data364 : CrepProg (BitVec 64) := crepBody364_17
def output364 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [104#8, 116#8, 97#8, 98#8, 95#8, 117#8, 110#8, 105#8, 111#8, 110#8, 95#8, 105#8, 110#8, 116#8, 111#8], [0, 1], crepProgToHOL data364)
end InitECandidate.Proofs.FrontendStages.Crep
