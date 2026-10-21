import InitECandidate.Proofs.FrontendStages.Crep.Translate515
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody531_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 1 (Flapjack.CrepExp.loadGlob 0#5)

def crepBody531_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody531_2 : CrepProg (BitVec 64) :=
.seq crepBody531_0 crepBody531_1

def crepBody531_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "frame_exception" [Flapjack.CrepExp.var 1]

def crepBody531_4 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody531_3

def crepBody531_5 : CrepProg (BitVec 64) :=
.seq crepBody531_2 crepBody531_4

def crepBody531_6 : CrepProg (BitVec 64) :=
.call (some (([2]), some ((8#64), crepBody531_5))) ("frame_prologue") ([])

def crepBody531_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 4)

def crepBody531_8 : CrepProg (BitVec 64) :=
.seq crepBody531_7 crepBody531_1

def crepBody531_9 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 1#64) crepBody531_8

def crepBody531_10 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 288#64]),
    Flapjack.CrepExp.const 32#64]) crepBody531_9

def crepBody531_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 0#64)) crepBody531_10 crepBody531_1

def crepBody531_12 : CrepProg (BitVec 64) :=
.seq crepBody531_6 crepBody531_11

def crepBody531_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody531_14 : CrepProg (BitVec 64) :=
.seq crepBody531_12 crepBody531_13

def crepBody531_15 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody531_14

def crepBody531_16 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody531_15

def data531 : CrepProg (BitVec 64) := crepBody531_16
def output531 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 115#8, 116#8, 97#8, 114#8, 116#8], [], crepProgToHOL data531)
end InitECandidate.Proofs.FrontendStages.Crep
