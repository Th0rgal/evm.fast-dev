import InitECandidate.Proofs.FrontendStages.Crep.Translate793
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody809_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 1 (Flapjack.CrepExp.loadGlob 0#5)

def crepBody809_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody809_2 : CrepProg (BitVec 64) :=
.seq crepBody809_0 crepBody809_1

def crepBody809_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 2 (Flapjack.CrepExp.const 0#64)

def crepBody809_4 : CrepProg (BitVec 64) :=
.seq crepBody809_3 crepBody809_1

def crepBody809_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 4)

def crepBody809_6 : CrepProg (BitVec 64) :=
.seq crepBody809_5 crepBody809_1

def crepBody809_7 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.var 1) crepBody809_6

def crepBody809_8 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 536#64]) crepBody809_7

def crepBody809_9 : CrepProg (BitVec 64) :=
.seq crepBody809_4 crepBody809_8

def crepBody809_10 : CrepProg (BitVec 64) :=
.seq crepBody809_2 crepBody809_9

def crepBody809_11 : CrepProg (BitVec 64) :=
.call (some (([3]), some ((9#64), crepBody809_10))) ("attempt_l7") ([Flapjack.CrepExp.var 0])

def crepBody809_12 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody809_11

def crepBody809_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 2]

def crepBody809_14 : CrepProg (BitVec 64) :=
.seq crepBody809_12 crepBody809_13

def crepBody809_15 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 1#64) crepBody809_14

def crepBody809_16 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody809_15

def data809 : CrepProg (BitVec 64) := crepBody809_16
def output809 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [118#8, 101#8, 114#8, 105#8, 102#8, 121#8, 95#8, 115#8, 116#8, 97#8, 116#8, 101#8, 108#8, 101#8, 115#8, 115#8, 95#8,
    110#8, 101#8, 119#8, 95#8, 112#8, 97#8, 121#8, 108#8, 111#8, 97#8, 100#8], [0], crepProgToHOL data809)
end InitECandidate.Proofs.FrontendStages.Crep
