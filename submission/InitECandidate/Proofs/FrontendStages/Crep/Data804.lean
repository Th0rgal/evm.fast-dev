import InitECandidate.Proofs.FrontendStages.Crep.Translate788
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody804_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 1 (Flapjack.CrepExp.loadGlob 0#5)

def crepBody804_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody804_2 : CrepProg (BitVec 64) :=
.seq crepBody804_0 crepBody804_1

def crepBody804_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.shMem Flapjack.WordMemOp.store8 1
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.const 2688614400#64, Flapjack.CrepExp.const 70#64])

def crepBody804_4 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.var 1) crepBody804_3

def crepBody804_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 2)

def crepBody804_6 : CrepProg (BitVec 64) :=
.seq crepBody804_5 crepBody804_1

def crepBody804_7 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 3#64) crepBody804_6

def crepBody804_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 9#64

def crepBody804_9 : CrepProg (BitVec 64) :=
.seq crepBody804_7 crepBody804_8

def crepBody804_10 : CrepProg (BitVec 64) :=
.seq crepBody804_4 crepBody804_9

def crepBody804_11 : CrepProg (BitVec 64) :=
.seq crepBody804_2 crepBody804_10

def crepBody804_12 : CrepProg (BitVec 64) :=
.call (some (([2]), some ((1#64), crepBody804_11))) ("attempt_l2") ([Flapjack.CrepExp.var 0])

def crepBody804_13 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody804_12

def crepBody804_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody804_15 : CrepProg (BitVec 64) :=
.seq crepBody804_13 crepBody804_14

def crepBody804_16 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody804_15

def data804 : CrepProg (BitVec 64) := crepBody804_16
def output804 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [97#8, 116#8, 116#8, 101#8, 109#8, 112#8, 116#8, 95#8, 108#8, 51#8], [0], crepProgToHOL data804)
end InitECandidate.Proofs.FrontendStages.Crep
