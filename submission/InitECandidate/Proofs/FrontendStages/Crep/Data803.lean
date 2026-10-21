import InitECandidate.Proofs.FrontendStages.Crep.Translate787
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody803_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 1 (Flapjack.CrepExp.loadGlob 0#5)

def crepBody803_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody803_2 : CrepProg (BitVec 64) :=
.seq crepBody803_0 crepBody803_1

def crepBody803_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.shMem Flapjack.WordMemOp.store8 1
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.const 2688614400#64, Flapjack.CrepExp.const 70#64])

def crepBody803_4 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.var 1) crepBody803_3

def crepBody803_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 2)

def crepBody803_6 : CrepProg (BitVec 64) :=
.seq crepBody803_5 crepBody803_1

def crepBody803_7 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 2#64) crepBody803_6

def crepBody803_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 9#64

def crepBody803_9 : CrepProg (BitVec 64) :=
.seq crepBody803_7 crepBody803_8

def crepBody803_10 : CrepProg (BitVec 64) :=
.seq crepBody803_4 crepBody803_9

def crepBody803_11 : CrepProg (BitVec 64) :=
.seq crepBody803_2 crepBody803_10

def crepBody803_12 : CrepProg (BitVec 64) :=
.call (some (([2]), some ((3#64), crepBody803_11))) ("attempt_l1") ([Flapjack.CrepExp.var 0])

def crepBody803_13 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody803_12

def crepBody803_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody803_15 : CrepProg (BitVec 64) :=
.seq crepBody803_13 crepBody803_14

def crepBody803_16 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody803_15

def data803 : CrepProg (BitVec 64) := crepBody803_16
def output803 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [97#8, 116#8, 116#8, 101#8, 109#8, 112#8, 116#8, 95#8, 108#8, 50#8], [0], crepProgToHOL data803)
end InitECandidate.Proofs.FrontendStages.Crep
