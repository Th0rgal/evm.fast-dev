import InitECandidate.Proofs.FrontendStages.Crep.Translate786
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody802_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 1 (Flapjack.CrepExp.loadGlob 0#5)

def crepBody802_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody802_2 : CrepProg (BitVec 64) :=
.seq crepBody802_0 crepBody802_1

def crepBody802_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.shMem Flapjack.WordMemOp.store8 1
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.const 2688614400#64, Flapjack.CrepExp.const 70#64])

def crepBody802_4 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.var 1) crepBody802_3

def crepBody802_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 2)

def crepBody802_6 : CrepProg (BitVec 64) :=
.seq crepBody802_5 crepBody802_1

def crepBody802_7 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 1#64) crepBody802_6

def crepBody802_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 9#64

def crepBody802_9 : CrepProg (BitVec 64) :=
.seq crepBody802_7 crepBody802_8

def crepBody802_10 : CrepProg (BitVec 64) :=
.seq crepBody802_4 crepBody802_9

def crepBody802_11 : CrepProg (BitVec 64) :=
.seq crepBody802_2 crepBody802_10

def crepBody802_12 : CrepProg (BitVec 64) :=
.call (some (([2]), some ((4#64), crepBody802_11))) ("run_attempt") ([Flapjack.CrepExp.var 0])

def crepBody802_13 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody802_12

def crepBody802_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody802_15 : CrepProg (BitVec 64) :=
.seq crepBody802_13 crepBody802_14

def crepBody802_16 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody802_15

def data802 : CrepProg (BitVec 64) := crepBody802_16
def output802 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [97#8, 116#8, 116#8, 101#8, 109#8, 112#8, 116#8, 95#8, 108#8, 49#8], [0], crepProgToHOL data802)
end InitECandidate.Proofs.FrontendStages.Crep
